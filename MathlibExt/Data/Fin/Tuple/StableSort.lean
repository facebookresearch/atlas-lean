/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Successive stable sorting and lexicographic labels

For a finite labeling `f : Fin n → α` in a linearly ordered alphabet, `s_f = Tuple.sort f`
sends sorted positions to input indices. Sorting is stable on equal labels.

If `g : Fin n → β` labels the positions after this first sort, the combined labeling on input
indices is `L(i) = (g(s_f⁻¹ i), f i)` in `β ×ₗ α`, with `β` compared first. Its sorting
permutation is `s_f * s_g`, using permutation multiplication `(p*q)(i) = p(q(i))`.

For alphabets `Fin a` and `Fin b`, the combined labels flatten to `Fin(b*a)` with value `a *
g(s_f⁻¹ i) + f i`, and the same sorting product is preserved.

Reference: Knuth, *The Art of Computer Programming*, Volume 3, Chapter 5.
-/

@[expose] public section
noncomputable section

namespace Tuple

variable {n : ℕ} {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- Let `n : ℕ` and let `α,β` be linearly ordered types. For a labeling `f : Fin n → α`, write
`s_f = Tuple.sort f`, so `s_f` maps sorted positions to input indices and `f ∘ s_f` is
nondecreasing, retaining input-index order on ties. For `g : α → β` with `StrictMono g`,
`Tuple.sort (g ∘ f) = Tuple.sort f`. Both comparisons and equal-label ties are preserved by
this relabeling. -/
theorem sort_comp_strictMono (f : Fin n → α) (g : α → β) (hg : StrictMono g) :
    sort (g ∘ f) = sort f := by
  apply Eq.symm
  apply eq_sort_iff.mpr
  obtain ⟨hmono, htie⟩ := (eq_sort_iff).mp (rfl : sort f = sort f)
  refine ⟨hg.monotone.comp hmono, ?_⟩
  intro i j hij h
  exact htie (i := i) (j := j) hij (hg.injective h)

/-- Let `n : ℕ` and let `α,β` be linearly ordered types. For a labeling `f : Fin n → α`, write
`s_f = Tuple.sort f`, so `s_f` maps sorted positions to input indices and `f ∘ s_f` is
nondecreasing, retaining input-index order on ties. For `g : Fin n → β` on the sorted
positions, `successiveStableLabels f g` is `i ↦ toLex(g(s_f⁻¹ i), f i) : Fin n → β ×ₗ α`. The
second-stage `β` label is primary and the first-stage `α` label is secondary. -/
def successiveStableLabels (f : Fin n → α) (g : Fin n → β) : Fin n → β ×ₗ α :=
  fun i => toLex (g ((sort f).symm i), f i)

/-- Let `n : ℕ` and let `α,β` be linearly ordered types. For a labeling `f : Fin n → α`, write
`s_f = Tuple.sort f`, so `s_f` maps sorted positions to input indices and `f ∘ s_f` is
nondecreasing, retaining input-index order on ties. For `g : Fin n → β`, let `L(i) =
toLex(g(s_f⁻¹ i), f i)`. Then `Tuple.sort L = s_f * Tuple.sort g`, where `(p*q)(i) = p(q(i))`. -/
theorem sort_successiveStableLabels (f : Fin n → α) (g : Fin n → β) :
    sort (successiveStableLabels f g) = sort f * sort g := by
  apply Eq.symm
  apply eq_sort_iff'.mpr
  obtain ⟨hfmono, hftie⟩ := (eq_sort_iff).mp (rfl : sort f = sort f)
  obtain ⟨hgmono, hgtie⟩ := (eq_sort_iff).mp (rfl : sort g = sort g)
  intro i j hij
  simp only [Equiv.trans_apply, Equiv.Perm.mul_apply]
  change (graphEquiv₁ (successiveStableLabels f g) (sort f (sort g i))).val <
    (graphEquiv₁ (successiveStableLabels f g) (sort f (sort g j))).val
  have hgraph (x : Fin n) : (graphEquiv₁ (successiveStableLabels f g) x).val =
      (successiveStableLabels f g x, x) := rfl
  rw [hgraph, hgraph]
  simp only [successiveStableLabels, Equiv.symm_apply_apply]
  apply Prod.Lex.toLex_lt_toLex.mpr
  obtain hgl | hge := (hgmono hij.le).lt_or_eq
  · exact Or.inl (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hgl))
  · have hindex : sort g i < sort g j :=
      lt_of_le_of_ne (hgtie (i := i) (j := j) hij.le hge)
        ((sort g).injective.ne hij.ne)
    obtain hfl | hfe := (hfmono hindex.le).lt_or_eq
    · exact Or.inl (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hge, hfl⟩))
    · exact Or.inr ⟨by exact congrArg toLex (Prod.ext hge hfe),
        lt_of_le_of_ne (hftie (i := sort g i) (j := sort g j) hindex.le hfe)
          ((sort f).injective.ne hindex.ne)⟩

/-- Let `n : ℕ` and let `α,β` be linearly ordered types. For a labeling `f : Fin n → α`, write
`s_f = Tuple.sort f`, so `s_f` maps sorted positions to input indices and `f ∘ s_f` is
nondecreasing, retaining input-index order on ties. The equivalence `(Fin n → α) × (Fin n → β)
≃ (Fin n → β ×ₗ α)` sends `(f,g)` to `i ↦ toLex(g(s_f⁻¹ i), f i)`. Given `h`, its inverse
takes `f(i) = (ofLex(h i)).2` and `g(j) = (ofLex(h(s_f j))).1`. -/
def successiveStableLabelsEquiv (n : ℕ) (α β : Type*) [LinearOrder α] [LinearOrder β] :
    (Fin n → α) × (Fin n → β) ≃ (Fin n → β ×ₗ α) where
  toFun z := successiveStableLabels z.1 z.2
  invFun h := (fun i => (ofLex (h i)).2, fun i => (ofLex (h (sort (fun i => (ofLex (h i)).2) i))).1)
  left_inv z := by
    apply Prod.ext
    · funext i
      rfl
    · funext i
      change z.2 ((sort z.1).symm (sort z.1 i)) = z.2 i
      rw [Equiv.symm_apply_apply]
  right_inv h := by
    funext i
    apply congrArg toLex
    apply Prod.ext
    · change (ofLex (h (sort (fun i => (ofLex (h i)).2)
        ((sort (fun i => (ofLex (h i)).2)).symm i)))).1 = (ofLex (h i)).1
      rw [Equiv.apply_symm_apply]
    · rfl

/-- For `a,b : ℕ`, the map `Fin a ×ₗ Fin b → Fin(a*b)` obtained from `finProdFinEquiv` is strictly
increasing for lexicographic order. Its value on `(i,j)` is the finite index with
natural-number value `b*i.val + j.val`. -/
theorem strictMono_finProdFinEquiv (a b : ℕ) :
    StrictMono (fun z : Fin a ×ₗ Fin b =>
      (finProdFinEquiv : Fin a × Fin b ≃ Fin (a * b)) (ofLex z)) := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
  obtain hfirst | ⟨heq, hsecond⟩ := Prod.Lex.toLex_lt_toLex.mp h
  · change x₂.val + b * x₁.val < y₂.val + b * y₁.val
    change x₁.val < y₁.val at hfirst
    calc
      x₂.val + b * x₁.val < b + b * x₁.val := Nat.add_lt_add_right x₂.isLt _
      _ = b * (x₁.val + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        exact Nat.add_comm _ _
      _ ≤ b * y₁.val := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hfirst)
      _ ≤ y₂.val + b * y₁.val := Nat.le_add_left _ _
  · change x₁ = y₁ at heq
    subst y₁
    change x₂.val + b * x₁.val < y₂.val + b * x₁.val
    exact Nat.add_lt_add_right hsecond _

/-- For `n,a,b : ℕ`, this is the equivalence `(Fin n → Fin a) × (Fin n → Fin b) ≃ (Fin n →
Fin(b*a))`. It sends `(f,g)` to the labeling whose value at input index `i` is
`finProdFinEquiv(g((Tuple.sort f)⁻¹ i), f i)`, with natural-number value `a*g((Tuple.sort f)⁻¹
i).val + (f i).val`. -/
def successiveStableFinLabelsEquiv (n a b : ℕ) :
    (Fin n → Fin a) × (Fin n → Fin b) ≃ (Fin n → Fin (b * a)) :=
  (successiveStableLabelsEquiv n (Fin a) (Fin b)).trans
    (Equiv.piCongrRight (fun _ =>
      (show Fin b ×ₗ Fin a ≃ Fin b × Fin a from Equiv.refl _).trans finProdFinEquiv))

/-- Let `n,a,b : ℕ` and `z = (f,g) : (Fin n → Fin a) × (Fin n → Fin b)`. The flattened combined
labeling satisfies `Tuple.sort (successiveStableFinLabelsEquiv n a b z) = Tuple.sort f *
Tuple.sort g`, using `(p*q)(i) = p(q(i))`. -/
theorem sort_successiveStableFinLabelsEquiv (n a b : ℕ)
    (z : (Fin n → Fin a) × (Fin n → Fin b)) :
    sort (successiveStableFinLabelsEquiv n a b z) = sort z.1 * sort z.2 := by
  rw [successiveStableFinLabelsEquiv, Equiv.trans_apply]
  change sort ((fun t : Fin b ×ₗ Fin a => finProdFinEquiv (ofLex t)) ∘
      successiveStableLabels z.1 z.2) = _
  rw [sort_comp_strictMono _ _ (strictMono_finProdFinEquiv b a), sort_successiveStableLabels]

end Tuple
