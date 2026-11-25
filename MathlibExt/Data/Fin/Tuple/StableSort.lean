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
# Actual successive stable sorting

Sorting the original first labels, then the labels on the sorted positions,
is exactly sorting the combined original lexicographic labels. The pair of
original labelings is in bijection with a labeling in the product
alphabet. These statements use the native exact sorting criterion and do
not supply a permutation-composition certificate.
-/

@[expose] public section
noncomputable section

namespace Tuple

variable {n : ℕ} {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- An actual strictly increasing change of alphabet preserves the original stable sorting permutation. -/
theorem sort_comp_strictMono (f : Fin n → α) (g : α → β) (hg : StrictMono g) :
    sort (g ∘ f) = sort f := by
  apply Eq.symm
  apply eq_sort_iff.mpr
  obtain ⟨hmono, htie⟩ := (eq_sort_iff).mp (rfl : sort f = sort f)
  refine ⟨hg.monotone.comp hmono, ?_⟩
  intro i j hij h
  exact htie (i := i) (j := j) hij (hg.injective h)

/-- The original combined labels, with second-stage labels first in the lexicographic order. -/
def successiveStableLabels (f : Fin n → α) (g : Fin n → β) : Fin n → β ×ₗ α :=
  fun i => toLex (g ((sort f).symm i), f i)

/-- The product of the original two sorting permutations is the sorting permutation of the actual combined labels. -/
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

/-- The original two labelings are in bijection with their original combined labels. -/
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

/-- The original finite product alphabet, in lexicographic order, is strictly ordered by its native flattening. -/
theorem strictMono_finProdFinEquiv (a b : ℕ) :
    StrictMono (fun z : Fin a ×ₗ Fin b => (finProdFinEquiv : Fin a × Fin b ≃ Fin (a * b)) (ofLex z)) := by
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

/-- The actual product alphabet bijection after native flattening. -/
def successiveStableFinLabelsEquiv (n a b : ℕ) :
    (Fin n → Fin a) × (Fin n → Fin b) ≃ (Fin n → Fin (b * a)) :=
  (successiveStableLabelsEquiv n (Fin a) (Fin b)).trans
    (Equiv.piCongrRight (fun _ =>
      (show Fin b ×ₗ Fin a ≃ Fin b × Fin a from Equiv.refl _).trans finProdFinEquiv))

/-- Native flattening keeps the exact product of the two original sorting permutations. -/
theorem sort_successiveStableFinLabelsEquiv (n a b : ℕ)
    (z : (Fin n → Fin a) × (Fin n → Fin b)) :
    sort (successiveStableFinLabelsEquiv n a b z) = sort z.1 * sort z.2 := by
  rw [successiveStableFinLabelsEquiv, Equiv.trans_apply]
  change sort ((fun t : Fin b ×ₗ Fin a => finProdFinEquiv (ofLex t)) ∘
      successiveStableLabels z.1 z.2) = _
  rw [sort_comp_strictMono _ _ (strictMono_finProdFinEquiv b a), sort_successiveStableLabels]

end Tuple
