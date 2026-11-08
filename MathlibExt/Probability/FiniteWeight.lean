/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Marginals and conditional independence for weights on finite configuration spaces

Variables indexed by a finite type `V` take values in a finite type `α`, so a configuration is a
function `x : V → α`, and a weight is a function `p : (V → α) → ℝ`. A nonnegative weight of
positive total mass is an unnormalized probability distribution; the definitions below are its
marginals and conditional independence. Marginals scale linearly with `p` and `CondIndep` is
unchanged when `p` is multiplied by a nonzero constant, so `p` need not be normalized. The
algebraic results hold for arbitrary real weights.

* `marginal p U x`: the total weight of the configurations that agree with `x` on `U`, the
  (unnormalized) marginal of `p` on the variables in `U` at `x`. `marginal_nonneg`,
  `marginal_anti`: for nonnegative weights marginals are nonnegative and decrease as more
  variables are fixed. `marginal_marginal`: marginalizing `p` to `W` and then to `U ⊆ W` gives the
  `U`-marginal of `p` up to the number of values of the variables outside `W`, so
  `condIndep_marginal_iff`: conditional independence among variables in `W` can be read off the
  `W`-marginal.
* `CondIndep p A B S`: `p(x_A, x_B, x_S) p(x_S) = p(x_A, x_S) p(x_B, x_S)` for every `x`.
  `CondIndep.cond_eq_mul` divides it into the conditional-probability form wherever
  `p(x_S) ≠ 0`; for a nonnegative weight, where `p(x_S) = 0` every marginal fixing `S` vanishes
  (`marginal_anti`) and the equation holds trivially. `condIndep_of_sdiff`: only the variables
  of `A` and `B` outside `S` matter.
* `marginal_mul`: if `f` depends only on the variables in `P` and `g` only on those in `Q`, with
  every variable in `P` or `Q` and `P ∩ Q ⊆ U`, the `U`-marginal of `f * g` is a product of a
  marginal of `f` and a marginal of `g`.
* `condIndep_of_dependsOn` (**factorization criterion**): if `p = f * g` with `f` depending only
  on `P` and `g` only on `Q`, and every variable is in `P` or `Q`, then variables `A` outside `Q`
  and `B` outside `P` are conditionally independent given `P ∩ Q`.

Mathlib's `ProbabilityTheory.CondIndepFun` states conditional independence of random variables
on a measure space through conditional expectations (`condExpKernel`); this file states the
atomwise identity for finite configuration spaces directly, in the form used by graphical models
(`CSLibExt/MachineLearning/GraphicalModels/MarkovRandomField.lean`). The equivalence of the two
for nonnegative weights is not formalized here.
-/

@[expose] public section

namespace MetaMathlibExt.FiniteWeight

open Finset

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]

open Classical in
/-- The (unnormalized) marginal of the weight `p` on the variables in `U`, at the values of `x`:
the total weight of the configurations that agree with `x` on `U`. -/
noncomputable def marginal (p : (V → α) → ℝ) (U : Set V) (x : V → α) : ℝ :=
  ∑ y ∈ univ.filter (fun y : V → α => ∀ v ∈ U, y v = x v), p y

theorem marginal_nonneg {p : (V → α) → ℝ} (hp : ∀ x, 0 ≤ p x) (U : Set V) (x : V → α) :
    0 ≤ marginal p U x := by
  classical
  exact sum_nonneg fun y _ => hp y

/-- For a nonnegative weight, fixing more variables decreases the marginal. -/
theorem marginal_anti {p : (V → α) → ℝ} (hp : ∀ x, 0 ≤ p x) {U U' : Set V} (h : U ⊆ U')
    (x : V → α) : marginal p U' x ≤ marginal p U x := by
  classical
  refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun y _ _ => hp y
  simp only [mem_filter, mem_univ, true_and] at hy ⊢
  exact fun v hv => hy v (h hv)

/-- The variables in `A` and in `B` are **conditionally independent given** those in `S` under
the weight `p`: `p(x_A, x_B, x_S) p(x_S) = p(x_A, x_S) p(x_B, x_S)` for every configuration,
where `p(x_U)` is `marginal p U x`. -/
def CondIndep (p : (V → α) → ℝ) (A B S : Set V) : Prop :=
  ∀ x, marginal p (A ∪ B ∪ S) x * marginal p S x = marginal p (A ∪ S) x * marginal p (B ∪ S) x

/-- Conditional independence in ratio form: where `p(x_S) ≠ 0`,
`p(x_A, x_B, x_S) / p(x_S) = (p(x_A, x_S) / p(x_S)) (p(x_B, x_S) / p(x_S))`. For a nonnegative
weight of positive total mass these ratios are the conditional probabilities of the normalized
distribution, so this is `P(x_A, x_B | x_S) = P(x_A | x_S) P(x_B | x_S)`. -/
theorem CondIndep.cond_eq_mul {p : (V → α) → ℝ} {A B S : Set V} (h : CondIndep p A B S)
    {x : V → α} (hx : marginal p S x ≠ 0) :
    marginal p (A ∪ B ∪ S) x / marginal p S x =
      (marginal p (A ∪ S) x / marginal p S x) * (marginal p (B ∪ S) x / marginal p S x) := by
  rw [div_mul_div_comm, ← h x, mul_div_mul_right _ _ hx]

/-- **Marginals of a product**: if `f` depends only on the variables in `P` and `g` only on those
in `Q`, with `P ∪ Q` everything and `P ∩ Q ⊆ U`, then summing `f * g` over the variables outside
`U` sums `f` and `g` separately: the free variables of `f` are those of `P` outside `U`, and the
free variables of `g` those of `Q` outside `U`. -/
theorem marginal_mul {f g : (V → α) → ℝ} {P Q U : Set V} (hf : DependsOn f P) (hg : DependsOn g Q)
    (hPQ : ∀ v, v ∈ P ∨ v ∈ Q) (hU : P ∩ Q ⊆ U) (x : V → α) :
    marginal (f * g) U x = marginal f (U ∪ Pᶜ) x * marginal g (U ∪ Qᶜ) x := by
  classical
  simp only [marginal]
  rw [sum_mul_sum, ← sum_product']
  refine sum_nbij' (fun y => (fun v => if v ∈ P then y v else x v,
      fun v => if v ∈ Q then y v else x v)) (fun z v => if v ∈ P then z.1 v else z.2 v)
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    simp only [mem_product, mem_filter, mem_univ, true_and, Set.mem_union, Set.mem_compl_iff]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · by_cases hvP : v ∈ P
      · simp only [hvP, ↓reduceIte]
        exact hy v (hv.resolve_right (not_not.mpr hvP))
      · simp only [hvP, ↓reduceIte]
    · by_cases hvQ : v ∈ Q
      · simp only [hvQ, ↓reduceIte]
        exact hy v (hv.resolve_right (not_not.mpr hvQ))
      · simp only [hvQ, ↓reduceIte]
  · intro z hz
    simp only [mem_product, mem_filter, mem_univ, true_and, Set.mem_union,
      Set.mem_compl_iff] at hz
    simp only [mem_filter, mem_univ, true_and]
    intro v hv
    by_cases hvP : v ∈ P
    · simp only [hvP, ↓reduceIte]
      exact hz.1 v (Or.inl hv)
    · simp only [hvP, ↓reduceIte]
      exact hz.2 v (Or.inl hv)
  · intro y _
    funext v
    by_cases hvP : v ∈ P
    · simp [hvP]
    · simp [hvP, (hPQ v).resolve_left hvP]
  · intro z hz
    simp only [mem_product, mem_filter, mem_univ, true_and, Set.mem_union,
      Set.mem_compl_iff] at hz
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · by_cases hvP : v ∈ P
      · simp [hvP]
      · simp only [hvP, ↓reduceIte]
        exact (hz.1 v (Or.inr hvP)).symm
    · by_cases hvQ : v ∈ Q
      · by_cases hvP : v ∈ P
        · simp only [hvQ, hvP, ↓reduceIte]
          rw [hz.1 v (Or.inl (hU ⟨hvP, hvQ⟩)), hz.2 v (Or.inl (hU ⟨hvP, hvQ⟩))]
        · simp [hvQ, hvP]
      · simp only [hvQ, ↓reduceIte]
        exact (hz.2 v (Or.inr hvQ)).symm
  · intro y _
    simp only [Pi.mul_apply]
    congr 1
    · exact hf fun v hv => by simp [hv]
    · exact hg fun v hv => by simp [hv]

/-- **The factorization criterion for conditional independence**: if `p = f * g`, where `f`
depends only on the variables in `P`, `g` only on those in `Q`, and every variable is in `P` or
`Q`, then variables `A` outside `Q` and `B` outside `P` are conditionally independent given
`P ∩ Q`. -/
theorem condIndep_of_dependsOn {f g : (V → α) → ℝ} {P Q : Set V} (hf : DependsOn f P)
    (hg : DependsOn g Q) (hPQ : ∀ v, v ∈ P ∨ v ∈ Q) {A B : Set V} (hA : ∀ v ∈ A, v ∉ Q)
    (hB : ∀ v ∈ B, v ∉ P) : CondIndep (f * g) A B (P ∩ Q) := by
  intro x
  have hsub : ∀ U : Set V, P ∩ Q ⊆ U ∪ P ∩ Q := fun U => Set.subset_union_right
  rw [marginal_mul hf hg hPQ (hsub _) x, marginal_mul hf hg hPQ subset_rfl x,
    marginal_mul hf hg hPQ (hsub _) x, marginal_mul hf hg hPQ (hsub _) x]
  have e1 : A ∪ B ∪ P ∩ Q ∪ Pᶜ = A ∪ P ∩ Q ∪ Pᶜ := by
    ext v
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    have := hB v
    tauto
  have e2 : A ∪ B ∪ P ∩ Q ∪ Qᶜ = B ∪ P ∩ Q ∪ Qᶜ := by
    ext v
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    have := hA v
    tauto
  have e3 : P ∩ Q ∪ Pᶜ = B ∪ P ∩ Q ∪ Pᶜ := by
    ext v
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    have := hB v
    tauto
  have e4 : P ∩ Q ∪ Qᶜ = A ∪ P ∩ Q ∪ Qᶜ := by
    ext v
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    have := hA v
    tauto
  rw [e1, e2, e3, e4]
  ring

/-- Conditional independence given `S` only involves the variables of `A` and `B` outside `S`. -/
theorem condIndep_of_sdiff {p : (V → α) → ℝ} {A B S : Set V}
    (h : CondIndep p (A \ S) (B \ S) S) : CondIndep p A B S := by
  intro x
  have e1 : A ∪ B ∪ S = A \ S ∪ B \ S ∪ S := by
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  have e2 : A ∪ S = A \ S ∪ S := by
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  have e3 : B ∪ S = B \ S ∪ S := by
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  rw [e1, e2, e3]
  exact h x

open Classical in
/-- The number of configurations that agree with `x` on `W` does not depend on `x`. -/
theorem card_filter_agree (W : Set V) (x z : V → α) :
    (univ.filter fun y : V → α => ∀ v ∈ W, y v = z v).card =
      (univ.filter fun y : V → α => ∀ v ∈ W, y v = x v).card := by
  refine card_nbij' (fun y v => if v ∈ W then x v else y v) (fun y v => if v ∈ W then z v else y v)
    ?_ ?_ ?_ ?_
  · intro y _
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    intro v hv
    simp [hv]
  · intro y _
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    intro v hv
    simp [hv]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
    funext v
    by_cases hv : v ∈ W <;> simp [hv, hy v]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
    funext v
    by_cases hv : v ∈ W <;> simp [hv, hy v]

open Classical in
/-- Marginalizing in two steps: for `U ⊆ W`, the `U`-marginal of the `W`-marginal of `p` is the
`U`-marginal of `p` times the number of configurations agreeing with `x` on `W` (the number of
values of the variables outside `W`). -/
theorem marginal_marginal (p : (V → α) → ℝ) {U W : Set V} (h : U ⊆ W) (x : V → α) :
    marginal (marginal p W) U x =
      (univ.filter fun y : V → α => ∀ v ∈ W, y v = x v).card * marginal p U x := by
  simp only [marginal]
  rw [sum_comm' (t' := univ.filter fun z : V → α => ∀ v ∈ U, z v = x v)
    (s' := fun z => univ.filter fun y : V → α => ∀ v ∈ W, y v = z v)]
  · rw [mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [sum_const, nsmul_eq_mul, card_filter_agree W x z]
  · intro y z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hy, hz⟩
      exact ⟨fun v hv => (hz v hv).symm, fun v hv => (hz v (h hv)).trans (hy v hv)⟩
    · rintro ⟨hy, hz⟩
      exact ⟨fun v hv => (hy v (h hv)).trans (hz v hv), fun v hv => (hy v hv).symm⟩

open Classical in
/-- Conditional independence among variables in `W` is the same for `p` and for its
`W`-marginal. -/
theorem condIndep_marginal_iff {p : (V → α) → ℝ} {A B S W : Set V} (hA : A ⊆ W) (hB : B ⊆ W)
    (hS : S ⊆ W) : CondIndep (marginal p W) A B S ↔ CondIndep p A B S := by
  have hpos : ∀ x : V → α,
      (0 : ℝ) < (univ.filter fun y : V → α => ∀ v ∈ W, y v = x v).card := fun x => by
    exact_mod_cast card_pos.mpr ⟨x, by simp⟩
  refine forall_congr' fun x => ?_
  rw [marginal_marginal p (Set.union_subset (Set.union_subset hA hB) hS),
    marginal_marginal p hS, marginal_marginal p (Set.union_subset hA hS),
    marginal_marginal p (Set.union_subset hB hS)]
  have h := (hpos x).ne'
  rw [mul_mul_mul_comm _ (marginal p (A ∪ B ∪ S) x), mul_mul_mul_comm _ (marginal p (A ∪ S) x),
    mul_right_inj' (mul_ne_zero h h)]

end MetaMathlibExt.FiniteWeight
