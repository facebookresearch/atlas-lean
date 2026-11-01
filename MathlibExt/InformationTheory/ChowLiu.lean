/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalMutualInformation

/-!
# Chow–Liu trees

Chow and Liu (1968) approximate a joint law `P` of finitely many discrete variables `X_i` by a
product of second-order terms along a dependence tree: each variable `X_i` has at most one parent
`X_{j(i)}`, and
`P_τ(x) = ∏_i P(x_i | x_{j(i)})`, with `P(x_i | x_{j(i)})` replaced by the marginal `P(x_i)` for
a variable without a parent. A `DependenceForest` records the parent map together with a rank
that strictly increases from parent to child, which certifies acyclicity; a dependence tree is
the case of a single parentless variable.

Chow and Liu show that the Kullback–Leibler divergence of `P_τ` from `P` is
`D(P ‖ P_τ) = ∑_i H(X_i) - H(X) - ∑_i I(X_i; X_{j(i)})`, so the best dependence tree maximizes the
total mutual information of its edges, which makes it a maximum-weight spanning tree for the
weights `I(X_i; X_k)`. Information is in bits.

## Main results

* `DependenceForest.sum_approx`: `P_τ` is a probability law (`∑_x P_τ(x) = 1`), packaged as
  `DependenceForest.approxPMF`; `DependenceForest.approx_pos` shows `P ≪ P_τ`.
* `DependenceForest.divergence_eq_klDiv`: `divergence` is Mathlib's `klDiv` of `P_τ` from `P`,
  in bits.
* `DependenceForest.divergence_eq` (**Chow–Liu identity**):
  `D(P ‖ P_τ) = ∑_i H(X_i) - H(X) - ∑_i I(X_i; X_{j(i)})`.
* `DependenceForest.divergence_le_divergence_iff` (**Chow–Liu optimality**): `τ` approximates `P`
  at least as well as `τ'` iff the mutual-information weight of `τ` is at least that of `τ'`.

Not covered: that `P_τ` minimizes the divergence among all laws factoring along `τ` (with other
conditional laws), the identification of dependence trees with spanning trees of the complete
graph, and the greedy maximum-weight spanning-tree computation itself.

## References

* C. K. Chow and C. N. Liu, "Approximating discrete probability distributions with dependence
  trees", *IEEE Trans. Inform. Theory* 14 (1968), 462–467.
-/

@[expose] public section

namespace InformationTheory

open MeasureTheory Real
open scoped ENNReal

/-- A dependence forest on the variables `ι` (Chow–Liu 1968): each variable has at most one parent,
and `rank` strictly increases from parent to child, so the parent relation has no cycles. -/
structure DependenceForest (ι : Type*) where
  /-- The parent `j(i)` of variable `i`, if any. -/
  parent : ι → Option ι
  /-- A rank certifying acyclicity. -/
  rank : ι → ℕ
  /-- A parent has strictly smaller rank than its child. -/
  rank_lt : ∀ i j, parent i = some j → rank j < rank i

namespace DependenceForest

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

/-- Chow–Liu's product approximation `P_τ(x) = ∏_i P(x_i | x_{j(i)})` of a joint law `p`, with the
marginal `P(x_i)` for a parentless `i`. The conditional `P(x_i | x_j)` is
`P(x_i, x_j) / P(x_j)`; where `P(x_j) = 0` the quotient is `0`, and such `x` have `P(x) = 0`. -/
noncomputable def approx (τ : DependenceForest ι) (p : PMF (∀ i, α i)) (x : ∀ i, α i) : ℝ :=
  ∏ i, match τ.parent i with
    | none => ((p.map fun y ↦ y i) (x i)).toReal
    | some j => ((p.map fun y ↦ (y i, y j)) (x i, x j)).toReal / ((p.map fun y ↦ y j) (x j)).toReal

/-- The factor of variable `i` in Chow–Liu's product approximation. -/
private noncomputable def factor (τ : DependenceForest ι) (p : PMF (∀ i, α i)) (i : ι)
    (x : ∀ i, α i) : ℝ :=
  match τ.parent i with
    | none => ((p.map fun y ↦ y i) (x i)).toReal
    | some j => ((p.map fun y ↦ (y i, y j)) (x i, x j)).toReal / ((p.map fun y ↦ y j) (x j)).toReal

private theorem approx_eq_prod (τ : DependenceForest ι) (p : PMF (∀ i, α i)) (x : ∀ i, α i) :
    τ.approx p x = ∏ i, τ.factor p i x := rfl

omit [Fintype ι] in
private theorem factor_nonneg (τ : DependenceForest ι) (p : PMF (∀ i, α i)) (i : ι)
    (x : ∀ i, α i) : 0 ≤ τ.factor p i x := by
  unfold factor
  split <;> positivity

omit [Fintype ι] in
private theorem factor_pos (τ : DependenceForest ι) (p : PMF (∀ i, α i)) (i : ι)
    {x : ∀ i, α i} (hx : p x ≠ 0) : 0 < τ.factor p i x := by
  have h0 : 0 < (p x).toReal := ENNReal.toReal_pos hx (PMF.apply_ne_top _ _)
  unfold factor
  split
  · exact h0.trans_le (toReal_le_map_apply p (fun y ↦ y i) x)
  · exact div_pos (h0.trans_le (toReal_le_map_apply p (fun y ↦ (y i, y _)) x))
      (h0.trans_le (toReal_le_map_apply p (fun y ↦ y _) x))

/-- The approximation is nonnegative. -/
theorem approx_nonneg (τ : DependenceForest ι) (p : PMF (∀ i, α i)) (x : ∀ i, α i) :
    0 ≤ τ.approx p x :=
  Finset.prod_nonneg fun i _ ↦ τ.factor_nonneg p i x

/-- `P ≪ P_τ`: the approximation is positive wherever `p` is. -/
theorem approx_pos (τ : DependenceForest ι) (p : PMF (∀ i, α i)) {x : ∀ i, α i} (hx : p x ≠ 0) :
    0 < τ.approx p x :=
  Finset.prod_pos fun i _ ↦ τ.factor_pos p i hx

omit [Fintype ι] in
/-- The factor of `k` vanishes where the marginal of its parent does. -/
private theorem factor_eq_zero (τ : DependenceForest ι) (p : PMF (∀ i, α i)) (k : ι)
    (x : ∀ i, α i) (hx : (p.map fun y ↦ y k) (x k) = 0) : τ.factor p k x = 0 := by
  unfold factor
  rcases h : τ.parent k with _ | j
  · simp [hx]
  · have : (p.map fun y ↦ (y k, y j)) (x k, x j) = 0 := by
      refine le_antisymm ?_ bot_le
      have := le_map_apply (p.map fun y ↦ (y k, y j)) Prod.fst (x k, x j)
      rw [PMF.map_comp] at this
      exact this.trans hx.le
    simp [this]

variable [DecidableEq ι] [∀ i, Fintype (α i)]

omit [Fintype ι] [∀ i, Fintype (α i)] in
/-- The factor of `k` depends only on `x k` and on the coordinate of its parent. -/
private theorem factor_update (τ : DependenceForest ι) (p : PMF (∀ i, α i)) {i k : ι}
    (hki : k ≠ i) (hpk : τ.parent k ≠ some i) (x : ∀ i, α i) (a : α i) :
    τ.factor p k (Function.update x i a) = τ.factor p k x := by
  unfold factor
  rcases h : τ.parent k with _ | j
  · simp only
    rw [Function.update_of_ne hki]
  · have hji : j ≠ i := fun hji ↦ hpk (h ▸ hji ▸ rfl)
    simp only
    rw [Function.update_of_ne hki, Function.update_of_ne hji]

omit [Fintype ι] in
/-- Summing the factor of `i` over `x i` gives `1`, unless the parent's marginal vanishes. -/
private theorem sum_factor_update (τ : DependenceForest ι) (p : PMF (∀ i, α i)) (i : ι)
    (x : ∀ i, α i) (hx : ∀ j, τ.parent i = some j → (p.map fun y ↦ y j) (x j) ≠ 0) :
    ∑ a, τ.factor p i (Function.update x i a) = 1 := by
  unfold factor
  rcases h : τ.parent i with _ | j
  · simp only [Function.update_self]
    have := PMF.tsum_coe (p.map fun y ↦ y i)
    rw [tsum_fintype] at this
    rw [← ENNReal.toReal_sum fun _ _ ↦ PMF.apply_ne_top _ _, this, ENNReal.toReal_one]
  · have hji : j ≠ i := fun hji ↦ by
      have := τ.rank_lt i j h
      rw [hji] at this
      exact lt_irrefl _ this
    simp only [Function.update_self, Function.update_of_ne hji]
    rw [← Finset.sum_div, ← toReal_map_snd_apply, PMF.map_comp]
    exact div_self (ENNReal.toReal_ne_zero.mpr ⟨hx j h, PMF.apply_ne_top _ _⟩)

omit [Fintype ι] [DecidableEq ι] in
/-- Averaging over the `i`-th coordinate: `∑_x ∑_a F (x[i ↦ a]) = |α i| ∑_x F x`. -/
private theorem sum_sum_update [DecidableEq ι] [Fintype ι] (i : ι) (F : (∀ i, α i) → ℝ) :
    ∑ x, ∑ a, F (Function.update x i a) = Fintype.card (α i) * ∑ x, F x := by
  set e := Equiv.piSplitAt i α
  have hupd : ∀ b a z, Function.update (e.symm (b, z)) i a = e.symm (a, z) := by
    intro b a z
    funext k
    by_cases hk : k = i
    · subst hk
      simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, hk]
  rw [← Fintype.sum_equiv e.symm (fun y ↦ ∑ a, F (Function.update (e.symm y) i a)) _
      (fun _ ↦ rfl), ← Fintype.sum_equiv e.symm (fun y ↦ F (e.symm y)) _ (fun _ ↦ rfl),
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [hupd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- If `G` ignores `x i` and, wherever `G ≠ 0`, `H` sums to one over `x i`, then
`|α i| ∑_x H x G x = ∑_x G x`. -/
private theorem card_mul_sum_mul [DecidableEq ι] [Fintype ι] (i : ι) (H G : (∀ i, α i) → ℝ)
    (hG : ∀ x a, G (Function.update x i a) = G x)
    (hH : ∀ x, G x = 0 ∨ ∑ a, H (Function.update x i a) = 1) :
    Fintype.card (α i) * ∑ x, H x * G x = ∑ x, G x := by
  rw [← sum_sum_update]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [hG, ← Finset.sum_mul]
  rcases hH x with h | h <;> simp [h]

/-- Partial products over a parent-closed set `S` of variables sum to `∏_{k ∉ S} |α k|`. -/
private theorem sum_prod_factor (τ : DependenceForest ι) (p : PMF (∀ i, α i)) :
    ∀ (n : ℕ) (S : Finset ι), S.card = n → (∀ k ∈ S, ∀ j, τ.parent k = some j → j ∈ S) →
      ∑ x, ∏ k ∈ S, τ.factor p k x = ∏ k ∈ Finset.univ \ S, (Fintype.card (α k) : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro S hS _
    rw [Finset.card_eq_zero.mp hS]
    simp [Fintype.card_pi]
  | succ n ih =>
    intro S hS hclosed
    have hne : S.Nonempty := Finset.card_pos.mp (hS ▸ Nat.succ_pos n)
    obtain ⟨i, hiS, himax⟩ := Finset.exists_max_image S τ.rank hne
    have hnot : ∀ k ∈ S.erase i, τ.parent k ≠ some i := by
      intro k hk hki
      have := τ.rank_lt k i hki
      exact absurd (himax k (Finset.mem_of_mem_erase hk)) (not_le.mpr this)
    have hclosed' : ∀ k ∈ S.erase i, ∀ j, τ.parent k = some j → j ∈ S.erase i := by
      intro k hk j hj
      refine Finset.mem_erase.mpr ⟨fun hji ↦ hnot k hk (hji ▸ hj), ?_⟩
      exact hclosed k (Finset.mem_of_mem_erase hk) j hj
    have hcard : (S.erase i).card = n := by rw [Finset.card_erase_of_mem hiS, hS]; rfl
    have ih' := ih (S.erase i) hcard hclosed'
    have hpos : (0 : ℝ) < Fintype.card (α i) := by
      obtain ⟨x, hx⟩ := p.support_nonempty
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨x i⟩
    have key := card_mul_sum_mul i (τ.factor p i) (fun x ↦ ∏ k ∈ S.erase i, τ.factor p k x)
      (fun x a ↦ Finset.prod_congr rfl fun k hk ↦
        τ.factor_update p (Finset.ne_of_mem_erase hk) (hnot k hk) x a)
      (fun x ↦ by
        by_cases h : ∃ j, τ.parent i = some j ∧ (p.map fun y ↦ y j) (x j) = 0
        · obtain ⟨j, hj, h0⟩ := h
          left
          refine Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨?_, hclosed i hiS j hj⟩)
            (τ.factor_eq_zero p j x h0)
          rintro rfl
          exact lt_irrefl _ (τ.rank_lt _ _ hj)
        · right
          push Not at h
          exact τ.sum_factor_update p i x h)
    have hsplit : Finset.univ \ S.erase i = insert i (Finset.univ \ S) := by
      ext k
      by_cases hk : k = i <;> simp [hk, hiS]
    rw [ih', hsplit, Finset.prod_insert (by simp [hiS])] at key
    rw [Finset.sum_congr rfl fun x _ ↦ (Finset.mul_prod_erase S (fun k ↦ τ.factor p k x) hiS).symm]
    exact mul_left_cancel₀ hpos.ne' key

/-- The approximation is a probability law: `∑_x P_τ(x) = 1`. -/
theorem sum_approx (τ : DependenceForest ι) (p : PMF (∀ i, α i)) :
    ∑ x, τ.approx p x = 1 := by
  simpa [approx_eq_prod] using
    τ.sum_prod_factor p _ Finset.univ rfl fun _ _ _ _ ↦ Finset.mem_univ _

/-- Chow–Liu's approximation `P_τ` as a probability mass function. -/
noncomputable def approxPMF (τ : DependenceForest ι) (p : PMF (∀ i, α i)) : PMF (∀ i, α i) :=
  PMF.ofFintype (fun x ↦ ENNReal.ofReal (τ.approx p x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ τ.approx_nonneg p x, sum_approx,
      ENNReal.ofReal_one])

/-- The mutual-information weight `∑_i I(X_i; X_{j(i)})` of a dependence forest, in bits. -/
noncomputable def weight (τ : DependenceForest ι) (p : PMF (∀ i, α i)) : ℝ :=
  ∑ i, match τ.parent i with
    | none => 0
    | some j => finiteMutualInformation (p.map fun y ↦ (y i, y j))

/-- The divergence `D(P ‖ P_τ) = ∑_x P(x) log₂ (P(x) / P_τ(x))` of Chow–Liu's approximation from
`P`, in bits (`divergence_eq_klDiv`). -/
noncomputable def divergence (τ : DependenceForest ι) (p : PMF (∀ i, α i)) : ℝ :=
  ∑ x, (p x).toReal * logb 2 ((p x).toReal / τ.approx p x)

/-- `divergence` is Mathlib's Kullback–Leibler divergence `klDiv` of `P_τ` from `P`, converted to
bits; the finite alphabet carries the discrete σ-algebra. -/
theorem divergence_eq_klDiv (τ : DependenceForest ι) (p : PMF (∀ i, α i)) :
    letI : MeasurableSpace (∀ i, α i) := ⊤
    τ.divergence p = (klDiv p.toMeasure (τ.approxPMF p).toMeasure).toReal / log 2 := by
  let : MeasurableSpace (∀ i, α i) := ⊤
  have : MeasurableSingletonClass (∀ i, α i) := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hq : ∀ x, ((τ.approxPMF p) x).toReal = τ.approx p x := fun x ↦ by
    simp [approxPMF, ENNReal.toReal_ofReal (τ.approx_nonneg p x)]
  have hpq : ∀ x, τ.approxPMF p x = 0 → p x = 0 := by
    intro x hx
    by_contra h0
    have := τ.approx_pos p h0
    simp only [approxPMF, PMF.ofFintype_apply, ENNReal.ofReal_eq_zero] at hx
    linarith
  rw [toReal_klDiv_toMeasure hpq, divergence, Finset.sum_div]
  simp only [hq, logb, mul_div_assoc]

/-- **Chow–Liu identity**: `D(P ‖ P_τ) = ∑_i H(X_i) - H(X) - ∑_i I(X_i; X_{j(i)})`. -/
theorem divergence_eq (τ : DependenceForest ι) (p : PMF (∀ i, α i)) :
    τ.divergence p =
      ∑ i, shannonEntropy (p.map fun y ↦ y i) - shannonEntropy p - τ.weight p := by
  have hlog : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  have hfac : ∀ i, ∑ x, (p x).toReal * log (τ.factor p i x) =
      (match τ.parent i with
        | none => 0
        | some j => finiteMutualInformation (p.map fun y ↦ (y i, y j))) * log 2 -
        shannonEntropy (p.map fun y ↦ y i) * log 2 := by
    intro i
    rcases h : τ.parent i with _ | j
    · simp only [factor, h]
      rw [sum_mul_log_map p (fun y ↦ y i)]
      ring
    · simp only [factor, h]
      have hx : ∀ x, (p x).toReal * log (((p.map fun y ↦ (y i, y j)) (x i, x j)).toReal /
          ((p.map fun y ↦ y j) (x j)).toReal) =
          (p x).toReal * log ((p.map fun y ↦ (y i, y j)) (x i, x j)).toReal -
            (p x).toReal * log ((p.map fun y ↦ y j) (x j)).toReal := by
        intro x
        rcases (ENNReal.toReal_nonneg : 0 ≤ (p x).toReal).eq_or_lt with h0 | h0
        · rw [← h0]; simp
        rw [log_div (h0.trans_le (toReal_le_map_apply p (fun y ↦ (y i, y j)) x)).ne'
          (h0.trans_le (toReal_le_map_apply p (fun y ↦ y j) x)).ne']
        ring
      rw [Finset.sum_congr rfl fun x _ ↦ hx x, Finset.sum_sub_distrib,
        sum_mul_log_map p (fun y ↦ (y i, y j)), sum_mul_log_map p (fun y ↦ y j),
        finiteMutualInformation_eq, PMF.map_comp, PMF.map_comp]
      simp only [Function.comp_def]
      ring
  have hx : ∀ x, (p x).toReal * logb 2 ((p x).toReal / τ.approx p x) =
      ((p x).toReal * log (p x).toReal - ∑ i, (p x).toReal * log (τ.factor p i x)) / log 2 := by
    intro x
    by_cases h0 : p x = 0
    · simp [h0]
    rw [logb, approx_eq_prod, log_div (ENNReal.toReal_pos h0 (PMF.apply_ne_top _ _)).ne'
      (Finset.prod_pos fun i _ ↦ τ.factor_pos p i h0).ne',
      log_prod fun i _ ↦ (τ.factor_pos p i h0).ne', ← Finset.mul_sum]
    ring
  rw [divergence, Finset.sum_congr rfl fun x _ ↦ hx x, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_comm, Finset.sum_congr rfl fun i _ ↦ hfac i, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, div_eq_iff hlog, weight]
  linear_combination shannonEntropy_mul_log_two p

/-- The divergence of Chow–Liu's approximation is nonnegative, so
`∑_i I(X_i; X_{j(i)}) ≤ ∑_i H(X_i) - H(X)` for every dependence forest. -/
theorem divergence_nonneg (τ : DependenceForest ι) (p : PMF (∀ i, α i)) :
    0 ≤ τ.divergence p := by
  rw [divergence_eq_klDiv]
  exact div_nonneg ENNReal.toReal_nonneg (log_pos one_lt_two).le

/-- **Chow–Liu optimality**: among dependence forests, a smaller divergence is the same as a
larger mutual-information weight, so minimizing `D(P ‖ P_τ)` over dependence trees is maximizing
the total mutual information `∑_i I(X_i; X_{j(i)})` of their edges. -/
theorem divergence_le_divergence_iff (τ τ' : DependenceForest ι) (p : PMF (∀ i, α i)) :
    τ.divergence p ≤ τ'.divergence p ↔ τ'.weight p ≤ τ.weight p := by
  rw [divergence_eq, divergence_eq]
  constructor <;> intro h <;> linarith

end DependenceForest

end InformationTheory
