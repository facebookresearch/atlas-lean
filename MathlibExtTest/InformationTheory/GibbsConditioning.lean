/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.InformationTheory.GibbsConditioning

/-! # Tests for `MathlibExt.InformationTheory.GibbsConditioning`

The draws are Boolean with `Q true = 1 / 3`, and the conditioning event is that all `n` draws are
equal: `Γ` consists of the two point masses. The point mass at `false` is the element of `Γ`
closest to `Q` in divergence (`log (3 / 2) < log 3`), so the conditional law of the first draws
tends to it, not to `Q`.
-/

namespace MathlibExtTest.GibbsConditioning

open Finset Real Filter Topology MathlibExt.InformationTheory.MethodOfTypes
  MathlibExt.InformationTheory.GibbsConditioningWanted

/-- The law on `Bool` with `Q true = 1 / 3`. -/
private noncomputable def Q : Bool → ℝ := fun b => if b then 1 / 3 else 2 / 3

/-- The point mass at `c`. -/
private noncomputable def pointMass (c : Bool) : Bool → ℝ := fun b => if b = c then 1 else 0

/-- The two point masses: the empirical distribution of `n ≥ 1` draws lies in `Γ` exactly when all
the draws are equal. -/
private noncomputable def Γ : Set (Bool → ℝ) := {pointMass true, pointMass false}

/-- `D(δ_true ‖ Q) = log 3`. -/
private theorem divergence_true :
    ∑ a, pointMass true a * log (pointMass true a / Q a) = log 3 := by
  simp [pointMass, Q]

/-- `D(δ_false ‖ Q) = log (3 / 2)`, the smaller of the two divergences. -/
private theorem divergence_false :
    ∑ a, pointMass false a * log (pointMass false a / Q a) = log (3 / 2) := by
  simp [pointMass, Q]

/-- All `n` draws `false`, for `n ≥ 1`, has empirical distribution the point mass at `false`. -/
private theorem empirical_replicate_false {n : ℕ} (hn : n ≠ 0) :
    empirical (Sym.replicate n false) = pointMass false := by
  funext b
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  cases b <;> simp [empirical, pointMass, Sym.coe_replicate, Multiset.count_replicate, hnR]

open Classical in
/-- Gibbs' conditioning principle for this example: given that all `n` draws are equal, the first
`k` draws spell `y` with probability tending to `∏ᵢ 1[yᵢ = false]`. -/
private theorem tendsto_prefix (k : ℕ) (y : Fin k → Bool) :
    Tendsto (fun n : ℕ =>
      iidProb Q (univ.filter fun x : Fin n → Bool =>
          empirical (seqType x) ∈ Γ ∧ ∀ i : Fin k, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = y i) /
        iidProb Q (univ.filter fun x : Fin n → Bool => empirical (seqType x) ∈ Γ))
      atTop (𝓝 (∏ i, pointMass false (y i))) := by
  have hQ : ∀ a, 0 < Q a := fun a => by cases a <;> norm_num [Q]
  have hQ1 : ∑ a, Q a = 1 := by norm_num [Q, Fintype.sum_bool]
  have hΓ : ∀ P ∈ Γ, (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1 := by
    rintro P (rfl | rfl) <;>
      exact ⟨fun a => by cases a <;> simp [pointMass], by simp [pointMass]⟩
  have hlt : log (3 / 2) < log 3 := log_lt_log (by norm_num) (by norm_num)
  have hr : ∀ P ∈ Γ, log (3 / 2) ≤ ∑ a, P a * log (P a / Q a) := by
    rintro P (rfl | rfl)
    · rw [divergence_true]; exact hlt.le
    · rw [divergence_false]
  have hs : ∀ᶠ n in atTop, empirical (Sym.replicate n false) ∈ Γ := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [empirical_replicate_false hn]
    exact Or.inr rfl
  have hlim : Tendsto (fun n => ∑ a, empirical (Sym.replicate n false) a *
      log (empirical (Sym.replicate n false) a / Q a)) atTop (𝓝 (log (3 / 2))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [empirical_replicate_false hn, divergence_false]
  have hclosure : closure Γ = Γ :=
    ((Set.finite_singleton (pointMass false)).insert (pointMass true)).isClosed.closure_eq
  have huniq : ∀ P ∈ closure Γ, ∑ a, P a * log (P a / Q a) = log (3 / 2) →
      P = pointMass false := by
    rw [hclosure]
    rintro P (rfl | rfl) hP
    · rw [divergence_true] at hP
      exact absurd hP hlt.ne'
    · rfl
  exact tendsto_iidProb_prefix_div_iidProb hQ hQ1 hΓ hr (fun n => Sym.replicate n false) hs hlim
    (by rw [hclosure]; exact Or.inr rfl) divergence_false huniq k y

-- Test section: conditioning selects the closest distribution of `Γ`. Unconditionally the first
-- draw is `true` with probability `1 / 3`; given that all draws are equal, this tends to `0`
-- (it is `1 / (1 + 2 ^ n)`, as all `true` is `2 ^ n` times less likely than all `false`).
open Classical in
example : Tendsto (fun n : ℕ =>
      iidProb Q (univ.filter fun x : Fin n → Bool =>
          empirical (seqType x) ∈ Γ ∧ ∀ i : Fin 1, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = ![true] i) /
        iidProb Q (univ.filter fun x : Fin n → Bool => empirical (seqType x) ∈ Γ))
      atTop (𝓝 0) := by
  simpa [pointMass] using tendsto_prefix 1 ![true]

-- The first two draws are both `false` with conditional probability tending to `1`.
open Classical in
example : Tendsto (fun n : ℕ =>
      iidProb Q (univ.filter fun x : Fin n → Bool =>
          empirical (seqType x) ∈ Γ ∧
            ∀ i : Fin 2, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = ![false, false] i) /
        iidProb Q (univ.filter fun x : Fin n → Bool => empirical (seqType x) ∈ Γ))
      atTop (𝓝 1) := by
  simpa [pointMass, Fin.prod_univ_two] using tendsto_prefix 2 ![false, false]

-- Edge case `k = 0`: the empty word has conditional probability `1` once `Γ` has positive
-- probability, and the limit is the empty product.
open Classical in
example : Tendsto (fun n : ℕ =>
      iidProb Q (univ.filter fun x : Fin n → Bool =>
          empirical (seqType x) ∈ Γ ∧ ∀ i : Fin 0, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = Fin.elim0 i) /
        iidProb Q (univ.filter fun x : Fin n → Bool => empirical (seqType x) ∈ Γ))
      atTop (𝓝 1) := by
  simpa using tendsto_prefix 0 Fin.elim0

end MathlibExtTest.GibbsConditioning
