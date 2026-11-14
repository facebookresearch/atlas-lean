/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Ecology.LevinsNetwork
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for the Levins metapopulation on a patch network

Three landscapes, each with a trajectory written down and checked against the system from the
definitions (derivatives computed by hand, not through the theorems under test):

* **Persistence.** Two patches colonizing each other at rate `2`, extinction rate `1`
  (`C₂ = !![0, 2; 2, 0]`). The uniform trajectory `p_i(t) = 1 / (2 (1 + e^{-t}))` starts at
  `1/4` and tends to `1/2 = 1 - 1/R₀` from below: the persistence bound is attained in the limit
  and never exceeded, so it cannot be raised.
* **Extinction.** Two patches colonizing each other at rate `1`, extinction rate `2`
  (`C₁ = !![0, 1; 1, 0]`, `R₀ = 1/2`). The uniform trajectory `p_i(t) = e^{-t} / (2 - e^{-t})`
  starts at `1` and decays like `e^{-t}`.
* **Irreducibility is needed.** Three patches: patches `0` and `1` colonize each other at rate
  `2`, patch `2` is isolated (`C₃`), all with extinction rate `1`. Here `R₀ ≥ 2 > 1`
  (Collatz–Wielandt bound, computed directly), yet the landscape with only patch `2` occupied,
  `p(t) = (0, 0, e^{-t})`, goes extinct.
-/

open Real Filter Set Matrix
open scoped Topology ENNReal

namespace MathlibExtTest.Biology.Ecology.LevinsNetwork

open MathlibExt.Biology.Ecology.LevinsNetwork

/-! ### The field -/

/-- Two patches colonizing each other at rate `2`. -/
def C₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 2, 0]

theorem C₂_nonneg : ∀ i j, 0 ≤ C₂ i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [C₂]

theorem C₂_rowSum : ∀ i, ∑ j, C₂ i j = 2 := by
  intro i; fin_cases i <;> norm_num [C₂, Fin.sum_univ_two]

/-- Patch `0` at `1/4`, patch `1` at `1/2`: `(3/4) · 1 - 1/4 = 1/2` and `(1/2) · (1/2) - 1/2`. -/
example : field C₂ (fun _ => 1) ![1 / 4, 1 / 2] = ![1 / 2, -1 / 4] := by
  funext i
  fin_cases i <;> norm_num [field, C₂, mulVec, dotProduct, Fin.sum_univ_two]

/-- The empty landscape is an equilibrium; the full landscape loses `e_i` per patch. -/
example : field C₂ (fun _ => 1) 0 = 0 ∧ field C₂ (fun _ => 1) 1 = fun _ => -1 := by
  refine ⟨field_zero _ _, ?_⟩
  funext i
  fin_cases i <;> norm_num [field, C₂, mulVec, dotProduct, Fin.sum_univ_two]

/-- The linear-minus-quadratic decomposition, checked at a point. -/
example : field C₂ (fun _ => 1) ![1 / 4, 1 / 2] =
    (C₂ - diagonal fun _ => 1) *ᵥ ![1 / 4, 1 / 2] -
      fun i => ![1 / 4, 1 / 2] i * (C₂ *ᵥ ![1 / 4, 1 / 2]) i :=
  field_eq_sub_mulVec _ _ _

/-! ### Persistence: `C₂`, `e ≡ 1` -/

/-- `C₂` is irreducible: `C₂` is positive off the diagonal and `C₂²` on it. -/
theorem isIrreducible_C₂ : C₂.IsIrreducible := by
  rw [isIrreducible_iff_exists_pow_pos C₂_nonneg]
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨2, two_pos, by norm_num [C₂, sq, mul_apply, Fin.sum_univ_two]⟩
  · exact ⟨1, one_pos, by norm_num [C₂]⟩
  · exact ⟨1, one_pos, by norm_num [C₂]⟩
  · exact ⟨2, two_pos, by norm_num [C₂, sq, mul_apply, Fin.sum_univ_two]⟩

/-- `R₀ = 2`. -/
theorem persistenceNumber_C₂ : persistenceNumber C₂ (fun _ => 1) = 2 := by
  rw [persistenceNumber_of_rowSum C₂_nonneg C₂_rowSum one_pos, div_one]

/-- An independent lower bound `R₀ ≥ 2`: the Collatz–Wielandt bound with `z = (1, 1)`,
`C₂ z = 2 z`, applied to `C₂ diag(1)⁻¹ = C₂`. -/
example : ENNReal.ofReal 2 ≤
    spectralRadius ℂ ((C₂ * (diagonal fun _ : Fin 2 => (1 : ℝ))⁻¹).map (algebraMap ℝ ℂ)) := by
  rw [diagonal_one, inv_one, Matrix.mul_one]
  refine le_spectralRadius_of_smul_le_mulVec C₂_nonneg (z := fun _ => 1)
    (fun _ => zero_le_one) (fun h => one_ne_zero (congrFun h 0)) zero_le_two fun i => ?_
  fin_cases i <;> norm_num [C₂, mulVec, dotProduct, Fin.sum_univ_two]

/-- The uniform trajectory `1 / (2 (1 + e^{-t}))`. -/
noncomputable def traj (t : ℝ) : ℝ := (2 * (1 + exp (-t)))⁻¹

theorem traj_zero : traj 0 = 1 / 4 := by norm_num [traj]

/-- `p_i(t) = traj t` solves the network system (derivative computed directly). -/
theorem isSolution_traj : IsSolution C₂ (fun _ => 1) (fun t _ => traj t) := by
  refine ⟨fun t _ => hasDerivAt_pi.2 fun i => ?_⟩
  have hu : HasDerivAt (fun s => exp (-s)) (-exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have hden : 2 * (1 + exp (-t)) ≠ 0 := by positivity
  have h := ((hu.const_add 1).const_mul 2).inv hden
  refine h.congr_deriv ?_
  simp only [field, mulVec, dotProduct, ← Finset.sum_mul, C₂_rowSum, traj]
  field_simp
  ring

/-- `traj` stays in `(0, 1/2)`. -/
theorem traj_mem_Ioo (t : ℝ) : traj t ∈ Ioo 0 (1 / 2) := by
  have hu := exp_pos (-t)
  refine ⟨by unfold traj; positivity, ?_⟩
  show (2 * (1 + exp (-t)))⁻¹ < 1 / 2
  rw [one_div]
  exact (inv_lt_inv₀ (by positivity) two_pos).2 (by linarith)

/-- `traj → 1/2`, computed directly from `e^{-t} → 0`. -/
theorem tendsto_traj : Tendsto traj atTop (𝓝 (1 / 2)) := by
  have h := ((tendsto_exp_neg_atTop_nhds_zero.const_add 1).const_mul 2).inv₀
    (by norm_num : (2 : ℝ) * (1 + 0) ≠ 0)
  rw [show (1 / 2 : ℝ) = (2 * (1 + 0))⁻¹ by norm_num]
  exact h

/-- The persistence theorem applies to the uniform trajectory: it comes within any `δ` of
`1 - 1/R₀ = 1/2` at arbitrarily late times. -/
example : ∀ δ > 0, ∀ T : ℝ, ∃ t ≥ T, 1 / 2 - δ < traj t := by
  intro δ hδ T
  obtain ⟨t, ht, i, hi⟩ := exists_lt_of_one_lt isIrreducible_C₂ (fun _ => one_pos)
    (by rw [persistenceNumber_C₂]; norm_num) isSolution_traj
    (fun _ => by rw [traj_zero]; norm_num) ⟨0, by rw [traj_zero]; norm_num⟩ δ hδ T
  rw [persistenceNumber_C₂] at hi
  exact ⟨t, ht, by norm_num at hi ⊢; linarith⟩

/-- **The bound is sharp.** The trajectory never reaches `1 - 1/R₀`, so the persistence bound
cannot be replaced by a larger level. -/
example (t : ℝ) (i : Fin 2) : (fun t (_ : Fin 2) => traj t) t i <
    1 - (persistenceNumber C₂ (fun _ => 1))⁻¹ := by
  rw [persistenceNumber_C₂]
  have := (traj_mem_Ioo t).2
  norm_num at this ⊢
  exact this

example : ¬ Tendsto (fun t (_ : Fin 2) => traj t) atTop (𝓝 0) :=
  not_tendsto_zero_of_one_lt isIrreducible_C₂ (fun _ => one_pos)
    (by rw [persistenceNumber_C₂]; norm_num) isSolution_traj
    (fun _ => by rw [traj_zero]; norm_num) ⟨0, by rw [traj_zero]; norm_num⟩

/-- The linearization `C₂ - I` has an unstable mode. -/
example : ∃ μ ∈ spectrum ℂ ((C₂ - diagonal fun _ => 1).map (algebraMap ℝ ℂ)), 0 < μ.re :=
  (exists_re_pos_iff C₂_nonneg fun _ => one_pos).2 (by rw [persistenceNumber_C₂]; norm_num)

/-- The box `[0, 1]²` contains the trajectory, as the invariance theorem predicts. -/
example (t : ℝ) (ht : 0 ≤ t) (i : Fin 2) : traj t ∈ Icc 0 1 :=
  isSolution_traj.mem_Icc C₂_nonneg (fun _ => zero_le_one)
    (fun _ => by rw [traj_zero]; norm_num) ht i

/-! ### Extinction: `C₁`, `e ≡ 2` -/

/-- Two patches colonizing each other at rate `1`. -/
def C₁ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem C₁_nonneg : ∀ i j, 0 ≤ C₁ i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [C₁]

theorem C₁_rowSum : ∀ i, ∑ j, C₁ i j = 1 := by
  intro i; fin_cases i <;> norm_num [C₁, Fin.sum_univ_two]

theorem persistenceNumber_C₁ : persistenceNumber C₁ (fun _ => 2) = 1 / 2 :=
  persistenceNumber_of_rowSum C₁_nonneg C₁_rowSum two_pos

/-- The uniform trajectory `e^{-t} / (2 - e^{-t})` from the full landscape. -/
noncomputable def trajExt (t : ℝ) : ℝ := exp (-t) / (2 - exp (-t))

theorem trajExt_zero : trajExt 0 = 1 := by norm_num [trajExt]

private theorem exp_neg_le_one {t : ℝ} (ht : 0 ≤ t) : exp (-t) ≤ 1 :=
  exp_le_one_iff.2 (by linarith)

/-- `p_i(t) = trajExt t` solves the network system (derivative computed directly). -/
theorem isSolution_trajExt : IsSolution C₁ (fun _ => 2) (fun t _ => trajExt t) := by
  refine ⟨fun t ht => hasDerivAt_pi.2 fun i => ?_⟩
  have hu : HasDerivAt (fun s => exp (-s)) (-exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have hden : 2 - exp (-t) ≠ 0 := by linarith [exp_neg_le_one ht]
  have hd : HasDerivAt (fun s => 2 - exp (-s)) (0 - -exp (-t)) t :=
    (hasDerivAt_const t (2 : ℝ)).sub hu
  have h := hu.div hd hden
  refine h.congr_deriv ?_
  simp only [field, mulVec, dotProduct, ← Finset.sum_mul, C₁_rowSum, trajExt]
  field_simp
  ring

/-- Direct decay `0 ≤ trajExt t ≤ e^{-t}`. -/
theorem trajExt_mem {t : ℝ} (ht : 0 ≤ t) : 0 ≤ trajExt t ∧ trajExt t ≤ exp (-t) := by
  have h1 := exp_neg_le_one ht
  exact ⟨div_nonneg (exp_pos _).le (by linarith), div_le_self (exp_pos _).le (by linarith)⟩

/-- The extinction theorem gives the same limit. -/
example : Tendsto (fun t (_ : Fin 2) => trajExt t) atTop (𝓝 0) :=
  tendsto_zero_of_lt_one C₁_nonneg (fun _ => two_pos)
    (by rw [persistenceNumber_C₁]; norm_num) isSolution_trajExt
    (fun _ => by rw [trajExt_zero]; norm_num)

/-- The exponential bound applies to the trajectory. -/
example : ∃ κ > 0, ∃ M : ℝ, ∀ t, 0 ≤ t → trajExt t ≤ M * exp (-(κ * t)) := by
  obtain ⟨κ, hκ, M, hM⟩ := exists_exp_bound_of_lt_one C₁_nonneg (fun _ => two_pos)
    (by rw [persistenceNumber_C₁]; norm_num)
  exact ⟨κ, hκ, M, fun t ht => hM _ isSolution_trajExt
    (fun _ => by rw [trajExt_zero]; norm_num) t ht 0⟩

/-- The linearization `C₁ - 2 I` is Hurwitz. -/
example : (C₁ - diagonal fun _ => 2).IsHurwitz :=
  (isHurwitz_iff C₁_nonneg fun _ => two_pos).2 (by rw [persistenceNumber_C₁]; norm_num)

/-! ### Irreducibility cannot be dropped -/

/-- Patches `0` and `1` colonize each other at rate `2`; patch `2` is isolated. -/
def C₃ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 2, 0; 2, 0, 0; 0, 0, 0]

theorem C₃_nonneg : ∀ i j, 0 ≤ C₃ i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [C₃]

/-- `R₀ > 1`, from the Collatz–Wielandt bound with `z = (1, 1, 0)`, `C₃ z = 2 z`. -/
theorem one_lt_persistenceNumber_C₃ : 1 < persistenceNumber C₃ (fun _ => 1) := by
  have hlow : ENNReal.ofReal 2 ≤ spectralRadius ℂ (C₃.map (algebraMap ℝ ℂ)) := by
    refine le_spectralRadius_of_smul_le_mulVec C₃_nonneg (z := ![1, 1, 0]) (fun i => ?_)
      (fun h => one_ne_zero (congrFun h 0)) zero_le_two fun i => ?_
    · fin_cases i <;> norm_num
    · fin_cases i <;> norm_num [C₃, mulVec, dotProduct, Fin.sum_univ_three]
  have hfin : spectralRadius ℂ (C₃.map (algebraMap ℝ ℂ)) ≠ ⊤ := by
    let _ : NormedRing (Matrix (Fin 3) (Fin 3) ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ) := Matrix.linftyOpNormedAlgebra
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm _)
  unfold persistenceNumber MathlibExt.Biology.Epidemiology.NextGenerationMatrix.R0
  rw [diagonal_one, inv_one, Matrix.mul_one]
  have := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hlow
  linarith

/-- Only the isolated patch occupied: `p(t) = (0, 0, e^{-t})`. -/
noncomputable def pIso (t : ℝ) : Fin 3 → ℝ := ![0, 0, exp (-t)]

/-- `pIso` solves the network system (derivative computed directly). -/
theorem isSolution_pIso : IsSolution C₃ (fun _ => 1) pIso := by
  refine ⟨fun t _ => hasDerivAt_pi.2 fun i => ?_⟩
  have hu : HasDerivAt (fun s => exp (-s)) (-exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  fin_cases i
  · simpa [pIso, field, C₃, mulVec, dotProduct, Fin.sum_univ_three] using
      hasDerivAt_const t (0 : ℝ)
  · simpa [pIso, field, C₃, mulVec, dotProduct, Fin.sum_univ_three] using
      hasDerivAt_const t (0 : ℝ)
  · simpa [pIso, field, C₃, mulVec, dotProduct, Fin.sum_univ_three] using hu

/-- `pIso` goes extinct (computed directly), although `R₀ > 1` and a patch starts occupied: the
persistence theorem needs `C` irreducible. -/
example : 1 < persistenceNumber C₃ (fun _ => 1) ∧ (∀ i, pIso 0 i ∈ Icc 0 1) ∧
    0 < pIso 0 2 ∧ Tendsto pIso atTop (𝓝 0) := by
  refine ⟨one_lt_persistenceNumber_C₃, fun i => ?_, by norm_num [pIso], ?_⟩
  · fin_cases i <;> norm_num [pIso]
  · refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · simp [pIso]
    · simp [pIso]
    · simpa [pIso] using tendsto_exp_neg_atTop_nhds_zero

end MathlibExtTest.Biology.Ecology.LevinsNetwork
