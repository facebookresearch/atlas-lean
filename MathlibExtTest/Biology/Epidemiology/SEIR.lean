/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.SEIR

/-!
# Tests for the closed SEIR model

The disease-free constant solution and its uniqueness; a purely latent seed
`(S, E, I, R)(0) = (99/100, 1/100, 0, 0)` with `β = 2`, `σ = γ = 1`, `N = 1`: existence,
`I(0) = 0` but `I'(0) > 0` and `I(t) > 0` for `t > 0`, limits and final size; standard simplex
data; the boundary `β = 0`; the field, `ℱ`, `𝒱`; and `R₀` at concrete rates.
-/

open Real Filter Set Matrix
open scoped Topology

namespace MathlibExtTest.Biology.Epidemiology.SEIR

open MathlibExt.Biology.Epidemiology MathlibExt.Biology.Epidemiology.SEIR

/-! ### The disease-free equilibrium -/

/-- Every disease-free state `(S₀, 0, 0, R₀)` is a constant solution (non-vacuity of
`IsSolution`). -/
theorem isSolution_dfe (β σ γ N S₀ R₀ : ℝ) :
    IsSolution β σ γ N (fun _ => S₀) (fun _ => 0) (fun _ => 0) (fun _ => R₀) :=
  ⟨fun t _ => by simpa using hasDerivAt_const t S₀,
    fun t _ => by simpa using hasDerivAt_const t (0 : ℝ),
    fun t _ => by simpa using hasDerivAt_const t (0 : ℝ),
    fun t _ => by simpa using hasDerivAt_const t R₀⟩

/-- Uniqueness: a solution starting disease-free stays disease-free. -/
example (β σ γ N S₀ R₀ : ℝ) (S E I R : ℝ → ℝ) (h : IsSolution β σ γ N S E I R)
    (hS : S 0 = S₀) (hE : E 0 = 0) (hI : I 0 = 0) (hR : R 0 = R₀) (t : ℝ) (ht : 0 ≤ t) :
    S t = S₀ ∧ E t = 0 ∧ I t = 0 ∧ R t = R₀ :=
  h.eq_of_initial (isSolution_dfe β σ γ N S₀ R₀) hS hE hI hR ht

/-! ### A purely latent seed -/

/-- Global existence at `(99/100, 1/100, 0, 0)`: nonnegative, total `1`. -/
example : ∃ S E I R : ℝ → ℝ, IsSolution 2 1 1 1 S E I R ∧ S 0 = 99 / 100 ∧ E 0 = 1 / 100 ∧
    I 0 = 0 ∧ R 0 = 0 ∧
      ∀ t, 0 ≤ t → 0 ≤ S t ∧ 0 ≤ E t ∧ 0 ≤ I t ∧ 0 ≤ R t ∧ S t + E t + I t + R t = 1 :=
  exists_isSolution_simplex (by norm_num) zero_le_one zero_le_one one_pos (by norm_num)
    (by norm_num) le_rfl le_rfl (by norm_num)

/-- A latent seed: no infectives at `t = 0`, yet `I'(0) > 0` and `I(t) > 0` for all `t > 0`;
`S` stays positive. -/
example : ∃ S E I R : ℝ → ℝ, IsSolution 2 1 1 1 S E I R ∧ I 0 = 0 ∧ 0 < deriv I 0 ∧
    ∀ t, 0 < t → 0 < I t ∧ 0 < S t := by
  obtain ⟨S, E, I, R, h, hS, hE, hI, hR, -⟩ := exists_isSolution_simplex (β := 2) (σ := 1)
    (γ := 1) (N := 1) (S₀ := 99 / 100) (E₀ := 1 / 100) (I₀ := 0) (R₀ := 0) (by norm_num)
    zero_le_one zero_le_one one_pos (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num)
  refine ⟨S, E, I, R, h, hI, h.deriv_infected_pos_of_exposed one_pos (by rw [hE]; norm_num) hI,
    fun t ht => ⟨?_, (h.susceptible_pos_iff ht.le).2 (by rw [hS]; norm_num)⟩⟩
  exact h.infected_pos_of_exposed_pos (by norm_num) one_pos zero_le_one zero_le_one
    (by rw [hS]; norm_num) (by rw [hE]; norm_num) hI.ge hR.ge ht

/-- Limits for the latent seed: `E, I → 0`, `S → S∞`, and `S∞` solves the final-size equation
`S∞ = (99/100) e^{-2 (1 - S∞)}` (`R₀ = 2`). -/
example : ∃ S E I R : ℝ → ℝ, IsSolution 2 1 1 1 S E I R ∧ Tendsto E atTop (𝓝 0) ∧
    Tendsto I atTop (𝓝 0) ∧ ∃ Sinf, Tendsto S atTop (𝓝 Sinf) ∧
      Sinf = 99 / 100 * exp (-(2 * (1 - Sinf))) := by
  obtain ⟨S, E, I, R, h, hS, hE, hI, hR, -⟩ := exists_isSolution_simplex (β := 2) (σ := 1)
    (γ := 1) (N := 1) (S₀ := 99 / 100) (E₀ := 1 / 100) (I₀ := 0) (R₀ := 0) (by norm_num)
    zero_le_one zero_le_one one_pos (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num)
  obtain ⟨Sinf, -, hSl, hEl, hIl, -, -, -, -, hfs⟩ := h.tendsto_final_size (by norm_num) one_pos
    one_pos zero_le_one (by rw [hS]; norm_num) (by rw [hE]; norm_num) hI.ge hR.ge
  refine ⟨S, E, I, R, h, hEl, hIl, Sinf, hSl, hfs.trans ?_⟩
  rw [hS, hE, hI]
  ring_nf

/-- Non-vacuity of `final_size_eq_of_root`: a root `x ≤ S(0)` of the final-size equation is the
limit of `S` (seed `E(0) + I(0) = 1/100 > 0`). -/
example (S E I R : ℝ → ℝ) (h : IsSolution 2 1 1 1 S E I R) (hS : S 0 = 99 / 100)
    (hE : E 0 = 1 / 100) (hI : I 0 = 0) (hR : R 0 = 0) {Sinf x : ℝ}
    (hSl : Tendsto S atTop (𝓝 Sinf)) (hx : x ≤ 99 / 100)
    (hxe : x = 99 / 100 * exp (-(2 / 1 * (1 - x) / 1))) : Sinf = x := by
  refine h.final_size_eq_of_root (by norm_num) one_pos one_pos one_pos (by rw [hS]; norm_num)
    (by rw [hE]; norm_num) hI.ge hR.ge (by rw [hE, hI]; norm_num) hSl (hS ▸ hx) ?_
  rw [hS, hE, hI]
  convert hxe using 5
  norm_num

/-! ### Standard simplex data and boundary cases -/

/-- `(97/100, 2/100, 1/100, 0)` with `β = 3/10`, `σ = 1/5`, `γ = 1/10`, `N = 1`. -/
example : ∃ S E I R : ℝ → ℝ, IsSolution (3 / 10) (1 / 5) (1 / 10) 1 S E I R ∧
    S 0 = 97 / 100 ∧ E 0 = 2 / 100 ∧ I 0 = 1 / 100 ∧ R 0 = 0 ∧
      ∀ t, 0 ≤ t → 0 ≤ S t ∧ 0 ≤ E t ∧ 0 ≤ I t ∧ 0 ≤ R t ∧ S t + E t + I t + R t = 1 :=
  exists_isSolution_simplex (by norm_num) (by norm_num) (by norm_num) one_pos (by norm_num)
    (by norm_num) (by norm_num) le_rfl (by norm_num)

/-- With an infectious seed, `E` becomes positive at once even if `E(0) = 0`, and the infected
total initially grows iff `R₀ S(0) / N > 1` (here `R₀ = 3`, `S(0) = 99/100`). -/
example : ∃ S E I R : ℝ → ℝ, IsSolution (3 / 10) (1 / 5) (1 / 10) 1 S E I R ∧ E 0 = 0 ∧
    (∀ t, 0 < t → 0 < E t) ∧ 0 < deriv (fun s => E s + I s) 0 := by
  obtain ⟨S, E, I, R, h, hS, hE, hI, hR, -⟩ := exists_isSolution_simplex (β := 3 / 10)
    (σ := 1 / 5) (γ := 1 / 10) (N := 1) (S₀ := 99 / 100) (E₀ := 0) (I₀ := 1 / 100) (R₀ := 0)
    (by norm_num) (by norm_num) (by norm_num) one_pos (by norm_num) le_rfl (by norm_num) le_rfl
    (by norm_num)
  refine ⟨S, E, I, R, h, hE, fun t ht => h.exposed_pos_of_infected_pos (by norm_num)
    (by norm_num) (by norm_num) one_pos (by rw [hS]; norm_num) hE.ge (by rw [hI]; norm_num)
    hR.ge ht, ?_⟩
  rw [h.deriv_exposed_add_infected_pos_iff (by norm_num) one_pos (by rw [hI]; norm_num), hS]
  norm_num

/-- No transmission (`β = 0`): `S` is constant. -/
example (σ γ N : ℝ) (S E I R : ℝ → ℝ) (h : IsSolution 0 σ γ N S E I R) (t : ℝ) (ht : 0 ≤ t) :
    S t = S 0 := by
  rw [h.susceptible_eq_mul_exp ht]
  simp

/-- Lower bounds `E(t) ≥ E(0) e^{-σ t}` and `I(t) ≥ I(0) e^{-γ t}` at a concrete time. -/
example (S E I R : ℝ → ℝ) (h : IsSolution 2 1 1 1 S E I R) (hS : S 0 = 1 / 2)
    (hE : E 0 = 1 / 4) (hI : I 0 = 1 / 4) (hR : R 0 = 0) :
    1 / 4 * exp (-(1 * 3)) ≤ E 3 ∧ 1 / 4 * exp (-(1 * 3)) ≤ I 3 := by
  refine ⟨hE ▸ h.exposed_ge (by norm_num) zero_le_one zero_le_one zero_le_one
    (by rw [hS]; norm_num) (by rw [hE]; norm_num) (by rw [hI]; norm_num) hR.ge (by norm_num),
    hI ▸ h.infected_ge (by norm_num) zero_le_one zero_le_one zero_le_one
    (by rw [hS]; norm_num) (by rw [hE]; norm_num) (by rw [hI]; norm_num) hR.ge (by norm_num)⟩

/-! ### The field and the next-generation splitting -/

example : seirField 2 1 1 1 0 ![1 / 2, 1 / 4, 1 / 4, 0] = ![-(1 / 4), 0, 0, 1 / 4] := by
  ext i
  fin_cases i <;> simp [seirField]

example : newInfections 2 1 (1 / 2) ![1 / 4, 1 / 4] = ![1 / 4, 0] := by
  ext i
  fin_cases i <;> simp [newInfections]

example : transfers 1 1 ![1 / 4, 1 / 4] = ![1 / 4, 0] := by
  ext i
  fin_cases i <;> simp [transfers]

/-- `E' = ℱ₀ - 𝒱₀` at a concrete state. -/
example : seirField 2 1 1 1 0 ![1 / 2, 1 / 4, 1 / 4, 0] 1 =
    newInfections 2 1 (1 / 2) ![1 / 4, 1 / 4] 0 - transfers 1 1 ![1 / 4, 1 / 4] 0 :=
  (seirField_infected_eq 2 1 1 1 0 _).1

/-! ### `R₀` -/

/-- `β = 3/10`, `σ = 1/5`, `γ = 1/10`: `R₀ = 3`, independent of `σ`. -/
example : NextGenerationMatrix.R0 !![0, 3 / 10; 0, 0] !![1 / 5, 0; -(1 / 5), 1 / 10] = 3 := by
  rw [R0_eq (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `R₀` computed from the literal derivatives of `ℱ` and `𝒱` at `N = 1000`. -/
example : NextGenerationMatrix.R0
    (LinearMap.toMatrix' (fderiv ℝ (newInfections 2 1000 1000) 0 :
      (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ))
    (LinearMap.toMatrix' (fderiv ℝ (transfers 1 (1 / 2)) 0 : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ)) =
      4 := by
  rw [R0_fderiv_eq (by norm_num) one_pos (by norm_num) (by norm_num)]
  norm_num

/-- `β = 0`: `R₀ = 0`. -/
example (σ γ : ℝ) (hσ : 0 < σ) (hγ : 0 < γ) :
    NextGenerationMatrix.R0 !![0, 0; 0, 0] !![σ, 0; -σ, γ] = 0 := by
  rw [R0_eq le_rfl hσ hγ, zero_div]

/-- Linearized threshold, both sides. -/
example : (!![0, 1 / 2; 0, 0] - !![1, 0; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsHurwitz :=
  (isHurwitz_iff (by norm_num) one_pos one_pos).2 (by norm_num)

example : ∃ μ ∈ spectrum ℂ ((!![0, 2; 0, 0] - !![1, 0; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).map
    (algebraMap ℝ ℂ)), 0 < μ.re :=
  (exists_re_pos_iff (by norm_num) one_pos one_pos).2 (by norm_num)

/-- The `F = 0` boundary: with `β = 0` the infected block is Hurwitz. -/
example : (!![0, 0; 0, 0] - !![1, 0; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsHurwitz :=
  (isHurwitz_iff le_rfl one_pos one_pos).2 one_pos

/-- The Jacobian of the infected rates at the disease-free state `(S, R) = (1, 0)`. -/
example : HasFDerivAt (fun x : Fin 2 → ℝ => ![seirField 2 1 1 1 0 ![1, x 0, x 1, 0] 1,
    seirField 2 1 1 1 0 ![1, x 0, x 1, 0] 2])
    (LinearMap.toContinuousLinearMap (Matrix.toLin' (!![0, 2; 0, 0] - !![1, 0; -1, 1]))) 0 :=
  hasFDerivAt_infectedField 0 0 one_ne_zero

end MathlibExtTest.Biology.Epidemiology.SEIR
