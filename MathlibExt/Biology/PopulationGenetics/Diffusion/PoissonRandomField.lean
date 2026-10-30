/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.Sojourn
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Poisson random field: expected site-frequency spectrum under selection

In the Poisson random field model of Sawyer and Hartl (1992), new mutations arise at the
scaled rate `θ = 4Nu` (time in units of `2N` generations, `u` the mutation rate per gene copy
per generation, summed over the sites of the locus) at independent sites, each with genic
selection of scaled strength `σ = 2Ns` on the derived allele. At stationarity the number of
sites whose derived-allele frequency lies in `(x, x + dx)` is Poisson with mean `φ(x) dx`, where

  `φ(x) = θ (1 - e^{-2σ(1 - x)}) / ((1 - e^{-2σ}) x (1 - x))`,   `φ(x) = θ / x` if `σ = 0`.

Writing `φ(x) = θ · u_σ(1 - x) / (x (1 - x))` with Kimura's fixation probability `u_σ`
(`kimuraFixation`) covers both cases at once. Sampling `n` gene copies, the expected number of
sites at which exactly `i` copies carry the derived allele (the unfolded site-frequency
spectrum) is `E ξ_i = ∫ x in 0..1, C(n, i) x ^ i (1 - x) ^ (n - i) φ(x)`; in the neutral case
it is `θ / i` (Fu 1995).

The Poisson-process construction itself is not formalized; the statements are the analytic
facts about `φ` and `E ξ_i`.

## Main results

* `prfDensity`, `expectedSFS`: the density `φ` and the expected spectrum `E ξ_i`.
* `prfDensity_of_ne_zero`, `prfDensity_zero`: the explicit formulas.
* `prfDensity_zero_eq_neutralGreen`: the neutral density is `θ / (2p) · G(p, x)` for `x ≥ p`,
  the sojourn density of mutations entering at frequency `p`.
* `forward_prfDensity`: the flux `F(x) = x (1 - x) φ(x)` solves the stationary forward
  (Fokker–Planck) equation `½ F'' - σ F' = 0` on `(0, 1)`, with boundary values
  `F(0⁺) = θ` (influx of new mutations) and `F(1⁻) = 0` (`tendsto_flux_prfDensity_zero`,
  `tendsto_flux_prfDensity_one`).
* `eq_prfDensity_of_forward`: these conditions characterize `φ` on `(0, 1)`.
* `expectedSFS_neutral`: `E ξ_i = θ / i` for `σ = 0` and `1 ≤ i ≤ n`.

## References

* S. A. Sawyer and D. L. Hartl, *Population genetics of polymorphism and divergence*,
  Genetics 132 (1992) 1161–1176.
* Y.-X. Fu, *Statistical properties of segregating sites*, Theor. Popul. Biol. 48 (1995)
  172–197.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The Sawyer–Hartl (1992) Poisson-random-field density: the expected number of sites per unit
frequency at which the derived allele has frequency `x`, for scaled mutation rate `θ = 4Nu`
and scaled genic selection `σ = 2Ns`:
`θ · u_σ(1 - x) / (x (1 - x))` with `u_σ = kimuraFixation σ`, i.e.
`θ (1 - e^{-2σ(1 - x)}) / ((1 - e^{-2σ}) x (1 - x))`, and `θ / x` when `σ = 0`.
The model domain is `θ > 0` and `x ∈ (0, 1)`; at `x = 0, 1` Lean's `a / 0 = 0` gives the junk
value `0`. -/
noncomputable def prfDensity (θ σ x : ℝ) : ℝ :=
  θ * kimuraFixation σ (1 - x) / (x * (1 - x))

/-- The Poisson-random-field density with selection, explicitly:
`θ (1 - e^{-2σ(1 - x)}) / ((1 - e^{-2σ}) x (1 - x))` for `σ ≠ 0`. -/
theorem prfDensity_of_ne_zero (θ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    prfDensity θ σ x = θ * (1 - exp (-2 * σ * (1 - x))) / ((1 - exp (-2 * σ)) * x * (1 - x)) := by
  simp only [prfDensity, kimuraFixation, hσ, ↓reduceIte]
  rw [mul_div_assoc', div_div, ← mul_assoc]

/-- The neutral Poisson-random-field density is `θ / x` (for `x ≠ 1`). -/
theorem prfDensity_zero (θ : ℝ) {x : ℝ} (hx : x ≠ 1) : prfDensity θ 0 x = θ / x := by
  have h1 : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  simp only [prfDensity, kimuraFixation_neutral]
  rw [mul_comm x, ← div_div, mul_div_cancel_right₀ _ h1]

/-- **The neutral density from the Green's function.** A new neutral mutation enters at a
small frequency `p`; with mutations arriving at rate `θ / (2p)` per unit time (so that the
mutational input of frequency is `θ / 2`), the expected sojourn density at `x ≥ p` is
`θ / (2p) · G(p, x) = θ / x`, the neutral Poisson-random-field density. -/
theorem prfDensity_zero_eq_neutralGreen (θ : ℝ) {p x : ℝ} (hp : 0 < p) (hpx : p ≤ x)
    (hx : x < 1) : prfDensity θ 0 x = θ / (2 * p) * neutralGreen p x := by
  have hx0 : 0 < x := hp.trans_le hpx
  rw [prfDensity_zero θ hx.ne, neutralGreen]
  split_ifs with h
  · have hxp : x = p := le_antisymm h hpx
    subst hxp
    have : 1 - x ≠ 0 := (sub_pos.2 hx).ne'
    field_simp
  · field_simp

/-- On `(0, 1)` the flux `x (1 - x) φ(x)` is `θ · u_σ(1 - x)`. -/
private theorem flux_prfDensity (θ σ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x * (1 - x) * prfDensity θ σ x = θ * kimuraFixation σ (1 - x) := by
  have h0 : x * (1 - x) ≠ 0 := mul_ne_zero hx.1.ne' (sub_pos.2 hx.2).ne'
  rw [prfDensity, mul_div_cancel₀ _ h0]

private theorem flux_eventuallyEq (θ σ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (fun y => y * (1 - y) * prfDensity θ σ y) =ᶠ[𝓝 x]
      fun y => θ * kimuraFixation σ (1 - y) :=
  eventually_of_mem (isOpen_Ioo.mem_nhds hx) fun _ hy => flux_prfDensity θ σ hy

private theorem hasDerivAt_flux (θ σ y : ℝ) :
    HasDerivAt (fun y => θ * kimuraFixation σ (1 - y))
      (-(θ * kimuraSlope σ) * exp (-2 * σ * (1 - y))) y := by
  have h := ((hasDerivAt_kimuraFixation σ (1 - y)).comp y
    ((hasDerivAt_id' y).const_sub 1)).const_mul θ
  exact h.congr_deriv (by ring)

/-- **Stationary forward equation (Sawyer–Hartl 1992).** On `(0, 1)` the flux
`F(x) = x (1 - x) φ(x)` of the Poisson-random-field density solves the stationary
Fokker–Planck equation `½ F'' - σ F' = 0` of the Wright–Fisher diffusion with genic selection
`σ` (the forward equation `½ (x (1 - x) φ)'' - (σ x (1 - x) φ)' = 0`). -/
theorem forward_prfDensity (θ σ : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv fun y => y * (1 - y) * prfDensity θ σ y) x / 2 -
      σ * deriv (fun y => y * (1 - y) * prfDensity θ σ y) x = 0 := by
  have hD : deriv (fun y => y * (1 - y) * prfDensity θ σ y) =ᶠ[𝓝 x]
      fun y => -(θ * kimuraSlope σ) * exp (-2 * σ * (1 - y)) :=
    (flux_eventuallyEq θ σ hx).deriv.trans
      (Eventually.of_forall fun y => (hasDerivAt_flux θ σ y).deriv)
  have h2 : HasDerivAt (fun y => -(θ * kimuraSlope σ) * exp (-2 * σ * (1 - y)))
      (-(θ * kimuraSlope σ) * (exp (-2 * σ * (1 - x)) * (2 * σ))) x := by
    refine HasDerivAt.const_mul _ ?_
    convert (((hasDerivAt_id' x).const_sub 1).const_mul (-2 * σ)).exp using 1
    ring
  rw [hD.deriv_eq, h2.deriv, hD.eq_of_nhds]
  ring

/-- **Influx boundary condition.** As `x → 0⁺` the flux `x (1 - x) φ(x)` tends to `θ`: new
mutations enter the frequency space at the boundary `0` at the scaled rate `θ`. -/
theorem tendsto_flux_prfDensity_zero (θ σ : ℝ) :
    Tendsto (fun y => y * (1 - y) * prfDensity θ σ y) (𝓝[>] 0) (𝓝 θ) := by
  have hc : Tendsto (fun y => θ * kimuraFixation σ (1 - y)) (𝓝[>] 0) (𝓝 θ) := by
    have hcont : Continuous fun y : ℝ => θ * kimuraFixation σ (1 - y) :=
      continuous_const.mul ((continuous_kimuraFixation σ).comp (continuous_const.sub continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with y hy
  exact (flux_prfDensity θ σ hy).symm

/-- **Absorbing boundary condition.** As `x → 1⁻` the flux `x (1 - x) φ(x)` tends to `0`. -/
theorem tendsto_flux_prfDensity_one (θ σ : ℝ) :
    Tendsto (fun y => y * (1 - y) * prfDensity θ σ y) (𝓝[<] 1) (𝓝 0) := by
  have hc : Tendsto (fun y => θ * kimuraFixation σ (1 - y)) (𝓝[<] 1) (𝓝 0) := by
    have hcont : Continuous fun y : ℝ => θ * kimuraFixation σ (1 - y) :=
      continuous_const.mul ((continuous_kimuraFixation σ).comp (continuous_const.sub continuous_id))
    simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with y hy
  exact (flux_prfDensity θ σ hy).symm

/-- **ODE characterization of the Poisson-random-field density.** Let `θ ≠ 0` and let `φ` be
a density on `(0, 1)` whose flux `x (1 - x) φ(x)` extends to a function `F` continuous on
`[0, 1]`, twice differentiable on `(0, 1)`, solving the stationary forward equation
`½ F'' - σ F' = 0` there, with influx `F(0) = θ` and `F(1) = 0`. Then `φ` is the Sawyer–Hartl
density on `(0, 1)`. -/
theorem eq_prfDensity_of_forward {θ σ : ℝ} (hθ : θ ≠ 0) {φ F : ℝ → ℝ}
    (hF : ∀ x ∈ Ioo (0 : ℝ) 1, F x = x * (1 - x) * φ x) (hcont : ContinuousOn F (Icc 0 1))
    (hdiff : DifferentiableOn ℝ F (Ioo 0 1)) (hdiff' : DifferentiableOn ℝ (deriv F) (Ioo 0 1))
    (hfwd : ∀ x ∈ Ioo (0 : ℝ) 1, deriv (deriv F) x / 2 - σ * deriv F x = 0)
    (h0 : F 0 = θ) (h1 : F 1 = 0) :
    ∀ x ∈ Ioo (0 : ℝ) 1, φ x = prfDensity θ σ x := by
  have hmem : ∀ y ∈ Ioo (0 : ℝ) 1, 1 - y ∈ Ioo (0 : ℝ) 1 := fun y hy =>
    ⟨sub_pos.2 hy.2, by linarith [hy.1]⟩
  -- `u y = F (1 - y) / θ` solves the backward fixation problem.
  set u : ℝ → ℝ := fun y => F (1 - y) / θ with hu
  have hd1 : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt u (-deriv F (1 - y) / θ) y := by
    intro y hy
    have hF' : HasDerivAt F (deriv F (1 - y)) (1 - y) :=
      (hdiff.differentiableAt (isOpen_Ioo.mem_nhds (hmem y hy))).hasDerivAt
    exact ((hF'.comp y ((hasDerivAt_id' y).const_sub 1)).div_const θ).congr_deriv (by ring)
  have hD : ∀ y ∈ Ioo (0 : ℝ) 1, deriv u =ᶠ[𝓝 y] fun z => -deriv F (1 - z) / θ := fun y hy =>
    eventually_of_mem (isOpen_Ioo.mem_nhds hy) fun z hz => (hd1 z hz).deriv
  have hd2 : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun z => -deriv F (1 - z) / θ) (deriv (deriv F) (1 - y) / θ) y := by
    intro y hy
    have hF'' : HasDerivAt (deriv F) (deriv (deriv F) (1 - y)) (1 - y) :=
      (hdiff'.differentiableAt (isOpen_Ioo.mem_nhds (hmem y hy))).hasDerivAt
    exact (((hF''.comp y ((hasDerivAt_id' y).const_sub 1)).neg).div_const θ).congr_deriv
      (by ring)
  have hkim := eq_kimuraFixation_of_generator_eq_zero (σ := σ) (u := u)
    (fun y hy => ((hcont (1 - y) ⟨sub_nonneg.2 hy.2, by linarith [hy.1]⟩).comp
      ((continuous_const.sub continuous_id).continuousWithinAt) (fun z hz =>
        ⟨sub_nonneg.2 hz.2, by linarith [hz.1]⟩)).div_const θ)
    (fun y hy => (hd1 y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => ((hd2 y hy).differentiableAt.congr_of_eventuallyEq
      (hD y hy)).differentiableWithinAt)
    (fun y hy => by
      rw [generator, (hD y hy).deriv_eq, (hd2 y hy).deriv, (hd1 y hy).deriv]
      have := hfwd (1 - y) (hmem y hy)
      field_simp
      linear_combination y * (1 - y) * 2 * this)
    (by simp [hu, h1]) (by simp [hu, h0, hθ])
  intro x hx
  have hx0 : x * (1 - x) ≠ 0 := mul_ne_zero hx.1.ne' (sub_pos.2 hx.2).ne'
  have hk := hkim (1 - x) ⟨sub_nonneg.2 hx.2.le, by linarith [hx.1]⟩
  simp only [hu, sub_sub_cancel] at hk
  rw [prfDensity, ← hk, mul_div_cancel₀ _ hθ, hF x hx, mul_div_cancel_left₀ _ hx0]

/-- The expected unfolded site-frequency spectrum of a sample of `n` gene copies under the
Poisson random field: the expected number of sites where exactly `i` of the `n` sampled copies
carry the derived allele, `E ξ_i = ∫ x in 0..1, C(n, i) x ^ i (1 - x) ^ (n - i) φ(x)`.
Meaningful for `1 ≤ i ≤ n`: for `i = 0` the integrand is not integrable at `0` (the expected
number of monomorphic sites is infinite) and Lean's integral returns its junk value `0`. -/
noncomputable def expectedSFS (θ σ : ℝ) (n i : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i) * prfDensity θ σ x

/-- The Beta integral at natural arguments: `∫₀¹ x^a (1 - x)^b dx = a! b! / (a + b + 1)!`. -/
private theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b =
      (a.factorial * b.factorial / (a + b + 1).factorial : ℝ) := by
  induction b generalizing a with
  | zero =>
    have : (a.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
    simp [integral_pow, Nat.factorial_succ]
    field_simp
  | succ b ih =>
    have h : ∀ x : ℝ, x ^ a * (1 - x) ^ (b + 1) =
        x ^ a * (1 - x) ^ b - x ^ (a + 1) * (1 - x) ^ b := fun x => by ring
    simp_rw [h]
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun x : ℝ => x ^ a * (1 - x) ^ b).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun x : ℝ => x ^ (a + 1) * (1 - x) ^ b).intervalIntegrable 0 1),
      ih a, ih (a + 1), show a + 1 + b + 1 = a + b + 1 + 1 by ring,
      show a + (b + 1) + 1 = a + b + 1 + 1 by ring, Nat.factorial_succ (a + b + 1),
      Nat.factorial_succ a, Nat.factorial_succ b]
    have : (a.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
    have : (b.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)
    have : ((a + b + 1).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    field_simp
    ring

/-- **Neutral site-frequency spectrum (Fu 1995).** With `σ = 0`, for `1 ≤ i ≤ n` the expected
number of sites with `i` derived copies in a sample of `n` is `θ / i`. -/
theorem expectedSFS_neutral (θ : ℝ) {n i : ℕ} (hi : 0 < i) (hin : i ≤ n) :
    expectedSFS θ 0 n i = θ / i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = j + 1 + m := ⟨n - (j + 1), by omega⟩
  have hsub : j + 1 + m - (j + 1) = m := by omega
  have hc : ((j + 1 + m).choose (j + 1) : ℝ) * (j + 1).factorial * m.factorial =
      (j + 1 + m).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (j + 1) m)
    rw [hsub] at this
    exact_mod_cast this
  have hint : expectedSFS θ 0 (j + 1 + m) (j + 1) =
      ∫ x in (0 : ℝ)..1, θ * ((j + 1 + m).choose (j + 1) : ℝ) * (x ^ j * (1 - x) ^ m) := by
    unfold expectedSFS
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
    rw [prfDensity, kimuraFixation, ite_eq_left rfl, hsub]
    field_simp
    ring
  have hC : ((j + 1 + m).choose (j + 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right _ _)).ne'
  have hj : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  rw [hint, intervalIntegral.integral_const_mul, integral_pow_mul_one_sub_pow,
    show j + m + 1 = j + 1 + m by ring, ← hc, Nat.factorial_succ j]
  push_cast
  field_simp

end MathlibExt.Biology.PopulationGenetics.Diffusion
