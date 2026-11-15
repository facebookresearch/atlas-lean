/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.SIS
public import MathlibExt.Biology.Epidemiology.SEIRGlobalStability
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue

/-!
# The SIS model with leaky vaccination: threshold, critical coverage and global stability

A closed population of size `N` mixes homogeneously. A fraction `p` of it has been vaccinated
(once, permanently) with a **leaky** vaccine of efficacy `ε`: a vaccinated susceptible is
infected at `1 - ε` times the rate of an unvaccinated one. Infection confers no immunity, and
recovery at rate `γ` returns an individual to the susceptible class of its own group. With
transmission rate `β` and force of infection `λ = β (I_u + I_v) / N`,

  `S_u' = -λ S_u + γ I_u`,             `I_u' = λ S_u - γ I_u`,
  `S_v' = -(1 - ε) λ S_v + γ I_v`,     `I_v' = (1 - ε) λ S_v - γ I_v`,

with `S_u + I_u = (1 - p) N` and `S_v + I_v = p N` conserved. For `ε = 0` the totals
`S = S_u + S_v`, `I = I_u + I_v` solve the unvaccinated SIS model
`MathlibExt.Biology.Epidemiology.SIS.IsSolution` (`IsSolution.toSIS`), whose analysis is
reused rather than repeated.

**Parameter domain.** The epidemiological parameters are `β ≥ 0`, `γ > 0`, `0 ≤ ε ≤ 1`,
`0 ≤ p ≤ 1` and `N > 0`; each theorem states the hypotheses it uses. `Rv` and
`criticalCoverage` are total functions that follow Lean's convention `x / 0 = 0`: `Rv` has its
epidemiological meaning for `γ > 0`, and `criticalCoverage` for `β, ε > 0`.

The **vaccinated reproduction number** is `R_v = R₀ (1 - ε p)` with `R₀ = β / γ`, and the
**critical vaccination coverage** is `p_c = (1 - 1 / R₀) / ε`. For `β, γ, ε > 0`,
`R_v < 1 ↔ p > p_c` (`Rv_lt_one_iff`). Without transmission (`β = 0`) there is no threshold:
`R_v = 0 < 1` at every coverage (`Rv_zero_transmission`), so the disease-free statements below
apply, while `criticalCoverage 0 γ ε = 1 / ε` is a convention value with no epidemiological
meaning. The threshold is sharp:

* **Disease-free side.** If `R_v < 1` (any `ε ∈ [0, 1]`), or `R_v = 1` and `ε < 1`, every
  solution with nonnegative initial state has `I_u, I_v → 0` and `S_u → (1 - p) N`,
  `S_v → p N`; the total `I_u + I_v` is nonincreasing (stability of the disease-free state) and,
  for `R_v < 1`, decays like `e^{-γ (1 - R_v) t}`. The proof uses
  `d/dt (I_u + I_v) = γ (R_v - 1) (I_u + I_v) - (β / N) (I_u + I_v) (I_u + (1 - ε) I_v)`.
* **Endemic side.** For `0 < p < 1` and `ε < 1`, a positive (endemic) equilibrium exists iff
  `R_v > 1` (`exists_isEndemicEq`, `one_lt_Rv_of_isEndemicEq`). It is unique, and it attracts
  every solution with nonnegative susceptibles and positive infectives in both groups, with an
  explicit stability bound (`IsSolution.endemic_stability`). The Lyapunov function is the sum
  of Volterra functions `V = g(I_u*, I_u) + g(I_v*, I_v)`, `g(a, x) = x - a - a log (x / a)`
  (`SEIRVital.volterra`), with

    `V' = -(β/N) I (I_u - I_u*)² / I_u - ((1-ε)β/N) I (I_v - I_v*)² / I_v
          - γ (I_u I_v* - I_v I_u*)² / ((I_u* + I_v*) I_u I_v) ≤ 0`,

  `I = I_u + I_v`; the last term is the two-group Cauchy–Schwarz (AM–HM) defect. As in
  `SISGlobalStability`, convergence is quantitative: `V(t) ≤ V(0) e^{-κ t}`.

So, for `β, γ, ε > 0`, `p > p_c` eliminates the infection, and `p < p_c` leaves it endemic when
`0 < p < 1` and `ε < 1` (`IsSolution.tendsto_endemic_of_lt`). Algebraically, for `ε > 0` the
critical coverage is attainable (`p_c ≤ 1`) iff `ε ≥ 1 - 1 / R₀` (`criticalCoverage_le_one_iff`);
the dynamic converse at full coverage `p = 1` is not proved here (`exists_isEndemicEq` needs
`p < 1`).

## Main results

* `IsSolution β γ ε N S_u I_u S_v I_v`, `Rv`, `criticalCoverage`.
* `IsSolution.toSIS`, `IsSolution.tendsto_totalInfected_endemic_of_efficacy_zero`: `ε = 0`
  reduces to SIS (`SIS.IsSolution.tendsto_infected_endemic`).
* `Rv_zero_coverage_eq_R0`: `R_v(p = 0)` is the SIS next-generation `R₀` of `SIS.R0_eq`.
* `Rv_lt_one_iff`, `Rv_le_one_iff`, `one_lt_Rv_iff`: the critical coverage, for `β, γ, ε > 0`.
* `Rv_zero_transmission`: without transmission `R_v = 0`.
* `IsSolution.nonneg`: forward invariance of the nonnegative orthant.
* `IsSolution.totalInfected_le_initial`, `IsSolution.totalInfected_le_exp`,
  `IsSolution.totalInfected_le_critical`: bounds on the disease-free side.
* `IsSolution.tendsto_dfe`, `IsSolution.tendsto_dfe_of_criticalCoverage_le`: extinction.
* `IsEndemicEq`, `one_lt_Rv_of_isEndemicEq`, `exists_isEndemicEq`, `isSolution_const_endemic`.
* `lyapunov`, `lyapunovDeriv`, `lyapunov_deriv_eq`, `IsSolution.hasDerivAt_lyapunov`.
* `IsSolution.exists_lyapunov_le_exp`, `IsSolution.tendsto_endemic`,
  `IsSolution.endemic_stability`, `IsEndemicEq.unique`, `IsSolution.tendsto_endemic_of_lt`.

## Scope

* A perfect vaccine at exactly the critical coverage (`ε = 1`, `R_v = 1`) is not covered:
  `IsSolution.tendsto_dfe` needs `R_v < 1`, or `R_v = 1` together with `ε < 1`.
* Endemic convergence is proved only when both groups start with infectives
  (`I_u(0), I_v(0) > 0`); a solution with `I_u(0) = 0` or `I_v(0) = 0` (and positive total) is
  not treated.
* Existence of general non-constant solutions is not proved. The hypotheses are shown
  satisfiable by the constant equilibria (`isSolution_const_dfe`, `isSolution_const_endemic`)
  and, in the tests, by an explicit non-constant solution for `ε = 1` built from
  `SIS.isSolution_sis`.

## References

* H. W. Hethcote, *The mathematics of infectious diseases*, SIAM Review 42 (2000) 599–653,
  §§3, 5 (SIS, herd immunity threshold `1 - 1 / R₀`).
* A. Lajmanovich and J. A. Yorke, *A deterministic model for gonorrhea in a nonhomogeneous
  population*, Math. Biosci. 28 (1976) 221–236 (multigroup SIS threshold and global stability).
* R. M. Anderson and R. M. May, *Infectious Diseases of Humans*, Oxford (1991), §5 (critical
  coverage with imperfect vaccines).
-/

@[expose] public section

open Real Filter Set Matrix
open scoped Topology

namespace MathlibExt.Biology.Epidemiology.SISVaccination

open SEIRVital (volterra volterra_nonneg hasDerivAt_volterra le_of_volterra_le sq_le_volterra)

/-! ### Two calculus lemmas on `[0, ∞)` -/

/-- **Nonnegativity propagates.** If `u(0) ≥ 0` and `u' ≥ 0` wherever `u < 0` on `[0, T]`, then
`u ≥ 0` on `[0, T]`. (After the last zero before a negative value, `u` would be negative and
nondecreasing.) -/
theorem nonneg_of_hasDerivAt {u u' : ℝ → ℝ} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt u (u' t) t) (h0 : 0 ≤ u 0)
    (hneg : ∀ t ∈ Icc 0 T, u t < 0 → 0 ≤ u' t) : ∀ t ∈ Icc 0 T, 0 ≤ u t := by
  intro t₁ ht₁
  by_contra hlt
  rw [not_le] at hlt
  have hcont : ContinuousOn u (Icc 0 t₁) := fun s hs =>
    (hd s ⟨hs.1, hs.2.trans ht₁.2⟩).continuousAt.continuousWithinAt
  set A : Set ℝ := Icc 0 t₁ ∩ u ⁻¹' Ici 0
  have hA : IsClosed A := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hne : A.Nonempty := ⟨0, ⟨le_rfl, ht₁.1⟩, h0⟩
  have hbdd : BddAbove A := ⟨t₁, fun s hs => hs.1.2⟩
  have hτ := hA.csSup_mem hne hbdd
  set τ := sSup A
  have hτ0 : 0 ≤ u τ := hτ.2
  have hτt : τ < t₁ := lt_of_le_of_ne hτ.1.2 fun h => by rw [h] at hτ0; linarith
  have hafter : ∀ s ∈ Ioc τ t₁, u s < 0 := fun s hs => by
    by_contra h
    exact absurd (le_csSup hbdd ⟨⟨hτ.1.1.trans hs.1.le, hs.2⟩, not_lt.1 h⟩) (not_le.2 hs.1)
  have hmono : MonotoneOn u (Icc τ t₁) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := u') (convex_Icc τ t₁)
      (fun s hs => (hd s ⟨hτ.1.1.trans hs.1, hs.2.trans ht₁.2⟩).continuousAt.continuousWithinAt)
      (fun s hs => ?_) (fun s hs => ?_) <;> rw [interior_Icc] at hs
    · exact (hd s ⟨hτ.1.1.trans hs.1.le, hs.2.le.trans ht₁.2⟩).hasDerivWithinAt
    · exact hneg s ⟨hτ.1.1.trans hs.1.le, hs.2.le.trans ht₁.2⟩ (hafter s ⟨hs.1, hs.2.le⟩)
  have := hmono ⟨le_rfl, hτt.le⟩ ⟨hτt.le, le_rfl⟩ hτt.le
  linarith

/-- **Exponential comparison.** If `W' ≤ -κ W` on `[0, ∞)`, then `W(t) ≤ W(0) e^{-κ t}`. -/
theorem le_mul_exp_of_hasDerivAt {W W' : ℝ → ℝ} {κ : ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt W (W' t) t) (h : ∀ t, 0 ≤ t → W' t ≤ -κ * W t)
    {t : ℝ} (ht : 0 ≤ t) : W t ≤ W 0 * exp (-κ * t) := by
  have hg : ∀ s, 0 ≤ s → HasDerivAt (fun s => W s * exp (κ * s))
      (W' s * exp (κ * s) + W s * (exp (κ * s) * κ)) s := fun s hs =>
    (hd s hs).mul (by simpa using ((hasDerivAt_id s).const_mul κ).exp)
  have hanti : AntitoneOn (fun s => W s * exp (κ * s)) (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun s => W' s * exp (κ * s) + W s * (exp (κ * s) * κ)) (convex_Ici 0)
      (fun s hs => (hg s hs).continuousAt.continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Ici] at hs
      exact (hg s (le_of_lt hs)).hasDerivWithinAt
    · rw [interior_Ici] at hs
      have h1 := mul_le_mul_of_nonneg_left (h s (le_of_lt hs)) (exp_pos (κ * s)).le
      nlinarith
  have h1 : W t * exp (κ * t) ≤ W 0 := by
    simpa using hanti (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  have h2 : W t = W t * exp (κ * t) * exp (-κ * t) := by
    rw [mul_assoc, ← exp_add]; simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (exp_pos _).le

/-! ### The model -/

/-- `(S_u, I_u, S_v, I_v)` solves the SIS model with leaky vaccination for `t ≥ 0`: transmission
rate `β`, recovery rate `γ`, vaccine efficacy `ε` (vaccinated susceptibles are infected at
`1 - ε` times the unvaccinated rate) and mixing population `N`. -/
structure IsSolution (β γ ε N : ℝ) (Su Iu Sv Iv : ℝ → ℝ) : Prop where
  /-- Unvaccinated susceptibles are infected at rate `β S_u I / N` and regained at rate
  `γ I_u`. -/
  hasDerivAt_Su : ∀ t, 0 ≤ t → HasDerivAt Su (-(β * Su t * (Iu t + Iv t) / N) + γ * Iu t) t
  /-- Unvaccinated infectives. -/
  hasDerivAt_Iu : ∀ t, 0 ≤ t → HasDerivAt Iu (β * Su t * (Iu t + Iv t) / N - γ * Iu t) t
  /-- Vaccinated susceptibles are infected at the reduced rate `(1 - ε) β S_v I / N`. -/
  hasDerivAt_Sv : ∀ t, 0 ≤ t →
    HasDerivAt Sv (-((1 - ε) * β * Sv t * (Iu t + Iv t) / N) + γ * Iv t) t
  /-- Vaccinated infectives. -/
  hasDerivAt_Iv : ∀ t, 0 ≤ t →
    HasDerivAt Iv ((1 - ε) * β * Sv t * (Iu t + Iv t) / N - γ * Iv t) t

/-- The **vaccinated reproduction number** `R_v = R₀ (1 - ε p)`, `R₀ = β / γ`: coverage `p`,
efficacy `ε`. It has its epidemiological meaning for `γ > 0`; at `γ = 0` Lean's convention
`β / 0 = 0` makes it `0`. -/
noncomputable def Rv (β γ ε p : ℝ) : ℝ := β / γ * (1 - ε * p)

/-- The **critical vaccination coverage** `p_c = (1 - 1 / R₀) / ε = (1 - γ / β) / ε`. It has its
epidemiological meaning for `β, ε > 0`; Lean's convention `x / 0 = 0` makes it `0` at `ε = 0` and
`1 / ε` at `β = 0`, and the threshold theorems (`Rv_lt_one_iff` and its variants) assume
`β, γ, ε > 0`. -/
noncomputable def criticalCoverage (β γ ε : ℝ) : ℝ := (1 - γ / β) / ε

/-! ### Threshold algebra -/

section Threshold

variable {β γ ε p : ℝ}

@[simp]
theorem Rv_zero_coverage (β γ ε : ℝ) : Rv β γ ε 0 = β / γ := by simp [Rv]

@[simp]
theorem Rv_zero_efficacy (β γ p : ℝ) : Rv β γ 0 p = β / γ := by simp [Rv]

/-- Without transmission (`β = 0`) the vaccinated reproduction number is `0` at every coverage,
so the disease-free results apply; the threshold equivalences need `β > 0`. -/
@[simp]
theorem Rv_zero_transmission (γ ε p : ℝ) : Rv 0 γ ε p = 0 := by simp [Rv]

/-- Without vaccination, `R_v` is the next-generation `R₀` of the SIS model (`SIS.R0_eq`). -/
theorem Rv_zero_coverage_eq_R0 (hβ : 0 ≤ β) (hγ : 0 < γ) :
    Rv β γ ε 0 = NextGenerationMatrix.R0 !![β] !![γ] := by
  rw [Rv_zero_coverage, SIS.R0_eq hβ hγ]

private theorem Rv_eq (β γ ε p : ℝ) : Rv β γ ε p = (β - β * ε * p) / γ := by
  unfold Rv; ring

private theorem criticalCoverage_eq (hβ : 0 < β) (hε : 0 < ε) :
    criticalCoverage β γ ε = (β - γ) / (β * ε) := by
  unfold criticalCoverage; field_simp

/-- **Critical coverage, strict.** For `β, γ, ε > 0`, `R_v < 1` iff the coverage exceeds `p_c`. -/
theorem Rv_lt_one_iff (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 < ε) :
    Rv β γ ε p < 1 ↔ criticalCoverage β γ ε < p := by
  rw [Rv_eq, criticalCoverage_eq hβ hε, div_lt_one hγ, div_lt_iff₀ (mul_pos hβ hε)]
  constructor <;> intro h <;> linarith

/-- **Critical coverage.** For `β, γ, ε > 0`, `R_v ≤ 1` iff the coverage is at least `p_c`. -/
theorem Rv_le_one_iff (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 < ε) :
    Rv β γ ε p ≤ 1 ↔ criticalCoverage β γ ε ≤ p := by
  rw [Rv_eq, criticalCoverage_eq hβ hε, div_le_one hγ, div_le_iff₀ (mul_pos hβ hε)]
  constructor <;> intro h <;> linarith

/-- For `β, γ, ε > 0`, `R_v > 1` iff the coverage is below `p_c`. -/
theorem one_lt_Rv_iff (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 < ε) :
    1 < Rv β γ ε p ↔ p < criticalCoverage β γ ε := by
  rw [← not_le, Rv_le_one_iff hβ hγ hε, not_le]

/-- **Herd immunity is attainable** (`p_c ≤ 1`) iff the efficacy is at least `1 - 1 / R₀`, for
`ε > 0` (`p_c` and `R₀` have their epidemiological meaning for `β, γ > 0`). -/
theorem criticalCoverage_le_one_iff (hε : 0 < ε) :
    criticalCoverage β γ ε ≤ 1 ↔ 1 - γ / β ≤ ε := by
  rw [criticalCoverage, div_le_one hε]

/-- If `R₀ = β / γ ≤ 1` then `p_c ≤ 0`: no vaccination is needed. -/
theorem criticalCoverage_nonpos (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 < ε) (hR : β / γ ≤ 1) :
    criticalCoverage β γ ε ≤ 0 := by
  rw [criticalCoverage_eq hβ hε]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [(div_le_one hγ).1 hR])
    (mul_pos hβ hε).le

end Threshold

/-! ### Conservation and the reduction to SIS -/

/-- A function with zero derivative on `[0, ∞)` is constant there. -/
private theorem eq_zero_of_hasDerivAt {F : ℝ → ℝ} (hF : ∀ t, 0 ≤ t → HasDerivAt F 0 t)
    {t : ℝ} (ht : 0 ≤ t) : F t = F 0 :=
  constant_of_has_deriv_right_zero (b := t)
    (fun s hs => (hF s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hF s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩

namespace IsSolution

variable {β γ ε N p : ℝ} {Su Iu Sv Iv : ℝ → ℝ}

/-- The unvaccinated group size `S_u + I_u` is conserved. -/
theorem unvaccinated_total (h : IsSolution β γ ε N Su Iu Sv Iv) {t : ℝ} (ht : 0 ≤ t) :
    Su t + Iu t = Su 0 + Iu 0 :=
  eq_zero_of_hasDerivAt (F := fun s => Su s + Iu s) (fun s hs => by
    convert (h.hasDerivAt_Su s hs).add (h.hasDerivAt_Iu s hs) using 1; ring) ht

/-- The vaccinated group size `S_v + I_v` is conserved. -/
theorem vaccinated_total (h : IsSolution β γ ε N Su Iu Sv Iv) {t : ℝ} (ht : 0 ≤ t) :
    Sv t + Iv t = Sv 0 + Iv 0 :=
  eq_zero_of_hasDerivAt (F := fun s => Sv s + Iv s) (fun s hs => by
    convert (h.hasDerivAt_Sv s hs).add (h.hasDerivAt_Iv s hs) using 1; ring) ht

/-- **A vaccine of zero efficacy changes nothing**: for `ε = 0` the totals
`(S_u + S_v, I_u + I_v)` solve the unvaccinated SIS model. -/
theorem toSIS (h : IsSolution β γ 0 N Su Iu Sv Iv) :
    SIS.IsSolution β γ N (fun t => Su t + Sv t) (fun t => Iu t + Iv t) :=
  ⟨fun t ht => by convert (h.hasDerivAt_Su t ht).add (h.hasDerivAt_Sv t ht) using 1; ring,
    fun t ht => by convert (h.hasDerivAt_Iu t ht).add (h.hasDerivAt_Iv t ht) using 1; ring⟩

/-- For `ε = 0`, `0 ≤ γ < β`, `N > 0` and `I(0) > 0`, the total infected converges to the SIS
endemic level `N (1 - γ / β)` (`SIS.IsSolution.tendsto_infected_endemic`). -/
theorem tendsto_totalInfected_endemic_of_efficacy_zero (h : IsSolution β γ 0 N Su Iu Sv Iv)
    (hγ : 0 ≤ γ) (hγβ : γ < β) (hN : 0 < N) (hS : Su 0 + Sv 0 + (Iu 0 + Iv 0) = N)
    (hI0 : 0 < Iu 0 + Iv 0) :
    Tendsto (fun t => Iu t + Iv t) atTop (𝓝 (N * (1 - γ / β))) :=
  h.toSIS.tendsto_infected_endemic hγ hγβ hN hS hI0

/-- **The total-infected equation.** With group sizes `(1 - p) N` and `p N`,
`I' = γ (R_v - 1) I - (β / N) I (I_u + (1 - ε) I_v)` for `I = I_u + I_v`. -/
theorem hasDerivAt_totalInfected (h : IsSolution β γ ε N Su Iu Sv Iv) (hN : N ≠ 0)
    (hγ : γ ≠ 0) (hu : Su 0 + Iu 0 = (1 - p) * N) (hv : Sv 0 + Iv 0 = p * N) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivAt (fun s => Iu s + Iv s)
      (γ * (Rv β γ ε p - 1) * (Iu t + Iv t) -
        β / N * (Iu t + Iv t) * (Iu t + (1 - ε) * Iv t)) t := by
  have hSu : Su t = (1 - p) * N - Iu t := by linarith [h.unvaccinated_total ht]
  have hSv : Sv t = p * N - Iv t := by linarith [h.vaccinated_total ht]
  refine ((h.hasDerivAt_Iu t ht).add (h.hasDerivAt_Iv t ht)).congr_deriv ?_
  rw [hSu, hSv, Rv]
  field_simp
  ring

/-! ### Forward invariance of the nonnegative orthant -/

/-- The total infected `I_u + I_v` stays nonnegative if it starts nonnegative: it solves the
linear equation `I' = k(t) I`, `k = β S_u / N + (1 - ε) β S_v / N - γ`. -/
theorem totalInfected_nonneg (h : IsSolution β γ ε N Su Iu Sv Iv) (hI0 : 0 ≤ Iu 0 + Iv 0)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Iu t + Iv t := by
  set k : ℝ → ℝ := fun s => β * Su s / N + (1 - ε) * β * Sv s / N - γ
  have hI : ∀ s, 0 ≤ s → HasDerivAt (fun s => Iu s + Iv s) (k s * (Iu s + Iv s)) s :=
    fun s hs => ((h.hasDerivAt_Iu s hs).add (h.hasDerivAt_Iv s hs)).congr_deriv (by ring)
  have hk : ContinuousOn k (Icc 0 t) := fun s hs => by
    have cu := (h.hasDerivAt_Su s hs.1).continuousAt
    have cv := (h.hasDerivAt_Sv s hs.1).continuousAt
    exact ((((cu.const_mul β).div_const N).add
      ((cv.const_mul ((1 - ε) * β)).div_const N)).sub continuousAt_const).continuousWithinAt
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hk
  have hkK : ∀ s ∈ Icc 0 t, k s ≤ K := fun s hs =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK s hs)
  have hw := nonneg_of_hasDerivAt (T := t) (u := fun s => exp (-K * s) * (Iu s + Iv s))
    (u' := fun s => exp (-K * s) * ((k s - K) * (Iu s + Iv s)))
    (fun s hs => by
      have he : HasDerivAt (fun x => exp (-K * x)) (exp (-K * s) * (-K)) s := by
        simpa using ((hasDerivAt_id s).const_mul (-K)).exp
      exact (he.mul (hI s hs.1)).congr_deriv (by ring))
    (by simpa using hI0)
    (fun s hs hneg => by
      have hIs : Iu s + Iv s < 0 := by
        by_contra hc
        exact absurd hneg (not_lt.2 (mul_nonneg (exp_pos _).le (not_lt.1 hc)))
      exact mul_nonneg (exp_pos _).le
        (mul_nonneg_of_nonpos_of_nonpos (by linarith [hkK s hs]) hIs.le))
    t ⟨ht, le_rfl⟩
  by_contra hc
  exact absurd hw (not_le.2 (mul_neg_of_pos_of_neg (exp_pos _) (not_le.1 hc)))

/-- **Forward invariance of the nonnegative orthant.** For `β, γ ≥ 0`, `ε ≤ 1` and `N > 0`, a
solution starting with all four classes nonnegative keeps them nonnegative. -/
theorem nonneg (h : IsSolution β γ ε N Su Iu Sv Iv) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hε : ε ≤ 1)
    (hN : 0 < N) (hSu0 : 0 ≤ Su 0) (hIu0 : 0 ≤ Iu 0) (hSv0 : 0 ≤ Sv 0) (hIv0 : 0 ≤ Iv 0)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Su t ∧ 0 ≤ Iu t ∧ 0 ≤ Sv t ∧ 0 ≤ Iv t := by
  have hI := fun s (hs : 0 ≤ s) => h.totalInfected_nonneg (by linarith) hs
  have hσ : 0 ≤ (1 - ε) * β := mul_nonneg (by linarith) hβ
  have mem : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  refine ⟨nonneg_of_hasDerivAt (fun s hs => h.hasDerivAt_Su s hs.1) hSu0 (fun s hs hneg => ?_)
      t mem,
    nonneg_of_hasDerivAt (fun s hs => h.hasDerivAt_Iu s hs.1) hIu0 (fun s hs hneg => ?_) t mem,
    nonneg_of_hasDerivAt (fun s hs => h.hasDerivAt_Sv s hs.1) hSv0 (fun s hs hneg => ?_) t mem,
    nonneg_of_hasDerivAt (fun s hs => h.hasDerivAt_Iv s hs.1) hIv0 (fun s hs hneg => ?_) t mem⟩
  · have hc := h.unvaccinated_total hs.1
    have : β * Su s * (Iu s + Iv s) / N ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hβ hneg.le) (hI s hs.1))
        hN.le
    nlinarith
  · have hc := h.unvaccinated_total hs.1
    have : 0 ≤ β * Su s * (Iu s + Iv s) / N :=
      div_nonneg (mul_nonneg (mul_nonneg hβ (by linarith)) (hI s hs.1)) hN.le
    nlinarith
  · have hc := h.vaccinated_total hs.1
    have : (1 - ε) * β * Sv s * (Iu s + Iv s) / N ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hσ hneg.le) (hI s hs.1))
        hN.le
    nlinarith
  · have hc := h.vaccinated_total hs.1
    have : 0 ≤ (1 - ε) * β * Sv s * (Iu s + Iv s) / N :=
      div_nonneg (mul_nonneg (mul_nonneg hσ (by linarith)) (hI s hs.1)) hN.le
    nlinarith

/-! ### The disease-free side: `R_v ≤ 1` -/

section DiseaseFree

variable (h : IsSolution β γ ε N Su Iu Sv Iv) (hβ : 0 ≤ β) (hγ : 0 < γ) (hε0 : 0 ≤ ε)
  (hε1 : ε ≤ 1) (hN : 0 < N) (hu : Su 0 + Iu 0 = (1 - p) * N) (hv : Sv 0 + Iv 0 = p * N)
  (hSu0 : 0 ≤ Su 0) (hIu0 : 0 ≤ Iu 0) (hSv0 : 0 ≤ Sv 0) (hIv0 : 0 ≤ Iv 0)
include h hβ hγ hε0 hε1 hN hu hv hSu0 hIu0 hSv0 hIv0

omit hu hv in
/-- On the nonnegative orthant, `I' ≤ γ (R_v - 1) I - (β / N) (1 - ε) I²`. -/
private theorem deriv_totalInfected_le {t : ℝ} (ht : 0 ≤ t) :
    γ * (Rv β γ ε p - 1) * (Iu t + Iv t) - β / N * (Iu t + Iv t) * (Iu t + (1 - ε) * Iv t) ≤
      γ * (Rv β γ ε p - 1) * (Iu t + Iv t) - β * (1 - ε) / N * (Iu t + Iv t) ^ 2 := by
  obtain ⟨-, hx, -, hy⟩ := h.nonneg hβ hγ.le hε1 hN hSu0 hIu0 hSv0 hIv0 ht
  have h1 : (1 - ε) * (Iu t + Iv t) ≤ Iu t + (1 - ε) * Iv t := by nlinarith
  have h2 : 0 ≤ β / N * (Iu t + Iv t) := mul_nonneg (div_nonneg hβ hN.le) (add_nonneg hx hy)
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  have e : β * (1 - ε) / N * (Iu t + Iv t) ^ 2 = β / N * (Iu t + Iv t) * ((1 - ε) * (Iu t + Iv t))
    := by ring
  linarith

/-- **Stability of the disease-free state.** If `R_v ≤ 1`, the total infected is
nonincreasing: `I_u(t) + I_v(t) ≤ I_u(0) + I_v(0)`. -/
theorem totalInfected_le_initial (hR : Rv β γ ε p ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    Iu t + Iv t ≤ Iu 0 + Iv 0 := by
  have := le_mul_exp_of_hasDerivAt (κ := 0)
    (fun s hs => h.hasDerivAt_totalInfected hN.ne' hγ.ne' hu hv hs) (fun s hs => by
      have := h.deriv_totalInfected_le (p := p) hβ hγ hε0 hε1 hN hSu0 hIu0 hSv0 hIv0 hs
      obtain ⟨-, hx, -, hy⟩ := h.nonneg hβ hγ.le hε1 hN hSu0 hIu0 hSv0 hIv0 hs
      have : γ * (Rv β γ ε p - 1) * (Iu s + Iv s) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hγ.le (by linarith))
          (add_nonneg hx hy)
      have : 0 ≤ β * (1 - ε) / N * (Iu s + Iv s) ^ 2 :=
        mul_nonneg (div_nonneg (mul_nonneg hβ (by linarith)) hN.le) (sq_nonneg _)
      simp only [neg_zero, zero_mul]
      linarith) ht
  simpa using this

/-- **Exponential bound on the total infected.** For every `R_v`,
`I_u(t) + I_v(t) ≤ (I_u(0) + I_v(0)) e^{-γ (1 - R_v) t}`; this is exponential decay when
`R_v < 1`. -/
theorem totalInfected_le_exp {t : ℝ} (ht : 0 ≤ t) :
    Iu t + Iv t ≤ (Iu 0 + Iv 0) * exp (-(γ * (1 - Rv β γ ε p)) * t) :=
  le_mul_exp_of_hasDerivAt
    (fun s hs => h.hasDerivAt_totalInfected hN.ne' hγ.ne' hu hv hs) (fun s hs => by
      have := h.deriv_totalInfected_le (p := p) hβ hγ hε0 hε1 hN hSu0 hIu0 hSv0 hIv0 hs
      have : 0 ≤ β * (1 - ε) / N * (Iu s + Iv s) ^ 2 :=
        mul_nonneg (div_nonneg (mul_nonneg hβ (by linarith)) hN.le) (sq_nonneg _)
      nlinarith) ht

/-- **Algebraic extinction at threshold.** If `R_v = 1`, then
`I(t) ≤ I(0) / (1 + c I(0) t)` with `I = I_u + I_v` and `c = β (1 - ε) / N`. -/
theorem totalInfected_le_critical (hR : Rv β γ ε p = 1) {t : ℝ} (ht : 0 ≤ t) :
    Iu t + Iv t ≤ (Iu 0 + Iv 0) / (1 + β * (1 - ε) / N * (Iu 0 + Iv 0) * t) := by
  set c := β * (1 - ε) / N with hc_def
  set I0 := Iu 0 + Iv 0
  have hc : 0 ≤ c := div_nonneg (mul_nonneg hβ (by linarith)) hN.le
  have hI0 : 0 ≤ I0 := add_nonneg hIu0 hIv0
  have hpos : ∀ s, 0 ≤ s → 0 < 1 + c * I0 * s := fun s hs => by
    have := mul_nonneg (mul_nonneg hc hI0) hs; linarith
  have hd := fun s (hs : 0 ≤ s) => h.hasDerivAt_totalInfected hN.ne' hγ.ne' hu hv hs
  have hw := nonneg_of_hasDerivAt (T := t)
    (u := fun s => I0 - (Iu s + Iv s) * (1 + c * I0 * s))
    (u' := fun s => -((γ * (Rv β γ ε p - 1) * (Iu s + Iv s) -
        β / N * (Iu s + Iv s) * (Iu s + (1 - ε) * Iv s)) * (1 + c * I0 * s) +
        (Iu s + Iv s) * (c * I0)))
    (fun s hs => by
      have hl : HasDerivAt (fun s => 1 + c * I0 * s) (c * I0) s := by
        simpa using ((hasDerivAt_id s).const_mul (c * I0)).const_add 1
      exact (((hd s hs.1).mul hl).const_sub I0).congr_deriv (by ring))
    (by simp [I0])
    (fun s hs hneg => by
      have hle := h.deriv_totalInfected_le (p := p) hβ hγ hε0 hε1 hN hSu0 hIu0 hSv0 hIv0 hs.1
      rw [hR, sub_self, mul_zero, zero_mul, zero_sub] at hle
      obtain ⟨-, hx, -, hy⟩ := h.nonneg hβ hγ.le hε1 hN hSu0 hIu0 hSv0 hIv0 hs.1
      have hIs : 0 ≤ Iu s + Iv s := add_nonneg hx hy
      have hp := hpos s hs.1
      have h1 := mul_le_mul_of_nonneg_right hle hp.le
      rw [hR, sub_self, mul_zero, zero_mul, zero_sub]
      have h2 : 0 ≤ c * (Iu s + Iv s) * ((Iu s + Iv s) * (1 + c * I0 * s) - I0) :=
        mul_nonneg (mul_nonneg hc hIs) (by linarith)
      nlinarith)
    t ⟨ht, le_rfl⟩
  rw [le_div_iff₀ (hpos t ht)]
  linarith

omit hε0 in
/-- The vaccinated and unvaccinated infectives are bounded by the total, and nonnegative. -/
private theorem tendsto_of_totalInfected (hI : Tendsto (fun t => Iu t + Iv t) atTop (𝓝 0)) :
    Tendsto Su atTop (𝓝 ((1 - p) * N)) ∧ Tendsto Iu atTop (𝓝 0) ∧
      Tendsto Sv atTop (𝓝 (p * N)) ∧ Tendsto Iv atTop (𝓝 0) := by
  have hnn := fun t (ht : 0 ≤ t) => h.nonneg hβ hγ.le hε1 hN hSu0 hIu0 hSv0 hIv0 ht
  have hx : Tendsto Iu atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hI ?_ ?_ <;>
      filter_upwards [eventually_ge_atTop 0] with t ht
    · exact (hnn t ht).2.1
    · linarith [(hnn t ht).2.2.2]
  have hy : Tendsto Iv atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hI ?_ ?_ <;>
      filter_upwards [eventually_ge_atTop 0] with t ht
    · exact (hnn t ht).2.2.2
    · linarith [(hnn t ht).2.1]
  refine ⟨?_, hx, ?_, hy⟩
  · have := hx.const_sub ((1 - p) * N)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    linarith [h.unvaccinated_total ht]
  · have := hy.const_sub (p * N)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    linarith [h.vaccinated_total ht]

/-- **Global attractivity of the disease-free equilibrium.** If `R_v < 1`, or `R_v = 1` with an
imperfect vaccine (`ε < 1`) and `β > 0`, every solution with group sizes `(1 - p) N` and `p N`
starting in the nonnegative orthant has `I_u, I_v → 0`, `S_u → (1 - p) N` and `S_v → p N`. -/
theorem tendsto_dfe (hR : Rv β γ ε p < 1 ∨ (Rv β γ ε p = 1 ∧ ε < 1 ∧ 0 < β)) :
    Tendsto Su atTop (𝓝 ((1 - p) * N)) ∧ Tendsto Iu atTop (𝓝 0) ∧
      Tendsto Sv atTop (𝓝 (p * N)) ∧ Tendsto Iv atTop (𝓝 0) := by
  have hnn := fun t (ht : 0 ≤ t) => h.nonneg hβ hγ.le hε1 hN hSu0 hIu0 hSv0 hIv0 ht
  refine h.tendsto_of_totalInfected hβ hγ hε1 hN hu hv hSu0 hIu0 hSv0 hIv0 ?_
  rcases hR with hR | ⟨hR, hε, hβ'⟩
  · have hκ : 0 < γ * (1 - Rv β γ ε p) := mul_pos hγ (by linarith)
    have hlim : Tendsto (fun t => (Iu 0 + Iv 0) * exp (-(γ * (1 - Rv β γ ε p)) * t)) atTop
        (𝓝 0) := by
      have := (tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hκ)).const_mul (Iu 0 + Iv 0)
      simpa [neg_mul] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_ <;>
      filter_upwards [eventually_ge_atTop 0] with t ht
    · exact add_nonneg (hnn t ht).2.1 (hnn t ht).2.2.2
    · exact h.totalInfected_le_exp hβ hγ hε0 hε1 hN hu hv hSu0 hIu0 hSv0 hIv0 ht
  · set c := β * (1 - ε) / N
    have hc : 0 < c := div_pos (mul_pos hβ' (by linarith)) hN
    have hlim : Tendsto (fun t : ℝ => c⁻¹ * t⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul c⁻¹
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with t ht
      exact add_nonneg (hnn t ht).2.1 (hnn t ht).2.2.2
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have hb := h.totalInfected_le_critical hβ hγ hε0 hε1 hN hu hv hSu0 hIu0 hSv0 hIv0 hR ht.le
      have hI0 : 0 ≤ Iu 0 + Iv 0 := add_nonneg hIu0 hIv0
      refine hb.trans ?_
      rw [div_le_iff₀ (by positivity), show c⁻¹ * t⁻¹ * (1 + c * (Iu 0 + Iv 0) * t) =
        c⁻¹ * t⁻¹ + (Iu 0 + Iv 0) by field_simp]
      have : 0 ≤ c⁻¹ * t⁻¹ := by positivity
      linarith

/-- **Vaccinating at or above the critical coverage eliminates the infection.** For an imperfect
but effective vaccine (`0 < ε < 1`), `β > 0` and coverage `p ≥ p_c`, every solution with group
sizes `(1 - p) N` and `p N` starting in the nonnegative orthant converges to the disease-free
equilibrium. -/
theorem tendsto_dfe_of_criticalCoverage_le (hβ' : 0 < β) (hε : 0 < ε) (hε' : ε < 1)
    (hp : criticalCoverage β γ ε ≤ p) :
    Tendsto Su atTop (𝓝 ((1 - p) * N)) ∧ Tendsto Iu atTop (𝓝 0) ∧
      Tendsto Sv atTop (𝓝 (p * N)) ∧ Tendsto Iv atTop (𝓝 0) := by
  refine h.tendsto_dfe hβ hγ hε0 hε1 hN hu hv hSu0 hIu0 hSv0 hIv0 ?_
  rcases ((Rv_le_one_iff hβ' hγ hε).2 hp).lt_or_eq with hR | hR
  · exact Or.inl hR
  · exact Or.inr ⟨hR, hε', hβ'⟩

end DiseaseFree

end IsSolution

/-! ### The endemic equilibrium -/

/-- `(I_u*, I_v*) = (a, c)` is an **endemic equilibrium**: both infected levels are positive and
the infected equations vanish with `S_u = (1 - p) N - a`, `S_v = p N - c`. -/
structure IsEndemicEq (β γ ε N p a c : ℝ) : Prop where
  /-- Positive unvaccinated infected level. -/
  pos_unvaccinated : 0 < a
  /-- Positive vaccinated infected level. -/
  pos_vaccinated : 0 < c
  /-- Equilibrium of the unvaccinated infectives. -/
  eq_unvaccinated : β * ((1 - p) * N - a) * (a + c) / N = γ * a
  /-- Equilibrium of the vaccinated infectives. -/
  eq_vaccinated : (1 - ε) * β * (p * N - c) * (a + c) / N = γ * c

/-- An endemic equilibrium is a constant solution. -/
theorem isSolution_const_endemic {β γ ε N p a c : ℝ} (he : IsEndemicEq β γ ε N p a c) :
    IsSolution β γ ε N (fun _ => (1 - p) * N - a) (fun _ => a) (fun _ => p * N - c)
      (fun _ => c) := by
  refine ⟨fun t _ => ?_, fun t _ => ?_, fun t _ => ?_, fun t _ => ?_⟩ <;>
    convert hasDerivAt_const t _ using 1
  · rw [he.eq_unvaccinated]; ring
  · rw [he.eq_unvaccinated]; ring
  · rw [he.eq_vaccinated]; ring
  · rw [he.eq_vaccinated]; ring

/-- The disease-free equilibrium is a constant solution. -/
theorem isSolution_const_dfe (β γ ε N p : ℝ) :
    IsSolution β γ ε N (fun _ => (1 - p) * N) (fun _ => 0) (fun _ => p * N) (fun _ => 0) := by
  refine ⟨fun t _ => ?_, fun t _ => ?_, fun t _ => ?_, fun t _ => ?_⟩ <;>
    convert hasDerivAt_const t _ using 1 <;> simp

section Endemic

variable {β γ ε N p a c : ℝ}

/-- Adding the two equilibrium equations:
`β (1 - ε p) (a + c) N = γ (a + c) N + β (a + c) (a + (1 - ε) c)`. -/
private theorem IsEndemicEq.sum_eq (he : IsEndemicEq β γ ε N p a c) (hN : N ≠ 0) :
    β * (1 - ε * p) * (a + c) * N = γ * (a + c) * N + β * (a + c) * (a + (1 - ε) * c) := by
  have e1 := he.eq_unvaccinated
  have e2 := he.eq_vaccinated
  rw [div_eq_iff hN] at e1 e2
  linear_combination e1 + e2

/-- **An endemic equilibrium forces `R_v > 1`** (`γ, N > 0`, `β ≥ 0`, `ε ≤ 1`). -/
theorem one_lt_Rv_of_isEndemicEq (he : IsEndemicEq β γ ε N p a c) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hε : ε ≤ 1) (hN : 0 < N) : 1 < Rv β γ ε p := by
  have hb : 0 < β := by
    rcases hβ.lt_or_eq with hβ | hβ
    · exact hβ
    · have := he.eq_unvaccinated
      rw [← hβ] at this
      simp only [zero_mul, zero_div] at this
      exact absurd this (mul_pos hγ he.pos_unvaccinated).ne
  have ha := he.pos_unvaccinated
  have hc := he.pos_vaccinated
  have key := he.sum_eq hN.ne'
  have hpos : 0 < β * (a + c) * (a + (1 - ε) * c) :=
    mul_pos (mul_pos hb (by linarith)) (by nlinarith)
  have hlt : γ * ((a + c) * N) < β * (1 - ε * p) * ((a + c) * N) := by nlinarith
  have := lt_of_mul_lt_mul_right hlt (by positivity)
  rw [Rv, div_mul_eq_mul_div, one_lt_div hγ]
  linarith

/-- **Existence of the endemic equilibrium above threshold.** For `β, γ, N > 0`, `0 < p < 1`,
`ε < 1` and `R_v > 1` there is an endemic equilibrium. The total `I* = a + c` solves
`f(I) = 1` with `f(I) = b_u N_u / (γ + b_u I) + b_v N_v / (γ + b_v I)` decreasing from
`f(0) = R_v > 1` to `f(N) ≤ 1` (`b_u = β / N`, `b_v = (1 - ε) β / N`, `N_u = (1 - p) N`,
`N_v = p N`); intermediate value theorem. -/
theorem exists_isEndemicEq (hβ : 0 < β) (hγ : 0 < γ) (hN : 0 < N) (hp0 : 0 < p) (hp1 : p < 1)
    (hε : ε < 1) (hR : 1 < Rv β γ ε p) : ∃ a c, IsEndemicEq β γ ε N p a c := by
  set bu := β / N with hbu
  set bv := (1 - ε) * β / N with hbv
  have hbu0 : 0 < bu := div_pos hβ hN
  have hbv0 : 0 < bv := div_pos (mul_pos (by linarith) hβ) hN
  set Nu := (1 - p) * N with hNu
  set Nv := p * N with hNv
  have hNu0 : 0 < Nu := mul_pos (by linarith) hN
  have hNv0 : 0 < Nv := mul_pos hp0 hN
  set f : ℝ → ℝ := fun I => bu * Nu / (γ + bu * I) + bv * Nv / (γ + bv * I) with hf
  have hcont : ContinuousOn f (Icc 0 N) := by
    refine ContinuousOn.add ?_ ?_ <;> refine continuousOn_const.div ?_ ?_
    · exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    · intro I hI; have := hI.1; positivity
    · exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    · intro I hI; have := hI.1; positivity
  have hf0 : f 0 = Rv β γ ε p := by
    simp only [hf, hbu, hbv, hNu, hNv, Rv, mul_zero, add_zero]
    field_simp
    ring
  have hfN : f N ≤ 1 := by
    have h1 : bu * Nu / (γ + bu * N) ≤ Nu / N := by
      rw [div_le_div_iff₀ (by positivity) hN]; nlinarith
    have h2 : bv * Nv / (γ + bv * N) ≤ Nv / N := by
      rw [div_le_div_iff₀ (by positivity) hN]; nlinarith
    have h3 : Nu / N + Nv / N = 1 := by rw [hNu, hNv]; field_simp; ring
    simp only [hf]
    linarith
  obtain ⟨I, hI, hfI⟩ := intermediate_value_Icc' hN.le hcont ⟨hfN, by rw [hf0]; exact hR.le⟩
  have hI0 : 0 < I := by
    rcases hI.1.lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, hf0] at hfI; linarith
  have hdu : 0 < γ + bu * I := by positivity
  have hdv : 0 < γ + bv * I := by positivity
  refine ⟨bu * I * Nu / (γ + bu * I), bv * I * Nv / (γ + bv * I), ⟨by positivity, by positivity,
    ?_, ?_⟩⟩
  all_goals
    have hsum : bu * I * Nu / (γ + bu * I) + bv * I * Nv / (γ + bv * I) = I := by
      have : bu * I * Nu / (γ + bu * I) + bv * I * Nv / (γ + bv * I) = I * f I := by
        simp only [hf]; ring
      rw [this, hfI, mul_one]
    rw [hsum]
  · rw [show β = bu * N by rw [hbu]; field_simp]
    field_simp
    ring
  · rw [show (1 - ε) * β = bv * N by rw [hbv]; field_simp]
    field_simp
    ring

end Endemic

/-! ### The Lyapunov function -/

/-- The **Lyapunov function** of the endemic equilibrium `(a, c) = (I_u*, I_v*)`:
`V(x, y) = g(a, x) + g(c, y)`, `g(a, x) = x - a - a log (x / a)`. -/
noncomputable def lyapunov (a c x y : ℝ) : ℝ := volterra a x + volterra c y

/-- The derivative of `lyapunov` along solutions (`lyapunov_deriv_eq`):
`-(β/N) I (x - a)² / x - ((1 - ε) β / N) I (y - c)² / y - γ (x c - y a)² / ((a + c) x y)`,
`I = x + y`. -/
noncomputable def lyapunovDeriv (β γ ε N a c x y : ℝ) : ℝ :=
  -(β * (x + y) * (x - a) ^ 2 / (N * x)) - (1 - ε) * β * (x + y) * (y - c) ^ 2 / (N * y) -
    γ * (x * c - y * a) ^ 2 / ((a + c) * x * y)

/-- `g(a, x) ≤ (x - a)² / x` (from `log y ≥ 1 - 1 / y`). -/
theorem volterra_le_sq_div {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    volterra a x ≤ (x - a) ^ 2 / x := by
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos (div_pos hx ha)) ha.le
  have e : a * (1 - (x / a)⁻¹) = a - a ^ 2 / x := by field_simp
  have e2 : (x - a) ^ 2 / x = x - 2 * a + a ^ 2 / x := by field_simp; ring
  rw [volterra]
  linarith

section Lyapunov

variable {β γ ε N p a c : ℝ}

/-- **The derivative identity.** At an endemic equilibrium `(a, c)`, for `N ≠ 0` and `x, y ≠ 0`,
`(1 - a / x) x' + (1 - c / y) y' = lyapunovDeriv` for the infected vector field with
`S_u = (1 - p) N - x`, `S_v = p N - y`. -/
theorem lyapunov_deriv_eq (he : IsEndemicEq β γ ε N p a c) (hN : N ≠ 0) {x y : ℝ} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    (1 - a / x) * (β * ((1 - p) * N - x) * (x + y) / N - γ * x) +
        (1 - c / y) * ((1 - ε) * β * (p * N - y) * (x + y) / N - γ * y) =
      lyapunovDeriv β γ ε N a c x y := by
  have hac : a + c ≠ 0 := (add_pos he.pos_unvaccinated he.pos_vaccinated).ne'
  have ha := he.eq_unvaccinated
  have hc := he.eq_vaccinated
  rw [lyapunovDeriv]
  linear_combination (norm := skip) ((1 - a / x) * (x + y) / (a + c)) * ha +
    ((1 - c / y) * (x + y) / (a + c)) * hc
  field_simp
  ring

/-- `V' ≤ -(β/N) I (x - a)² / x - ((1 - ε) β / N) I (y - c)² / y` for `x, y > 0` and `γ ≥ 0`:
the dropped term `γ (x c - y a)² / ((a + c) x y)` is nonnegative. -/
theorem lyapunovDeriv_le (he : IsEndemicEq β γ ε N p a c) (hγ : 0 ≤ γ) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) :
    lyapunovDeriv β γ ε N a c x y ≤
      -(β * (x + y) * (x - a) ^ 2 / (N * x)) - (1 - ε) * β * (x + y) * (y - c) ^ 2 / (N * y) := by
  have hac := add_pos he.pos_unvaccinated he.pos_vaccinated
  have : 0 ≤ γ * (x * c - y * a) ^ 2 / ((a + c) * x * y) := by positivity
  rw [lyapunovDeriv]
  linarith

theorem lyapunov_nonneg (he : IsEndemicEq β γ ε N p a c) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ lyapunov a c x y :=
  add_nonneg (volterra_nonneg he.pos_unvaccinated hx) (volterra_nonneg he.pos_vaccinated hy)

/-- `a < (1 - p) N` and `c < p N` at an endemic equilibrium (`γ, N > 0`, `β ≥ 0`, `ε ≤ 1`). -/
theorem IsEndemicEq.lt_groups (he : IsEndemicEq β γ ε N p a c) (hγ : 0 < γ) (hN : 0 < N)
    (hβ : 0 ≤ β) (hε : ε ≤ 1) : a < (1 - p) * N ∧ c < p * N := by
  have ha := he.pos_unvaccinated
  have hc := he.pos_vaccinated
  have e1 := he.eq_unvaccinated
  have e2 := he.eq_vaccinated
  rw [div_eq_iff hN.ne'] at e1 e2
  have h1 : 0 < γ * a * N := by positivity
  have h2 : 0 < γ * c * N := by positivity
  constructor
  · by_contra hcon
    have : β * ((1 - p) * N - a) * (a + c) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hβ (by linarith))
        (by linarith)
    linarith
  · by_contra hcon
    have : (1 - ε) * β * (p * N - c) * (a + c) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hβ) (by linarith))
        (by linarith)
    linarith

end Lyapunov

namespace IsSolution

variable {β γ ε N p a c : ℝ} {Su Iu Sv Iv : ℝ → ℝ}

/-- **The Lyapunov derivative along solutions.** At a time `t ≥ 0` with `I_u(t), I_v(t) > 0`,
`d/dt V(I_u(t), I_v(t)) = lyapunovDeriv (I_u(t), I_v(t))`. -/
theorem hasDerivAt_lyapunov (h : IsSolution β γ ε N Su Iu Sv Iv)
    (he : IsEndemicEq β γ ε N p a c) (hN : N ≠ 0) (hu : Su 0 + Iu 0 = (1 - p) * N)
    (hv : Sv 0 + Iv 0 = p * N) {t : ℝ} (ht : 0 ≤ t) (hx : 0 < Iu t) (hy : 0 < Iv t) :
    HasDerivAt (fun s => lyapunov a c (Iu s) (Iv s))
      (lyapunovDeriv β γ ε N a c (Iu t) (Iv t)) t := by
  have hSu : Su t = (1 - p) * N - Iu t := by linarith [h.unvaccinated_total ht]
  have hSv : Sv t = p * N - Iv t := by linarith [h.vaccinated_total ht]
  have dx := (hasDerivAt_volterra he.pos_unvaccinated.ne' hx.ne').comp t (h.hasDerivAt_Iu t ht)
  have dy := (hasDerivAt_volterra he.pos_vaccinated.ne' hy.ne').comp t (h.hasDerivAt_Iv t ht)
  refine (dx.add dy).congr_deriv ?_
  rw [hSu, hSv]
  exact lyapunov_deriv_eq he hN hx.ne' hy.ne'

section Endemic

variable (h : IsSolution β γ ε N Su Iu Sv Iv) (he : IsEndemicEq β γ ε N p a c) (hβ : 0 ≤ β)
  (hγ : 0 < γ) (hε : ε < 1) (hN : 0 < N) (hu : Su 0 + Iu 0 = (1 - p) * N)
  (hv : Sv 0 + Iv 0 = p * N) (hSu0 : 0 ≤ Su 0) (hSv0 : 0 ≤ Sv 0) (hIu0 : 0 < Iu 0)
  (hIv0 : 0 < Iv 0)
include h he hβ hγ hε hN hu hv hSu0 hSv0 hIu0 hIv0

omit he hu hv in
/-- **Positivity of the infectives**: `I_u(t), I_v(t) > 0` for `t ≥ 0`; the proof bounds them
below by `I_u(0) e^{-γ t}` and `I_v(0) e^{-γ t}`. -/
theorem infected_pos {t : ℝ} (ht : 0 ≤ t) : 0 < Iu t ∧ 0 < Iv t := by
  have hnn := fun s (hs : 0 ≤ s) =>
    h.nonneg hβ hγ.le hε.le hN hSu0 hIu0.le hSv0 hIv0.le hs
  have hσ : 0 ≤ (1 - ε) * β := mul_nonneg (by linarith) hβ
  have hx := le_mul_exp_of_hasDerivAt (W := fun s => -Iu s) (κ := γ)
    (fun s hs => (h.hasDerivAt_Iu s hs).neg) (fun s hs => by
      obtain ⟨h1, -, -, -⟩ := hnn s hs
      have : 0 ≤ β * Su s * (Iu s + Iv s) / N := div_nonneg (mul_nonneg (mul_nonneg hβ h1)
        (add_nonneg (hnn s hs).2.1 (hnn s hs).2.2.2)) hN.le
      linarith) ht
  have hy := le_mul_exp_of_hasDerivAt (W := fun s => -Iv s) (κ := γ)
    (fun s hs => (h.hasDerivAt_Iv s hs).neg) (fun s hs => by
      obtain ⟨-, -, h1, -⟩ := hnn s hs
      have : 0 ≤ (1 - ε) * β * Sv s * (Iu s + Iv s) / N := div_nonneg (mul_nonneg
        (mul_nonneg hσ h1) (add_nonneg (hnn s hs).2.1 (hnn s hs).2.2.2)) hN.le
      linarith) ht
  have e1 := mul_pos hIu0 (exp_pos (-γ * t))
  have e2 := mul_pos hIv0 (exp_pos (-γ * t))
  constructor <;> linarith

/-- **`V` is nonincreasing**: `V(t) ≤ V(0)`. -/
theorem lyapunov_le_initial {t : ℝ} (ht : 0 ≤ t) :
    lyapunov a c (Iu t) (Iv t) ≤ lyapunov a c (Iu 0) (Iv 0) := by
  have hpos := fun s (hs : 0 ≤ s) =>
    h.infected_pos hβ hγ hε hN hSu0 hSv0 hIu0 hIv0 hs
  have := le_mul_exp_of_hasDerivAt (κ := 0)
    (fun s hs => h.hasDerivAt_lyapunov he hN.ne' hu hv hs (hpos s hs).1 (hpos s hs).2)
    (fun s hs => by
      have h1 := lyapunovDeriv_le he hγ.le (hpos s hs).1 (hpos s hs).2
      have hs' := add_pos (hpos s hs).1 (hpos s hs).2
      have h2 : 0 ≤ β * (Iu s + Iv s) * (Iu s - a) ^ 2 / (N * Iu s) := by
        have := (hpos s hs).1; positivity
      have h3 : 0 ≤ (1 - ε) * β * (Iu s + Iv s) * (Iv s - c) ^ 2 / (N * Iv s) := by
        have := (hpos s hs).2
        have : 0 ≤ 1 - ε := by linarith
        positivity
      simp only [neg_zero, zero_mul]
      linarith) ht
  simpa using this

/-- **Uniform persistence**: `I_u(t) ≥ m := a e^{-(V(0) + a) / a} > 0`. -/
theorem persistence {t : ℝ} (ht : 0 ≤ t) :
    a * exp (-(lyapunov a c (Iu 0) (Iv 0) + a) / a) ≤ Iu t := by
  have hpos := h.infected_pos hβ hγ hε hN hSu0 hSv0 hIu0 hIv0 ht
  have hV := h.lyapunov_le_initial he hβ hγ hε hN hu hv hSu0 hSv0 hIu0 hIv0 ht
  have hg := volterra_nonneg he.pos_vaccinated hpos.2
  exact le_of_volterra_le he.pos_unvaccinated hpos.1 ((le_add_of_nonneg_right hg).trans hV)

/-- **Exponential decay of the Lyapunov function**: `V(t) ≤ V(0) e^{-κ t}` for some `κ > 0`
(`κ = min(β, (1 - ε) β) m / N`, `m` the persistence bound; needs `β > 0`). -/
theorem exists_lyapunov_le_exp (hβ' : 0 < β) :
    ∃ κ > 0, ∀ t, 0 ≤ t →
      lyapunov a c (Iu t) (Iv t) ≤ lyapunov a c (Iu 0) (Iv 0) * exp (-κ * t) := by
  have ha := he.pos_unvaccinated
  have hc := he.pos_vaccinated
  set m := a * exp (-(lyapunov a c (Iu 0) (Iv 0) + a) / a) with hm_def
  have hm : 0 < m := mul_pos ha (exp_pos _)
  have hb : 0 < min β ((1 - ε) * β) := lt_min hβ' (mul_pos (by linarith) hβ')
  set κ := min β ((1 - ε) * β) * m / N with hκ_def
  have hκ : 0 < κ := by positivity
  refine ⟨κ, hκ, fun t ht => ?_⟩
  have hpos := fun s (hs : 0 ≤ s) =>
    h.infected_pos hβ hγ hε hN hSu0 hSv0 hIu0 hIv0 hs
  refine le_mul_exp_of_hasDerivAt
    (fun s hs => h.hasDerivAt_lyapunov he hN.ne' hu hv hs (hpos s hs).1 (hpos s hs).2)
    (fun s hs => ?_) ht
  obtain ⟨hx, hy⟩ := hpos s hs
  have hmx := h.persistence he hβ hγ hε hN hu hv hSu0 hSv0 hIu0 hIv0 hs
  have hmI : m ≤ Iu s + Iv s := by linarith
  have h1 := lyapunovDeriv_le he hγ.le hx hy
  have hV : lyapunov a c (Iu s) (Iv s) ≤ (Iu s - a) ^ 2 / Iu s + (Iv s - c) ^ 2 / Iv s :=
    add_le_add (volterra_le_sq_div ha hx) (volterra_le_sq_div hc hy)
  have hq1 : 0 ≤ (Iu s - a) ^ 2 / Iu s := by positivity
  have hq2 : 0 ≤ (Iv s - c) ^ 2 / Iv s := by positivity
  have hk1 : κ ≤ β * (Iu s + Iv s) / N := by
    rw [hκ_def]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (min_le_left _ _) hmI hm.le hβ) hN.le
  have hk2 : κ ≤ (1 - ε) * β * (Iu s + Iv s) / N := by
    rw [hκ_def]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (min_le_right _ _) hmI hm.le (mul_nonneg (by linarith) hβ)) hN.le
  have e1 : β * (Iu s + Iv s) * (Iu s - a) ^ 2 / (N * Iu s) =
      β * (Iu s + Iv s) / N * ((Iu s - a) ^ 2 / Iu s) := by
    field_simp
  have e2 : (1 - ε) * β * (Iu s + Iv s) * (Iv s - c) ^ 2 / (N * Iv s) =
      (1 - ε) * β * (Iu s + Iv s) / N * ((Iv s - c) ^ 2 / Iv s) := by
    field_simp
  have i1 := mul_le_mul_of_nonneg_right hk1 hq1
  have i2 := mul_le_mul_of_nonneg_right hk2 hq2
  have i3 := mul_le_mul_of_nonneg_left hV hκ.le
  rw [e1, e2] at h1
  nlinarith

/-- `(I_u - a)² + (I_v - c)² ≤ 2 N V(I_u, I_v)` along solutions (the equilibrium itself forces
`0 < p < 1`). -/
theorem sq_add_sq_le_lyapunov {t : ℝ} (ht : 0 ≤ t) :
    (Iu t - a) ^ 2 + (Iv t - c) ^ 2 ≤ 2 * N * lyapunov a c (Iu t) (Iv t) := by
  have hpos := h.infected_pos hβ hγ hε hN hSu0 hSv0 hIu0 hIv0 ht
  have hnn := h.nonneg hβ hγ.le hε.le hN hSu0 hIu0.le hSv0 hIv0.le ht
  have hlt := he.lt_groups hγ hN hβ hε.le
  have hSu : Su t = (1 - p) * N - Iu t := by linarith [h.unvaccinated_total ht]
  have hSv : Sv t = p * N - Iv t := by linarith [h.vaccinated_total ht]
  have h1 := sq_le_volterra he.pos_unvaccinated hpos.1 hlt.1.le (by linarith [hnn.1])
  have h2 := sq_le_volterra he.pos_vaccinated hpos.2 hlt.2.le (by linarith [hnn.2.2.1])
  have g1 := volterra_nonneg he.pos_unvaccinated hpos.1
  have g2 := volterra_nonneg he.pos_vaccinated hpos.2
  have m1 : 2 * ((1 - p) * N) * volterra a (Iu t) ≤ 2 * N * volterra a (Iu t) := by
    have : (1 - p) * N ≤ N := by nlinarith
    nlinarith
  have m2 : 2 * (p * N) * volterra c (Iv t) ≤ 2 * N * volterra c (Iv t) := by
    have : p * N ≤ N := by nlinarith
    nlinarith
  unfold lyapunov
  linarith

/-- **Global attractivity of the endemic equilibrium.** For `β, γ, N > 0`,
`ε < 1` and an endemic equilibrium `(a, c)`, every solution with group sizes `(1 - p) N` and
`p N`, `S_u(0), S_v(0) ≥ 0` and `I_u(0), I_v(0) > 0` converges: `S_u → (1 - p) N - a`,
`I_u → a`, `S_v → p N - c`, `I_v → c`. -/
theorem tendsto_endemic (hβ' : 0 < β) :
    Tendsto Su atTop (𝓝 ((1 - p) * N - a)) ∧ Tendsto Iu atTop (𝓝 a) ∧
      Tendsto Sv atTop (𝓝 (p * N - c)) ∧ Tendsto Iv atTop (𝓝 c) := by
  obtain ⟨κ, hκ, hdec⟩ := h.exists_lyapunov_le_exp he hβ hγ hε hN hu hv hSu0 hSv0 hIu0 hIv0 hβ'
  set V0 := lyapunov a c (Iu 0) (Iv 0)
  have hlim : Tendsto (fun t => 2 * N * (V0 * exp (-κ * t))) atTop (𝓝 0) := by
    have := (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hκ)).const_mul V0
    simpa [neg_mul] using this.const_mul (2 * N)
  have hbound : ∀ᶠ t in atTop, (Iu t - a) ^ 2 + (Iv t - c) ^ 2 ≤ 2 * N * (V0 * exp (-κ * t)) := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (h.sq_add_sq_le_lyapunov he hβ hγ hε hN hu hv hSu0 hSv0 hIu0 hIv0 ht).trans
      (mul_le_mul_of_nonneg_left (hdec t ht) (by positivity))
  have hsq1 : Tendsto (fun t => (Iu t - a) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _) ?_ hlim
    filter_upwards [hbound] with t ht
    nlinarith [sq_nonneg (Iv t - c)]
  have hsq2 : Tendsto (fun t => (Iv t - c) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _) ?_ hlim
    filter_upwards [hbound] with t ht
    nlinarith [sq_nonneg (Iu t - a)]
  have conv : ∀ {f : ℝ → ℝ} {L : ℝ}, Tendsto (fun t => (f t - L) ^ 2) atTop (𝓝 0) →
      Tendsto f atTop (𝓝 L) := fun {f L} hsq => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have := hsq.sqrt
    simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at this
    simpa [Real.norm_eq_abs] using this
  have hx := conv hsq1
  have hy := conv hsq2
  refine ⟨?_, hx, ?_, hy⟩
  · refine (hx.const_sub ((1 - p) * N)).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    linarith [h.unvaccinated_total ht]
  · refine (hy.const_sub (p * N)).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    linarith [h.vaccinated_total ht]

/-- **Lyapunov stability of the endemic equilibrium**, with an explicit bound: for `t ≥ 0`,
`(I_u(t) - a)² + (I_v(t) - c)² ≤ 2 N ((I_u(0) - a)² / I_u(0) + (I_v(0) - c)² / I_v(0))`. -/
theorem endemic_stability {t : ℝ} (ht : 0 ≤ t) :
    (Iu t - a) ^ 2 + (Iv t - c) ^ 2 ≤
      2 * N * ((Iu 0 - a) ^ 2 / Iu 0 + (Iv 0 - c) ^ 2 / Iv 0) := by
  have h1 := h.sq_add_sq_le_lyapunov he hβ hγ hε hN hu hv hSu0 hSv0 hIu0 hIv0 ht
  have h2 := h.lyapunov_le_initial he hβ hγ hε hN hu hv hSu0 hSv0 hIu0 hIv0 ht
  have h3 : lyapunov a c (Iu 0) (Iv 0) ≤ (Iu 0 - a) ^ 2 / Iu 0 + (Iv 0 - c) ^ 2 / Iv 0 :=
    add_le_add (volterra_le_sq_div he.pos_unvaccinated hIu0)
      (volterra_le_sq_div he.pos_vaccinated hIv0)
  have hN2 : 0 ≤ 2 * N := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (h2.trans h3) hN2]

end Endemic

end IsSolution

/-- **Uniqueness of the endemic equilibrium.** For `β, γ, N > 0` and `ε < 1`, two
endemic equilibria coincide (the constant solution at one converges to the other). -/
theorem IsEndemicEq.unique {β γ ε N p a c a' c' : ℝ} (he : IsEndemicEq β γ ε N p a c)
    (he' : IsEndemicEq β γ ε N p a' c') (hβ : 0 < β) (hγ : 0 < γ) (hε : ε < 1) (hN : 0 < N) :
    a = a' ∧ c = c' := by
  have hlt := he'.lt_groups hγ hN hβ.le hε.le
  obtain ⟨-, hx, -, hy⟩ := (isSolution_const_endemic he').tendsto_endemic he hβ.le hγ hε hN
    (by simp) (by simp) (show (0 : ℝ) ≤ (1 - p) * N - a' by linarith)
    (show (0 : ℝ) ≤ p * N - c' by linarith) he'.pos_unvaccinated he'.pos_vaccinated hβ
  exact ⟨(tendsto_nhds_unique tendsto_const_nhds hx).symm,
    (tendsto_nhds_unique tendsto_const_nhds hy).symm⟩

/-- **The threshold theorem for coverage.** For `β, γ, N > 0`, `0 < p < 1` and an imperfect but
effective vaccine `0 < ε < 1`: if `p < p_c` there is an endemic equilibrium `(a, c)` and it
attracts every solution with group sizes `(1 - p) N` and `p N`, nonnegative susceptibles and
positive infectives in both groups. -/
theorem IsSolution.tendsto_endemic_of_lt {β γ ε N p : ℝ} {Su Iu Sv Iv : ℝ → ℝ}
    (h : IsSolution β γ ε N Su Iu Sv Iv) (hβ : 0 < β) (hγ : 0 < γ) (hε0 : 0 < ε) (hε : ε < 1)
    (hN : 0 < N) (hp0 : 0 < p) (hp1 : p < 1) (hp : p < criticalCoverage β γ ε)
    (hu : Su 0 + Iu 0 = (1 - p) * N) (hv : Sv 0 + Iv 0 = p * N) (hSu0 : 0 ≤ Su 0)
    (hSv0 : 0 ≤ Sv 0) (hIu0 : 0 < Iu 0) (hIv0 : 0 < Iv 0) :
    ∃ a c, IsEndemicEq β γ ε N p a c ∧ Tendsto Su atTop (𝓝 ((1 - p) * N - a)) ∧
      Tendsto Iu atTop (𝓝 a) ∧ Tendsto Sv atTop (𝓝 (p * N - c)) ∧ Tendsto Iv atTop (𝓝 c) := by
  obtain ⟨a, c, he⟩ := exists_isEndemicEq hβ hγ hN hp0 hp1 hε ((one_lt_Rv_iff hβ hγ hε0).2 hp)
  exact ⟨a, c, he, h.tendsto_endemic he hβ.le hγ hε hN hu hv hSu0 hSv0 hIu0 hIv0 hβ⟩

end MathlibExt.Biology.Epidemiology.SISVaccination
