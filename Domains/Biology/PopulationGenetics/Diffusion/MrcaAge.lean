/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.Sojourn
public import MathlibExt.Analysis.ODE.GreenKernel
public import MathlibExt.Analysis.SpecialFunctions.Dilog
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# How old is the most recent ancestor of two copies of an allele?

Patterson (2005) studies the age of the most recent common ancestor (MRCA) of two
copies of an allele at present-day population frequency `y`, for a neutral allele in a
panmictic diploid population of constant effective size `N`. Time is in units of `2N`
generations, as in `WrightFisher` and `Sojourn`. Tracing the allele frequency backward
in time gives the Wright-Fisher diffusion killed at rate `1 / x` when the frequency is
`x` (coalescence of the two copies), with backward equation
`∂C/∂t = x (1 - x) / 2 * ∂²C/∂x² - C / x` for the killed transition density `C`.

As in `Sojourn` and `AlleleAge`, only the analytic statements are formalized. The
neutral Wright-Fisher process itself is constructed elsewhere in this library
(`NeutralWrightFisherRaw`, `KimuraFixationProcess`); what is missing is the killed
process, i.e. the frequency process killed at the coalescence time `ζ` and its
coupling to the two-copy coalescent, so Patterson's process-level statements are not
formalized here. The probabilistic readings below are Patterson's; the Lean
statements are facts about the explicit real functions that appear in his formulas.
In particular the spectral expansions of Patterson's Theorems 1 and 2 (which need a
general theory of Jacobi polynomials, absent from Mathlib) and the survival-function
formulas of his Theorems 5(1) and 6(1) (which need the killed transition density
`C`) are not formalized here, and neither is the martingale proof of his
Theorem 5(2). His Theorem 3 is `neutralGreen` (used in Corollary 1 below) and his
Corollary 2 is `integral_neutralGreen` (both `Sojourn`; the value is
`meanAbsorptionTime` in `WrightFisher`); neither is restated here.

* `killedGreen x y` is Patterson's `G_C(x, y)` (Theorem 4), the Green's function of
  the killed diffusion: in the diffusion reading, `G_C(x, y) = ∫₀^∞ C(x, y; t) dt`.
  It is built from the two solutions `pattersonAux1`, `pattersonAux2` of
  `x² (1 - x) / 2 * w'' = w` in his Appendix.
* `pattersonDilog x = Real.li2PowerSeries (1 - x)` is his `dilog` (Equation 16), using the
  generic dilogarithm power-series API in `MathlibExt.Analysis.SpecialFunctions.Dilog`;
  `pattersonDilog_eq_integral` identifies it on `(0, 1)` with Patterson's integral
  `∫₁ˣ (log t) / (1 - t) dt`.
* `meanMrcaNew y` is `M₁(y)` (Equation 16), in the diffusion reading the expected
  MRCA age of two copies of an allele known to be new (nonancestral) at frequency `y`;
  `meanMrcaOld y` is `M₂(y)` (Equation 17), the same expectation for an old
  (ancestral) allele.

## Main results

* `pattersonAux1_ode`, `pattersonAux2_ode`: the Appendix solutions satisfy
  `generator 0 w x = w x / x` on `(0, 1)`, which is Patterson's Equation A2
  (`x² (1 - x) / 2 * w'' = w`) divided by `x`.
* `killedGreen_ode_lt`, `killedGreen_ode_gt`: off the diagonal, `killedGreen (·, y)`
  satisfies the same homogeneous killed equation `generator 0 G x = G x / x` on
  `(0, 1)`, the integrated form of Patterson's Equation 4.
* `continuousAt_killedGreen_diagonal`: `killedGreen (·, y)` is continuous at `x = y`.
* `killedGreen_deriv_jump`: its derivative jumps by `-2 / (y (1 - y))` at `x = y`, as a
  Green's function for `∂C/∂t` with unit source must.
* `killedGreen_eq_greenKernel`, `pattersonAux_wronskian`: on `(0, 1)`, `G_C` is the
  two-solution `GreenKernel.kernel` built from `a₁`, `a₂` with normalization
  `2 / y²`, and the two Appendix solutions have Wronskian `-1`.
* `tendsto_killedGreen_zero`, `tendsto_killedGreen_one`: `G_C(x, y) → 0` as
  `x → 0⁺` and as `x → 1⁻`, the Dirichlet boundary values.
* `pattersonAux1_pos`, `killedGreen_pos`: `a₁` and `G_C` are positive on `(0, 1)`.
* `neutralGreen_old_ratio_eq`: Corollary 1 in analytic form. The Green values
  `neutralGreen ε x = 2ε / x` and `neutralGreen (1 - ε) x = 2ε / (1 - x)` normalize to
  posterior probability `x` that an allele at frequency `x` is old.
* `hasDerivAt_pattersonDilog`, `pattersonDilog_one`: `dilog` differentiates to
  `log x / (1 - x)` on `(0, 1)` and vanishes at `1`.
* `pattersonDilog_eq_integral`: on `(0, 1)`, the `Real.li2PowerSeries` definition agrees with
  Patterson's integral definition of `dilog`.
* `pattersonDilog_zero`, `pattersonDilog_reflection`: `dilog 0 = π² / 6`, and
  `dilog y + dilog (1 - y) + log y * log (1 - y) = π² / 6` (corollaries of
  `Real.li2PowerSeries_one` and `Real.li2PowerSeries_reflection`, in Patterson's normalization).
* `meanMrcaNew_eq_integral`: `M₁(y) = y ∫₀¹ G_C(x, y) / x dx`, Patterson's route to
  Equation 16 (p. 1103): Equation 16 is derived here from Theorem 4, not transcribed.
* `killedGreen_weighted_integral_add_pattersonAux1` and
  `tendsto_killedGreen_one_sub_div`:
  `y (1 - y) ∫₀¹ G_C(x, y) / (x (1 - x)) dx + a₁(y) = y`, where `a₁(y)` is the limit
  of `y (1 - y) G_C(1 - ε, y) / (2ε)`. This is the analytic content of Patterson's
  headline result (Theorem 5(2), via Equation 14 integrated over `t`) that the
  expected MRCA age at unknown ancestry is `y` in scaled time, i.e. `2Ny`
  generations.
* `meanMrca_mixture`: `(1 - y) M₁(y) + y M₂(y) = y` on `(0, 1)`. This is
  Equation 17 rearranged: Patterson obtains `M₂` by solving this mixture for it
  (p. 1098), and `meanMrcaOld` is defined by Equation 17, so the identity itself is
  immediate algebra; the content of Theorem 5(2) is the integral identity above.
* `tendsto_meanMrcaNew_one`: `M₁(y) → 2 (π² - 9) / 3` as `y → 1⁻` (p. 1094, item 6).
* `pattersonTaylorStep_new`, `pattersonTaylorStep_unknown`: the two one-step
  computations behind Corollaries 3 and 4 (p. 1100) for Patterson's Taylor recursion
  (Theorem 7): the step sends `y / x²` to `0` and `y (1 - y) / (x² (1 - x))` to its
  negative. The density conclusions of the corollaries need `C` and are not stated.
* `eigeninstance_two_zero`, `eigeninstance_two_one`, `eigeninstance_two_two`:
  the `k = 2`, `n = 0, 1, 2` instances of the separated-solution ODE of Theorem 1
  (Appendix Equation A1) for the Table A1 polynomials `w = 1, 6x - 4, 28x² - 35x + 10`
  with eigenvalues `3, 6, 10`.

## References

* N. J. Patterson, *How old is the most recent ancestor of two copies of an allele?*,
  Genetics 169 (2005) 1093-1104.
* W. J. Ewens, *The diffusion equation and a pseudo-distribution in genetics*,
  J. Roy. Statist. Soc. Ser. B 25 (1963) 405-412. (Theorem 3, here `neutralGreen`.)
* M. Kimura and T. Ohta, *The age of a neutral mutant persisting in a finite
  population*, Genetics 75 (1973) 199-212. (Corollary 1.)
* S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic
  Press (1981). (Diffusions with killing, Green's functions.)
-/

@[expose] public section

open Real Set Filter Polynomial
open scoped Topology

namespace Domains.Biology.PopulationGenetics.Diffusion

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Patterson's first Appendix solution `a₁` (Equation A3):
`a₁(x) = 2 - x + 2 (1 - x) log (1 - x) / x`. It solves `generator 0 w x = w x / x` on
`(0, 1)` (`pattersonAux1_ode`; this is his Equation A2, `x² (1 - x) / 2 * w'' = w`,
divided by `x`), tends to `0` at `x = 0` and equals `1` at `x = 1` (Equations A5,
A6). At `x = 0` the Lean value is the totalized `2` (from `u / 0 = 0`), not the limit; at `x = 1`
the term `(1 - x) log (1 - x)` is `0` (with `log 0 = 0`). For `x > 1` the logarithm is
`log (x - 1)` (`log u = log |u|`). -/
noncomputable def pattersonAux1 (x : ℝ) : ℝ :=
  2 - x + 2 * ((1 - x) * log (1 - x) / x)

/-- Patterson's second Appendix solution `a₂` (Equation A4): `a₂(x) = (1 - x) / x`.
It solves `generator 0 w x = w x / x` on `(0, 1)` (`pattersonAux2_ode`, his
Equation A2 divided by `x`) and vanishes at `x = 1` (Equation A8). With `x / 0 = 0`,
`a₂(0) = 0`. -/
noncomputable def pattersonAux2 (x : ℝ) : ℝ :=
  (1 - x) / x

/-- The Green's function `G_C` of the Wright-Fisher diffusion killed at rate `1 / x`
(coalescence of two allele copies), Patterson's Theorem 4: for `x ≤ y`,

  `G_C(x, y) = -2 (x² + 2x log (1 - x) - 2x - 2 log (1 - x)) / (y² x)`,

and for `x > y`,

  `G_C(x, y) = 2 (1 - x) (2y - y² + 2 log (1 - y) - 2y log (1 - y)) / ((1 - y) y² x)`.

In the diffusion reading (not formalized here), `G_C(x, y) = ∫₀^∞ C(x, y; t) dt` for
the killed transition density `C` of his Equation 4, with `y` the present-day
frequency and `x` the frequency backward in time. For `x ≠ 0` and `y ≠ 0` the branches are
`2 a₁(x) / y²` and, if also `y ≠ 1`, `2 a₁(y) a₂(x) / ((1 - y) y)` (`killedGreen_eq_aux_left`,
`killedGreen_eq_aux_right`); at `x = 0 < y` the formula gives `0`, whereas `2 a₁(0) / y² = 4 / y²`.
The formula is meaningful for `x, y ∈ (0, 1)`; outside that range Lean's totalized division takes
over: with `u / 0 = 0` the value is `0` when `x = 0`, when `y = 0` and when `x > y = 1`, and
logarithms are taken with `log 0 = 0` and `log u = log |u|` for negative `u`. -/
noncomputable def killedGreen (x y : ℝ) : ℝ :=
  if x ≤ y then -2 * (x ^ 2 + 2 * x * log (1 - x) - 2 * x - 2 * log (1 - x)) / (y ^ 2 * x)
  else 2 * (1 - x) * (2 * y - y ^ 2 + 2 * log (1 - y) - 2 * y * log (1 - y)) /
    ((1 - y) * y ^ 2 * x)

/-- Patterson's `dilog` (Equation 16), defined here by
`pattersonDilog x = Real.li2PowerSeries (1 - x)`, using the generic dilogarithm power-series API in
`MathlibExt.Analysis.SpecialFunctions.Dilog`. Patterson's own definition is the
integral `∫₁ˣ (log t) / (1 - t) dt`; `pattersonDilog_eq_integral` proves that the
two agree on `(0, 1)`. This is his sign and normalization convention:
`dilog 1 = 0`, derivative `log x / (1 - x)` on `(0, 1)`. In classical notation
`pattersonDilog x = Li₂(1 - x)` for `0 ≤ x ≤ 2` (Maple's `dilog`), where the series converges; for
`x < 0` and `x > 2` it is not summable and the value is `0`, not a continuation of `Li₂`. -/
noncomputable def pattersonDilog (x : ℝ) : ℝ :=
  Real.li2PowerSeries (1 - x)

/-- Patterson's `M₁(y)` (Equation 16, Theorem 6(2)): in the diffusion reading, the
expected age (in units of `2N` generations) of the MRCA of two copies of an allele
known to be new (nonancestral) and now at frequency `y`:

  `M₁(y) = -4 + 2 log y + (2π² - 12 dilog y) / (3y) + 2 (log y) / (1 - y)`.

Meaningful for `y ∈ (0, 1)`. At `y = 1` the Lean value is `2π² / 3 - 4`: the last
term `2 log 1 / (1 - 1)` evaluates to `0` by totalized division, so the value at `1`
is an artifact, `2` more than the limit `2 (π² - 9) / 3` of
`tendsto_meanMrcaNew_one`. At `y = 0` the value is `-4` (with `log 0 = 0`), and for `y < 0` the
logarithm is `log |y|`. The identity `meanMrcaNew_eq_integral` derives this formula from
Theorem 4. -/
noncomputable def meanMrcaNew (y : ℝ) : ℝ :=
  -4 + 2 * log y + (2 * π ^ 2 - 12 * pattersonDilog y) / (3 * y) + 2 * log y / (1 - y)

/-- Patterson's `M₂(y)` (Equation 17): in the diffusion reading, the expected MRCA
age of two copies of an old (ancestral) allele now at frequency `y`,
`M₂(y) = 1 - (1 - y) M₁(y) / y`. Meaningful for `y ∈ (0, 1)`; at `y = 1` the Lean
value is `1`, since the `1 - y` factor annihilates the (totalized) `M₁` value; at `y = 0` it is
also `1` (`x / 0 = 0`). -/
noncomputable def meanMrcaOld (y : ℝ) : ℝ :=
  1 - (1 - y) * meanMrcaNew y / y

/-- One step of Patterson's Taylor recursion (Theorem 7):
`f ↦ (x (1 - x) f(x) / 2)'' - f(x) / x`. In his Theorem 7, iterating this step `n`
times from `f₀ = f` and evaluating at the present frequency `y` gives the `n`-th
`t`-derivative at `t = 0` of `F(y, f; t) = ∫₀¹ f(x) C(x, y; t) dx`; that theorem
needs the killed density `C` and is not formalized here. Derivatives that do not exist are taken
to be `0`, and `f 0 / 0 = 0`. -/
noncomputable def pattersonTaylorStep (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv fun x => x * (1 - x) * f x / 2) x - f x / x

/-- If `f` and `f'` have the stated derivatives at every point of an open set `s`,
then `deriv (deriv f) = f''` on `s`. -/
private theorem deriv_deriv_eq_of_hasDerivAt {f f' f'' : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (h1 : ∀ x ∈ s, HasDerivAt f (f' x) x)
    (h2 : ∀ x ∈ s, HasDerivAt f' (f'' x) x) {x : ℝ} (hx : x ∈ s) :
    deriv (deriv f) x = f'' x := by
  have heq : deriv f =ᶠ[𝓝 x] f' := by
    filter_upwards [hs.mem_nhds hx] with z hz
    exact (h1 z hz).deriv
  rw [heq.deriv_eq]
  exact (h2 x hx).deriv

private theorem hasDerivAt_log_one_sub {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt (fun x => log (1 - x)) (-(1 - x)⁻¹) x := by
  have h1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have h := (Real.hasDerivAt_log h1).comp x
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x))
  apply h.congr_deriv
  simp

private theorem hasDerivAt_pattersonAux2 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt pattersonAux2 (-1 / x ^ 2) x := by
  change HasDerivAt (fun x => (1 - x) / x) (-1 / x ^ 2) x
  have h := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)).div (hasDerivAt_id' x) hx
  apply h.congr_deriv
  simp only [Pi.sub_apply]
  field_simp
  ring

private theorem hasDerivAt_neg_one_div_sq {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => -1 / x ^ 2) (2 / x ^ 3) x := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    have h := (hasDerivAt_id' x).pow 2
    apply h.congr_deriv
    simp
  have h := (hasDerivAt_const x (-1 : ℝ)).div hpow (pow_ne_zero 2 hx)
  apply h.congr_deriv
  field_simp
  ring

private theorem hasDerivAt_pattersonAux1_num {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt (fun x => (1 - x) * log (1 - x)) (-log (1 - x) - 1) x := by
  have h1mx : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)
    apply h.congr_deriv
    simp
  have h := h1mx.mul (hasDerivAt_log_one_sub hx)
  apply h.congr_deriv
  have h1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  field_simp
  ring

private theorem hasDerivAt_pattersonAux1_frac {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (fun x => (1 - x) * log (1 - x) / x) (-(log (1 - x) + x) / x ^ 2) x := by
  have h := (hasDerivAt_pattersonAux1_num hx1).div (hasDerivAt_id' x) hx0
  apply h.congr_deriv
  field_simp
  ring

private theorem hasDerivAt_pattersonAux1 {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt pattersonAux1 (-1 - 2 * (log (1 - x) + x) / x ^ 2) x := by
  change HasDerivAt (fun x => 2 - x + 2 * ((1 - x) * log (1 - x) / x))
    (-1 - 2 * (log (1 - x) + x) / x ^ 2) x
  have hfrac := (hasDerivAt_pattersonAux1_frac hx0 hx1).const_mul (2 : ℝ)
  have hlin : HasDerivAt (fun x : ℝ => 2 - x) (-1) x := by
    have h := (hasDerivAt_const x (2 : ℝ)).sub (hasDerivAt_id' x)
    apply h.congr_deriv
    simp
  have h := hlin.add hfrac
  apply h.congr_deriv
  ring

private theorem hasDerivAt_pattersonAux1' {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (fun x => -1 - 2 * (log (1 - x) + x) / x ^ 2)
      ((2 * x ^ 2 / (1 - x) + 4 * log (1 - x) + 4 * x) / x ^ 3) x := by
  have h1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    have h := (hasDerivAt_id' x).pow 2
    apply h.congr_deriv
    simp
  have hsum : HasDerivAt (fun x => log (1 - x) + x) (-(1 - x)⁻¹ + 1) x :=
    (hasDerivAt_log_one_sub hx1).add (hasDerivAt_id' x)
  have hdiv := (hsum.const_mul (2 : ℝ)).div hpow (pow_ne_zero 2 hx0)
  have h := (hasDerivAt_const x (-1 : ℝ)).sub hdiv
  apply h.congr_deriv
  field_simp
  ring

/-- **Patterson's Equation A2 for `a₂`**, in generator form: on `(0, 1)`,
`generator 0 a₂ x = a₂(x) / x` (his `x² (1 - x) / 2 * a₂''(x) = a₂(x)` divided
by `x`). -/
theorem pattersonAux2_ode {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    generator 0 pattersonAux2 x = pattersonAux2 x / x := by
  rw [generator]
  simp only [zero_mul, add_zero]
  rw [deriv_deriv_eq_of_hasDerivAt isOpen_Ioo
    (fun z hz => hasDerivAt_pattersonAux2 hz.1.ne')
    (fun z hz => hasDerivAt_neg_one_div_sq hz.1.ne') hx]
  change x * (1 - x) / 2 * (2 / x ^ 3) = ((1 - x) / x) / x
  field_simp

/-- **Patterson's Equation A2 for `a₁`**, in generator form: on `(0, 1)`,
`generator 0 a₁ x = a₁(x) / x` (his `x² (1 - x) / 2 * a₁''(x) = a₁(x)` divided
by `x`). -/
theorem pattersonAux1_ode {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    generator 0 pattersonAux1 x = pattersonAux1 x / x := by
  rw [generator]
  simp only [zero_mul, add_zero]
  rw [deriv_deriv_eq_of_hasDerivAt isOpen_Ioo
    (fun z hz => hasDerivAt_pattersonAux1 hz.1.ne' (ne_of_lt hz.2))
    (fun z hz => hasDerivAt_pattersonAux1' hz.1.ne' (ne_of_lt hz.2)) hx]
  change x * (1 - x) / 2 * ((2 * x ^ 2 / (1 - x) + 4 * log (1 - x) + 4 * x) / x ^ 3) =
    (2 - x + 2 * ((1 - x) * log (1 - x) / x)) / x
  have hx0 : x ≠ 0 := hx.1.ne'
  have h1 : (1 : ℝ) - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  field_simp
  ring

/-- Patterson's Equation A6: `a₁(1) = 1`. At `x = 1` the Lean computation uses
`(1 - x) * log (1 - x) = 0 * log 0 = 0` (with `log 0 = 0`); `tendsto_pattersonAux1_nhdsLT_one` shows
the value is also the limit from below. -/
theorem pattersonAux1_one : pattersonAux1 1 = 1 := by
  norm_num [pattersonAux1]

/-- Patterson's Equation A8: `a₂(1) = 0`. -/
theorem pattersonAux2_one : pattersonAux2 1 = 0 := by
  norm_num [pattersonAux2]

/-- The `x ≤ y` branch of Theorem 4 in terms of `a₁`: for `x ≤ y` with `x ≠ 0` and `y ≠ 0`,
`G_C(x, y) = 2 a₁(x) / y²`. -/
theorem killedGreen_eq_aux_left {x y : ℝ} (hxy : x ≤ y) (hx : x ≠ 0) (hy : y ≠ 0) :
    killedGreen x y = (2 / y ^ 2) * pattersonAux1 x := by
  unfold killedGreen pattersonAux1
  rw [ite_eq_left hxy]
  field_simp
  ring

/-- The `y < x` branch of Theorem 4 in terms of `a₁, a₂`: for `y < x` with `x ≠ 0`, `y ≠ 0` and
`y ≠ 1`, `G_C(x, y) = (2 a₁(y) / ((1 - y) y)) a₂(x)`. -/
theorem killedGreen_eq_aux_right {x y : ℝ} (hxy : y < x) (hx : x ≠ 0) (hy0 : y ≠ 0)
    (hy1 : y ≠ 1) :
    killedGreen x y = (2 * pattersonAux1 y / ((1 - y) * y)) * pattersonAux2 x := by
  have h1y : (1 : ℝ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
  unfold killedGreen pattersonAux1 pattersonAux2
  rw [ite_eq_right (not_le.mpr hxy)]
  field_simp
  ring

/-- The Wronskian of Patterson's two Appendix solutions is `-1` on `(0, 1)`. This is
the normalization behind the constant in `killedGreen_deriv_jump`. -/
theorem pattersonAux_wronskian {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    GreenKernel.wronskian pattersonAux1 pattersonAux2 y = -1 := by
  have hy0 : y ≠ 0 := hy.1.ne'
  have h1y : (1 : ℝ) - y ≠ 0 := (sub_pos.mpr hy.2).ne'
  rw [GreenKernel.wronskian,
    (hasDerivAt_pattersonAux1 hy0 (ne_of_lt hy.2)).deriv,
    (hasDerivAt_pattersonAux2 hy0).deriv]
  simp only [pattersonAux1, pattersonAux2]
  field_simp
  ring

/-- Patterson's killed Green function is the two-solution `GreenKernel.kernel`
built from `a₁` and `a₂`, with normalization `C y = 2 / y²`, on `(0, 1)`. -/
theorem killedGreen_eq_greenKernel {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    killedGreen x y =
      GreenKernel.kernel pattersonAux1 pattersonAux2 (fun y => 2 / y ^ 2) x y := by
  by_cases h : x ≤ y
  · rw [killedGreen_eq_aux_left h hx.1.ne' hy.1.ne', GreenKernel.kernel_of_le h]
  · have hlt : y < x := not_le.mp h
    have hx0 : x ≠ 0 := hx.1.ne'
    have hy0 : y ≠ 0 := hy.1.ne'
    have h1y : (1 : ℝ) - y ≠ 0 := (sub_pos.mpr hy.2).ne'
    rw [killedGreen_eq_aux_right hlt hx0 hy0 (ne_of_lt hy.2),
      GreenKernel.kernel_of_lt hlt]
    simp only [pattersonAux2]
    field_simp

/-- At the diagonal the right branch takes the same value as the left branch. -/
private theorem killedGreen_self_eq_aux_right {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    killedGreen y y = (2 * pattersonAux1 y / ((1 - y) * y)) * pattersonAux2 y := by
  rw [killedGreen_eq_aux_left le_rfl hy.1.ne' hy.1.ne']
  change (2 / y ^ 2) * pattersonAux1 y =
    (2 * pattersonAux1 y / ((1 - y) * y)) * ((1 - y) / y)
  have hy0 : y ≠ 0 := hy.1.ne'
  have h1y : (1 : ℝ) - y ≠ 0 := (sub_pos.mpr hy.2).ne'
  field_simp

private theorem killedGreen_eventuallyEq_aux_left {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (fun x => killedGreen x y) =ᶠ[𝓝[Iic y] y]
      fun x => (2 / y ^ 2) * pattersonAux1 x := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hy.1)] with z hz1 hz2
  exact killedGreen_eq_aux_left hz1 hz2.ne' hy.1.ne'

private theorem killedGreen_eventuallyEq_aux_right {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (fun x => killedGreen x y) =ᶠ[𝓝[Ici y] y]
      fun x => (2 * pattersonAux1 y / ((1 - y) * y)) * pattersonAux2 x := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  rcases hz.eq_or_lt with rfl | h
  · exact killedGreen_self_eq_aux_right hy
  · exact killedGreen_eq_aux_right h (hy.1.trans h).ne' hy.1.ne' (ne_of_lt hy.2)

private theorem hasDerivAt_killedGreen_of_lt {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) (hxy : x < y) :
    HasDerivAt (fun x => killedGreen x y)
      ((2 / y ^ 2) * (-1 - 2 * (log (1 - x) + x) / x ^ 2)) x := by
  have hbr := (hasDerivAt_pattersonAux1 hx.1.ne' (ne_of_lt hx.2)).const_mul (2 / y ^ 2)
  apply hbr.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hxy, Ioi_mem_nhds hx.1] with z hz1 hz2
  exact killedGreen_eq_aux_left hz1.le hz2.ne' hy.1.ne'

private theorem hasDerivAt_killedGreen_of_gt {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) (hxy : y < x) :
    HasDerivAt (fun x => killedGreen x y)
      ((2 * pattersonAux1 y / ((1 - y) * y)) * (-1 / x ^ 2)) x := by
  have hbr := (hasDerivAt_pattersonAux2 hx.1.ne').const_mul
    (2 * pattersonAux1 y / ((1 - y) * y))
  apply hbr.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hxy] with z hz
  exact killedGreen_eq_aux_right hz (hy.1.trans hz).ne' hy.1.ne' (ne_of_lt hy.2)

/-- **The killed backward equation below the diagonal.** For `0 < x < y < 1`,
`generator 0 (G_C(·, y)) x = G_C(x, y) / x`, the time-integrated form of
Patterson's Equation 4 off the diagonal. -/
theorem killedGreen_ode_lt {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hxy : x < y) :
    generator 0 (fun x => killedGreen x y) x = killedGreen x y / x := by
  rw [generator]
  simp only [zero_mul, add_zero]
  rw [deriv_deriv_eq_of_hasDerivAt isOpen_Ioo (s := Ioo 0 y)
    (fun z hz => hasDerivAt_killedGreen_of_lt ⟨hz.1, hz.2.trans hy.2⟩ hy hz.2)
    (fun z hz => (hasDerivAt_pattersonAux1' hz.1.ne'
      (ne_of_lt (hz.2.trans hy.2))).const_mul _)
    ⟨hx.1, hxy⟩]
  rw [killedGreen_eq_aux_left hxy.le hx.1.ne' hy.1.ne']
  change x * (1 - x) / 2 *
      ((2 / y ^ 2) * ((2 * x ^ 2 / (1 - x) + 4 * log (1 - x) + 4 * x) / x ^ 3)) =
    ((2 / y ^ 2) * (2 - x + 2 * ((1 - x) * log (1 - x) / x))) / x
  have hx0 : x ≠ 0 := hx.1.ne'
  have hy0 : y ≠ 0 := hy.1.ne'
  have h1 : (1 : ℝ) - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  field_simp
  ring

/-- **The killed backward equation above the diagonal.** For `0 < y < x < 1`,
`generator 0 (G_C(·, y)) x = G_C(x, y) / x`. -/
theorem killedGreen_ode_gt {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hxy : y < x) :
    generator 0 (fun x => killedGreen x y) x = killedGreen x y / x := by
  rw [generator]
  simp only [zero_mul, add_zero]
  rw [deriv_deriv_eq_of_hasDerivAt isOpen_Ioo (s := Ioo y 1)
    (fun z hz => hasDerivAt_killedGreen_of_gt ⟨hy.1.trans hz.1, hz.2⟩ hy hz.1)
    (fun z hz => (hasDerivAt_neg_one_div_sq (hy.1.trans hz.1).ne').const_mul _)
    ⟨hxy, hx.2⟩]
  rw [killedGreen_eq_aux_right hxy hx.1.ne' hy.1.ne' (ne_of_lt hy.2)]
  change x * (1 - x) / 2 *
      ((2 * pattersonAux1 y / ((1 - y) * y)) * (2 / x ^ 3)) =
    ((2 * pattersonAux1 y / ((1 - y) * y)) * ((1 - x) / x)) / x
  have hx0 : x ≠ 0 := hx.1.ne'
  have hy0 : y ≠ 0 := hy.1.ne'
  have h1y : (1 : ℝ) - y ≠ 0 := (sub_pos.mpr hy.2).ne'
  field_simp

/-- Left derivative of `G_C(·, y)` at the diagonal `x = y`, for `y ∈ (0, 1)`:
`(2 / y²) (-1 - 2 (log (1 - y) + y) / y²)`. -/
theorem hasDerivWithinAt_killedGreen_Iic {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fun x => killedGreen x y)
      ((2 / y ^ 2) * (-1 - 2 * (log (1 - y) + y) / y ^ 2)) (Iic y) y := by
  have hbr := ((hasDerivAt_pattersonAux1 hy.1.ne'
    (ne_of_lt hy.2)).const_mul (2 / y ^ 2)).hasDerivWithinAt (s := Iic y)
  exact hbr.congr_of_eventuallyEq_of_mem (killedGreen_eventuallyEq_aux_left hy)
    (mem_Iic.mpr le_rfl)

/-- Right derivative of `G_C(·, y)` at the diagonal `x = y`, for `y ∈ (0, 1)`:
`-2 a₁(y) / ((1 - y) y³)`. -/
theorem hasDerivWithinAt_killedGreen_Ici {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fun x => killedGreen x y)
      ((2 * pattersonAux1 y / ((1 - y) * y)) * (-1 / y ^ 2)) (Ici y) y := by
  have hbr := ((hasDerivAt_pattersonAux2 hy.1.ne').const_mul
    (2 * pattersonAux1 y / ((1 - y) * y))).hasDerivWithinAt (s := Ici y)
  exact hbr.congr_of_eventuallyEq_of_mem (killedGreen_eventuallyEq_aux_right hy)
    (mem_Ici.mpr le_rfl)

/-- The derivative jump of `G_C(·, y)` at the diagonal, for `y ∈ (0, 1)`: right derivative minus
left derivative is `-2 / (y (1 - y))`, the unit-source condition for the Green's function
of Patterson's Equation 4. -/
theorem killedGreen_deriv_jump {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    derivWithin (fun x => killedGreen x y) (Ici y) y -
        derivWithin (fun x => killedGreen x y) (Iic y) y =
      -2 / (y * (1 - y)) := by
  rw [(hasDerivWithinAt_killedGreen_Ici hy).derivWithin (uniqueDiffWithinAt_Ici y),
    (hasDerivWithinAt_killedGreen_Iic hy).derivWithin (uniqueDiffWithinAt_Iic y)]
  have hy0 : y ≠ 0 := hy.1.ne'
  have h1y : (1 : ℝ) - y ≠ 0 := (sub_pos.mpr hy.2).ne'
  simp only [pattersonAux1]
  field_simp
  ring

/-- `G_C(·, y)` is continuous across the diagonal `x = y` for `y ∈ (0, 1)`. -/
theorem continuousAt_killedGreen_diagonal {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (fun x => killedGreen x y) y := by
  have hL : ContinuousWithinAt (fun x => killedGreen x y) (Iic y) y := by
    have hT : Tendsto (fun x => killedGreen x y) (𝓝[Iic y] y)
        (𝓝 ((2 / y ^ 2) * pattersonAux1 y)) :=
      ((hasDerivAt_pattersonAux1 hy.1.ne'
        (ne_of_lt hy.2)).continuousAt.const_mul (2 / y ^ 2)).continuousWithinAt.congr'
          (killedGreen_eventuallyEq_aux_left hy).symm
    rwa [← killedGreen_eq_aux_left le_rfl hy.1.ne' hy.1.ne'] at hT
  have hR : ContinuousWithinAt (fun x => killedGreen x y) (Ici y) y := by
    have hT : Tendsto (fun x => killedGreen x y) (𝓝[Ici y] y)
        (𝓝 ((2 * pattersonAux1 y / ((1 - y) * y)) * pattersonAux2 y)) :=
      ((hasDerivAt_pattersonAux2 hy.1.ne').continuousAt.const_mul
        (2 * pattersonAux1 y / ((1 - y) * y))).continuousWithinAt.congr'
          (killedGreen_eventuallyEq_aux_right hy).symm
    rwa [← killedGreen_self_eq_aux_right hy] at hT
  have h := hL.union hR
  rwa [Set.Iic_union_Ici, continuousWithinAt_univ] at h

private theorem norm_log_div_one_sub_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖log t / (1 - t)‖ ≤ 1 / t := by
  rcases ht1.eq_or_lt with rfl | h
  · simp
  · have hlog : -log t ≤ (1 - t) / t := by
      have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr ht0)
      rw [Real.log_inv] at hh
      have he : t⁻¹ - 1 = (1 - t) / t := by
        field_simp
      rwa [he] at hh
    have hnorm : ‖log t / (1 - t)‖ = (-log t) / (1 - t) := by
      rw [Real.norm_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos ht0.le ht1) (sub_pos.mpr h).le),
        neg_div]
    rw [hnorm]
    calc (-log t) / (1 - t) ≤ ((1 - t) / t) / (1 - t) := by gcongr
      _ = 1 / t := by field_simp

private theorem intervalIntegrable_log_div_one_sub {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) :
    IntervalIntegrable (fun t => log t / (1 - t)) MeasureTheory.volume a b := by
  have hbound : ∀ t ∈ Set.Icc (min a b) 1, ‖log t / (1 - t)‖ ≤ 1 / min a b := by
    intro t ht
    have ht0 : 0 < t := (lt_min ha hb).trans_le ht.1
    exact (norm_log_div_one_sub_le ht0 ht.2).trans
      (one_div_le_one_div_of_le (lt_min ha hb) ht.1)
  have hmeas : Measurable (fun t => log t / (1 - t)) :=
    Real.measurable_log.div (measurable_const.sub measurable_id)
  have key : ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Icc (min a b) 1 →
      MeasureTheory.volume s < ⊤ →
      MeasureTheory.IntegrableOn (fun t => log t / (1 - t)) s MeasureTheory.volume := by
    intro s hsmeas hs hsfin
    refine MeasureTheory.IntegrableOn.of_bound hsfin hmeas.aestronglyMeasurable
      (1 / min a b) ?_
    rw [MeasureTheory.ae_restrict_iff' hsmeas]
    exact Filter.Eventually.of_forall fun t ht => hbound t (hs ht)
  refine ⟨key (Set.Ioc a b) measurableSet_Ioc ?_ ?_,
    key (Set.Ioc b a) measurableSet_Ioc ?_ ?_⟩
  · intro t ht
    exact ⟨(min_le_left a b).trans ht.1.le, ht.2.trans hb1⟩
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · intro t ht
    exact ⟨(min_le_right a b).trans ht.1.le, ht.2.trans ha1⟩
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top

/-- Patterson's `dilog` vanishes at `1`, since `Real.li2PowerSeries 0 = 0`. -/
theorem pattersonDilog_one : pattersonDilog 1 = 0 := by
  simp only [pattersonDilog, sub_self, Real.li2PowerSeries_zero]

/-- The derivative of Patterson's `dilog` on `(0, 1)` is `log x / (1 - x)`, from
`Real.hasDerivAt_li2PowerSeries` by the chain rule. -/
theorem hasDerivAt_pattersonDilog {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt pattersonDilog (log x / (1 - x)) x := by
  have h1mx : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)
    refine h.congr_deriv ?_
    simp
  have habs : |(1 : ℝ) - x| < 1 := by
    rw [abs_of_pos (sub_pos.mpr hx.2)]
    exact sub_lt_self 1 hx.1
  have h := (Real.hasDerivAt_li2PowerSeries habs (sub_pos.mpr hx.2).ne').comp x h1mx
  change HasDerivAt (fun x => Real.li2PowerSeries (1 - x)) (log x / (1 - x)) x
  refine h.congr_deriv ?_
  have e : (1 : ℝ) - (1 - x) = x := by ring
  rw [e, mul_neg, mul_one, neg_div, neg_neg]

/-- `log y / (1 - y) → -1` as `y → 1⁻` (the slope of `log` at `1`). -/
private theorem tendsto_log_div_one_sub_nhdsLT_one :
    Tendsto (fun y => log y / (1 - y)) (𝓝[<] (1 : ℝ)) (𝓝 (-1)) := by
  have h := (Real.hasDerivAt_log (one_ne_zero)).tendsto_slope
  have h2 : Tendsto (slope log 1) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hh := h.mono_left (nhdsWithin_mono (1 : ℝ) (s := Set.Iio (1 : ℝ))
      (fun z hz => ne_of_lt hz))
    simpa using hh
  have h3 : Tendsto (fun y => -(slope log 1 y)) (𝓝[<] (1 : ℝ)) (𝓝 (-1)) := h2.neg
  refine h3.congr (fun y => ?_)
  by_cases hy1 : y = 1
  · subst hy1
    simp [slope]
  · rw [slope_def_field, log_one, sub_zero, ← div_neg, neg_sub]

/-- `(1 - x) log (1 - x) → 0` as `x → 1⁻` (continuity of `negMulLog` at `0`). -/
private theorem tendsto_one_sub_mul_log_one_sub_nhdsLT_one :
    Tendsto (fun x => (1 - x) * log (1 - x)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hsub : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => (1 : ℝ) - x) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
      (continuous_const.sub continuous_id).tendsto (1 : ℝ)
    have h' : Tendsto (fun x : ℝ => (1 : ℝ) - x) (𝓝[<] (1 : ℝ))
        (𝓝 ((1 : ℝ) - 1)) :=
      h.mono_left nhdsWithin_le_nhds
    simpa using h'
  have h0 : negMulLog (0 : ℝ) = 0 := by simp [negMulLog]
  have h2 : Tendsto (fun x => negMulLog (1 - x)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h3 : Tendsto (fun x => negMulLog (1 - x)) (𝓝[<] (1 : ℝ))
        (𝓝 (negMulLog 0)) :=
      (continuous_negMulLog.tendsto 0).comp hsub
    rwa [h0] at h3
  have h1 : Tendsto (fun x => -negMulLog (1 - x)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa using h2.neg
  refine h1.congr (fun x => ?_)
  simp only [negMulLog]
  ring

/-- Patterson's `dilog` tends to `0` at `1` from below, by continuity of
`Real.li2PowerSeries` at `0`. -/
theorem tendsto_pattersonDilog_nhdsLT_one :
    Tendsto pattersonDilog (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hsub : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => (1 : ℝ) - x) (𝓝[<] (1 : ℝ))
        (𝓝 ((1 : ℝ) - 1)) :=
      ((continuous_const.sub continuous_id).tendsto (1 : ℝ)).mono_left
        nhdsWithin_le_nhds
    simpa using h
  have hcont : Tendsto Real.li2PowerSeries (𝓝 (0 : ℝ)) (𝓝 (Real.li2PowerSeries 0)) :=
    Real.continuousAt_li2PowerSeries_zero.tendsto
  rw [Real.li2PowerSeries_zero] at hcont
  exact hcont.comp hsub

/-- On `(0, 1)`, Patterson's `dilog`, defined here through `Real.li2PowerSeries`, agrees
with Patterson's integral definition `∫₁ˣ (log t) / (1 - t) dt`. The proof
integrates the derivative from `x` to `1` and uses the limit `0` at `1`. -/
theorem pattersonDilog_eq_integral {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    pattersonDilog x = ∫ t in (1 : ℝ)..x, log t / (1 - t) := by
  have hderiv : ∀ t ∈ Set.Ioo x 1,
      HasDerivAt pattersonDilog (log t / (1 - t)) t :=
    fun t ht => hasDerivAt_pattersonDilog ⟨hx.1.trans ht.1, ht.2⟩
  have hint : IntervalIntegrable (fun t => log t / (1 - t))
      MeasureTheory.volume x 1 :=
    intervalIntegrable_log_div_one_sub hx.1 hx.2.le one_pos le_rfl
  have hlimx : Tendsto pattersonDilog (𝓝[>] x) (𝓝 (pattersonDilog x)) :=
    (hasDerivAt_pattersonDilog hx).continuousAt.continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx.2
    hderiv hint hlimx tendsto_pattersonDilog_nhdsLT_one
  rw [intervalIntegral.integral_symm, h]
  simp

/-- **The value `dilog 0 = π² / 6`** in Patterson's normalization, the
`Real.li2PowerSeries_one` Basel value. -/
theorem pattersonDilog_zero : pattersonDilog 0 = π ^ 2 / 6 := by
  simp only [pattersonDilog, sub_zero, Real.li2PowerSeries_one]

/-- Derivative of `pattersonDilog (1 - z)` on `(0, 1)`. -/
private theorem hasDerivAt_pattersonDilog_one_sub {z : ℝ}
    (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => pattersonDilog (1 - z)) (-(log (1 - z) / z)) z := by
  have h1mx : HasDerivAt (fun z : ℝ => 1 - z) (-1) z := by
    have h := (hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id' z)
    apply h.congr_deriv
    simp
  have h := (hasDerivAt_pattersonDilog
    ⟨sub_pos.mpr hz.2, by linarith [hz.1]⟩).comp z h1mx
  refine h.congr_deriv ?_
  have e : (1 : ℝ) - (1 - z) = z := by ring
  rw [e]
  ring

/-- **Euler's reflection formula for Patterson's `dilog`**: for `y ∈ (0, 1)`,
`dilog y + dilog (1 - y) + log y * log (1 - y) = π² / 6`. This is
`Real.li2PowerSeries_reflection` in Patterson's normalization. -/
theorem pattersonDilog_reflection {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    pattersonDilog y + pattersonDilog (1 - y) + log y * log (1 - y) =
      π ^ 2 / 6 := by
  have h := Real.li2PowerSeries_reflection hy
  have e : (1 : ℝ) - (1 - y) = y := by ring
  simp only [pattersonDilog]
  rw [e]
  linarith [h]

/-- **Patterson's Corollary 1, analytic form.** For `0 < ε < x < 1 - ε`, the Green
values `G_K(ε, x) = 2ε / x` (allele new) and `G_K(1 - ε, x) = 2ε / (1 - x)` (allele
old), with `G_K = neutralGreen` his Theorem 3, normalize to `x`: in his Bayesian
reading, the posterior probability that an allele at frequency `x` is old is `x`.
The Green-value equalities are exact for every such `ε`, not only in the limit. -/
theorem neutralGreen_old_ratio_eq {ε x : ℝ} (hε : 0 < ε) (h1 : ε < x)
    (h2 : x < 1 - ε) :
    neutralGreen (1 - ε) x / (neutralGreen ε x + neutralGreen (1 - ε) x) = x := by
  have hx0 : (0 : ℝ) < x := hε.trans h1
  have hx1 : x < 1 := by linarith
  have hnew : neutralGreen ε x = 2 * ε / x := by
    simp only [neutralGreen, ite_eq_right (not_le.mpr h1)]
  have hold : neutralGreen (1 - ε) x = 2 * ε / (1 - x) := by
    simp only [neutralGreen, ite_eq_left h2.le]
    rw [show (1 : ℝ) - (1 - ε) = ε from by ring]
  have hε0 : ε ≠ 0 := hε.ne'
  have hx00 : x ≠ 0 := hx0.ne'
  have h1x : (1 : ℝ) - x ≠ 0 := (sub_pos.mpr hx1).ne'
  rw [hnew, hold]
  field_simp
  ring

/-- **Equation 17 rearranged.** For `y ∈ (0, 1)`, `(1 - y) M₁(y) + y M₂(y) = y`.
Patterson derives Equation 17 from this mixture (p. 1098: "This follows
immediately, since by Theorem 5 and Corollary 1: `(1 - y) M₁(y) + y M₂(y) = y`"),
solving for `M₂`; since `meanMrcaOld` is defined by Equation 17, the identity here
is immediate algebra and holds with `M₁` replaced by any function. The analytic
content of Theorem 5(2) is `killedGreen_weighted_integral_add_pattersonAux1`. -/
theorem meanMrca_mixture {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (1 - y) * meanMrcaNew y + y * meanMrcaOld y = y := by
  have hy0 : y ≠ 0 := hy.1.ne'
  simp only [meanMrcaOld]
  field_simp
  ring

/-- **Limit of `M₁` at frequency `1`** (Patterson p. 1094, item 6):
`M₁(y) → 2 (π² - 9) / 3` as `y → 1⁻`. The value `meanMrcaNew 1 = 2π² / 3 - 4`, from `x / 0 = 0`,
differs from this limit. -/
theorem tendsto_meanMrcaNew_one :
    Tendsto meanMrcaNew (𝓝[<] (1 : ℝ)) (𝓝 (2 * (π ^ 2 - 9) / 3)) := by
  have hlog : Tendsto (fun y => log y) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h : Tendsto log (𝓝[<] (1 : ℝ)) (𝓝 (log 1)) :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
        nhdsWithin_le_nhds
    simpa using h
  have hdiv : Tendsto (fun y => (2 * π ^ 2 - 12 * pattersonDilog y) / (3 * y))
      (𝓝[<] (1 : ℝ)) (𝓝 ((2 * π ^ 2 - 12 * 0) / (3 * 1))) := by
    refine Tendsto.div ?_ ?_ (by norm_num)
    · exact tendsto_const_nhds.sub
        (tendsto_const_nhds.mul tendsto_pattersonDilog_nhdsLT_one)
    · exact tendsto_const_nhds.mul
        ((continuous_id.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hlast : Tendsto (fun y => 2 * log y / (1 - y)) (𝓝[<] (1 : ℝ))
      (𝓝 (2 * -1)) := by
    have hh : Tendsto (fun y => (2 : ℝ) * (log y / (1 - y))) (𝓝[<] (1 : ℝ))
        (𝓝 (2 * -1)) :=
      tendsto_const_nhds.mul tendsto_log_div_one_sub_nhdsLT_one
    exact hh.congr (fun y => (mul_div_assoc _ _ _).symm)
  have key : Tendsto (fun y => -4 + 2 * log y +
        (2 * π ^ 2 - 12 * pattersonDilog y) / (3 * y) + 2 * log y / (1 - y))
      (𝓝[<] (1 : ℝ)) (𝓝 (-4 + 2 * 0 + (2 * π ^ 2 - 12 * 0) / (3 * 1) + 2 * -1)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul hlog)).add hdiv).add hlast
  have hval : (-4 + 2 * (0 : ℝ) + (2 * π ^ 2 - 12 * 0) / (3 * 1) + 2 * -1) =
      2 * (π ^ 2 - 9) / 3 := by ring
  rw [hval] at key
  exact key

private theorem hasDerivAt_one_div {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => 1 / x) (-1 / x ^ 2) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id' x) hx
  apply h.congr_deriv
  field_simp
  ring

/-- **The one-step computation behind Corollary 3** (Patterson p. 1100): Patterson's
Taylor step (Theorem 7) sends `f₀(x) = y / x²`, the input for a new allele, to `0` on `(0, 1)`,
for every real `y`. Hence every higher Taylor coefficient at `t = 0` vanishes in his Corollary 3;
the density conclusion there needs the killed density `C` and is not stated here. -/
theorem pattersonTaylorStep_new {y x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    pattersonTaylorStep (fun x => y / x ^ 2) x = 0 := by
  have h1 : ∀ z ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun x => x * (1 - x) * (y / x ^ 2) / 2) ((y / 2) * (-1 / z ^ 2)) z := by
    intro z hz
    have hbr := (hasDerivAt_pattersonAux2 hz.1.ne').const_mul (y / 2)
    refine hbr.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hz.1] with w hw
    change w * (1 - w) * (y / w ^ 2) / 2 = (y / 2) * ((1 - w) / w)
    have hw0 : w ≠ 0 := hw.ne'
    field_simp
  have hdd : deriv (deriv fun x => x * (1 - x) * (y / x ^ 2) / 2) x =
      (y / 2) * (2 / x ^ 3) :=
    deriv_deriv_eq_of_hasDerivAt isOpen_Ioo h1
      (fun z hz => (hasDerivAt_neg_one_div_sq hz.1.ne').const_mul _) hx
  change deriv (deriv fun x => x * (1 - x) * (y / x ^ 2) / 2) x - (y / x ^ 2) / x = 0
  rw [hdd]
  have hx0 : x ≠ 0 := hx.1.ne'
  field_simp
  ring

/-- **The one-step computation behind Corollary 4** (Patterson p. 1100): the Taylor
step sends `f₀(x) = y (1 - y) / (x² (1 - x))`, the input at unknown ancestry, to
`-f₀` on `(0, 1)`, for every real `y`. Iterating gives `fₙ = (-1)ⁿ f₀` in his Corollary 4; the
density conclusion there needs the killed density `C` and is not stated here. -/
theorem pattersonTaylorStep_unknown {y x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    pattersonTaylorStep (fun x => y * (1 - y) / (x ^ 2 * (1 - x))) x =
      -(y * (1 - y) / (x ^ 2 * (1 - x))) := by
  have h1 : ∀ z ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun x => x * (1 - x) * (y * (1 - y) / (x ^ 2 * (1 - x))) / 2)
        ((y * (1 - y) / 2) * (-1 / z ^ 2)) z := by
    intro z hz
    have hbr := (hasDerivAt_one_div hz.1.ne').const_mul (y * (1 - y) / 2)
    refine hbr.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hz.1, Iio_mem_nhds hz.2] with w hw0 hw1
    have hw00 : w ≠ 0 := hw0.ne'
    have hw11 : (1 : ℝ) - w ≠ 0 := (sub_pos.mpr hw1).ne'
    field_simp
  have hdd : deriv (deriv fun x => x * (1 - x) * (y * (1 - y) / (x ^ 2 * (1 - x))) / 2) x =
      (y * (1 - y) / 2) * (2 / x ^ 3) :=
    deriv_deriv_eq_of_hasDerivAt isOpen_Ioo h1
      (fun z hz => (hasDerivAt_neg_one_div_sq hz.1.ne').const_mul _) hx
  change deriv (deriv fun x => x * (1 - x) * (y * (1 - y) / (x ^ 2 * (1 - x))) / 2) x -
      (y * (1 - y) / (x ^ 2 * (1 - x))) / x = -(y * (1 - y) / (x ^ 2 * (1 - x)))
  rw [hdd]
  have hx0 : x ≠ 0 := hx.1.ne'
  have h1x : (1 : ℝ) - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  field_simp
  ring

/-- **Eigen-instance of Theorem 1, `k = 2`, `n = 0`.** With `w₀ = 1` (Table A1) and
eigenvalue `λ = 3`, `β(x) = x² (1 - x)` satisfies Appendix Equation A1,
`(1 - 3x) β(x) = x² (1 - x) / 2 * β''(x)`. The separated solution of Patterson's
Equation 4 is then `e^{-3t} β(x)`; the general spectral statement needs Jacobi
polynomial theory absent from Mathlib and is not formalized here. -/
theorem eigeninstance_two_zero (x : ℝ) :
    (1 - 3 * x) * (x ^ 2 * (1 - x)) =
      x ^ 2 * (1 - x) / 2 * deriv (deriv (fun x => x ^ 2 * (1 - x))) x := by
  have h : (fun x : ℝ => x ^ 2 * (1 - x)) = fun x => (X ^ 2 * (1 - X) : ℝ[X]).eval x := by
    funext y
    simp
  have hd1 : deriv (fun x : ℝ => x ^ 2 * (1 - x)) =
      fun x => (2 * X - 3 * X ^ 2 : ℝ[X]).eval x := by
    rw [h]
    funext y
    rw [Polynomial.deriv]
    simp
    ring
  rw [hd1]
  have hd2 : deriv (fun x => (2 * X - 3 * X ^ 2 : ℝ[X]).eval x) x = 2 - 6 * x := by
    rw [Polynomial.deriv]
    simp
    ring
  rw [hd2]
  ring

/-- **Eigen-instance of Theorem 1, `k = 2`, `n = 1`.** With `w₁ = 6x - 4` (Table A1)
and eigenvalue `λ = 6`, `β(x) = x² (1 - x) (6x - 4)` satisfies Equation A1. -/
theorem eigeninstance_two_one (x : ℝ) :
    (1 - 6 * x) * (x ^ 2 * (1 - x) * (6 * x - 4)) =
      x ^ 2 * (1 - x) / 2 * deriv (deriv (fun x => x ^ 2 * (1 - x) * (6 * x - 4))) x := by
  have h : (fun x : ℝ => x ^ 2 * (1 - x) * (6 * x - 4)) =
      fun x => (X ^ 2 * (1 - X) * (6 * X - 4) : ℝ[X]).eval x := by
    funext y
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_ofNat]
  have hd1 : deriv (fun x : ℝ => x ^ 2 * (1 - x) * (6 * x - 4)) =
      fun x => (-24 * X ^ 3 + 30 * X ^ 2 - 8 * X : ℝ[X]).eval x := by
    rw [h]
    funext y
    rw [Polynomial.deriv]
    simp
    ring
  rw [hd1]
  have hd2 : deriv (fun x => (-24 * X ^ 3 + 30 * X ^ 2 - 8 * X : ℝ[X]).eval x) x =
      -72 * x ^ 2 + 60 * x - 8 := by
    rw [Polynomial.deriv]
    simp
    ring
  rw [hd2]
  ring

/-- **Eigen-instance of Theorem 1, `k = 2`, `n = 2`.** With `w₂ = 28x² - 35x + 10`
(Table A1) and eigenvalue `λ = 10`, `β(x) = x² (1 - x) (28x² - 35x + 10)` satisfies
Equation A1. -/
theorem eigeninstance_two_two (x : ℝ) :
    (1 - 10 * x) * (x ^ 2 * (1 - x) * (28 * x ^ 2 - 35 * x + 10)) =
      x ^ 2 * (1 - x) / 2 *
        deriv (deriv (fun x => x ^ 2 * (1 - x) * (28 * x ^ 2 - 35 * x + 10))) x := by
  have h : (fun x : ℝ => x ^ 2 * (1 - x) * (28 * x ^ 2 - 35 * x + 10)) =
      fun x => (X ^ 2 * (1 - X) * (28 * X ^ 2 - 35 * X + 10) : ℝ[X]).eval x := by
    funext y
    simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_one, eval_ofNat]
  have hd1 : deriv (fun x : ℝ => x ^ 2 * (1 - x) * (28 * x ^ 2 - 35 * x + 10)) =
      fun x => (-140 * X ^ 4 + 252 * X ^ 3 - 135 * X ^ 2 + 20 * X : ℝ[X]).eval x := by
    rw [h]
    funext y
    rw [Polynomial.deriv]
    simp
    ring
  rw [hd1]
  have hd2 : deriv
      (fun x => (-140 * X ^ 4 + 252 * X ^ 3 - 135 * X ^ 2 + 20 * X : ℝ[X]).eval x) x =
      -560 * x ^ 3 + 756 * x ^ 2 - 270 * x + 20 := by
    rw [Polynomial.deriv]
    simp
    ring
  rw [hd2]
  ring

/-- `log (1 - t) / t → -1` as `t → 0⁺` (the slope of `log (1 - ·)` at `0`). -/
private theorem tendsto_log_one_sub_div_nhdsGT_zero :
    Tendsto (fun t => log (1 - t) / t) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
  have h0 : HasDerivAt (fun x => log (1 - x)) (-1) 0 :=
    (hasDerivAt_log_one_sub (by norm_num)).congr_deriv (by norm_num)
  refine (h0.tendsto_slope_zero_right).congr (fun t => ?_)
  simp only [zero_add, log_one, sub_zero, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

/-- `a₁(x) → 0` as `x → 0⁺` (Patterson's Equation A5, as a limit: the Lean value
`pattersonAux1 0` is the totalized `2`). -/
theorem tendsto_pattersonAux1_nhdsGT_zero :
    Tendsto pattersonAux1 (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hslope := tendsto_log_one_sub_div_nhdsGT_zero
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have key : Tendsto (fun x => 2 - x + 2 * ((1 - x) * log (1 - x) / x)) (𝓝[>] (0 : ℝ))
      (𝓝 (2 - 0 + 2 * ((1 - 0) * -1))) := by
    refine Tendsto.add (tendsto_const_nhds.sub hid) (tendsto_const_nhds.mul ?_)
    have hh : Tendsto (fun x => (1 - x) * (log (1 - x) / x)) (𝓝[>] (0 : ℝ))
        (𝓝 ((1 - 0) * -1)) :=
      (tendsto_const_nhds.sub hid).mul hslope
    exact hh.congr (fun x => (mul_div_assoc _ _ _).symm)
  have hval : (2 - (0 : ℝ) + 2 * ((1 - 0) * -1)) = 0 := by ring
  rw [hval] at key
  exact key

/-- `a₁(x) → 1` as `x → 1⁻`: the endpoint value of `pattersonAux1_one` (Equation
A6) is the limit from below, since `(1 - x) log (1 - x) → 0`. -/
theorem tendsto_pattersonAux1_nhdsLT_one :
    Tendsto pattersonAux1 (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  have hmul := tendsto_one_sub_mul_log_one_sub_nhdsLT_one
  have hid : Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    (continuous_id.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have key : Tendsto (fun x => 2 - x + 2 * ((1 - x) * log (1 - x) / x))
      (𝓝[<] (1 : ℝ)) (𝓝 (2 - 1 + 2 * (0 / 1))) :=
    (tendsto_const_nhds.sub hid).add
      (tendsto_const_nhds.mul (hmul.div hid one_ne_zero))
  have hval : (2 - (1 : ℝ) + 2 * (0 / 1)) = 1 := by norm_num
  rw [hval] at key
  exact key

/-- Boundary value of the killed Green's function at `x = 0`: for `y ∈ (0, 1)`,
`G_C(x, y) → 0` as `x → 0⁺`. -/
theorem tendsto_killedGreen_zero {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => killedGreen x y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hEv : (fun x => killedGreen x y) =ᶠ[𝓝[>] (0 : ℝ)]
      fun x => (2 / y ^ 2) * pattersonAux1 x := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hy.1)] with z hz1 hz2
    exact killedGreen_eq_aux_left hz2.le hz1.ne' hy.1.ne'
  have hT : Tendsto (fun x => (2 / y ^ 2) * pattersonAux1 x) (𝓝[>] (0 : ℝ))
      (𝓝 ((2 / y ^ 2) * 0)) :=
    tendsto_pattersonAux1_nhdsGT_zero.const_mul _
  rw [mul_zero] at hT
  exact hT.congr' hEv.symm

/-- Boundary value of the killed Green's function at `x = 1`: for `y ∈ (0, 1)`,
`G_C(x, y) → 0` as `x → 1⁻`. -/
theorem tendsto_killedGreen_one {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => killedGreen x y) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hEv : (fun x => killedGreen x y) =ᶠ[𝓝[<] (1 : ℝ)]
      fun x => (2 * pattersonAux1 y / ((1 - y) * y)) * pattersonAux2 x := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hy.2)] with z hz1 hz2
    exact killedGreen_eq_aux_right hz2 (hy.1.trans hz2).ne' hy.1.ne' (ne_of_lt hy.2)
  have hT : Tendsto
      (fun x => (2 * pattersonAux1 y / ((1 - y) * y)) * pattersonAux2 x)
      (𝓝[<] (1 : ℝ))
      (𝓝 ((2 * pattersonAux1 y / ((1 - y) * y)) * pattersonAux2 1)) :=
    ((hasDerivAt_pattersonAux2 one_ne_zero).continuousAt.const_mul _).continuousWithinAt
  rw [pattersonAux2_one, mul_zero] at hT
  exact hT.congr' hEv.symm

private theorem hasDerivAt_aux1PosAux {x : ℝ} (hx1 : x ≠ 1) :
    HasDerivAt (fun x => x * (2 - x) / (2 * (1 - x)) + log (1 - x))
      (x ^ 2 / (2 * (1 - x) ^ 2)) x := by
  have hnum : HasDerivAt (fun x : ℝ => x * (2 - x)) (2 - 2 * x) x := by
    have h := (hasDerivAt_id' x).mul ((hasDerivAt_const x (2 : ℝ)).sub (hasDerivAt_id' x))
    apply h.congr_deriv
    simp only [Pi.sub_apply]
    ring
  have hden : HasDerivAt (fun x : ℝ => 2 * (1 - x)) (-2) x := by
    have h := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)).const_mul (2 : ℝ)
    apply h.congr_deriv
    ring
  have h1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hdiv := hnum.div hden (mul_ne_zero two_ne_zero h1)
  have h := hdiv.add (hasDerivAt_log_one_sub hx1)
  apply h.congr_deriv
  field_simp
  ring

/-- The auxiliary function `φ(x) = x (2 - x) / (2 (1 - x)) + log (1 - x)` in the
factorization `pattersonAux1_eq_factor` is positive on `(0, 1)`: it vanishes at `0`
and its derivative `x² / (2 (1 - x)²)` is positive. -/
private theorem aux1PosAux_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < x * (2 - x) / (2 * (1 - x)) + log (1 - x) := by
  have hmono : StrictMonoOn (fun t => t * (2 - t) / (2 * (1 - t)) + log (1 - t))
      (Icc 0 x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 x) ?_ ?_
    · apply ContinuousOn.add
      · exact (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).div
          (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
          (fun t ht => mul_ne_zero two_ne_zero (sub_pos.mpr (ht.2.trans_lt hx.2)).ne')
      · exact Real.continuousOn_log.comp (continuousOn_const.sub continuousOn_id)
          (fun t ht => (sub_pos.mpr (ht.2.trans_lt hx.2)).ne')
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hasDerivAt_aux1PosAux (ne_of_lt (hz.2.trans hx.2))).deriv]
      exact div_pos (pow_pos hz.1 2)
        (mul_pos two_pos (pow_pos (sub_pos.mpr (hz.2.trans hx.2)) 2))
  have hφ0 : (0 : ℝ) * (2 - 0) / (2 * (1 - 0)) + log (1 - (0 : ℝ)) = 0 := by
    simp
  have h := hmono ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1
  simp only [hφ0] at h
  exact h

/-- Upper bound for the same auxiliary function: `φ(x) ≤ x³ / (2 (1 - x)²)` on
`(0, 1)`, from `φ(0) = 0` and `φ'(t) ≤ x² / (2 (1 - x)²)` on `[0, x]` (mean value
theorem). -/
private theorem aux1PosAux_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x * (2 - x) / (2 * (1 - x)) + log (1 - x) ≤ x ^ 3 / (2 * (1 - x) ^ 2) := by
  have hbound : ∀ t ∈ Icc (0 : ℝ) x, ‖t ^ 2 / (2 * (1 - t) ^ 2)‖ ≤
      x ^ 2 / (2 * (1 - x) ^ 2) := by
    intro t ht
    have ht1 : t < 1 := ht.2.trans_lt hx.2
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have htx : t ≤ x := ht.2
    have h1t : (0 : ℝ) < 1 - t := sub_pos.mpr ht1
    have h1x : (0 : ℝ) < 1 - x := sub_pos.mpr hx.2
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
  have hmvt := (convex_Icc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (ht : t ∈ Icc (0 : ℝ) x) =>
      (hasDerivAt_aux1PosAux (ne_of_lt (ht.2.trans_lt hx.2))).hasDerivWithinAt)
    hbound ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩
  have hφ0 : (0 : ℝ) * (2 - 0) / (2 * (1 - 0)) + log (1 - (0 : ℝ)) = 0 := by
    simp
  simp only [hφ0] at hmvt
  simp only [sub_zero] at hmvt
  refine (le_norm_self _).trans (hmvt.trans_eq ?_)
  rw [Real.norm_of_nonneg hx.1.le]
  ring

/-- Factorization of `a₁` through the auxiliary function `φ` of
`aux1PosAux_pos`: `a₁(x) = (2 (1 - x) / x) φ(x)` on `(0, 1)`. -/
private theorem pattersonAux1_eq_factor {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    pattersonAux1 x =
      (2 * (1 - x) / x) * (x * (2 - x) / (2 * (1 - x)) + log (1 - x)) := by
  unfold pattersonAux1
  have hx0 : x ≠ 0 := hx.1.ne'
  have h1 : (1 : ℝ) - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  field_simp

/-- Bounds for `a₁(x) / (x (1 - x))` and `a₁(x) / x` on `(0, 1)`, from
`pattersonAux1_eq_factor` and `aux1PosAux_le`; these give the integrability of
`G_C(x, y) / (x (1 - x))` and `G_C(x, y) / x` near `x = 0`. -/
private theorem pattersonAux1_div_bounds {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    pattersonAux1 z / (z * (1 - z)) ≤ z / (1 - z) ^ 2 ∧
      pattersonAux1 z / z ≤ z / (1 - z) := by
  have hz0 : z ≠ 0 := hz.1.ne'
  have h1z : (1 : ℝ) - z ≠ 0 := (sub_pos.mpr hz.2).ne'
  have hφnonneg : (0 : ℝ) ≤ z * (2 - z) / (2 * (1 - z)) + log (1 - z) :=
    (aux1PosAux_pos hz).le
  have h1 : pattersonAux1 z / (z * (1 - z)) =
      2 * (z * (2 - z) / (2 * (1 - z)) + log (1 - z)) / z ^ 2 := by
    rw [pattersonAux1_eq_factor hz]
    field_simp
  have h2 : pattersonAux1 z / z =
      2 * (1 - z) * (z * (2 - z) / (2 * (1 - z)) + log (1 - z)) / z ^ 2 := by
    rw [pattersonAux1_eq_factor hz]
    field_simp
  constructor
  · rw [h1]
    have hmul : 2 * (z * (2 - z) / (2 * (1 - z)) + log (1 - z)) ≤
        2 * (z ^ 3 / (2 * (1 - z) ^ 2)) :=
      mul_le_mul_of_nonneg_left (aux1PosAux_le hz) (by norm_num)
    have hdiv : 2 * (z * (2 - z) / (2 * (1 - z)) + log (1 - z)) / z ^ 2 ≤
        2 * (z ^ 3 / (2 * (1 - z) ^ 2)) / z ^ 2 := by
      gcongr
    exact hdiv.trans_eq (by field_simp)
  · rw [h2]
    have hcoef : (0 : ℝ) ≤ 2 * (1 - z) := by
      have : (0 : ℝ) < 1 - z := sub_pos.mpr hz.2
      positivity
    have hmul : 2 * (1 - z) * (z * (2 - z) / (2 * (1 - z)) + log (1 - z)) ≤
        2 * (1 - z) * (z ^ 3 / (2 * (1 - z) ^ 2)) :=
      mul_le_mul_of_nonneg_left (aux1PosAux_le hz) hcoef
    have hdiv : 2 * (1 - z) * (z * (2 - z) / (2 * (1 - z)) + log (1 - z)) / z ^ 2 ≤
        2 * (1 - z) * (z ^ 3 / (2 * (1 - z) ^ 2)) / z ^ 2 := by
      gcongr
    exact hdiv.trans_eq (by field_simp)

/-- `a₁` is positive on `(0, 1)`, by `pattersonAux1_eq_factor` and
`aux1PosAux_pos`. -/
theorem pattersonAux1_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < pattersonAux1 x := by
  rw [pattersonAux1_eq_factor hx]
  exact mul_pos (div_pos (mul_pos two_pos (sub_pos.mpr hx.2)) hx.1)
    (aux1PosAux_pos hx)

/-- The killed Green's function is positive on `(0, 1) × (0, 1)`, as a Green's
function of the killed diffusion must be. -/
theorem killedGreen_pos {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 < killedGreen x y := by
  by_cases h : x ≤ y
  · rw [killedGreen_eq_aux_left h hx.1.ne' hy.1.ne']
    exact mul_pos (div_pos two_pos (pow_pos hy.1 2)) (pattersonAux1_pos hx)
  · have h' : y < x := not_le.mp h
    rw [killedGreen_eq_aux_right h' hx.1.ne' hy.1.ne' (ne_of_lt hy.2)]
    apply mul_pos
    · exact div_pos (mul_pos two_pos (pattersonAux1_pos hy))
        (mul_pos (sub_pos.mpr hy.2) hy.1)
    · change 0 < (1 - x) / x
      exact div_pos (sub_pos.mpr hx.2) hx.1

/-- The boundary ratio in the integrated form of Patterson's Equation 14: for `y ∈ (0, 1)`,
`G_C(1 - ε, y) / (2ε) → a₁(y) / ((1 - y) y)` as `ε → 0⁺`, the contribution of an
allele that was fixed, since for `0 < ε < 1 - y` (so that `1 - ε > y` lies on the upper branch)
`G_C(1 - ε, y) = (2 a₁(y) / ((1 - y) y)) a₂(1 - ε)` and `a₂(1 - ε) = ε / (1 - ε)`. -/
theorem tendsto_killedGreen_one_sub_div {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => killedGreen (1 - ε) y / (2 * ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (pattersonAux1 y / ((1 - y) * y))) := by
  have hy0 : y ≠ 0 := hy.1.ne'
  have h1y : (1 : ℝ) - y ≠ 0 := (sub_pos.mpr hy.2).ne'
  have hEv : (fun ε => killedGreen (1 - ε) y / (2 * ε)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => pattersonAux1 y / ((1 - y) * y * (1 - ε)) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (sub_pos.mpr hy.2))]
      with ε hεpos hεlt
    have hε0 : ε ≠ 0 := hεpos.ne'
    have hε1 : ε < 1 := hεlt.trans (sub_lt_self 1 hy.1)
    have h1ε : (1 : ℝ) - ε ≠ 0 := (sub_pos.mpr hε1).ne'
    have hgt : y < 1 - ε := by linarith [hεlt]
    rw [killedGreen_eq_aux_right hgt h1ε hy.1.ne' (ne_of_lt hy.2)]
    change ((2 * pattersonAux1 y / ((1 - y) * y)) * ((1 - (1 - ε)) / (1 - ε))) /
        (2 * ε) = pattersonAux1 y / ((1 - y) * y * (1 - ε))
    field_simp
    ring
  have hid0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hT : Tendsto (fun ε => pattersonAux1 y / ((1 - y) * y * (1 - ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (pattersonAux1 y / ((1 - y) * y * (1 - 0)))) := by
    refine tendsto_const_nhds.div (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub hid0)) ?_
    simp only [sub_zero]
    exact mul_ne_zero (mul_ne_zero h1y hy0) one_ne_zero
  have hval : pattersonAux1 y / ((1 - y) * y * (1 - (0 : ℝ))) =
      pattersonAux1 y / ((1 - y) * y) := by simp
  rw [hval] at hT
  exact hT.congr' hEv.symm

private theorem measurable_pattersonAux1 : Measurable pattersonAux1 := by
  unfold pattersonAux1
  exact (measurable_const.sub measurable_id).add
    (measurable_const.mul (((measurable_const.sub measurable_id).mul
      (Real.measurable_log.comp (measurable_const.sub measurable_id))).div
        measurable_id))

/-- Antiderivative below the diagonal for the weighted integral:
`d/dx [(x - 2) log (1 - x) / x] = a₁(x) / (x (1 - x))`. -/
private theorem hasDerivAt_antideriv_aux1_div {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (fun x => (x - 2) * log (1 - x) / x)
      (pattersonAux1 x / (x * (1 - x))) x := by
  have h1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hnum : HasDerivAt (fun x => (x - 2) * log (1 - x))
      (1 * log (1 - x) + (x - 2) * (-(1 - x)⁻¹)) x :=
    ((hasDerivAt_id' x).sub_const (2 : ℝ)).mul (hasDerivAt_log_one_sub hx1)
  have h := hnum.div (hasDerivAt_id' x) hx0
  apply h.congr_deriv
  simp only [pattersonAux1]
  field_simp
  ring

/-- The antiderivative `(x - 2) log (1 - x) / x` tends to `2` at `0⁺`. -/
private theorem tendsto_antideriv_aux1_div_zero :
    Tendsto (fun x => (x - 2) * log (1 - x) / x) (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  have hid0 : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have key : Tendsto (fun x => (x - 2) * (log (1 - x) / x)) (𝓝[>] (0 : ℝ))
      (𝓝 ((0 - 2) * -1)) :=
    (hid0.sub tendsto_const_nhds).mul tendsto_log_one_sub_div_nhdsGT_zero
  have hval : ((0 : ℝ) - 2) * -1 = 2 := by ring
  rw [hval] at key
  exact key.congr (fun x => (mul_div_assoc _ _ _).symm)

/-- The derivative of `-(C / x)` is `C / x²`: the antiderivative above the diagonal
for the weighted integral. -/
private theorem hasDerivAt_neg_const_div {C x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => -(C / x)) (C / x ^ 2) x := by
  have h := ((hasDerivAt_const x C).div (hasDerivAt_id' x) hx).neg
  apply h.congr_deriv
  field_simp
  ring

/-- Integrability of `(2 / y²) a₁(x) / (x (1 - x))` on `[0, y]`, from the bound
`pattersonAux1_div_bounds`. -/
private theorem intervalIntegrable_aux1_div_mul {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (2 / y ^ 2) * (pattersonAux1 x / (x * (1 - x))))
      MeasureTheory.volume 0 y := by
  have h1y : (0 : ℝ) < 1 - y := sub_pos.mpr hy.2
  have hy0' : (0 : ℝ) ≤ y := hy.1.le
  have hC0 : (0 : ℝ) ≤ (2 / y ^ 2) * (y / (1 - y) ^ 2) := by positivity
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) y,
      ‖(2 / y ^ 2) * (pattersonAux1 t / (t * (1 - t)))‖ ≤
        (2 / y ^ 2) * (y / (1 - y) ^ 2) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · have hz : pattersonAux1 0 / ((0 : ℝ) * (1 - 0)) = 0 := by simp
      rw [hz]
      simpa using hC0
    · have htIoo : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht.2.trans_lt hy.2⟩
      have hnn : (0 : ℝ) ≤ (2 / y ^ 2) * (pattersonAux1 t / (t * (1 - t))) :=
        mul_nonneg (by positivity)
          (div_nonneg (pattersonAux1_pos htIoo).le
            (mul_pos ht0 (sub_pos.mpr htIoo.2)).le)
      rw [Real.norm_of_nonneg hnn]
      have step1 : (2 / y ^ 2) * (pattersonAux1 t / (t * (1 - t))) ≤
          (2 / y ^ 2) * (t / (1 - t) ^ 2) :=
        mul_le_mul_of_nonneg_left (pattersonAux1_div_bounds htIoo).1 (by positivity)
      have step2 : (2 / y ^ 2) * (t / (1 - t) ^ 2) ≤
          (2 / y ^ 2) * (y / (1 - y) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hty : t ≤ y := ht.2
        have ht0' : (0 : ℝ) ≤ t := ht0.le
        have hle : (1 : ℝ) - y ≤ 1 - t := by linarith [hty]
        have h1t : (0 : ℝ) < 1 - t := sub_pos.mpr htIoo.2
        gcongr
      exact step1.trans step2
  have hmeas : Measurable
      (fun x => (2 / y ^ 2) * (pattersonAux1 x / (x * (1 - x)))) :=
    (measurable_pattersonAux1.div
      (measurable_id.mul (measurable_const.sub measurable_id))).const_mul _
  have key : ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Icc (0 : ℝ) y →
      MeasureTheory.volume s < ⊤ → MeasureTheory.IntegrableOn
        (fun x => (2 / y ^ 2) * (pattersonAux1 x / (x * (1 - x))))
        s MeasureTheory.volume := by
    intro s hsmeas hs hsfin
    refine MeasureTheory.IntegrableOn.of_bound hsfin hmeas.aestronglyMeasurable
      ((2 / y ^ 2) * (y / (1 - y) ^ 2)) ?_
    rw [MeasureTheory.ae_restrict_iff' hsmeas]
    exact Filter.Eventually.of_forall fun t ht => hbound t (hs ht)
  refine ⟨key (Set.Ioc 0 y) measurableSet_Ioc ?_ ?_,
    key (Set.Ioc y 0) measurableSet_Ioc ?_ ?_⟩
  · intro t ht
    exact ⟨ht.1.le, ht.2⟩
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · intro t ht
    exact absurd (ht.1.trans_le ht.2) (not_lt.mpr hy.1.le)
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top

/-- **Patterson's Theorem 5(2), analytic content.** For `y ∈ (0, 1)`,
`y (1 - y) ∫₀¹ G_C(x, y) / (x (1 - x)) dx + a₁(y) = y`. Integrating Patterson's
Equation 14 over `t` writes the expected MRCA age at unknown ancestry as
`y (1 - y) [∫₀¹ G_C(x, y) / (x (1 - x)) dx + lim_{ε → 0⁺} G_C(1 - ε, y) / (2ε)]`,
and by `tendsto_killedGreen_one_sub_div` the second summand contributes `a₁(y)`
after multiplication by `y (1 - y)`; so this identity is his conclusion that the
expected age is `y` in scaled time (`2Ny` generations), proved here from
Theorem 4's explicit Green function. His own proof of Theorem 5(2) is a martingale
argument (Lemma 1), not formalized. -/
theorem killedGreen_weighted_integral_add_pattersonAux1 {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    y * (1 - y) * (∫ x in (0 : ℝ)..1, killedGreen x y / (x * (1 - x))) +
      pattersonAux1 y = y := by
  have hy0 : y ≠ 0 := hy.1.ne'
  have h1y : (1 : ℝ) - y ≠ 0 := (sub_pos.mpr hy.2).ne'
  have hFderiv : ∀ x ∈ Ioo (0 : ℝ) y,
      HasDerivAt (fun x => (2 / y ^ 2) * ((x - 2) * log (1 - x) / x))
        ((2 / y ^ 2) * (pattersonAux1 x / (x * (1 - x)))) x :=
    fun x hx => (hasDerivAt_antideriv_aux1_div hx.1.ne'
      (ne_of_lt (hx.2.trans hy.2))).const_mul _
  have hFa : Tendsto (fun x => (2 / y ^ 2) * ((x - 2) * log (1 - x) / x))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 / y ^ 2) * 2)) :=
    tendsto_antideriv_aux1_div_zero.const_mul _
  have hFb : Tendsto (fun x => (2 / y ^ 2) * ((x - 2) * log (1 - x) / x))
      (𝓝[<] y) (𝓝 ((2 / y ^ 2) * ((y - 2) * log (1 - y) / y))) :=
    ((hasDerivAt_antideriv_aux1_div hy.1.ne'
      (ne_of_lt hy.2)).const_mul _).continuousAt.continuousWithinAt
  have hint1 := intervalIntegrable_aux1_div_mul hy
  have hbelowF : (∫ x in (0 : ℝ)..y, (2 / y ^ 2) * (pattersonAux1 x / (x * (1 - x)))) =
      (2 / y ^ 2) * ((y - 2) * log (1 - y) / y) - (2 / y ^ 2) * 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hy.1 hFderiv hint1
      hFa hFb
  have hEqBelow : Set.EqOn (fun x => killedGreen x y / (x * (1 - x)))
      (fun x => (2 / y ^ 2) * (pattersonAux1 x / (x * (1 - x)))) (Set.uIoo 0 y) := by
    rw [Set.uIoo_of_le hy.1.le]
    intro z hz
    change killedGreen z y / (z * (1 - z)) =
      (2 / y ^ 2) * (pattersonAux1 z / (z * (1 - z)))
    rw [killedGreen_eq_aux_left hz.2.le hz.1.ne' hy.1.ne', mul_div_assoc]
  have hbelow : (∫ x in (0 : ℝ)..y, killedGreen x y / (x * (1 - x))) =
      (2 / y ^ 2) * ((y - 2) * log (1 - y) / y) - (2 / y ^ 2) * 2 := by
    rw [intervalIntegral.integral_congr_uIoo hEqBelow]
    exact hbelowF
  have hintBelow : IntervalIntegrable (fun x => killedGreen x y / (x * (1 - x)))
      MeasureTheory.volume 0 y :=
    hint1.congr_uIoo hEqBelow.symm
  have hGcont : ContinuousOn (fun x => (2 * pattersonAux1 y / ((1 - y) * y)) / x ^ 2)
      (Set.uIcc y 1) := by
    rw [Set.uIcc_of_le hy.2.le]
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt (hy.1.trans_le hz.1)))
  have hintG : IntervalIntegrable
      (fun x => (2 * pattersonAux1 y / ((1 - y) * y)) / x ^ 2)
      MeasureTheory.volume y 1 :=
    hGcont.intervalIntegrable
  have haboveG : (∫ x in y..(1 : ℝ), (2 * pattersonAux1 y / ((1 - y) * y)) / x ^ 2) =
      (-((2 * pattersonAux1 y / ((1 - y) * y)) / 1)) -
        (-((2 * pattersonAux1 y / ((1 - y) * y)) / y)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := y) (b := 1)
      (fun z hz => by
        rw [Set.uIcc_of_le hy.2.le] at hz
        exact hasDerivAt_neg_const_div (ne_of_gt (hy.1.trans_le hz.1))) hintG
  have hEqAbove : Set.EqOn (fun x => killedGreen x y / (x * (1 - x)))
      (fun x => (2 * pattersonAux1 y / ((1 - y) * y)) / x ^ 2) (Set.uIoo y 1) := by
    rw [Set.uIoo_of_le hy.2.le]
    intro z hz
    have hz0 : z ≠ 0 := (hy.1.trans hz.1).ne'
    have h1z : (1 : ℝ) - z ≠ 0 := (sub_pos.mpr hz.2).ne'
    change killedGreen z y / (z * (1 - z)) =
      (2 * pattersonAux1 y / ((1 - y) * y)) / z ^ 2
    rw [killedGreen_eq_aux_right hz.1 hz0 hy.1.ne' (ne_of_lt hy.2)]
    change ((2 * pattersonAux1 y / ((1 - y) * y)) * ((1 - z) / z)) / (z * (1 - z)) =
      (2 * pattersonAux1 y / ((1 - y) * y)) / z ^ 2
    field_simp
  have habove : (∫ x in y..(1 : ℝ), killedGreen x y / (x * (1 - x))) =
      (-((2 * pattersonAux1 y / ((1 - y) * y)) / 1)) -
        (-((2 * pattersonAux1 y / ((1 - y) * y)) / y)) := by
    rw [intervalIntegral.integral_congr_uIoo hEqAbove]
    exact haboveG
  have hintAbove : IntervalIntegrable (fun x => killedGreen x y / (x * (1 - x)))
      MeasureTheory.volume y 1 :=
    hintG.congr_uIoo hEqAbove.symm
  have htotal : (∫ x in (0 : ℝ)..1, killedGreen x y / (x * (1 - x))) =
      (∫ x in (0 : ℝ)..y, killedGreen x y / (x * (1 - x))) +
        (∫ x in y..(1 : ℝ), killedGreen x y / (x * (1 - x))) :=
    (intervalIntegral.integral_add_adjacent_intervals hintBelow hintAbove).symm
  rw [htotal, hbelow, habove]
  simp only [pattersonAux1]
  field_simp
  ring

/-- Antiderivative below the diagonal for `a₁(x) / x`:
`F(x) = -x - 2 (1 - x) log (1 - x) / x + 2 dilog (1 - x)` satisfies
`F'(x) = a₁(x) / x` on `(0, 1)`. -/
private theorem hasDerivAt_antideriv_aux1 {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => -x - 2 * ((1 - x) * log (1 - x) / x) +
      2 * pattersonDilog (1 - x)) (pattersonAux1 x / x) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have h1x : (1 : ℝ) - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1) x := (hasDerivAt_id' x).neg
  have hfrac : HasDerivAt (fun x => 2 * ((1 - x) * log (1 - x) / x))
      (2 * (-(log (1 - x) + x) / x ^ 2)) x :=
    (hasDerivAt_pattersonAux1_frac hx0 (ne_of_lt hx.2)).const_mul 2
  have hdil : HasDerivAt (fun x => 2 * pattersonDilog (1 - x))
      (2 * (-(log (1 - x) / x))) x :=
    (hasDerivAt_pattersonDilog_one_sub hx).const_mul 2
  refine ((hneg.sub hfrac).add hdil).congr_deriv ?_
  simp only [pattersonAux1]
  field_simp
  ring

/-- The antiderivative `F` of `hasDerivAt_antideriv_aux1` tends to `2` at `0⁺`. -/
private theorem tendsto_antideriv_aux1_zero :
    Tendsto (fun x => -x - 2 * ((1 - x) * log (1 - x) / x) +
      2 * pattersonDilog (1 - x)) (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  have hid0 : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hfrac : Tendsto (fun x => 2 * ((1 - x) * log (1 - x) / x)) (𝓝[>] (0 : ℝ))
      (𝓝 (-2 : ℝ)) := by
    have hh : Tendsto (fun x => (1 - x) * (log (1 - x) / x)) (𝓝[>] (0 : ℝ))
        (𝓝 (-1 : ℝ)) := by
      have hmul : Tendsto (fun x => (1 - x) * (log (1 - x) / x)) (𝓝[>] (0 : ℝ))
          (𝓝 (((1 : ℝ) - 0) * -1)) :=
        (tendsto_const_nhds.sub hid0).mul tendsto_log_one_sub_div_nhdsGT_zero
      simpa using hmul
    have h2 : Tendsto (fun x => 2 * ((1 - x) * (log (1 - x) / x)))
        (𝓝[>] (0 : ℝ)) (𝓝 (-2 : ℝ)) := by
      simpa using hh.const_mul (2 : ℝ)
    refine h2.congr (fun x => ?_)
    rw [mul_div_assoc]
  have hdil : Tendsto (fun x => 2 * pattersonDilog (1 - x)) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    have hmap : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h : Tendsto (fun x : ℝ => (1 : ℝ) - x) (𝓝[>] (0 : ℝ))
            (𝓝 ((1 : ℝ) - 0)) :=
          ((continuous_const.sub continuous_id).tendsto (0 : ℝ)).mono_left
            nhdsWithin_le_nhds
        simpa using h
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact sub_lt_self 1 hx
    have hcomp := tendsto_pattersonDilog_nhdsLT_one.comp hmap
    simpa using hcomp.const_mul (2 : ℝ)
  have key := (hid0.neg.sub hfrac).add hdil
  simpa using key

/-- Integrability of `(2 / y²) a₁(x) / x` on `[0, y]`, from the bound
`pattersonAux1_div_bounds`. -/
private theorem intervalIntegrable_aux1_div_self_mul {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (2 / y ^ 2) * (pattersonAux1 x / x))
      MeasureTheory.volume 0 y := by
  have h1y : (0 : ℝ) < 1 - y := sub_pos.mpr hy.2
  have hy0' : (0 : ℝ) ≤ y := hy.1.le
  have hC0 : (0 : ℝ) ≤ (2 / y ^ 2) * (y / (1 - y)) := by positivity
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) y,
      ‖(2 / y ^ 2) * (pattersonAux1 t / t)‖ ≤ (2 / y ^ 2) * (y / (1 - y)) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · have hz : pattersonAux1 0 / (0 : ℝ) = 0 := by simp
      rw [hz]
      simpa using hC0
    · have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0, ht.2.trans_lt hy.2⟩
      have hnn : (0 : ℝ) ≤ (2 / y ^ 2) * (pattersonAux1 t / t) :=
        mul_nonneg (by positivity)
          (div_nonneg (pattersonAux1_pos htIoo).le ht0.le)
      rw [Real.norm_of_nonneg hnn]
      have step1 : (2 / y ^ 2) * (pattersonAux1 t / t) ≤
          (2 / y ^ 2) * (t / (1 - t)) :=
        mul_le_mul_of_nonneg_left (pattersonAux1_div_bounds htIoo).2 (by positivity)
      have step2 : (2 / y ^ 2) * (t / (1 - t)) ≤ (2 / y ^ 2) * (y / (1 - y)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hty : t ≤ y := ht.2
        have ht0' : (0 : ℝ) ≤ t := ht0.le
        have hle : (1 : ℝ) - y ≤ 1 - t := by linarith [hty]
        have h1t : (0 : ℝ) < 1 - t := sub_pos.mpr htIoo.2
        gcongr
      exact step1.trans step2
  have hmeas : Measurable (fun x => (2 / y ^ 2) * (pattersonAux1 x / x)) :=
    (measurable_pattersonAux1.div measurable_id).const_mul _
  have key : ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Icc (0 : ℝ) y →
      MeasureTheory.volume s < ⊤ → MeasureTheory.IntegrableOn
        (fun x => (2 / y ^ 2) * (pattersonAux1 x / x)) s MeasureTheory.volume := by
    intro s hsmeas hs hsfin
    refine MeasureTheory.IntegrableOn.of_bound hsfin hmeas.aestronglyMeasurable
      ((2 / y ^ 2) * (y / (1 - y))) ?_
    rw [MeasureTheory.ae_restrict_iff' hsmeas]
    exact Filter.Eventually.of_forall fun t ht => hbound t (hs ht)
  refine ⟨key (Set.Ioc 0 y) measurableSet_Ioc ?_ ?_,
    key (Set.Ioc y 0) measurableSet_Ioc ?_ ?_⟩
  · intro t ht
    exact ⟨ht.1.le, ht.2⟩
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · intro t ht
    exact absurd (ht.1.trans_le ht.2) (not_lt.mpr hy.1.le)
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top

/-- **Patterson's Equation 16 derived from Theorem 4**: for `y ∈ (0, 1)`,
`M₁(y) = y ∫₀¹ G_C(x, y) / x dx`. The integral representation is Patterson's
(p. 1103); the closed form `meanMrcaNew` is obtained from it by the two
antiderivatives `hasDerivAt_antideriv_aux1` (below the diagonal) and
`-C / x - C log x` with `C = 2 a₁(y) / ((1 - y) y)` (above), the reflection
formula `pattersonDilog_reflection`, and `pattersonDilog_zero`. In the diffusion
reading, the right side is `∫₀^∞ B(t) dt` for his Equation 15; the weight `y / x`
is the new-allele frequency density of Theorem 3 (here `neutralGreen`): it equals
`G_K(ε, x) / G_K(ε, y) = (2ε / x) / (2ε / y)` once `ε < min x y`, and the
coalescence rate `1 / x` acts through the killing in `G_C`. -/
theorem meanMrcaNew_eq_integral {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    meanMrcaNew y = y * ∫ x in (0 : ℝ)..1, killedGreen x y / x := by
  have hy0 : y ≠ 0 := hy.1.ne'
  have h1y : (1 : ℝ) - y ≠ 0 := (sub_pos.mpr hy.2).ne'
  have hFderiv : ∀ x ∈ Set.Ioo (0 : ℝ) y,
      HasDerivAt (fun x => (2 / y ^ 2) * (-x - 2 * ((1 - x) * log (1 - x) / x) +
        2 * pattersonDilog (1 - x))) ((2 / y ^ 2) * (pattersonAux1 x / x)) x :=
    fun x hx => (hasDerivAt_antideriv_aux1 ⟨hx.1, hx.2.trans hy.2⟩).const_mul _
  have hFa : Tendsto (fun x => (2 / y ^ 2) * (-x - 2 * ((1 - x) * log (1 - x) / x) +
      2 * pattersonDilog (1 - x))) (𝓝[>] (0 : ℝ)) (𝓝 ((2 / y ^ 2) * 2)) :=
    tendsto_antideriv_aux1_zero.const_mul _
  have hFb : Tendsto (fun x => (2 / y ^ 2) * (-x - 2 * ((1 - x) * log (1 - x) / x) +
      2 * pattersonDilog (1 - x))) (𝓝[<] y)
      (𝓝 ((2 / y ^ 2) * (-y - 2 * ((1 - y) * log (1 - y) / y) +
        2 * pattersonDilog (1 - y)))) :=
    ((hasDerivAt_antideriv_aux1 hy).const_mul _).continuousAt.continuousWithinAt
  have hint1 := intervalIntegrable_aux1_div_self_mul hy
  have hbelowF : (∫ x in (0 : ℝ)..y, (2 / y ^ 2) * (pattersonAux1 x / x)) =
      (2 / y ^ 2) * (-y - 2 * ((1 - y) * log (1 - y) / y) +
        2 * pattersonDilog (1 - y)) - (2 / y ^ 2) * 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hy.1 hFderiv hint1
      hFa hFb
  have hEqBelow : Set.EqOn (fun x => killedGreen x y / x)
      (fun x => (2 / y ^ 2) * (pattersonAux1 x / x)) (Set.uIoo 0 y) := by
    rw [Set.uIoo_of_le hy.1.le]
    intro z hz
    change killedGreen z y / z = (2 / y ^ 2) * (pattersonAux1 z / z)
    rw [killedGreen_eq_aux_left hz.2.le hz.1.ne' hy.1.ne', mul_div_assoc]
  have hbelow : (∫ x in (0 : ℝ)..y, killedGreen x y / x) =
      (2 / y ^ 2) * (-y - 2 * ((1 - y) * log (1 - y) / y) +
        2 * pattersonDilog (1 - y)) - (2 / y ^ 2) * 2 := by
    rw [intervalIntegral.integral_congr_uIoo hEqBelow]
    exact hbelowF
  have hintBelow : IntervalIntegrable (fun x => killedGreen x y / x)
      MeasureTheory.volume 0 y :=
    hint1.congr_uIoo hEqBelow.symm
  have hGcont : ContinuousOn
      (fun x => (2 * pattersonAux1 y / ((1 - y) * y)) * (1 - x) / x ^ 2)
      (Set.uIcc y 1) := by
    rw [Set.uIcc_of_le hy.2.le]
    exact (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).div
      (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt (hy.1.trans_le hz.1)))
  have hintG : IntervalIntegrable
      (fun x => (2 * pattersonAux1 y / ((1 - y) * y)) * (1 - x) / x ^ 2)
      MeasureTheory.volume y 1 :=
    hGcont.intervalIntegrable
  have haboveG : (∫ x in y..(1 : ℝ),
        (2 * pattersonAux1 y / ((1 - y) * y)) * (1 - x) / x ^ 2) =
      (-((2 * pattersonAux1 y / ((1 - y) * y)) / 1) -
          (2 * pattersonAux1 y / ((1 - y) * y)) * log 1) -
        (-((2 * pattersonAux1 y / ((1 - y) * y)) / y) -
          (2 * pattersonAux1 y / ((1 - y) * y)) * log y) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := y) (b := 1)
      (f := fun x => -((2 * pattersonAux1 y / ((1 - y) * y)) / x) -
        (2 * pattersonAux1 y / ((1 - y) * y)) * log x)
      (f' := fun x => (2 * pattersonAux1 y / ((1 - y) * y)) * (1 - x) / x ^ 2)
      (fun z hz => by
        rw [Set.uIcc_of_le hy.2.le] at hz
        have hz0 : z ≠ 0 := (hy.1.trans_le hz.1).ne'
        refine ((hasDerivAt_neg_const_div
          (C := 2 * pattersonAux1 y / ((1 - y) * y)) hz0).sub
          ((Real.hasDerivAt_log hz0).const_mul
            (2 * pattersonAux1 y / ((1 - y) * y)))).congr_deriv ?_
        field_simp) hintG
  have hEqAbove : Set.EqOn (fun x => killedGreen x y / x)
      (fun x => (2 * pattersonAux1 y / ((1 - y) * y)) * (1 - x) / x ^ 2)
      (Set.uIoo y 1) := by
    rw [Set.uIoo_of_le hy.2.le]
    intro z hz
    have hz0 : z ≠ 0 := (hy.1.trans hz.1).ne'
    have h1z : (1 : ℝ) - z ≠ 0 := (sub_pos.mpr hz.2).ne'
    change killedGreen z y / z =
      (2 * pattersonAux1 y / ((1 - y) * y)) * (1 - z) / z ^ 2
    rw [killedGreen_eq_aux_right hz.1 hz0 hy.1.ne' (ne_of_lt hy.2)]
    change ((2 * pattersonAux1 y / ((1 - y) * y)) * ((1 - z) / z)) / z =
      (2 * pattersonAux1 y / ((1 - y) * y)) * (1 - z) / z ^ 2
    field_simp
  have habove : (∫ x in y..(1 : ℝ), killedGreen x y / x) =
      (-((2 * pattersonAux1 y / ((1 - y) * y)) / 1) -
          (2 * pattersonAux1 y / ((1 - y) * y)) * log 1) -
        (-((2 * pattersonAux1 y / ((1 - y) * y)) / y) -
          (2 * pattersonAux1 y / ((1 - y) * y)) * log y) := by
    rw [intervalIntegral.integral_congr_uIoo hEqAbove]
    exact haboveG
  have hintAbove : IntervalIntegrable (fun x => killedGreen x y / x)
      MeasureTheory.volume y 1 :=
    hintG.congr_uIoo hEqAbove.symm
  have htotal : (∫ x in (0 : ℝ)..1, killedGreen x y / x) =
      (∫ x in (0 : ℝ)..y, killedGreen x y / x) +
        (∫ x in y..(1 : ℝ), killedGreen x y / x) :=
    (intervalIntegral.integral_add_adjacent_intervals hintBelow hintAbove).symm
  have hd : pattersonDilog (1 - y) =
      π ^ 2 / 6 - pattersonDilog y - log y * log (1 - y) := by
    have hrefl := pattersonDilog_reflection hy
    linarith [hrefl]
  rw [htotal, hbelow, habove, hd]
  unfold meanMrcaNew
  simp only [pattersonAux1, log_one, mul_zero, sub_zero, div_one]
  field_simp
  ring

end Domains.Biology.PopulationGenetics.Diffusion
