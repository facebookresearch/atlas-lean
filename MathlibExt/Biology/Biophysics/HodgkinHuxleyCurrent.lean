/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Biophysics.HodgkinHuxley
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.IntermediateValue

/-!
# Hodgkin–Huxley with a constant applied current: the equilibrium branch and its linear stability

`HodgkinHuxley.lean` proves global existence, boundedness and the stability of the squid resting
state for `I = 0` (T199), and that the squid steady-state current `steadyCurrent squid` is
strictly increasing on `[-12, 115]` mV (T256). This file adds the applied current `I` as a
parameter (`squidI I`, the squid parameters with current `I`) and follows the equilibrium branch.

## The branch

Every equilibrium of `squidI I` is `eqPoint V = (V, m∞(V), h∞(V), n∞(V))` for a voltage `V` with
`I∞(V) = I`, where `I∞ = Iss` abbreviates the steady-state current–voltage relation
`steadyCurrent squid` (`field_squidI_eq_zero_iff`). So `V ↦ (I∞(V), eqPoint V)` parametrizes all
equilibria of all currents; `V = 0` is T199's resting state (`steadyCurrent_squid_zero`,
`eqPoint_zero`), and every current has at least one equilibrium (`exists_equilibrium`). The
current does not enter the Jacobian, which along the branch is the arrowhead matrix
`(arrowAt V).mat` (`jac_eqPoint`).

## Main results

* `Arrow.det_eq_charQ`, `Arrow.mem_spectrum_iff`: for an arrowhead matrix
  `[[a, b], [c, -diag k]]`, `det (μ - M)` is an explicit quartic `charQ`, and the eigenvalues are
  its roots.
* `re_neg_of_quartic_eq_zero`, `Arrow.isHurwitz_of_hdet_pos`: **Routh–Hurwitz for quartics**
  (sufficiency): `a₁, a₃, a₄ > 0` and `Δ₃ = a₁ a₂ a₃ - a₃² - a₁² a₄ > 0` put every root in the open
  left half-plane.
* `quartic_eq_mul_of_hurwitz3_eq_zero`, `Arrow.isSpectralHopfCandidate_of_hdet_eq_zero`:
  **spectral Hopf candidate from the coefficients**: `Δ₃ = 0` with `a₁, a₃, a₄ > 0` gives
  `IsSpectralHopfCandidate ω`, `ω = √(a₃ / a₁)`: `± i ω` are eigenvalues, every other eigenvalue
  has negative real part, and `i ω` is a simple root of the characteristic polynomial. These are
  eigenvalue conditions only; a Hopf bifurcation also needs a transversal crossing, not shown.
* `hurwitz3_eq_zero_of_quartic_I_mul`, `hdet_eq_zero_of_imaginary_eigenvalue`: conversely, a
  nonzero purely imaginary eigenvalue forces `Δ₃ = 0`.
* `arrowAt_0_signs`, `arrowAt_15_signs`, `arrowAt_15_hdet_neg`: certified interval arithmetic on
  the rate functions. At rest the Routh–Hurwitz conditions hold; at `V = 15` mV
  (`I∞(15) ≈ 62` µA/cm² in floating point) `coef₂ < 0` and `Δ₃ < 0` while `coef₃, coef₄ > 0`.
* `coef₄_eq_deriv_Iss`, `zero_mem_spectrum_jac_iff`: `coef₄ = k₁ k₂ k₃ · I∞'(V)`, so `0` is an
  eigenvalue on the branch exactly at critical points of the I–V curve. A fold would need
  further nondegeneracy, which is not shown.
* `exists_spectral_hopf_candidate_or_zero_eigenvalue`: there is `V* ∈ (0, 15)` mV such that, at
  the equilibrium `eqPoint V*` of the current `I* = I∞(V*)`, either the spectral Hopf conditions
  hold and every branch equilibrium with `V ∈ [0, V*)` has a Hurwitz Jacobian, or `0` is an
  eigenvalue (`I∞'(V*) = 0`). The zero-eigenvalue alternative says nothing about the branch
  below `V*`.
* `exists_spectral_hopf_candidate_of_deriv_Iss_pos`: if `I∞' > 0` on `[0, 15]`, the
  zero-eigenvalue case is excluded and the candidate sits at a current `I* ∈ (0, I∞(15))`.
* `exists_spectral_hopf_candidate`: **main theorem.** T256's `steadyCurrentDeriv_squid_pos`
  gives `I∞' > 0` on `[0, 15]`, so there is `V* ∈ (0, 15)` mV with Hurwitz Jacobians along the
  branch for `V ∈ [0, V*)` and the spectral Hopf conditions at `V*`, at a current
  `I* ∈ (0, I∞(15))`: the branch first stops being Hurwitz at a spectral Hopf candidate, where
  `0` is not an eigenvalue.
* `eqPoint_globalSolution_decay`: at a branch point with a Hurwitz Jacobian, solutions defined on
  all of `[0, ∞)` that start nearby decay exponentially to it. This is the conditional form of
  linearized stability: it does not assert that such solutions exist.

## Scope: what is weakened or deferred

The task asks for the Hopf bifurcation in `I` (rest → periodic firing). Proved here are the
equilibrium branch, Hurwitz Jacobians along it up to `V*`, and the spectral Hopf conditions at
`V*` (`exists_spectral_hopf_candidate`): a Hopf candidate, not a Hopf bifurcation. Deferred,
exactly:

1. **`V*` is not located.** It comes from the intermediate value theorem on `[0, 15]`.
   Floating-point evaluation of these definitions puts the first zero of `Δ₃` near `V ≈ 5.3` mV,
   `I ≈ 9.8` µA/cm², consistent with Rinzel and Miller (1980); none of these numbers is proved.
2. **Transversality is not proved.** The sign of `d Re λ / d I` at `I*` is not controlled, since
   `V*` is only characterized as the first voltage where the branch Jacobian stops being Hurwitz;
   without it `V*` is only a spectral Hopf candidate.
3. **No periodic orbits.** Mathlib has no Hopf bifurcation theorem. Rinzel and Miller (1980)
   compute that the squid Hopf bifurcation at this current is subcritical, so the orbits born
   there are unstable; repetitive firing (the stable large-amplitude limit cycle) is not
   addressed. The second Hopf bifurcation they report (`I ≈ 154` µA/cm²) is not treated.
4. **Stability is linear.** Along the branch segment `V ∈ [0, V*)` the Jacobian is Hurwitz;
   `eqPoint_globalSolution_decay` adds decay of global solutions near such a point but not their
   existence, and uniqueness of the equilibrium for those currents is not shown.

## Source receipt (reuse search, 2026-11-14)

Reused from ATLAS: `HodgkinHuxley` (T199: rates, `field`, `field_eq_zero_iff`, `jac`,
`hasFDerivAt_field`, rate values at `V = 0`; T256: `mInf`, `hInf`, `nInf`, `steadyCurrent`,
`hasDerivAt_steady`, `hasDerivAt_steadyCurrent`, `steadyCurrentDeriv_squid_pos`),
`Matrix.IsHurwitz` and `LinearizedStability.globalSolution_decay_of_hasFDerivAt`. ATLAS has only
the planar Routh–Hurwitz criterion (`PlanarStability`); Mathlib has none. Reused from Mathlib:
`Matrix.det_succ_row_zero`, `Matrix.det_fin_three`, `Matrix.isUnit_iff_isUnit_det`,
`Real.exp_bound`, `intermediate_value_Icc'`, `IsClosed.csInf_mem`, `strictMonoOn_of_deriv_pos`.

## References

* A. L. Hodgkin and A. F. Huxley, J. Physiol. 117 (1952) 500–544.
* J. Rinzel and R. N. Miller, "Numerical calculation of stable and unstable periodic solutions to
  the Hodgkin–Huxley equations", Math. Biosci. 49 (1980) 27–59.
* W. M. Liu, "Criterion of Hopf bifurcations without using eigenvalues", J. Math. Anal. Appl. 182
  (1994) 250–256.
* G. B. Ermentrout and D. H. Terman, *Mathematical Foundations of Neuroscience*, Springer (2010).
-/

@[expose] public section

open Real Set Filter
open scoped Topology

namespace MathlibExt.Biology.Biophysics.HodgkinHuxleyCurrent

open MathlibExt.Biology.Biophysics.HodgkinHuxley

/-! ## A. Quartics: Routh–Hurwitz, the factorization at `Δ₃ = 0`, necessity of `Δ₃ = 0` -/

/-- The monic real quartic `μ⁴ + a₁ μ³ + a₂ μ² + a₃ μ + a₄`, evaluated at a complex `μ`. -/
noncomputable def quartic (a₁ a₂ a₃ a₄ : ℝ) (μ : ℂ) : ℂ :=
  μ ^ 4 + a₁ * μ ^ 3 + a₂ * μ ^ 2 + a₃ * μ + a₄

/-- Its derivative `4 μ³ + 3 a₁ μ² + 2 a₂ μ + a₃`. -/
noncomputable def quarticDeriv (a₁ a₂ a₃ : ℝ) (μ : ℂ) : ℂ :=
  4 * μ ^ 3 + 3 * a₁ * μ ^ 2 + 2 * a₂ * μ + a₃

/-- The third Hurwitz determinant `Δ₃ = a₁ a₂ a₃ - a₃² - a₁² a₄` of the quartic. -/
def hurwitz3 (a₁ a₂ a₃ a₄ : ℝ) : ℝ := a₁ * a₂ * a₃ - a₃ ^ 2 - a₁ ^ 2 * a₄

theorem hasDerivAt_quartic (a₁ a₂ a₃ a₄ : ℝ) (μ : ℂ) :
    HasDerivAt (quartic a₁ a₂ a₃ a₄) (quarticDeriv a₁ a₂ a₃ μ) μ := by
  have h := ((((hasDerivAt_pow 4 μ).add ((hasDerivAt_pow 3 μ).const_mul (a₁ : ℂ))).add
    ((hasDerivAt_pow 2 μ).const_mul (a₂ : ℂ))).add
      ((hasDerivAt_id' μ).const_mul (a₃ : ℂ))).add_const (a₄ : ℂ)
  exact h.congr_deriv (by norm_num [quarticDeriv]; ring)

/-- Real and imaginary parts of `μ² + p μ + q`. -/
private theorem quad_re_im (p q : ℝ) (μ : ℂ) :
    (μ ^ 2 + p * μ + q).re = μ.re ^ 2 - μ.im ^ 2 + p * μ.re + q ∧
      (μ ^ 2 + p * μ + q).im = μ.im * (2 * μ.re + p) := by
  constructor
  · simp [pow_two]
  · simp [pow_two]; ring

/-- Roots of `μ² + p μ + q` with `p, q > 0` lie in the open left half-plane. -/
theorem re_neg_of_quad_eq_zero {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {μ : ℂ}
    (h : μ ^ 2 + p * μ + q = 0) : μ.re < 0 := by
  obtain ⟨hre, him⟩ := quad_re_im p q μ
  rw [h, Complex.zero_re] at hre
  rw [h, Complex.zero_im] at him
  by_contra hx
  rw [not_lt] at hx
  have hy : μ.im = 0 := by
    rcases mul_eq_zero.mp him.symm with h | h
    · exact h
    · linarith
  rw [hy] at hre
  nlinarith

/-- **Routh–Hurwitz for quartics (sufficiency).** If `a₁, a₃, a₄ > 0` and `Δ₃ > 0`, every root
of the quartic has negative real part. -/
theorem re_neg_of_quartic_eq_zero {a₁ a₂ a₃ a₄ : ℝ} (h₁ : 0 < a₁) (h₃ : 0 < a₃) (h₄ : 0 < a₄)
    (hH : 0 < hurwitz3 a₁ a₂ a₃ a₄) {μ : ℂ} (hμ : quartic a₁ a₂ a₃ a₄ μ = 0) : μ.re < 0 := by
  unfold hurwitz3 at hH
  have h₂ : 0 < a₂ := by
    by_contra h
    rw [not_lt] at h
    have : a₁ * a₂ * a₃ ≤ 0 := by
      have := mul_pos h₁ h₃
      nlinarith
    nlinarith [sq_nonneg a₃, mul_pos (mul_pos h₁ h₁) h₄]
  by_contra hx
  rw [not_lt] at hx
  by_cases hy : μ.im = 0
  · -- a real root `x ≥ 0` is impossible
    have hμx : μ = (μ.re : ℂ) := Complex.ext (by simp) (by simp [hy])
    rw [hμx] at hμ
    have hr : ((μ.re ^ 4 + a₁ * μ.re ^ 3 + a₂ * μ.re ^ 2 + a₃ * μ.re + a₄ : ℝ) : ℂ) = 0 := by
      rw [← hμ]; simp [quartic]
    have hr' : μ.re ^ 4 + a₁ * μ.re ^ 3 + a₂ * μ.re ^ 2 + a₃ * μ.re + a₄ = 0 := by
      exact_mod_cast hr
    have : 0 < μ.re ^ 4 + a₁ * μ.re ^ 3 + a₂ * μ.re ^ 2 + a₃ * μ.re + a₄ := by
      have := pow_nonneg hx 4
      have := mul_nonneg h₁.le (pow_nonneg hx 3)
      have := mul_nonneg h₂.le (pow_nonneg hx 2)
      have := mul_nonneg h₃.le hx
      linarith
    linarith
  · -- divide by the real factor `μ² + P μ + R` with `P = -2 Re μ`, `R = |μ|²`
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = -2 * μ.re := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = μ.re ^ 2 + μ.im ^ 2 := ⟨_, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p : ℝ, a₁ = P + p := ⟨a₁ - P, by ring⟩
    obtain ⟨q, hq⟩ : ∃ q : ℝ, a₂ = R + q + P * p := ⟨a₂ - R - P * p, by ring⟩
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = a₃ - (P * q + p * R) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = a₄ - R * q := ⟨_, rfl⟩
    have hfac : quartic a₁ a₂ a₃ a₄ μ = (μ ^ 2 + P * μ + R) * (μ ^ 2 + p * μ + q) +
        ((r : ℂ) * μ + (s : ℂ)) := by
      simp only [quartic, hp, hq, hr, hs]; push_cast; ring
    have hz : μ ^ 2 + P * μ + R = 0 := by
      apply Complex.ext
      · rw [(quad_re_im P R μ).1, Complex.zero_re, hP, hR]; ring
      · rw [(quad_re_im P R μ).2, Complex.zero_im, hP]; ring
    rw [hz, zero_mul, zero_add] at hfac
    rw [hfac] at hμ
    have him := congrArg Complex.im hμ
    have hre := congrArg Complex.re hμ
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.zero_im] at him
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.zero_re] at hre
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact h
      · exact absurd h hy
    rw [hr0, zero_mul, zero_add] at hre
    have ha₃ : a₃ = P * q + p * R := by linarith
    have ha₄ : a₄ = R * q := by linarith
    have hid : a₁ * a₂ * a₃ - a₃ ^ 2 - a₁ ^ 2 * a₄ = P * p * ((R - q) ^ 2 + a₁ * a₃) := by
      rw [ha₃, ha₄, hp, hq]; ring
    have hX : 0 < (R - q) ^ 2 + a₁ * a₃ := by have := mul_pos h₁ h₃; positivity
    have hPp : 0 < P * p := by
      by_contra h
      rw [not_lt] at h
      have := mul_nonpos_of_nonpos_of_nonneg h hX.le
      linarith
    have hP0 : P ≤ 0 := by rw [hP]; linarith
    have hp0 : p < 0 := by
      by_contra h
      rw [not_lt] at h
      have := mul_nonpos_of_nonpos_of_nonneg hP0 h
      linarith
    linarith

/-- **The factorization at `Δ₃ = 0`.** If `Δ₃ = 0` with `a₁, a₃, a₄ > 0`, then with
`ω² = a₃ / a₁` and `c = a₁ a₄ / a₃ > 0`, the quartic factors as `(μ² + ω²)(μ² + a₁ μ + c)`. -/
theorem quartic_eq_mul_of_hurwitz3_eq_zero {a₁ a₂ a₃ a₄ : ℝ} (h₁ : 0 < a₁) (h₃ : 0 < a₃)
    (hH : hurwitz3 a₁ a₂ a₃ a₄ = 0) (μ : ℂ) :
    quartic a₁ a₂ a₃ a₄ μ = (μ ^ 2 + ((√(a₃ / a₁) : ℝ) : ℂ) ^ 2) *
      (μ ^ 2 + a₁ * μ + ((a₁ * a₄ / a₃ : ℝ) : ℂ)) := by
  have hω : √(a₃ / a₁) ^ 2 = a₃ / a₁ := Real.sq_sqrt (div_pos h₃ h₁).le
  unfold hurwitz3 at hH
  have e₂ : a₂ = a₁ * a₄ / a₃ + √(a₃ / a₁) ^ 2 := by
    rw [hω]; field_simp; linear_combination hH
  have e₃ : a₃ = a₁ * √(a₃ / a₁) ^ 2 := by rw [hω]; field_simp
  have e₄ : a₄ = a₁ * a₄ / a₃ * √(a₃ / a₁) ^ 2 := by rw [hω]; field_simp
  have key : quartic a₁ a₂ a₃ a₄ μ = μ ^ 4 + a₁ * μ ^ 3 +
      ((a₁ * a₄ / a₃ + √(a₃ / a₁) ^ 2 : ℝ) : ℂ) * μ ^ 2 + ((a₁ * √(a₃ / a₁) ^ 2 : ℝ) : ℂ) * μ +
      ((a₁ * a₄ / a₃ * √(a₃ / a₁) ^ 2 : ℝ) : ℂ) := by
    simp only [quartic]; rw [← e₂, ← e₃, ← e₄]
  rw [key]; push_cast; ring

/-- **Necessity of `Δ₃ = 0`.** If `i ω` (with `ω ≠ 0`) is a root of the quartic, then
`a₃ = a₁ ω²` and `Δ₃ = 0`. -/
theorem hurwitz3_eq_zero_of_quartic_I_mul {a₁ a₂ a₃ a₄ ω : ℝ} (hω : ω ≠ 0)
    (h : quartic a₁ a₂ a₃ a₄ (Complex.I * ω) = 0) :
    a₃ = a₁ * ω ^ 2 ∧ hurwitz3 a₁ a₂ a₃ a₄ = 0 := by
  have e : quartic a₁ a₂ a₃ a₄ (Complex.I * ω) =
      ((ω ^ 4 - a₂ * ω ^ 2 + a₄ : ℝ) : ℂ) + ((a₃ * ω - a₁ * ω ^ 3 : ℝ) : ℂ) * Complex.I := by
    simp only [quartic]; push_cast
    linear_combination ((ω : ℂ) ^ 4 * (Complex.I ^ 2 - 1) + a₁ * ω ^ 3 * Complex.I +
      a₂ * ω ^ 2) * Complex.I_sq
  rw [e] at h
  have key : ∀ u v : ℝ, (u : ℂ) + v * Complex.I = 0 → u = 0 ∧ v = 0 := fun u v huv => by
    exact ⟨by simpa using congrArg Complex.re huv, by simpa using congrArg Complex.im huv⟩
  obtain ⟨hre, him⟩ := key _ _ h
  have h3 : a₃ = a₁ * ω ^ 2 := by
    have : (a₃ - a₁ * ω ^ 2) * ω = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hω
  refine ⟨h3, ?_⟩
  unfold hurwitz3
  have h4 : a₄ = a₂ * ω ^ 2 - ω ^ 4 := by linarith
  rw [h3, h4]; ring

/-! ## B. Arrowhead matrices -/

/-- The entries of an arrowhead matrix `[[a, b₁, b₂, b₃], [c₁, -k₁, 0, 0], [c₂, 0, -k₂, 0],
[c₃, 0, 0, -k₃]]`, the shape of the Hodgkin–Huxley Jacobian. -/
structure Arrow where
  a : ℝ
  b₁ : ℝ
  b₂ : ℝ
  b₃ : ℝ
  c₁ : ℝ
  c₂ : ℝ
  c₃ : ℝ
  k₁ : ℝ
  k₂ : ℝ
  k₃ : ℝ

namespace Arrow

variable (A : Arrow)

/-- The matrix. -/
def mat : Matrix (Fin 4) (Fin 4) ℝ :=
  !![A.a, A.b₁, A.b₂, A.b₃; A.c₁, -A.k₁, 0, 0; A.c₂, 0, -A.k₂, 0; A.c₃, 0, 0, -A.k₃]

/-- Cubic coefficient of the characteristic quartic `det (μ - M)`: minus the trace. -/
def coef₁ : ℝ := -A.a + (A.k₁ + A.k₂ + A.k₃)
/-- Quadratic coefficient of the characteristic quartic. -/
def coef₂ : ℝ := -A.a * (A.k₁ + A.k₂ + A.k₃) + (A.k₁ * A.k₂ + A.k₁ * A.k₃ + A.k₂ * A.k₃) -
  (A.b₁ * A.c₁ + A.b₂ * A.c₂ + A.b₃ * A.c₃)
/-- Linear coefficient of the characteristic quartic. -/
def coef₃ : ℝ := -A.a * (A.k₁ * A.k₂ + A.k₁ * A.k₃ + A.k₂ * A.k₃) + A.k₁ * A.k₂ * A.k₃ -
  A.b₁ * A.c₁ * (A.k₂ + A.k₃) - A.b₂ * A.c₂ * (A.k₁ + A.k₃) - A.b₃ * A.c₃ * (A.k₁ + A.k₂)
/-- Constant coefficient of the characteristic quartic: `det M`. -/
def coef₄ : ℝ := -A.a * (A.k₁ * A.k₂ * A.k₃) - A.b₁ * A.c₁ * (A.k₂ * A.k₃) -
  A.b₂ * A.c₂ * (A.k₁ * A.k₃) - A.b₃ * A.c₃ * (A.k₁ * A.k₂)

/-- The characteristic quartic. -/
noncomputable def charQ (μ : ℂ) : ℂ := quartic A.coef₁ A.coef₂ A.coef₃ A.coef₄ μ

/-- The Hurwitz determinant `Δ₃` of the characteristic quartic. -/
def hdet : ℝ := hurwitz3 A.coef₁ A.coef₂ A.coef₃ A.coef₄

/-- `charQ` is the characteristic polynomial: `det (μ I - M) = charQ μ`. -/
theorem det_eq_charQ (μ : ℂ) :
    (algebraMap ℂ (Matrix (Fin 4) (Fin 4) ℂ) μ - A.mat.map (algebraMap ℝ ℂ)).det = A.charQ μ := by
  have hM : algebraMap ℂ (Matrix (Fin 4) (Fin 4) ℂ) μ - A.mat.map (algebraMap ℝ ℂ) =
      !![μ - A.a, -A.b₁, -A.b₂, -A.b₃; -A.c₁, μ + A.k₁, 0, 0; -A.c₂, 0, μ + A.k₂, 0;
        -A.c₃, 0, 0, μ + A.k₃] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.algebraMap_matrix_apply]
  rw [hM, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, charQ, quartic, coef₁, coef₂,
    coef₃, coef₄]
  ring

/-- Eigenvalues are exactly the roots of the characteristic quartic. -/
theorem mem_spectrum_iff (μ : ℂ) :
    μ ∈ spectrum ℂ (A.mat.map (algebraMap ℝ ℂ)) ↔ A.charQ μ = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not, A.det_eq_charQ]

/-- **Routh–Hurwitz.** `coef₁, coef₃, coef₄ > 0` and `Δ₃ > 0` make the matrix Hurwitz. -/
theorem isHurwitz_of_hdet_pos (h₁ : 0 < A.coef₁) (h₃ : 0 < A.coef₃) (h₄ : 0 < A.coef₄)
    (hH : 0 < A.hdet) : A.mat.IsHurwitz := fun μ hμ =>
  re_neg_of_quartic_eq_zero h₁ h₃ h₄ hH ((A.mem_spectrum_iff μ).1 hμ)

/-- The spectral Hopf conditions at frequency `ω`, which make the point a Hopf candidate:
`± i ω` are eigenvalues, they are the only eigenvalues in the closed right half-plane, and `i ω`
is a simple root of the characteristic polynomial. No parameter crossing is part of this, so it
does not by itself give a Hopf bifurcation. -/
def IsSpectralHopfCandidate (ω : ℝ) : Prop :=
  0 < ω ∧ Complex.I * ω ∈ spectrum ℂ (A.mat.map (algebraMap ℝ ℂ)) ∧
    -(Complex.I * ω) ∈ spectrum ℂ (A.mat.map (algebraMap ℝ ℂ)) ∧
    (∀ μ ∈ spectrum ℂ (A.mat.map (algebraMap ℝ ℂ)), 0 ≤ μ.re →
      μ = Complex.I * ω ∨ μ = -(Complex.I * ω)) ∧
    quarticDeriv A.coef₁ A.coef₂ A.coef₃ (Complex.I * ω) ≠ 0

/-- **Spectral Hopf candidate from the coefficients.** `Δ₃ = 0` with `coef₁, coef₃, coef₄ > 0`
gives the spectral Hopf conditions at `ω = √(coef₃ / coef₁)`. -/
theorem isSpectralHopfCandidate_of_hdet_eq_zero (h₁ : 0 < A.coef₁) (h₃ : 0 < A.coef₃)
    (h₄ : 0 < A.coef₄) (hH : A.hdet = 0) : A.IsSpectralHopfCandidate √(A.coef₃ / A.coef₁) := by
  set ω := √(A.coef₃ / A.coef₁) with hωdef
  set c := A.coef₁ * A.coef₄ / A.coef₃ with hcdef
  have hω : 0 < ω := Real.sqrt_pos.2 (div_pos h₃ h₁)
  have hc : 0 < c := by positivity
  have hfac := quartic_eq_mul_of_hurwitz3_eq_zero h₁ h₃ hH
  rw [← hωdef, ← hcdef] at hfac
  have hIω : (Complex.I * ω) ^ 2 + (ω : ℂ) ^ 2 = 0 := by
    linear_combination (ω : ℂ) ^ 2 * Complex.I_sq
  have hIω' : (-(Complex.I * ω)) ^ 2 + (ω : ℂ) ^ 2 = 0 := by
    linear_combination (ω : ℂ) ^ 2 * Complex.I_sq
  have hsecond : ∀ μ : ℂ, 0 ≤ μ.re → μ ^ 2 + A.coef₁ * μ + (c : ℂ) ≠ 0 := fun μ hμ h =>
    absurd (re_neg_of_quad_eq_zero h₁ hc h) (not_lt.2 hμ)
  refine ⟨hω, ?_, ?_, ?_, ?_⟩
  · rw [A.mem_spectrum_iff, charQ, hfac, hIω, zero_mul]
  · rw [A.mem_spectrum_iff, charQ, hfac, hIω', zero_mul]
  · intro μ hμ hre
    rw [A.mem_spectrum_iff, charQ, hfac] at hμ
    rcases mul_eq_zero.mp hμ with h | h
    · have : (μ - Complex.I * ω) * (μ + Complex.I * ω) = 0 := by
        linear_combination h - (ω : ℂ) ^ 2 * Complex.I_sq
      rcases mul_eq_zero.mp this with h' | h'
      · exact Or.inl (sub_eq_zero.mp h')
      · exact Or.inr (eq_neg_of_add_eq_zero_left h')
    · exact absurd h (hsecond μ hre)
  · -- `Q' = 2 μ (μ² + a₁ μ + c) + (μ² + ω²)(2 μ + a₁)`, and the first term is nonzero at `i ω`
    have hd : quarticDeriv A.coef₁ A.coef₂ A.coef₃ (Complex.I * ω) =
        2 * (Complex.I * ω) * ((Complex.I * ω) ^ 2 + A.coef₁ * (Complex.I * ω) + (c : ℂ)) := by
      have hderiv := hasDerivAt_quartic A.coef₁ A.coef₂ A.coef₃ A.coef₄ (Complex.I * ω)
      have hfun : quartic A.coef₁ A.coef₂ A.coef₃ A.coef₄ =
          fun μ => (μ ^ 2 + (ω : ℂ) ^ 2) * (μ ^ 2 + A.coef₁ * μ + (c : ℂ)) := funext hfac
      rw [hfun] at hderiv
      have h2 : HasDerivAt (fun μ : ℂ => (μ ^ 2 + (ω : ℂ) ^ 2) * (μ ^ 2 + A.coef₁ * μ + (c : ℂ)))
          (2 * (Complex.I * ω) * ((Complex.I * ω) ^ 2 + A.coef₁ * (Complex.I * ω) + (c : ℂ)) +
            ((Complex.I * ω) ^ 2 + (ω : ℂ) ^ 2) * (2 * (Complex.I * ω) + A.coef₁))
          (Complex.I * ω) := by
        have hp1 := ((hasDerivAt_pow 2 (Complex.I * ω)).add_const ((ω : ℂ) ^ 2))
        have hp2 := (((hasDerivAt_pow 2 (Complex.I * ω)).add
          ((hasDerivAt_id' (Complex.I * ω)).const_mul (A.coef₁ : ℂ))).add_const (c : ℂ))
        convert hp1.mul hp2 using 1
        norm_num
      rw [hderiv.unique h2, hIω, zero_mul, add_zero]
    rw [hd]
    refine mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero Complex.I_ne_zero ?_)) ?_
    · exact_mod_cast hω.ne'
    · exact hsecond _ (by simp)

/-- **Necessity.** A nonzero purely imaginary eigenvalue forces `Δ₃ = 0`. -/
theorem hdet_eq_zero_of_mem_spectrum {ω : ℝ} (hω : ω ≠ 0)
    (h : Complex.I * ω ∈ spectrum ℂ (A.mat.map (algebraMap ℝ ℂ))) : A.hdet = 0 :=
  (hurwitz3_eq_zero_of_quartic_I_mul hω ((A.mem_spectrum_iff _).1 h)).2

/-- Zero is an eigenvalue iff `coef₄ = 0`. -/
theorem zero_mem_spectrum_iff :
    (0 : ℂ) ∈ spectrum ℂ (A.mat.map (algebraMap ℝ ℂ)) ↔ A.coef₄ = 0 := by
  rw [A.mem_spectrum_iff]; simp [charQ, quartic]

end Arrow

/-! ## C. The equilibrium branch -/

/-- The squid parameters with applied current `I`. -/
noncomputable def squidI (I : ℝ) : Params := { squid with I := I }

theorem squidI_valid (I : ℝ) : (squidI I).Valid :=
  ⟨by norm_num [squidI, squid], by norm_num [squidI, squid], by norm_num [squidI, squid],
    by norm_num [squidI, squid]⟩

theorem squidI_zero : squidI 0 = squid := rfl

/-- The applied current does not enter the ionic current or the Jacobian. -/
theorem ionic_squidI (I : ℝ) : ionic (squidI I) = ionic squid := rfl
theorem jac_squidI (I : ℝ) : jac (squidI I) = jac squid := rfl

theorem continuous_mInf : Continuous mInf :=
  contDiff_alphaM.continuous.div (contDiff_alphaM.continuous.add contDiff_betaM.continuous)
    fun V => (add_pos (alphaM_pos V) (betaM_pos V)).ne'
theorem continuous_hInf : Continuous hInf :=
  contDiff_alphaH.continuous.div (contDiff_alphaH.continuous.add contDiff_betaH.continuous)
    fun V => (add_pos (alphaH_pos V) (betaH_pos V)).ne'
theorem continuous_nInf : Continuous nInf :=
  contDiff_alphaN.continuous.div (contDiff_alphaN.continuous.add contDiff_betaN.continuous)
    fun V => (add_pos (alphaN_pos V) (betaN_pos V)).ne'

/-- The point of the branch at voltage `V`: `(V, m∞(V), h∞(V), n∞(V))`. -/
noncomputable def eqPoint (V : ℝ) : Fin 4 → ℝ := ![V, mInf V, hInf V, nInf V]

theorem eqPoint_zero : eqPoint 0 = rest := rfl

/-- The squid steady-state current–voltage relation `I∞ = steadyCurrent squid`. -/
noncomputable abbrev Iss : ℝ → ℝ := steadyCurrent squid

theorem continuous_Iss : Continuous Iss :=
  continuous_iff_continuousAt.2 fun V => (hasDerivAt_steadyCurrent squid V).continuousAt

/-- **Equilibria for constant current `I`.** `x` is an equilibrium of the squid system with
current `I` iff it is the branch point over its own voltage and `I∞(V) = I`. -/
theorem field_squidI_eq_zero_iff (I : ℝ) (x : Fin 4 → ℝ) :
    field (squidI I) x = 0 ↔ x = eqPoint (x 0) ∧ Iss (x 0) = I := by
  rw [field_eq_zero_iff (squidI_valid I)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, h4⟩
    funext i
    fin_cases i
    · rfl
    · exact h1
    · exact h2
    · exact h3
  · rintro ⟨hx, hI⟩
    have e1 : x 1 = mInf (x 0) := by rw [hx]; rfl
    have e2 : x 2 = hInf (x 0) := by rw [hx]; rfl
    have e3 : x 3 = nInf (x 0) := by rw [hx]; rfl
    exact ⟨e1, e2, e3, hI⟩

theorem field_eqPoint (V : ℝ) : field (squidI (Iss V)) (eqPoint V) = 0 :=
  (field_squidI_eq_zero_iff _ _).2 ⟨rfl, rfl⟩

/-- Below `EK = -12` the steady-state current is at most the leak current. -/
private theorem Iss_le_leak {V : ℝ} (hV : V ≤ -12) : Iss V ≤ 3 / 10 * (V - squidEL) := by
  have hm := mInf_mem_Ioo V
  have hh := hInf_mem_Ioo V
  have hn := nInf_mem_Ioo V
  have h1 : 0 ≤ 120 * mInf V ^ 3 * hInf V := by
    have := pow_pos hm.1 3; have := hh.1; positivity
  have h2 : 0 ≤ 36 * nInf V ^ 4 := by have := pow_pos hn.1 4; positivity
  have t1 : 120 * mInf V ^ 3 * hInf V * (V - 115) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1 (by linarith)
  have t2 : 36 * nInf V ^ 4 * (V - -12) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 (by linarith)
  simp only [Iss, steadyCurrent, ionic, squid]
  linarith

/-- Above `ENa = 115` the steady-state current is at least the leak current. -/
private theorem leak_le_Iss {V : ℝ} (hV : 115 ≤ V) : 3 / 10 * (V - squidEL) ≤ Iss V := by
  have hm := mInf_mem_Ioo V
  have hh := hInf_mem_Ioo V
  have hn := nInf_mem_Ioo V
  have h1 : 0 ≤ 120 * mInf V ^ 3 * hInf V := by
    have := pow_pos hm.1 3; have := hh.1; positivity
  have h2 : 0 ≤ 36 * nInf V ^ 4 := by have := pow_pos hn.1 4; positivity
  have t1 : 0 ≤ 120 * mInf V ^ 3 * hInf V * (V - 115) := mul_nonneg h1 (by linarith)
  have t2 : 0 ≤ 36 * nInf V ^ 4 * (V - -12) := mul_nonneg h2 (by linarith)
  simp only [Iss, steadyCurrent, ionic, squid]
  linarith

/-- **Existence of an equilibrium for every applied current.** -/
theorem exists_equilibrium (I : ℝ) : ∃ V, Iss V = I ∧ field (squidI I) (eqPoint V) = 0 := by
  set a := min (-12) (squidEL + 10 / 3 * I)
  set b := max 115 (squidEL + 10 / 3 * I)
  have ha : Iss a ≤ I := by
    have := Iss_le_leak (min_le_left (-12 : ℝ) (squidEL + 10 / 3 * I))
    have := min_le_right (-12 : ℝ) (squidEL + 10 / 3 * I)
    linarith
  have hb : I ≤ Iss b := by
    have := leak_le_Iss (le_max_left (115 : ℝ) (squidEL + 10 / 3 * I))
    have := le_max_right (115 : ℝ) (squidEL + 10 / 3 * I)
    linarith
  obtain ⟨V, hV⟩ := intermediate_value_univ a b continuous_Iss ⟨ha, hb⟩
  exact ⟨V, hV, hV ▸ field_eqPoint V⟩

/-! ## D. The Jacobian along the branch -/

/-- The arrowhead entries of the Jacobian at the branch point `eqPoint V`. -/
noncomputable def arrowAt (V : ℝ) : Arrow where
  a := -(120 * mInf V ^ 3 * hInf V + 36 * nInf V ^ 4 + 3 / 10)
  b₁ := 360 * mInf V ^ 2 * hInf V * (115 - V)
  b₂ := 120 * mInf V ^ 3 * (115 - V)
  b₃ := -(4 * 36 * nInf V ^ 3 * (V - -12))
  c₁ := deriv alphaM V * (1 - mInf V) - deriv betaM V * mInf V
  c₂ := deriv alphaH V * (1 - hInf V) - deriv betaH V * hInf V
  c₃ := deriv alphaN V * (1 - nInf V) - deriv betaN V * nInf V
  k₁ := alphaM V + betaM V
  k₂ := alphaH V + betaH V
  k₃ := alphaN V + betaN V

theorem jac_eqPoint (V : ℝ) : jac squid (eqPoint V) = (arrowAt V).mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jac, Arrow.mat, arrowAt, squid, eqPoint] <;> ring

theorem arrowAt_k₁_pos (V : ℝ) : 0 < (arrowAt V).k₁ := add_pos (alphaM_pos V) (betaM_pos V)
theorem arrowAt_k₂_pos (V : ℝ) : 0 < (arrowAt V).k₂ := add_pos (alphaH_pos V) (betaH_pos V)
theorem arrowAt_k₃_pos (V : ℝ) : 0 < (arrowAt V).k₃ := add_pos (alphaN_pos V) (betaN_pos V)

theorem arrowAt_coef₁_pos (V : ℝ) : 0 < (arrowAt V).coef₁ := by
  have hm := mInf_mem_Ioo V
  have hh := hInf_mem_Ioo V
  have hn := nInf_mem_Ioo V
  have h1 : 0 ≤ 120 * mInf V ^ 3 * hInf V := by
    have := pow_pos hm.1 3; have := hh.1; positivity
  have h2 : 0 ≤ 36 * nInf V ^ 4 := by have := pow_pos hn.1 4; positivity
  have := arrowAt_k₁_pos V
  have := arrowAt_k₂_pos V
  have := arrowAt_k₃_pos V
  simp only [Arrow.coef₁] at *
  simp only [arrowAt] at *
  linarith

/-- The coefficients along the branch are continuous in `V`. -/
theorem continuous_arrowAt :
    Continuous (fun V => (arrowAt V).coef₃) ∧ Continuous (fun V => (arrowAt V).coef₄) ∧
      Continuous (fun V => (arrowAt V).hdet) := by
  have hm := continuous_mInf
  have hh := continuous_hInf
  have hn := continuous_nInf
  have h1 := contDiff_alphaM.continuous
  have h2 := contDiff_betaM.continuous
  have h3 := contDiff_alphaH.continuous
  have h4 := contDiff_betaH.continuous
  have h5 := contDiff_alphaN.continuous
  have h6 := contDiff_betaN.continuous
  have d1 := contDiff_alphaM.continuous_deriv le_rfl
  have d2 := contDiff_betaM.continuous_deriv le_rfl
  have d3 := contDiff_alphaH.continuous_deriv le_rfl
  have d4 := contDiff_betaH.continuous_deriv le_rfl
  have d5 := contDiff_alphaN.continuous_deriv le_rfl
  have d6 := contDiff_betaN.continuous_deriv le_rfl
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Arrow.hdet, hurwitz3, Arrow.coef₁, Arrow.coef₂, Arrow.coef₃, Arrow.coef₄,
      arrowAt] <;> fun_prop


/-! ## E. Interval arithmetic helpers -/

private theorem widen {x l u l' u' : ℝ} (h : l ≤ x ∧ x ≤ u) (hl : l' ≤ l) (hu : u ≤ u') :
    l' ≤ x ∧ x ≤ u' := ⟨hl.trans h.1, h.2.trans hu⟩

private theorem mul_bounds {a b al au bl bu : ℝ} (ha : al ≤ a ∧ a ≤ au) (hb : bl ≤ b ∧ b ≤ bu)
    (hal : 0 ≤ al) (hbl : 0 ≤ bl) : al * bl ≤ a * b ∧ a * b ≤ au * bu :=
  ⟨mul_le_mul ha.1 hb.1 hbl (hal.trans ha.1),
    mul_le_mul ha.2 hb.2 (hbl.trans hb.1) ((hal.trans ha.1).trans ha.2)⟩

private theorem div_bounds {a b al au bl bu : ℝ} (ha : al ≤ a ∧ a ≤ au) (hb : bl ≤ b ∧ b ≤ bu)
    (hal : 0 ≤ al) (hbl : 0 < bl) : al / bu ≤ a / b ∧ a / b ≤ au / bl :=
  ⟨div_le_div₀ (hal.trans ha.1) ha.1 (hbl.trans_le hb.1) hb.2,
    div_le_div₀ ((hal.trans ha.1).trans ha.2) ha.2 hbl hb.1⟩

private theorem add_bounds {a b al au bl bu : ℝ} (ha : al ≤ a ∧ a ≤ au) (hb : bl ≤ b ∧ b ≤ bu) :
    al + bl ≤ a + b ∧ a + b ≤ au + bu := ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩

private theorem sub_bounds {a b al au bl bu : ℝ} (ha : al ≤ a ∧ a ≤ au) (hb : bl ≤ b ∧ b ≤ bu) :
    al - bu ≤ a - b ∧ a - b ≤ au - bl := ⟨sub_le_sub ha.1 hb.2, sub_le_sub ha.2 hb.1⟩

private theorem neg_bounds {a al au : ℝ} (ha : al ≤ a ∧ a ≤ au) : -au ≤ -a ∧ -a ≤ -al :=
  ⟨neg_le_neg ha.2, neg_le_neg ha.1⟩

private theorem pow_bounds {a al au : ℝ} (ha : al ≤ a ∧ a ≤ au) (n : ℕ) (hal : 0 ≤ al) :
    al ^ n ≤ a ^ n ∧ a ^ n ≤ au ^ n :=
  ⟨pow_le_pow_left₀ hal ha.1 n, pow_le_pow_left₀ (hal.trans ha.1) ha.2 n⟩

private theorem steady_bounds {α β αl αu βl βu : ℝ} (hα : αl ≤ α ∧ α ≤ αu)
    (hβ : βl ≤ β ∧ β ≤ βu) (hαl : 0 < αl) (hβl : 0 < βl) :
    αl / (αl + βu) ≤ α / (α + β) ∧ α / (α + β) ≤ αu / (αu + βl) := by
  have hα0 : 0 < α := hαl.trans_le hα.1
  have hβ0 : 0 < β := hβl.trans_le hβ.1
  constructor
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hα.1 hβ0.le, mul_le_mul_of_nonneg_left hβ.2 hα0.le]
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hα.2 hβl.le, mul_le_mul_of_nonneg_left hβ.1 hα0.le]

/-- Degree-5 Taylor enclosure of `exp` on `[-1, 1]`. -/
private theorem exp_near (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 - x ^ 6 * (7 / 4320) ≤ exp x ∧
      exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 * (7 / 4320) := by
  have hx : |x| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
  have h := Real.exp_bound hx (n := 6) (by norm_num)
  have e1 : (∑ i ∈ Finset.range 6, x ^ i / (i.factorial : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  have hc : ((Nat.succ 6 : ℕ) : ℝ) / (((Nat.factorial 6 : ℕ) : ℝ) * ((6 : ℕ) : ℝ)) = 7 / 4320 := by
    norm_num [Nat.factorial]
  rw [e1, Even.pow_abs ⟨3, rfl⟩, hc] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-! ## F. Rates and their derivatives at `V = 15` -/

theorem hasDerivAt_betaM (V : ℝ) : HasDerivAt betaM (-(2 / 9) * exp (-V / 18)) V :=
  ((((hasDerivAt_neg' (x := V)).div_const 18).exp).const_mul 4).congr_deriv (by ring)

theorem hasDerivAt_alphaH (V : ℝ) : HasDerivAt alphaH (-(7 / 2000) * exp (-V / 20)) V :=
  ((((hasDerivAt_neg' (x := V)).div_const 20).exp).const_mul (7 / 100)).congr_deriv (by ring)

theorem hasDerivAt_betaN (V : ℝ) : HasDerivAt betaN (-(1 / 640) * exp (-V / 80)) V :=
  ((((hasDerivAt_neg' (x := V)).div_const 80).exp).const_mul (1 / 8)).congr_deriv (by ring)

theorem hasDerivAt_betaH (V : ℝ) :
    HasDerivAt betaH (exp ((30 - V) / 10) / (10 * (exp ((30 - V) / 10) + 1) ^ 2)) V := by
  have hne : exp ((30 - V) / 10) + 1 ≠ 0 := by positivity
  have h := (((((hasDerivAt_id' V).const_sub 30).div_const 10).exp).add_const 1).inv hne
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun W => ?_)
  · field_simp
  · simp [betaH]

theorem hasDerivAt_alphaM_of_ne {V : ℝ} (hV : V ≠ 25) :
    HasDerivAt alphaM ((exp ((25 - V) / 10) - 1 - (25 - V) / 10 * exp ((25 - V) / 10)) /
      (exp ((25 - V) / 10) - 1) ^ 2 * (-1 / 10)) V := by
  have hx : (25 - V) / 10 ≠ 0 := fun h => hV (by linarith)
  have hin : HasDerivAt (fun W : ℝ => (25 - W) / 10) (-1 / 10) V := by
    simpa using ((hasDerivAt_id V).const_sub 25).div_const 10
  exact (hasDerivAt_vtrap hx).comp V hin

theorem hasDerivAt_alphaN_of_ne {V : ℝ} (hV : V ≠ 10) :
    HasDerivAt alphaN ((exp ((10 - V) / 10) - 1 - (10 - V) / 10 * exp ((10 - V) / 10)) /
      (exp ((10 - V) / 10) - 1) ^ 2 * (-1 / 10) / 10) V := by
  have hx : (10 - V) / 10 ≠ 0 := fun h => hV (by linarith)
  have hin : HasDerivAt (fun W : ℝ => (10 - W) / 10) (-1 / 10) V := by
    simpa using ((hasDerivAt_id V).const_sub 10).div_const 10
  exact ((hasDerivAt_vtrap hx).comp V hin).div_const 10

private theorem exp_neg_half_lt_one : exp (-1 / 2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)

theorem alphaM_15 : alphaM 15 = 1 / (exp 1 - 1) := by
  rw [alphaM, show ((25 : ℝ) - 15) / 10 = 1 by norm_num, vtrap_of_ne one_ne_zero]
theorem betaM_15 : betaM 15 = 4 * exp (-15 / 18) := rfl
theorem alphaH_15 : alphaH 15 = 7 / 100 * exp (-15 / 20) := rfl
theorem betaH_15 : betaH 15 = 1 / (exp 1 * exp (1 / 2) + 1) := by
  rw [betaH, show ((30 : ℝ) - 15) / 10 = 1 + 1 / 2 by norm_num, exp_add]
theorem alphaN_15 : alphaN 15 = 1 / 2 / (1 - exp (-1 / 2)) / 10 := by
  rw [alphaN, show ((10 : ℝ) - 15) / 10 = -1 / 2 by norm_num, vtrap_of_ne (by norm_num)]
  have h1 : exp (-1 / 2) - 1 ≠ 0 := by linarith [exp_neg_half_lt_one]
  have h2 : 1 - exp (-1 / 2) ≠ 0 := by linarith [exp_neg_half_lt_one]
  congr 1
  rw [div_eq_div_iff h1 h2]
  ring
theorem betaN_15 : betaN 15 = 1 / 8 * exp (-15 / 80) := rfl

theorem deriv_alphaM_15 : deriv alphaM 15 = 1 / (10 * (exp 1 - 1) ^ 2) := by
  rw [(hasDerivAt_alphaM_of_ne (by norm_num)).deriv, show ((25 : ℝ) - 15) / 10 = 1 by norm_num]
  have he : exp 1 - 1 ≠ 0 := by linarith [add_one_lt_exp (x := 1) one_ne_zero]
  field_simp
  ring
theorem deriv_betaM_15 : deriv betaM 15 = -(2 / 9) * exp (-15 / 18) := (hasDerivAt_betaM 15).deriv
theorem deriv_alphaH_15 : deriv alphaH 15 = -(7 / 2000) * exp (-15 / 20) :=
  (hasDerivAt_alphaH 15).deriv
theorem deriv_betaH_15 :
    deriv betaH 15 = exp 1 * exp (1 / 2) / (10 * (exp 1 * exp (1 / 2) + 1) ^ 2) := by
  rw [(hasDerivAt_betaH 15).deriv, show ((30 : ℝ) - 15) / 10 = 1 + 1 / 2 by norm_num, exp_add]
theorem deriv_alphaN_15 :
    deriv alphaN 15 = (1 - 3 / 2 * exp (-1 / 2)) / (100 * (1 - exp (-1 / 2)) ^ 2) := by
  rw [(hasDerivAt_alphaN_of_ne (by norm_num)).deriv, show ((10 : ℝ) - 15) / 10 = -1 / 2 by norm_num]
  have h1 : exp (-1 / 2) - 1 ≠ 0 := by linarith [exp_neg_half_lt_one]
  have h2 : 1 - exp (-1 / 2) ≠ 0 := by linarith [exp_neg_half_lt_one]
  field_simp
  ring
theorem deriv_betaN_15 : deriv betaN 15 = -(1 / 640) * exp (-15 / 80) :=
  (hasDerivAt_betaN 15).deriv

private theorem exp_five_halves_eq : exp (5 / 2) = exp 1 * exp 1 * exp (1 / 2) := by
  rw [← exp_add, ← exp_add]; norm_num
private theorem exp_three_eq : exp 3 = exp 1 * exp 1 * exp 1 := by
  rw [← exp_add, ← exp_add]; norm_num

/-! ## G. Signs of the characteristic coefficients at `V = 15` and `V = 0` -/

set_option maxHeartbeats 2000000 in
-- The interval-arithmetic chain discharges a few hundred `norm_num`/`linarith` goals.
/-- At `V = 15` mV: `coef₂ < 0` and `coef₃, coef₄ > 0`. -/
theorem arrowAt_15_signs :
    (arrowAt 15).coef₂ < 0 ∧ 0 < (arrowAt 15).coef₃ ∧ 0 < (arrowAt 15).coef₄ := by
  have he : (67957 / 25000 : ℝ) ≤ exp 1 ∧ exp 1 ≤ (271829 / 100000 : ℝ) :=
      ⟨(lt_trans (by norm_num) exp_one_gt_d9).le, (lt_trans exp_one_lt_d9 (by norm_num)).le⟩
  have hq : (164867 / 100000 : ℝ) ≤ exp (1 / 2) ∧ exp (1 / 2) ≤ (164873 / 100000 : ℝ) := by
    obtain ⟨l, u⟩ := exp_near (1 / 2) (by norm_num) (by norm_num)
    constructor <;> linarith
  have hE1 : (10841 / 25000 : ℝ) ≤ exp (-15 / 18) ∧ exp (-15 / 18) ≤ (217363 / 500000 : ℝ) := by
    obtain ⟨l, u⟩ := exp_near (-15 / 18) (by norm_num) (by norm_num)
    constructor <;> linarith
  have hE2 : (94371 / 200000 : ℝ) ≤ exp (-15 / 20) ∧ exp (-15 / 20) ≤ (29527 / 62500 : ℝ) := by
    obtain ⟨l, u⟩ := exp_near (-15 / 20) (by norm_num) (by norm_num)
    constructor <;> linarith
  have hE4 : (121297 / 200000 : ℝ) ≤ exp (-1 / 2) ∧ exp (-1 / 2) ≤ (75817 / 125000 : ℝ) := by
    obtain ⟨l, u⟩ := exp_near (-1 / 2) (by norm_num) (by norm_num)
    constructor <;> linarith
  have hE5 : (207257 / 250000 : ℝ) ≤ exp (-15 / 80) ∧ exp (-15 / 80) ≤ (82903 / 100000 : ℝ) := by
    obtain ⟨l, u⟩ := exp_near (-15 / 80) (by norm_num) (by norm_num)
    constructor <;> linarith
  have em1 : (8591 / 5000 : ℝ) ≤ exp 1 - 1 ∧ exp 1 - 1 ≤ (17183 / 10000 : ℝ) :=
    widen (sub_bounds he ⟨le_refl _, le_refl _⟩) (by norm_num) (by norm_num)
  have am_ : (58197 / 100000 : ℝ) ≤ 1 / (exp 1 - 1) ∧ 1 / (exp 1 - 1) ≤ (58201 / 100000 : ℝ) :=
    widen (div_bounds ⟨le_refl _,
        le_refl _⟩ em1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have ham : (58197 / 100000 : ℝ) ≤ alphaM 15 ∧ alphaM 15 ≤ (58201 / 100000 : ℝ) := by
    rw [alphaM_15]; exact am_
  have bm_ : (3469 / 2000 : ℝ) ≤ 4 * exp (-15 / 18) ∧ 4 * exp (-15 / 18) ≤ (1739 / 1000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ hE1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hbm : (3469 / 2000 : ℝ) ≤ betaM 15 ∧ betaM 15 ≤ (1739 / 1000 : ℝ) := by
    rw [betaM_15]; exact bm_
  have ah_ : (33029 / 1000000 : ℝ) ≤ (7 / 100) * exp (-15 / 20) ∧ (7 / 100) * exp (-15 / 20) ≤
      (33071 / 1000000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ hE2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hah : (33029 / 1000000 : ℝ) ≤ alphaH 15 ∧ alphaH 15 ≤ (33071 / 1000000 : ℝ) := by
    rw [alphaH_15]; exact ah_
  have E3 : (8963 / 2000 : ℝ) ≤ exp 1 * exp (1 / 2) ∧ exp 1 * exp (1 / 2) ≤ (22409 / 5000 : ℝ) :=
    widen (mul_bounds he hq (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have E3p1 : (10963 / 2000 : ℝ) ≤ exp 1 * exp (1 / 2) + 1 ∧ exp 1 * exp (1 / 2) + 1 ≤
      (27409 / 5000 : ℝ) :=
    widen (add_bounds E3 ⟨le_refl _, le_refl _⟩) (by norm_num) (by norm_num)
  have bh_ : (9121 / 50000 : ℝ) ≤ 1 / (exp 1 * exp (1 / 2) + 1) ∧
      1 / (exp 1 * exp (1 / 2) + 1) ≤ (4561 / 25000 : ℝ) :=
    widen (div_bounds ⟨le_refl _,
        le_refl _⟩ E3p1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hbh : (9121 / 50000 : ℝ) ≤ betaH 15 ∧ betaH 15 ≤ (4561 / 25000 : ℝ) := by
    rw [betaH_15]; exact bh_
  have om4 : (19673 / 50000 : ℝ) ≤ 1 - exp (-1 / 2) ∧ 1 - exp (-1 / 2) ≤ (4919 / 12500 : ℝ) :=
    widen (sub_bounds ⟨le_refl _, le_refl _⟩ hE4) (by norm_num) (by norm_num)
  have an1 : (2541 / 2000 : ℝ) ≤ (1 / 2) / (1 - exp (-1 / 2)) ∧ (1 / 2) / (1 - exp (-1 / 2)) ≤
      (3177 / 2500 : ℝ) :=
    widen (div_bounds ⟨le_refl _,
        le_refl _⟩ om4 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have an_ : (2541 / 20000 : ℝ) ≤ ((1 / 2) / (1 - exp (-1 / 2))) / 10 ∧
      ((1 / 2) / (1 - exp (-1 / 2))) / 10 ≤ (3177 / 25000 : ℝ) :=
    widen (div_bounds an1 ⟨le_refl _,
        le_refl _⟩ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have han : (2541 / 20000 : ℝ) ≤ alphaN 15 ∧ alphaN 15 ≤ (3177 / 25000 : ℝ) := by
    rw [alphaN_15]; exact an_
  have bn_ : (5181 / 50000 : ℝ) ≤ (1 / 8) * exp (-15 / 80) ∧ (1 / 8) * exp (-15 / 80) ≤
      (10363 / 100000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ hE5 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hbn : (5181 / 50000 : ℝ) ≤ betaN 15 ∧ betaN 15 ≤ (10363 / 100000 : ℝ) := by
    rw [betaN_15]; exact bn_
  have em1sq : (14761 / 5000 : ℝ) ≤ (exp 1 - 1) ^ 2 ∧ (exp 1 - 1) ^ 2 ≤ (14763 / 5000 : ℝ) :=
    widen (pow_bounds em1 2 (by norm_num)) (by norm_num) (by norm_num)
  have dam_d : (14761 / 500 : ℝ) ≤ 10 * ((exp 1 - 1) ^ 2) ∧ 10 * ((exp 1 - 1) ^ 2) ≤
      (14763 / 500 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ em1sq (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have dam : (8467 / 250000 : ℝ) ≤ 1 / (10 * ((exp 1 - 1) ^ 2)) ∧
      1 / (10 * ((exp 1 - 1) ^ 2)) ≤ (16937 / 500000 : ℝ) :=
    widen (div_bounds ⟨le_refl _,
        le_refl _⟩ dam_d (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have nbm : (24091 / 250000 : ℝ) ≤ (2 / 9) * exp (-15 / 18) ∧ (2 / 9) * exp (-15 / 18) ≤
      (48303 / 500000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ hE1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have nah : (8257 / 5000000 : ℝ) ≤ (7 / 2000) * exp (-15 / 20) ∧ (7 / 2000) * exp (-15 / 20) ≤
      (2067 / 1250000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ hE2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have E3p1sq : (15023 / 500 : ℝ) ≤ (exp 1 * exp (1 / 2) + 1) ^ 2 ∧
      (exp 1 * exp (1 / 2) + 1) ^ 2 ≤ (30051 / 1000 : ℝ) :=
    widen (pow_bounds E3p1 2 (by norm_num)) (by norm_num) (by norm_num)
  have dbh_d : (15023 / 50 : ℝ) ≤ 10 * ((exp 1 * exp (1 / 2) + 1) ^ 2) ∧
      10 * ((exp 1 * exp (1 / 2) + 1) ^ 2) ≤ (30051 / 100 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ E3p1sq (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have dbh : (233 / 15625 : ℝ) ≤
      (exp 1 * exp (1 / 2)) / (10 * ((exp 1 * exp (1 / 2) + 1) ^ 2)) ∧
          (exp 1 * exp (1 / 2)) / (10 * ((exp 1 * exp (1 / 2) + 1) ^ 2)) ≤ (14917 / 1000000 : ℝ) :=
    widen (div_bounds E3 dbh_d (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have dan_n1 : (22743 / 25000 : ℝ) ≤ (3 / 2) * exp (-1 / 2) ∧ (3 / 2) * exp (-1 / 2) ≤
      (90981 / 100000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ hE4 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have dan_n : (9019 / 100000 : ℝ) ≤ 1 - ((3 / 2) * exp (-1 / 2)) ∧
      1 - ((3 / 2) * exp (-1 / 2)) ≤ (2257 / 25000 : ℝ) :=
    widen (sub_bounds ⟨le_refl _, le_refl _⟩ dan_n1) (by norm_num) (by norm_num)
  have om4sq : (15481 / 100000 : ℝ) ≤ (1 - exp (-1 / 2)) ^ 2 ∧ (1 - exp (-1 / 2)) ^ 2 ≤
      (7743 / 50000 : ℝ) :=
    widen (pow_bounds om4 2 (by norm_num)) (by norm_num) (by norm_num)
  have dan_d : (15481 / 1000 : ℝ) ≤ 100 * ((1 - exp (-1 / 2)) ^ 2) ∧
      100 * ((1 - exp (-1 / 2)) ^ 2) ≤ (7743 / 500 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ om4sq (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have dan : (58239 / 10000000 : ℝ) ≤
      (1 - ((3 / 2) * exp (-1 / 2))) / (100 * ((1 - exp (-1 / 2)) ^ 2)) ∧
          (1 - ((3 / 2) * exp (-1 / 2))) / (100 * ((1 - exp (-1 / 2)) ^ 2)) ≤
              (58317 / 10000000 : ℝ) :=
    widen (div_bounds dan_n dan_d (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have nbn : (12953 / 10000000 : ℝ) ≤ (1 / 640) * exp (-15 / 80) ∧ (1 / 640) * exp (-15 / 80) ≤
      (6477 / 5000000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ hE5 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hm : (12537 / 50000 : ℝ) ≤ mInf 15 ∧ mInf 15 ≤ (201 / 800 : ℝ) :=
    widen (steady_bounds ham hbm (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hh : (479 / 3125 : ℝ) ≤ hInf 15 ∧ hInf 15 ≤ (15347 / 100000 : ℝ) :=
    widen (steady_bounds hah hbh (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hn : (13769 / 25000 : ℝ) ≤ nInf 15 ∧ nInf 15 ≤ (11017 / 20000 : ℝ) :=
    widen (steady_bounds han hbn (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hk1 : (5791 / 2500 : ℝ) ≤ (arrowAt 15).k₁ ∧ (arrowAt 15).k₁ ≤ (23211 / 10000 : ℝ) :=
    widen (add_bounds ham hbm) (by norm_num) (by norm_num)
  have hk2 : (2693 / 12500 : ℝ) ≤ (arrowAt 15).k₂ ∧ (arrowAt 15).k₂ ≤ (1347 / 6250 : ℝ) :=
    widen (add_bounds hah hbh) (by norm_num) (by norm_num)
  have hk3 : (23067 / 100000 : ℝ) ≤ (arrowAt 15).k₃ ∧ (arrowAt 15).k₃ ≤ (23071 / 100000 : ℝ) :=
    widen (add_bounds han hbn) (by norm_num) (by norm_num)
  have om : (599 / 800 : ℝ) ≤ 1 - mInf 15 ∧ 1 - mInf 15 ≤ (37463 / 50000 : ℝ) :=
    widen (sub_bounds ⟨le_refl _, le_refl _⟩ hm) (by norm_num) (by norm_num)
  have oh : (84653 / 100000 : ℝ) ≤ 1 - hInf 15 ∧ 1 - hInf 15 ≤ (2646 / 3125 : ℝ) :=
    widen (sub_bounds ⟨le_refl _, le_refl _⟩ hh) (by norm_num) (by norm_num)
  have on : (8983 / 20000 : ℝ) ≤ 1 - nInf 15 ∧ 1 - nInf 15 ≤ (11231 / 25000 : ℝ) :=
    widen (sub_bounds ⟨le_refl _, le_refl _⟩ hn) (by norm_num) (by norm_num)
  have P1 : (12679 / 500000 : ℝ) ≤ (1 / (10 * ((exp 1 - 1) ^ 2))) * (1 - mInf 15) ∧
      (1 / (10 * ((exp 1 - 1) ^ 2))) * (1 - mInf 15) ≤ (25381 / 1000000 : ℝ) :=
    widen (mul_bounds dam om (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have P2 : (12081 / 500000 : ℝ) ≤ ((2 / 9) * exp (-15 / 18)) * mInf 15 ∧
      ((2 / 9) * exp (-15 / 18)) * mInf 15 ≤ (24273 / 1000000 : ℝ) :=
    widen (mul_bounds nbm hm (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have P3 : (13979 / 10000000 : ℝ) ≤ ((7 / 2000) * exp (-15 / 20)) * (1 - hInf 15) ∧
      ((7 / 2000) * exp (-15 / 20)) * (1 - hInf 15) ≤ (7001 / 5000000 : ℝ) :=
    widen (mul_bounds nah oh (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have P4 : (22857 / 10000000 : ℝ) ≤
      ((exp 1 * exp (1 / 2)) / (10 * ((exp 1 * exp (1 / 2) + 1) ^ 2))) * hInf 15 ∧
          ((exp 1 * exp (1 / 2)) / (10 * ((exp 1 * exp (1 / 2) + 1) ^ 2))) * hInf 15 ≤
              (11447 / 5000000 : ℝ) :=
    widen (mul_bounds dbh hh (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have P5 : (13079 / 5000000 : ℝ) ≤
      ((1 - ((3 / 2) * exp (-1 / 2))) / (100 * ((1 - exp (-1 / 2)) ^ 2))) * (1 - nInf 15) ∧
          ((1 - ((3 / 2) * exp (-1 / 2))) / (100 * ((1 - exp (-1 / 2)) ^ 2))) * (1 - nInf 15) ≤
              (26199 / 10000000 : ℝ) :=
    widen (mul_bounds dan on (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have P6 : (71339 / 100000000 : ℝ) ≤ ((1 / 640) * exp (-15 / 80)) * nInf 15 ∧
      ((1 / 640) * exp (-15 / 80)) * nInf 15 ≤ (35679 / 50000000 : ℝ) :=
    widen (mul_bounds nbn hn (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hc1 : (619 / 12500 : ℝ) ≤ (arrowAt 15).c₁ ∧ (arrowAt 15).c₁ ≤ (24827 / 500000 : ℝ) := by
    simp only [arrowAt, deriv_alphaM_15, deriv_betaM_15]
    constructor <;> linarith [P1.1, P1.2, P2.1, P2.2]
  have hc2 : (-1153 / 312500 : ℝ) ≤ (arrowAt 15).c₂ ∧ (arrowAt 15).c₂ ≤ (-9209 / 2500000 : ℝ) := by
    simp only [arrowAt, deriv_alphaH_15, deriv_betaH_15]
    constructor <;> linarith [P3.1, P3.2, P4.1, P4.2]
  have hnc2 : (9209 / 2500000 : ℝ) ≤ -(arrowAt 15).c₂ ∧ -(arrowAt 15).c₂ ≤ (1153 / 312500 : ℝ) :=
    widen (neg_bounds hc2) (by norm_num) (by norm_num)
  have hc3 : (33291 / 10000000 : ℝ) ≤ (arrowAt 15).c₃ ∧ (arrowAt 15).c₃ ≤ (6667 / 2000000 : ℝ) := by
    simp only [arrowAt, deriv_alphaN_15, deriv_betaN_15]
    constructor <;> linarith [P5.1, P5.2, P6.1, P6.2]
  have m2 : (6287 / 100000 : ℝ) ≤ mInf 15 ^ 2 ∧ mInf 15 ^ 2 ≤ (63127 / 1000000 : ℝ) :=
    widen (pow_bounds hm 2 (by norm_num)) (by norm_num) (by norm_num)
  have m3 : (3941 / 250000 : ℝ) ≤ mInf 15 ^ 3 ∧ mInf 15 ^ 3 ≤ (15861 / 1000000 : ℝ) :=
    widen (pow_bounds hm 3 (by norm_num)) (by norm_num) (by norm_num)
  have n3 : (8353 / 50000 : ℝ) ≤ nInf 15 ^ 3 ∧ nInf 15 ^ 3 ≤ (3343 / 20000 : ℝ) :=
    widen (pow_bounds hn 3 (by norm_num)) (by norm_num) (by norm_num)
  have n4 : (92013 / 1000000 : ℝ) ≤ nInf 15 ^ 4 ∧ nInf 15 ^ 4 ≤ (46037 / 500000 : ℝ) :=
    widen (pow_bounds hn 4 (by norm_num)) (by norm_num) (by norm_num)
  have b1a : (22633 / 1000 : ℝ) ≤ 360 * (mInf 15 ^ 2) ∧ 360 * (mInf 15 ^ 2) ≤ (11363 / 500 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ m2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b1b : (34691 / 10000 : ℝ) ≤ (360 * (mInf 15 ^ 2)) * hInf 15 ∧
      (360 * (mInf 15 ^ 2)) * hInf 15 ≤ (17439 / 5000 : ℝ) :=
    widen (mul_bounds b1a hh (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hb1 : (34691 / 100 : ℝ) ≤ (arrowAt 15).b₁ ∧ (arrowAt 15).b₁ ≤ (17439 / 50 : ℝ) :=
    widen (mul_bounds b1b ⟨le_refl _,
        le_refl _⟩ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b2a : (4729 / 2500 : ℝ) ≤ 120 * (mInf 15 ^ 3) ∧ 120 * (mInf 15 ^ 3) ≤ (9517 / 5000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ m3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hb2 : (4729 / 25 : ℝ) ≤ (arrowAt 15).b₂ ∧ (arrowAt 15).b₂ ≤ (9517 / 50 : ℝ) :=
    widen (mul_bounds b2a ⟨le_refl _,
        le_refl _⟩ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b3a : (144 : ℝ) ≤ 4 * 36 ∧ 4 * 36 ≤ (144 : ℝ) :=
    widen (mul_bounds ⟨le_refl _, le_refl _⟩ ⟨le_refl _,
        le_refl _⟩ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b3b : (3007 / 125 : ℝ) ≤ (4 * 36) * (nInf 15 ^ 3) ∧ (4 * 36) * (nInf 15 ^ 3) ≤
      (2407 / 100 : ℝ) :=
    widen (mul_bounds b3a n3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b3c : (64951 / 100 : ℝ) ≤ ((4 * 36) * (nInf 15 ^ 3)) * (15 - -12) ∧
      ((4 * 36) * (nInf 15 ^ 3)) * (15 - -12) ≤ (64989 / 100 : ℝ) :=
    widen (mul_bounds b3b ⟨le_refl _,
        le_refl _⟩ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hb3 : (-64989 / 100 : ℝ) ≤ (arrowAt 15).b₃ ∧ (arrowAt 15).b₃ ≤ (-64951 / 100 : ℝ) :=
    widen (neg_bounds b3c) (by norm_num) (by norm_num)
  have hnb3 : (64951 / 100 : ℝ) ≤ -(arrowAt 15).b₃ ∧ -(arrowAt 15).b₃ ≤ (64989 / 100 : ℝ) :=
    widen (neg_bounds hb3) (by norm_num) (by norm_num)
  have A1 : (4729 / 2500 : ℝ) ≤ 120 * (mInf 15 ^ 3) ∧ 120 * (mInf 15 ^ 3) ≤ (9517 / 5000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ m3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have A2 : (14497 / 50000 : ℝ) ≤ (120 * (mInf 15 ^ 3)) * hInf 15 ∧
      (120 * (mInf 15 ^ 3)) * hInf 15 ≤ (7303 / 25000 : ℝ) :=
    widen (mul_bounds A1 hh (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have A3 : (8281 / 2500 : ℝ) ≤ 36 * (nInf 15 ^ 4) ∧ 36 * (nInf 15 ^ 4) ≤ (33147 / 10000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ n4 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have A4 : (36023 / 10000 : ℝ) ≤ (120 * (mInf 15 ^ 3)) * hInf 15 + (36 * (nInf 15 ^ 4)) ∧
      (120 * (mInf 15 ^ 3)) * hInf 15 + (36 * (nInf 15 ^ 4)) ≤ (36069 / 10000 : ℝ) :=
    widen (add_bounds A2 A3) (by norm_num) (by norm_num)
  have A5 : (39023 / 10000 : ℝ) ≤
      (120 * (mInf 15 ^ 3)) * hInf 15 + (36 * (nInf 15 ^ 4)) + (3 / 10) ∧
          (120 * (mInf 15 ^ 3)) * hInf 15 + (36 * (nInf 15 ^ 4)) + (3 / 10) ≤ (39069 / 10000 : ℝ) :=
    widen (add_bounds A4 ⟨le_refl _, le_refl _⟩) (by norm_num) (by norm_num)
  have ha : (-39069 / 10000 : ℝ) ≤ (arrowAt 15).a ∧ (arrowAt 15).a ≤ (-39023 / 10000 : ℝ) :=
    widen (neg_bounds A5) (by norm_num) (by norm_num)
  have hA : (39023 / 10000 : ℝ) ≤ -(arrowAt 15).a ∧ -(arrowAt 15).a ≤ (39069 / 10000 : ℝ) :=
    widen (neg_bounds ha) (by norm_num) (by norm_num)
  have s1 : (8589 / 500 : ℝ) ≤ (arrowAt 15).b₁ * (arrowAt 15).c₁ ∧
      (arrowAt 15).b₁ * (arrowAt 15).c₁ ≤ (17319 / 1000 : ℝ) :=
    widen (mul_bounds hb1 hc1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t2 : (34839 / 50000 : ℝ) ≤ (arrowAt 15).b₂ * (-(arrowAt 15).c₂) ∧
      (arrowAt 15).b₂ * (-(arrowAt 15).c₂) ≤ (17557 / 25000 : ℝ) :=
    widen (mul_bounds hb2 hnc2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t3 : (10811 / 5000 : ℝ) ≤ (-(arrowAt 15).b₃) * (arrowAt 15).c₃ ∧
      (-(arrowAt 15).b₃) * (arrowAt 15).c₃ ≤ (4333 / 2000 : ℝ) :=
    widen (mul_bounds hnb3 hc3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak1 : (11299 / 1250 : ℝ) ≤ (-(arrowAt 15).a) * (arrowAt 15).k₁ ∧
      (-(arrowAt 15).a) * (arrowAt 15).k₁ ≤ (22671 / 2500 : ℝ) :=
    widen (mul_bounds hA hk1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak2 : (84071 / 100000 : ℝ) ≤ (-(arrowAt 15).a) * (arrowAt 15).k₂ ∧
      (-(arrowAt 15).a) * (arrowAt 15).k₂ ≤ (42101 / 50000 : ℝ) :=
    widen (mul_bounds hA hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak3 : (45007 / 50000 : ℝ) ≤ (-(arrowAt 15).a) * (arrowAt 15).k₃ ∧
      (-(arrowAt 15).a) * (arrowAt 15).k₃ ≤ (90137 / 100000 : ℝ) :=
    widen (mul_bounds hA hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have k12 : (3119 / 6250 : ℝ) ≤ (arrowAt 15).k₁ * (arrowAt 15).k₂ ∧
      (arrowAt 15).k₁ * (arrowAt 15).k₂ ≤ (2001 / 4000 : ℝ) :=
    widen (mul_bounds hk1 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have k13 : (6679 / 12500 : ℝ) ≤ (arrowAt 15).k₁ * (arrowAt 15).k₃ ∧
      (arrowAt 15).k₁ * (arrowAt 15).k₃ ≤ (53551 / 100000 : ℝ) :=
    widen (mul_bounds hk1 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have k23 : (9939 / 200000 : ℝ) ≤ (arrowAt 15).k₂ * (arrowAt 15).k₃ ∧
      (arrowAt 15).k₂ * (arrowAt 15).k₃ ≤ (49723 / 1000000 : ℝ) :=
    widen (mul_bounds hk2 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak12 : (9737 / 5000 : ℝ) ≤ ((-(arrowAt 15).a) * (arrowAt 15).k₁) * (arrowAt 15).k₂ ∧
      ((-(arrowAt 15).a) * (arrowAt 15).k₁) * (arrowAt 15).k₂ ≤ (3909 / 2000 : ℝ) :=
    widen (mul_bounds Ak1 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak13 : (417 / 200 : ℝ) ≤ ((-(arrowAt 15).a) * (arrowAt 15).k₁) * (arrowAt 15).k₃ ∧
      ((-(arrowAt 15).a) * (arrowAt 15).k₁) * (arrowAt 15).k₃ ≤ (10461 / 5000 : ℝ) :=
    widen (mul_bounds Ak1 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak23 : (606 / 3125 : ℝ) ≤ ((-(arrowAt 15).a) * (arrowAt 15).k₂) * (arrowAt 15).k₃ ∧
      ((-(arrowAt 15).a) * (arrowAt 15).k₂) * (arrowAt 15).k₃ ≤ (19427 / 100000 : ℝ) :=
    widen (mul_bounds Ak2 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have k123 : (11511 / 100000 : ℝ) ≤ ((arrowAt 15).k₁ * (arrowAt 15).k₂) * (arrowAt 15).k₃ ∧
      ((arrowAt 15).k₁ * (arrowAt 15).k₂) * (arrowAt 15).k₃ ≤ (5771 / 50000 : ℝ) :=
    widen (mul_bounds k12 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have s1k2 : (2313 / 625 : ℝ) ≤ ((arrowAt 15).b₁ * (arrowAt 15).c₁) * (arrowAt 15).k₂ ∧
      ((arrowAt 15).b₁ * (arrowAt 15).c₁) * (arrowAt 15).k₂ ≤ (18663 / 5000 : ℝ) :=
    widen (mul_bounds s1 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have s1k3 : (4953 / 1250 : ℝ) ≤ ((arrowAt 15).b₁ * (arrowAt 15).c₁) * (arrowAt 15).k₃ ∧
      ((arrowAt 15).b₁ * (arrowAt 15).c₁) * (arrowAt 15).k₃ ≤ (39957 / 10000 : ℝ) :=
    widen (mul_bounds s1 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t2k1 : (807 / 500 : ℝ) ≤ ((arrowAt 15).b₂ * (-(arrowAt 15).c₂)) * (arrowAt 15).k₁ ∧
      ((arrowAt 15).b₂ * (-(arrowAt 15).c₂)) * (arrowAt 15).k₁ ≤ (16301 / 10000 : ℝ) :=
    widen (mul_bounds t2 hk1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t2k3 : (2009 / 12500 : ℝ) ≤ ((arrowAt 15).b₂ * (-(arrowAt 15).c₂)) * (arrowAt 15).k₃ ∧
      ((arrowAt 15).b₂ * (-(arrowAt 15).c₂)) * (arrowAt 15).k₃ ≤ (16203 / 100000 : ℝ) :=
    widen (mul_bounds t2 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t3k1 : (10017 / 2000 : ℝ) ≤ ((-(arrowAt 15).b₃) * (arrowAt 15).c₃) * (arrowAt 15).k₁ ∧
      ((-(arrowAt 15).b₃) * (arrowAt 15).c₃) * (arrowAt 15).k₁ ≤ (50287 / 10000 : ℝ) :=
    widen (mul_bounds t3 hk1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t3k2 : (23291 / 50000 : ℝ) ≤ ((-(arrowAt 15).b₃) * (arrowAt 15).c₃) * (arrowAt 15).k₂ ∧
      ((-(arrowAt 15).b₃) * (arrowAt 15).c₃) * (arrowAt 15).k₂ ≤ (46693 / 100000 : ℝ) :=
    widen (mul_bounds t3 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak123 : (1123 / 2500 : ℝ) ≤
      (((-(arrowAt 15).a) * (arrowAt 15).k₁) * (arrowAt 15).k₂) * (arrowAt 15).k₃ ∧
          (((-(arrowAt 15).a) * (arrowAt 15).k₁) * (arrowAt 15).k₂) * (arrowAt 15).k₃ ≤
              (45093 / 100000 : ℝ) :=
    widen (mul_bounds Ak12 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have s1k23 : (42683 / 50000 : ℝ) ≤
      (((arrowAt 15).b₁ * (arrowAt 15).c₁) * (arrowAt 15).k₂) * (arrowAt 15).k₃ ∧
          (((arrowAt 15).b₁ * (arrowAt 15).c₁) * (arrowAt 15).k₂) * (arrowAt 15).k₃ ≤
              (17223 / 20000 : ℝ) :=
    widen (mul_bounds s1k2 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t2k13 : (3723 / 10000 : ℝ) ≤
      (((arrowAt 15).b₂ * (-(arrowAt 15).c₂)) * (arrowAt 15).k₁) * (arrowAt 15).k₃ ∧
          (((arrowAt 15).b₂ * (-(arrowAt 15).c₂)) * (arrowAt 15).k₁) * (arrowAt 15).k₃ ≤
              (37609 / 100000 : ℝ) :=
    widen (mul_bounds t2k1 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t3k12 : (1079 / 1000 : ℝ) ≤
      (((-(arrowAt 15).b₃) * (arrowAt 15).c₃) * (arrowAt 15).k₁) * (arrowAt 15).k₂ ∧
          (((-(arrowAt 15).b₃) * (arrowAt 15).c₃) * (arrowAt 15).k₁) * (arrowAt 15).k₂ ≤
              (5419 / 5000 : ℝ) :=
    widen (mul_bounds t3k1 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have ha1 : (8331 / 1250 : ℝ) ≤ (arrowAt 15).coef₁ ∧ (arrowAt 15).coef₁ ≤ (66743 / 10000 : ℝ) := by
    simp only [Arrow.coef₁]
    constructor <;> linarith [hA.1, hA.2, hk1.1, hk1.2, hk2.1, hk2.2, hk3.1, hk3.2]
  have ha2 : (-2597 / 1000 : ℝ) ≤ (arrowAt 15).coef₂ ∧ (arrowAt 15).coef₂ ≤
      (-24119 / 10000 : ℝ) := by
    simp only [Arrow.coef₂]
    constructor <;> linarith [Ak1.1, Ak1.2, Ak2.1, Ak2.2, Ak3.1, Ak3.2, k12.1, k12.2, k13.1,
        k13.2, k23.1, k23.2, s1.1, s1.2, t2.1, t2.2, t3.1, t3.2]
  have ha3 : (38621 / 10000 : ℝ) ≤ (arrowAt 15).coef₃ ∧ (arrowAt 15).coef₃ ≤ (3981 / 1000 : ℝ) := by
    simp only [Arrow.coef₃]
    constructor <;> linarith [Ak12.1, Ak12.2, Ak13.1, Ak13.2, Ak23.1, Ak23.2, k123.1, k123.2,
        s1k2.1, s1k2.2, s1k3.1, s1k3.2, t2k1.1, t2k1.2, t2k3.1, t2k3.2, t3k1.1, t3k1.2, t3k2.1,
            t3k2.2]
  have ha4 : (10393 / 10000 : ℝ) ≤ (arrowAt 15).coef₄ ∧ (arrowAt 15).coef₄ ≤ (2643 / 2500 : ℝ) := by
    simp only [Arrow.coef₄]
    constructor <;> linarith [Ak123.1, Ak123.2, s1k23.1, s1k23.2, t2k13.1, t2k13.2, t3k12.1,
        t3k12.2]
  exact ⟨by linarith [ha2.2], by linarith [ha3.1], by linarith [ha4.1]⟩

/-- `Δ₃ < 0` at `V = 15` mV. -/
theorem arrowAt_15_hdet_neg : (arrowAt 15).hdet < 0 := by
  obtain ⟨h2, h3, h4⟩ := arrowAt_15_signs
  have h1 := arrowAt_coef₁_pos 15
  simp only [Arrow.hdet, hurwitz3]
  nlinarith [mul_pos h1 h3, mul_pos (mul_pos h1 h1) h4, mul_neg_of_pos_of_neg (mul_pos h1 h3) h2]

set_option maxHeartbeats 2000000 in
-- The interval-arithmetic chain discharges a few hundred `norm_num`/`linarith` goals.
/-- At rest (`V = 0`): `coef₃, coef₄ > 0` and `Δ₃ > 0` (the Routh–Hurwitz conditions). -/
theorem arrowAt_0_signs :
    0 < (arrowAt 0).coef₃ ∧ 0 < (arrowAt 0).coef₄ ∧ 0 < (arrowAt 0).hdet := by
  have he : (67957 / 25000 : ℝ) ≤ exp 1 ∧ exp 1 ≤ (271829 / 100000 : ℝ) :=
      ⟨(lt_trans (by norm_num) exp_one_gt_d9).le, (lt_trans exp_one_lt_d9 (by norm_num)).le⟩
  have hq : (164867 / 100000 : ℝ) ≤ exp (1 / 2) ∧ exp (1 / 2) ≤ (164873 / 100000 : ℝ) := by
    obtain ⟨l, u⟩ := exp_near (1 / 2) (by norm_num) (by norm_num)
    constructor <;> linarith
  have Y1 : (7389 / 1000 : ℝ) ≤ exp 1 * exp 1 ∧ exp 1 * exp 1 ≤ (18473 / 2500 : ℝ) :=
    widen (mul_bounds he he (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Y2 : (6091 / 500 : ℝ) ≤ (exp 1 * exp 1) * exp (1 / 2) ∧ (exp 1 * exp 1) * exp (1 / 2) ≤
      (12183 / 1000 : ℝ) :=
    widen (mul_bounds Y1 hq (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hY : (6091 / 500 : ℝ) ≤ exp (5 / 2) ∧ exp (5 / 2) ≤ (12183 / 1000 : ℝ) := by
    rw [exp_five_halves_eq]; exact Y2
  have Z2 : (4017 / 200 : ℝ) ≤ (exp 1 * exp 1) * exp 1 ∧ (exp 1 * exp 1) * exp 1 ≤
      (10043 / 500 : ℝ) :=
    widen (mul_bounds Y1 he (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hZ : (4017 / 200 : ℝ) ≤ exp 3 ∧ exp 3 ≤ (10043 / 500 : ℝ) := by
    rw [exp_three_eq]; exact Z2
  have Ym1 : (5591 / 500 : ℝ) ≤ exp (5 / 2) - 1 ∧ exp (5 / 2) - 1 ≤ (11183 / 1000 : ℝ) :=
    widen (sub_bounds hY ⟨le_refl _, le_refl _⟩) (by norm_num) (by norm_num)
  have am_ : (4471 / 20000 : ℝ) ≤ (5 / 2) / (exp (5 / 2) - 1) ∧ (5 / 2) / (exp (5 / 2) - 1) ≤
      (11179 / 50000 : ℝ) :=
    widen (div_bounds ⟨le_refl _,
        le_refl _⟩ Ym1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have ham : (4471 / 20000 : ℝ) ≤ alphaM 0 ∧ alphaM 0 ≤ (11179 / 50000 : ℝ) := by
    rw [alphaM_zero]; exact am_
  have hbm : (4 : ℝ) ≤ betaM 0 ∧ betaM 0 ≤ (4 : ℝ) := by rw [betaM_zero]; exact ⟨le_refl _,
      le_refl _⟩
  have hah : (7 / 100 : ℝ) ≤ alphaH 0 ∧ alphaH 0 ≤ (7 / 100 : ℝ) :=
      by rw [alphaH_zero]; exact ⟨le_refl _, le_refl _⟩
  have Zp1 : (4217 / 200 : ℝ) ≤ exp 3 + 1 ∧ exp 3 + 1 ≤ (10543 / 500 : ℝ) :=
    widen (add_bounds hZ ⟨le_refl _, le_refl _⟩) (by norm_num) (by norm_num)
  have bh_ : (741 / 15625 : ℝ) ≤ 1 / (exp 3 + 1) ∧ 1 / (exp 3 + 1) ≤ (11857 / 250000 : ℝ) :=
    widen (div_bounds ⟨le_refl _,
        le_refl _⟩ Zp1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hbh : (741 / 15625 : ℝ) ≤ betaH 0 ∧ betaH 0 ≤ (11857 / 250000 : ℝ) := by
    rw [betaH_zero]; exact bh_
  have em1 : (8591 / 5000 : ℝ) ≤ exp 1 - 1 ∧ exp 1 - 1 ≤ (17183 / 10000 : ℝ) :=
    widen (sub_bounds he ⟨le_refl _, le_refl _⟩) (by norm_num) (by norm_num)
  have an_d : (8591 / 500 : ℝ) ≤ 10 * (exp 1 - 1) ∧ 10 * (exp 1 - 1) ≤ (17183 / 1000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ em1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have an_ : (58197 / 1000000 : ℝ) ≤ 1 / (10 * (exp 1 - 1)) ∧ 1 / (10 * (exp 1 - 1)) ≤
      (58201 / 1000000 : ℝ) :=
    widen (div_bounds ⟨le_refl _,
        le_refl _⟩ an_d (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have han : (58197 / 1000000 : ℝ) ≤ alphaN 0 ∧ alphaN 0 ≤ (58201 / 1000000 : ℝ) := by
    rw [alphaN_zero]; exact an_
  have hbn : (1 / 8 : ℝ) ≤ betaN 0 ∧ betaN 0 ≤ (1 / 8 : ℝ) :=
      by rw [betaN_zero]; exact ⟨le_refl _, le_refl _⟩
  have dam_n1 : (18273 / 1000 : ℝ) ≤ (3 / 2) * exp (5 / 2) ∧ (3 / 2) * exp (5 / 2) ≤
      (731 / 40 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ hY (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have dam_n : (19273 / 1000 : ℝ) ≤ (3 / 2) * exp (5 / 2) + 1 ∧ (3 / 2) * exp (5 / 2) + 1 ≤
      (771 / 40 : ℝ) :=
    widen (add_bounds dam_n1 ⟨le_refl _, le_refl _⟩) (by norm_num) (by norm_num)
  have Ym1sq : (12503 / 100 : ℝ) ≤ (exp (5 / 2) - 1) ^ 2 ∧ (exp (5 / 2) - 1) ^ 2 ≤
      (6253 / 50 : ℝ) :=
    widen (pow_bounds Ym1 2 (by norm_num)) (by norm_num) (by norm_num)
  have dam_d : (12503 / 10 : ℝ) ≤ 10 * ((exp (5 / 2) - 1) ^ 2) ∧ 10 * ((exp (5 / 2) - 1) ^ 2) ≤
      (6253 / 5 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ Ym1sq (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have dam : (15411 / 1000000 : ℝ) ≤
      ((3 / 2) * exp (5 / 2) + 1) / (10 * ((exp (5 / 2) - 1) ^ 2)) ∧
          ((3 / 2) * exp (5 / 2) + 1) / (10 * ((exp (5 / 2) - 1) ^ 2)) ≤ (15417 / 1000000 : ℝ) :=
    widen (div_bounds dam_n dam_d (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Zp1sq : (44457 / 100 : ℝ) ≤ (exp 3 + 1) ^ 2 ∧ (exp 3 + 1) ^ 2 ≤ (22231 / 50 : ℝ) :=
    widen (pow_bounds Zp1 2 (by norm_num)) (by norm_num) (by norm_num)
  have dbh_d : (44457 / 10 : ℝ) ≤ 10 * ((exp 3 + 1) ^ 2) ∧ 10 * ((exp 3 + 1) ^ 2) ≤
      (22231 / 5 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ Zp1sq (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have dbh : (45173 / 10000000 : ℝ) ≤ exp 3 / (10 * ((exp 3 + 1) ^ 2)) ∧
      exp 3 / (10 * ((exp 3 + 1) ^ 2)) ≤ (45181 / 10000000 : ℝ) :=
    widen (div_bounds hZ dbh_d (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have em1sq : (14761 / 5000 : ℝ) ≤ (exp 1 - 1) ^ 2 ∧ (exp 1 - 1) ^ 2 ≤ (14763 / 5000 : ℝ) :=
    widen (pow_bounds em1 2 (by norm_num)) (by norm_num) (by norm_num)
  have dan_d : (14761 / 50 : ℝ) ≤ 100 * ((exp 1 - 1) ^ 2) ∧ 100 * ((exp 1 - 1) ^ 2) ≤
      (14763 / 50 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ em1sq (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have dan : (8467 / 2500000 : ℝ) ≤ 1 / (100 * ((exp 1 - 1) ^ 2)) ∧
      1 / (100 * ((exp 1 - 1) ^ 2)) ≤ (16937 / 5000000 : ℝ) :=
    widen (div_bounds ⟨le_refl _,
        le_refl _⟩ dan_d (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hm : (52929 / 1000000 : ℝ) ≤ mInf 0 ∧ mInf 0 ≤ (52937 / 1000000 : ℝ) :=
    widen (steady_bounds ham hbm (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hh : (5961 / 10000 : ℝ) ≤ hInf 0 ∧ hInf 0 ≤ (29807 / 50000 : ℝ) :=
    widen (steady_bounds hah hbh (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hn : (31767 / 100000 : ℝ) ≤ nInf 0 ∧ nInf 0 ≤ (31769 / 100000 : ℝ) :=
    widen (steady_bounds han hbn (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hk1 : (8447 / 2000 : ℝ) ≤ (arrowAt 0).k₁ ∧ (arrowAt 0).k₁ ≤ (10559 / 2500 : ℝ) :=
    widen (add_bounds ham hbm) (by norm_num) (by norm_num)
  have hk2 : (5871 / 50000 : ℝ) ≤ (arrowAt 0).k₂ ∧ (arrowAt 0).k₂ ≤ (11743 / 100000 : ℝ) :=
    widen (add_bounds hah hbh) (by norm_num) (by norm_num)
  have hk3 : (18319 / 100000 : ℝ) ≤ (arrowAt 0).k₃ ∧ (arrowAt 0).k₃ ≤ (18321 / 100000 : ℝ) :=
    widen (add_bounds han hbn) (by norm_num) (by norm_num)
  have om : (47353 / 50000 : ℝ) ≤ 1 - mInf 0 ∧ 1 - mInf 0 ≤ (23677 / 25000 : ℝ) :=
    widen (sub_bounds ⟨le_refl _, le_refl _⟩ hm) (by norm_num) (by norm_num)
  have oh : (20193 / 50000 : ℝ) ≤ 1 - hInf 0 ∧ 1 - hInf 0 ≤ (4039 / 10000 : ℝ) :=
    widen (sub_bounds ⟨le_refl _, le_refl _⟩ hh) (by norm_num) (by norm_num)
  have on : (68231 / 100000 : ℝ) ≤ 1 - nInf 0 ∧ 1 - nInf 0 ≤ (68233 / 100000 : ℝ) :=
    widen (sub_bounds ⟨le_refl _, le_refl _⟩ hn) (by norm_num) (by norm_num)
  have P1 : (2919 / 200000 : ℝ) ≤
      (((3 / 2) * exp (5 / 2) + 1) / (10 * ((exp (5 / 2) - 1) ^ 2))) * (1 - mInf 0) ∧
          (((3 / 2) * exp (5 / 2) + 1) / (10 * ((exp (5 / 2) - 1) ^ 2))) * (1 - mInf 0) ≤
              (7301 / 500000 : ℝ) :=
    widen (mul_bounds dam om (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have P4 : (26927 / 10000000 : ℝ) ≤ (exp 3 / (10 * ((exp 3 + 1) ^ 2))) * hInf 0 ∧
      (exp 3 / (10 * ((exp 3 + 1) ^ 2))) * hInf 0 ≤ (5387 / 2000000 : ℝ) :=
    widen (mul_bounds dbh hh (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have P5 : (5777 / 2500000 : ℝ) ≤ (1 / (100 * ((exp 1 - 1) ^ 2))) * (1 - nInf 0) ∧
      (1 / (100 * ((exp 1 - 1) ^ 2))) * (1 - nInf 0) ≤ (11557 / 5000000 : ℝ) :=
    widen (mul_bounds dan on (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hc1 : (26357 / 1000000 : ℝ) ≤ (arrowAt 0).c₁ ∧ (arrowAt 0).c₁ ≤ (13183 / 500000 : ℝ) := by
    simp only [arrowAt, hasDerivAt_alphaM_zero.deriv, hasDerivAt_betaM_zero.deriv]
    constructor <;> linarith [P1.1, P1.2, hm.1, hm.2]
  have hc2 : (-2567 / 625000 : ℝ) ≤ (arrowAt 0).c₂ ∧ (arrowAt 0).c₂ ≤ (-20531 / 5000000 : ℝ) := by
    simp only [arrowAt, hasDerivAt_alphaH_zero.deriv, hasDerivAt_betaH_zero.deriv]
    constructor <;> linarith [hh.1, hh.2, P4.1, P4.2]
  have hnc2 : (20531 / 5000000 : ℝ) ≤ -(arrowAt 0).c₂ ∧ -(arrowAt 0).c₂ ≤ (2567 / 625000 : ℝ) :=
    widen (neg_bounds hc2) (by norm_num) (by norm_num)
  have hc3 : (28071 / 10000000 : ℝ) ≤ (arrowAt 0).c₃ ∧ (arrowAt 0).c₃ ≤ (14039 / 5000000 : ℝ) := by
    simp only [arrowAt, hasDerivAt_alphaN_zero.deriv, hasDerivAt_betaN_zero.deriv]
    constructor <;> linarith [P5.1, P5.2, hn.1, hn.2]
  have m2 : (14007 / 5000000 : ℝ) ≤ mInf 0 ^ 2 ∧ mInf 0 ^ 2 ≤ (3503 / 1250000 : ℝ) :=
    widen (pow_bounds hm 2 (by norm_num)) (by norm_num) (by norm_num)
  have m3 : (14827 / 100000000 : ℝ) ≤ mInf 0 ^ 3 ∧ mInf 0 ^ 3 ≤ (2967 / 20000000 : ℝ) :=
    widen (pow_bounds hm 3 (by norm_num)) (by norm_num) (by norm_num)
  have n3 : (32057 / 1000000 : ℝ) ≤ nInf 0 ^ 3 ∧ nInf 0 ^ 3 ≤ (501 / 15625 : ℝ) :=
    widen (pow_bounds hn 3 (by norm_num)) (by norm_num) (by norm_num)
  have n4 : (10183 / 1000000 : ℝ) ≤ nInf 0 ^ 4 ∧ nInf 0 ^ 4 ≤ (10187 / 1000000 : ℝ) :=
    widen (pow_bounds hn 4 (by norm_num)) (by norm_num) (by norm_num)
  have b1a : (2017 / 2000 : ℝ) ≤ 360 * (mInf 0 ^ 2) ∧ 360 * (mInf 0 ^ 2) ≤ (10089 / 10000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ m2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b1b : (15029 / 25000 : ℝ) ≤ (360 * (mInf 0 ^ 2)) * hInf 0 ∧
      (360 * (mInf 0 ^ 2)) * hInf 0 ≤ (12029 / 20000 : ℝ) :=
    widen (mul_bounds b1a hh (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hb1 : (69133 / 1000 : ℝ) ≤ (arrowAt 0).b₁ ∧ (arrowAt 0).b₁ ≤ (69167 / 1000 : ℝ) :=
    widen (mul_bounds b1b ⟨le_refl _,
        le_refl _⟩ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b2a : (278 / 15625 : ℝ) ≤ 120 * (mInf 0 ^ 3) ∧ 120 * (mInf 0 ^ 3) ≤ (8901 / 500000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ m3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hb2 : (1023 / 500 : ℝ) ≤ (arrowAt 0).b₂ ∧ (arrowAt 0).b₂ ≤ (20473 / 10000 : ℝ) :=
    widen (mul_bounds b2a ⟨le_refl _,
        le_refl _⟩ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b3a : (144 : ℝ) ≤ 4 * 36 ∧ 4 * 36 ≤ (144 : ℝ) :=
    widen (mul_bounds ⟨le_refl _, le_refl _⟩ ⟨le_refl _,
        le_refl _⟩ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b3b : (23081 / 5000 : ℝ) ≤ (4 * 36) * (nInf 0 ^ 3) ∧ (4 * 36) * (nInf 0 ^ 3) ≤
      (46173 / 10000 : ℝ) :=
    widen (mul_bounds b3a n3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have b3c : (27697 / 500 : ℝ) ≤ ((4 * 36) * (nInf 0 ^ 3)) * (0 - -12) ∧
      ((4 * 36) * (nInf 0 ^ 3)) * (0 - -12) ≤ (6926 / 125 : ℝ) :=
    widen (mul_bounds b3b ⟨le_refl _,
        le_refl _⟩ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hb3 : (-6926 / 125 : ℝ) ≤ (arrowAt 0).b₃ ∧ (arrowAt 0).b₃ ≤ (-27697 / 500 : ℝ) :=
    widen (neg_bounds b3c) (by norm_num) (by norm_num)
  have hnb3 : (27697 / 500 : ℝ) ≤ -(arrowAt 0).b₃ ∧ -(arrowAt 0).b₃ ≤ (6926 / 125 : ℝ) :=
    widen (neg_bounds hb3) (by norm_num) (by norm_num)
  have A1 : (278 / 15625 : ℝ) ≤ 120 * (mInf 0 ^ 3) ∧ 120 * (mInf 0 ^ 3) ≤ (8901 / 500000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ m3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have A2 : (2121 / 200000 : ℝ) ≤ (120 * (mInf 0 ^ 3)) * hInf 0 ∧
      (120 * (mInf 0 ^ 3)) * hInf 0 ≤ (10613 / 1000000 : ℝ) :=
    widen (mul_bounds A1 hh (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have A3 : (18329 / 50000 : ℝ) ≤ 36 * (nInf 0 ^ 4) ∧ 36 * (nInf 0 ^ 4) ≤ (18337 / 50000 : ℝ) :=
    widen (mul_bounds ⟨le_refl _,
        le_refl _⟩ n4 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have A4 : (18859 / 50000 : ℝ) ≤ (120 * (mInf 0 ^ 3)) * hInf 0 + (36 * (nInf 0 ^ 4)) ∧
      (120 * (mInf 0 ^ 3)) * hInf 0 + (36 * (nInf 0 ^ 4)) ≤ (4717 / 12500 : ℝ) :=
    widen (add_bounds A2 A3) (by norm_num) (by norm_num)
  have A5 : (33859 / 50000 : ℝ) ≤
      (120 * (mInf 0 ^ 3)) * hInf 0 + (36 * (nInf 0 ^ 4)) + (3 / 10) ∧
          (120 * (mInf 0 ^ 3)) * hInf 0 + (36 * (nInf 0 ^ 4)) + (3 / 10) ≤ (8467 / 12500 : ℝ) :=
    widen (add_bounds A4 ⟨le_refl _, le_refl _⟩) (by norm_num) (by norm_num)
  have ha : (-8467 / 12500 : ℝ) ≤ (arrowAt 0).a ∧ (arrowAt 0).a ≤ (-33859 / 50000 : ℝ) :=
    widen (neg_bounds A5) (by norm_num) (by norm_num)
  have hA : (33859 / 50000 : ℝ) ≤ -(arrowAt 0).a ∧ -(arrowAt 0).a ≤ (8467 / 12500 : ℝ) :=
    widen (neg_bounds ha) (by norm_num) (by norm_num)
  have s1 : (18221 / 10000 : ℝ) ≤ (arrowAt 0).b₁ * (arrowAt 0).c₁ ∧
      (arrowAt 0).b₁ * (arrowAt 0).c₁ ≤ (18237 / 10000 : ℝ) :=
    widen (mul_bounds hb1 hc1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t2 : (21003 / 2500000 : ℝ) ≤ (arrowAt 0).b₂ * (-(arrowAt 0).c₂) ∧
      (arrowAt 0).b₂ * (-(arrowAt 0).c₂) ≤ (84087 / 10000000 : ℝ) :=
    widen (mul_bounds hb2 hnc2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t3 : (15549 / 100000 : ℝ) ≤ (-(arrowAt 0).b₃) * (arrowAt 0).c₃ ∧
      (-(arrowAt 0).b₃) * (arrowAt 0).c₃ ≤ (7779 / 50000 : ℝ) :=
    widen (mul_bounds hnb3 hc3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak1 : (143 / 50 : ℝ) ≤ (-(arrowAt 0).a) * (arrowAt 0).k₁ ∧
      (-(arrowAt 0).a) * (arrowAt 0).k₁ ≤ (28609 / 10000 : ℝ) :=
    widen (mul_bounds hA hk1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak2 : (39757 / 500000 : ℝ) ≤ (-(arrowAt 0).a) * (arrowAt 0).k₂ ∧
      (-(arrowAt 0).a) * (arrowAt 0).k₂ ≤ (79543 / 1000000 : ℝ) :=
    widen (mul_bounds hA hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak3 : (2481 / 20000 : ℝ) ≤ (-(arrowAt 0).a) * (arrowAt 0).k₃ ∧
      (-(arrowAt 0).a) * (arrowAt 0).k₃ ≤ (1241 / 10000 : ℝ) :=
    widen (mul_bounds hA hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have k12 : (6199 / 12500 : ℝ) ≤ (arrowAt 0).k₁ * (arrowAt 0).k₂ ∧
      (arrowAt 0).k₁ * (arrowAt 0).k₂ ≤ (24799 / 50000 : ℝ) :=
    widen (mul_bounds hk1 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have k13 : (7737 / 10000 : ℝ) ≤ (arrowAt 0).k₁ * (arrowAt 0).k₃ ∧
      (arrowAt 0).k₁ * (arrowAt 0).k₃ ≤ (77381 / 100000 : ℝ) :=
    widen (mul_bounds hk1 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have k23 : (2151 / 100000 : ℝ) ≤ (arrowAt 0).k₂ * (arrowAt 0).k₃ ∧
      (arrowAt 0).k₂ * (arrowAt 0).k₃ ≤ (4303 / 200000 : ℝ) :=
    widen (mul_bounds hk2 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak12 : (16791 / 50000 : ℝ) ≤ ((-(arrowAt 0).a) * (arrowAt 0).k₁) * (arrowAt 0).k₂ ∧
      ((-(arrowAt 0).a) * (arrowAt 0).k₁) * (arrowAt 0).k₂ ≤ (8399 / 25000 : ℝ) :=
    widen (mul_bounds Ak1 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak13 : (6549 / 12500 : ℝ) ≤ ((-(arrowAt 0).a) * (arrowAt 0).k₁) * (arrowAt 0).k₃ ∧
      ((-(arrowAt 0).a) * (arrowAt 0).k₁) * (arrowAt 0).k₃ ≤ (10483 / 20000 : ℝ) :=
    widen (mul_bounds Ak1 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak23 : (7283 / 500000 : ℝ) ≤ ((-(arrowAt 0).a) * (arrowAt 0).k₂) * (arrowAt 0).k₃ ∧
      ((-(arrowAt 0).a) * (arrowAt 0).k₂) * (arrowAt 0).k₃ ≤ (7287 / 500000 : ℝ) :=
    widen (mul_bounds Ak2 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have k123 : (90847 / 1000000 : ℝ) ≤ ((arrowAt 0).k₁ * (arrowAt 0).k₂) * (arrowAt 0).k₃ ∧
      ((arrowAt 0).k₁ * (arrowAt 0).k₂) * (arrowAt 0).k₃ ≤ (90869 / 1000000 : ℝ) :=
    widen (mul_bounds k12 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have s1k2 : (4279 / 20000 : ℝ) ≤ ((arrowAt 0).b₁ * (arrowAt 0).c₁) * (arrowAt 0).k₂ ∧
      ((arrowAt 0).b₁ * (arrowAt 0).c₁) * (arrowAt 0).k₂ ≤ (2677 / 12500 : ℝ) :=
    widen (mul_bounds s1 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have s1k3 : (33379 / 100000 : ℝ) ≤ ((arrowAt 0).b₁ * (arrowAt 0).c₁) * (arrowAt 0).k₃ ∧
      ((arrowAt 0).b₁ * (arrowAt 0).c₁) * (arrowAt 0).k₃ ≤ (33413 / 100000 : ℝ) :=
    widen (mul_bounds s1 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t2k1 : (17741 / 500000 : ℝ) ≤ ((arrowAt 0).b₂ * (-(arrowAt 0).c₂)) * (arrowAt 0).k₁ ∧
      ((arrowAt 0).b₂ * (-(arrowAt 0).c₂)) * (arrowAt 0).k₁ ≤ (7103 / 200000 : ℝ) :=
    widen (mul_bounds t2 hk1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t2k3 : (1539 / 1000000 : ℝ) ≤ ((arrowAt 0).b₂ * (-(arrowAt 0).c₂)) * (arrowAt 0).k₃ ∧
      ((arrowAt 0).b₂ * (-(arrowAt 0).c₂)) * (arrowAt 0).k₃ ≤ (7703 / 5000000 : ℝ) :=
    widen (mul_bounds t2 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t3k1 : (65671 / 100000 : ℝ) ≤ ((-(arrowAt 0).b₃) * (arrowAt 0).c₃) * (arrowAt 0).k₁ ∧
      ((-(arrowAt 0).b₃) * (arrowAt 0).c₃) * (arrowAt 0).k₁ ≤ (65711 / 100000 : ℝ) :=
    widen (mul_bounds t3 hk1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t3k2 : (18257 / 1000000 : ℝ) ≤ ((-(arrowAt 0).b₃) * (arrowAt 0).c₃) * (arrowAt 0).k₂ ∧
      ((-(arrowAt 0).b₃) * (arrowAt 0).c₃) * (arrowAt 0).k₂ ≤ (1827 / 100000 : ℝ) :=
    widen (mul_bounds t3 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have Ak123 : (30759 / 500000 : ℝ) ≤
      (((-(arrowAt 0).a) * (arrowAt 0).k₁) * (arrowAt 0).k₂) * (arrowAt 0).k₃ ∧
          (((-(arrowAt 0).a) * (arrowAt 0).k₁) * (arrowAt 0).k₂) * (arrowAt 0).k₃ ≤
              (3847 / 62500 : ℝ) :=
    widen (mul_bounds Ak12 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have s1k23 : (39193 / 1000000 : ℝ) ≤
      (((arrowAt 0).b₁ * (arrowAt 0).c₁) * (arrowAt 0).k₂) * (arrowAt 0).k₃ ∧
          (((arrowAt 0).b₁ * (arrowAt 0).c₁) * (arrowAt 0).k₂) * (arrowAt 0).k₃ ≤
              (39237 / 1000000 : ℝ) :=
    widen (mul_bounds s1k2 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t2k13 : (64999 / 10000000 : ℝ) ≤
      (((arrowAt 0).b₂ * (-(arrowAt 0).c₂)) * (arrowAt 0).k₁) * (arrowAt 0).k₃ ∧
          (((arrowAt 0).b₂ * (-(arrowAt 0).c₂)) * (arrowAt 0).k₁) * (arrowAt 0).k₃ ≤
              (16267 / 2500000 : ℝ) :=
    widen (mul_bounds t2k1 hk3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have t3k12 : (7711 / 100000 : ℝ) ≤
      (((-(arrowAt 0).b₃) * (arrowAt 0).c₃) * (arrowAt 0).k₁) * (arrowAt 0).k₂ ∧
          (((-(arrowAt 0).b₃) * (arrowAt 0).c₃) * (arrowAt 0).k₁) * (arrowAt 0).k₂ ≤
              (15433 / 200000 : ℝ) :=
    widen (mul_bounds t3k1 hk2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have ha1 : (13003 / 2500 : ℝ) ≤ (arrowAt 0).coef₁ ∧ (arrowAt 0).coef₁ ≤ (3251 / 625 : ℝ) := by
    simp only [Arrow.coef₁]
    constructor <;> linarith [hA.1, hA.2, hk1.1, hk1.2, hk2.1, hk2.2, hk3.1, hk3.2]
  have ha2 : (6737 / 2500 : ℝ) ≤ (arrowAt 0).coef₂ ∧ (arrowAt 0).coef₂ ≤ (13489 / 5000 : ℝ) := by
    simp only [Arrow.coef₂]
    constructor <;> linarith [Ak1.1, Ak1.2, Ak2.1, Ak2.2, Ak3.1, Ak3.2, k12.1, k12.2, k13.1,
        k13.2, k23.1, k23.2, s1.1, s1.2, t2.1, t2.2, t3.1, t3.2]
  have ha3 : (1411 / 1250 : ℝ) ≤ (arrowAt 0).coef₃ ∧ (arrowAt 0).coef₃ ≤ (11303 / 10000 : ℝ) := by
    simp only [Arrow.coef₃]
    constructor <;> linarith [Ak12.1, Ak12.2, Ak13.1, Ak13.2, Ak23.1, Ak23.2, k123.1, k123.2,
        s1k2.1, s1k2.2, s1k3.1, s1k3.2, t2k1.1, t2k1.2, t2k3.1, t2k3.2, t3k1.1, t3k1.2, t3k2.1,
            t3k2.2]
  have ha4 : (10589 / 100000 : ℝ) ≤ (arrowAt 0).coef₄ ∧ (arrowAt 0).coef₄ ≤ (2651 / 25000 : ℝ) := by
    simp only [Arrow.coef₄]
    constructor <;> linarith [Ak123.1, Ak123.2, s1k23.1, s1k23.2, t2k13.1, t2k13.2, t3k12.1,
        t3k12.2]
  have a12 : (1752 / 125 : ℝ) ≤ (arrowAt 0).coef₁ * (arrowAt 0).coef₂ ∧
      (arrowAt 0).coef₁ * (arrowAt 0).coef₂ ≤ (14033 / 1000 : ℝ) :=
    widen (mul_bounds ha1 ha2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have a123 : (15821 / 1000 : ℝ) ≤
      ((arrowAt 0).coef₁ * (arrowAt 0).coef₂) * (arrowAt 0).coef₃ ∧
          ((arrowAt 0).coef₁ * (arrowAt 0).coef₂) * (arrowAt 0).coef₃ ≤ (7931 / 500 : ℝ) :=
    widen (mul_bounds a12 ha3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have a33 : (12741 / 10000 : ℝ) ≤ (arrowAt 0).coef₃ * (arrowAt 0).coef₃ ∧
      (arrowAt 0).coef₃ * (arrowAt 0).coef₃ ≤ (1597 / 1250 : ℝ) :=
    widen (mul_bounds ha3 ha3 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have a11 : (6763 / 250 : ℝ) ≤ (arrowAt 0).coef₁ * (arrowAt 0).coef₁ ∧
      (arrowAt 0).coef₁ * (arrowAt 0).coef₁ ≤ (27057 / 1000 : ℝ) :=
    widen (mul_bounds ha1 ha1 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have a114 : (5729 / 2000 : ℝ) ≤ ((arrowAt 0).coef₁ * (arrowAt 0).coef₁) * (arrowAt 0).coef₄ ∧
      ((arrowAt 0).coef₁ * (arrowAt 0).coef₁) * (arrowAt 0).coef₄ ≤ (7173 / 2500 : ℝ) :=
    widen (mul_bounds a11 ha4 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hH : (5837 / 500 : ℝ) ≤ (arrowAt 0).hdet ∧ (arrowAt 0).hdet ≤ (2931 / 250 : ℝ) := by
    simp only [Arrow.hdet, hurwitz3]
    constructor <;> linarith [a123.1, a123.2, a33.1, a33.2, a114.1, a114.2]
  exact ⟨by linarith [ha3.1], by linarith [ha4.1], by linarith [hH.1]⟩


/-! ## H. A spectral Hopf candidate or a zero eigenvalue along the branch -/

/-- **`Δ₃ = 0` or `coef₄ = 0` along the branch (coefficient form).** Between `V = 0` (rest,
`I = 0`) and `V = 15` mV there is a branch voltage `V*` where either

* `Δ₃ = 0` with `coef₃, coef₄ > 0`, and for every `W ∈ [0, V*)` the Routh–Hurwitz conditions
  `coef₃, coef₄, Δ₃ > 0` hold, so `V*` is where they first fail; or
* `coef₄ = 0`, i.e. `0` is an eigenvalue. This alternative says nothing about `[0, V*)`, where the
  Routh–Hurwitz conditions may already have failed. -/
theorem exists_hdet_eq_zero_or_coef₄_eq_zero :
    ∃ V ∈ Ioo (0 : ℝ) 15,
      ((arrowAt V).hdet = 0 ∧ 0 < (arrowAt V).coef₃ ∧ 0 < (arrowAt V).coef₄ ∧
        ∀ W ∈ Ico 0 V, 0 < (arrowAt W).coef₃ ∧ 0 < (arrowAt W).coef₄ ∧ 0 < (arrowAt W).hdet) ∨
      (arrowAt V).coef₄ = 0 := by
  obtain ⟨c3, c4, cH⟩ := continuous_arrowAt
  obtain ⟨h03, h04, h0H⟩ := arrowAt_0_signs
  have h15H := arrowAt_15_hdet_neg
  have h154 := arrowAt_15_signs.2.2
  by_cases hA : ∀ V ∈ Icc (0 : ℝ) 15, 0 < (arrowAt V).coef₄
  · set S : Set ℝ := Icc 0 15 ∩ {V | (arrowAt V).hdet ≤ 0} with hS
    have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le cH continuous_const)
    have hSne : S.Nonempty := ⟨15, ⟨by norm_num, by norm_num⟩, h15H.le⟩
    have hSb : BddBelow S := ⟨0, fun V hV => hV.1.1⟩
    have hV₀S : sInf S ∈ S := hSc.csInf_mem hSne hSb
    set V₀ := sInf S with hV₀
    have hbelow : ∀ W ∈ Ico 0 V₀, 0 < (arrowAt W).hdet := by
      intro W hW
      by_contra h
      rw [not_lt] at h
      have : V₀ ≤ W := csInf_le hSb ⟨⟨hW.1, by linarith [hV₀S.1.2, hW.2]⟩, h⟩
      linarith [hW.2]
    have hV₀pos : 0 < V₀ := by
      rcases hV₀S.1.1.eq_or_lt with h | h
      · exfalso
        have h2 : (arrowAt V₀).hdet ≤ 0 := hV₀S.2
        rw [← h] at h2
        linarith
      · exact h
    have hH0 : (arrowAt V₀).hdet = 0 := by
      by_contra hne
      have hneg : (arrowAt V₀).hdet < 0 := lt_of_le_of_ne hV₀S.2 hne
      obtain ⟨W, hW, hWz⟩ := intermediate_value_Ioo' hV₀pos.le cH.continuousOn ⟨hneg, h0H⟩
      have hWz' : (arrowAt W).hdet = 0 := hWz
      have := hbelow W ⟨hW.1.le, hW.2⟩
      rw [hWz'] at this
      exact lt_irrefl _ this
    have hV₀lt : V₀ < 15 := by
      rcases hV₀S.1.2.eq_or_lt with h | h
      · rw [h] at hH0
        linarith
      · exact h
    have hH_nonneg : ∀ W ∈ Icc 0 V₀, 0 ≤ (arrowAt W).hdet := by
      intro W hW
      rcases hW.2.eq_or_lt with h | h
      · rw [h, hH0]
      · exact (hbelow W ⟨hW.1, h⟩).le
    have h3pos : ∀ W ∈ Icc 0 V₀, 0 < (arrowAt W).coef₃ := by
      intro W hW
      by_contra h
      rw [not_lt] at h
      obtain ⟨U, hU, hUz⟩ := intermediate_value_Icc' hW.1 c3.continuousOn ⟨h, h03.le⟩
      have hUz' : (arrowAt U).coef₃ = 0 := hUz
      have hU' : U ∈ Icc 0 V₀ := ⟨hU.1, hU.2.trans hW.2⟩
      have h4 := hA U ⟨hU'.1, by linarith [hU'.2]⟩
      have h1 := arrowAt_coef₁_pos U
      have hHU := hH_nonneg U hU'
      simp only [Arrow.hdet, hurwitz3, hUz'] at hHU
      nlinarith [mul_pos (mul_pos h1 h1) h4]
    refine ⟨V₀, ⟨hV₀pos, hV₀lt⟩, Or.inl ⟨hH0, h3pos V₀ ⟨hV₀pos.le, le_rfl⟩,
      hA V₀ ⟨hV₀pos.le, hV₀lt.le⟩, fun W hW => ⟨h3pos W ⟨hW.1, hW.2.le⟩,
        hA W ⟨hW.1, by linarith [hW.2]⟩, hbelow W hW⟩⟩⟩
  · simp only [not_forall, not_lt] at hA
    obtain ⟨V, hV, hV4⟩ := hA
    obtain ⟨U, hU, hUz⟩ := intermediate_value_Icc' hV.1 c4.continuousOn ⟨hV4, h04.le⟩
    have hUz' : (arrowAt U).coef₄ = 0 := hUz
    have hU0 : 0 < U := by
      rcases hU.1.eq_or_lt with h | h
      · rw [← h] at hUz'
        linarith
      · exact h
    have hU15 : U < 15 := by
      rcases (hU.2.trans hV.2).eq_or_lt with h | h
      · rw [h] at hUz'
        linarith
      · exact h
    exact ⟨U, ⟨hU0, hU15⟩, Or.inr hUz'⟩

/-- **Conditional decay at a branch point with a Hurwitz Jacobian.** For the current
`I = I∞(V)` there are `δ, K, α > 0` such that every solution of the squid system on `[0, ∞)`
starting within `δ` of `eqPoint V` satisfies `‖x t - eqPoint V‖ ≤ K e^{-α t} ‖x 0 - eqPoint V‖`.
Like `LinearizedStability.globalSolution_decay_of_hasFDerivAt`, which it specializes, this does
not assert that such solutions exist, so it is not by itself local exponential stability. -/
theorem eqPoint_globalSolution_decay {V : ℝ} (h : (jac squid (eqPoint V)).IsHurwitz) :
    ∃ δ K α : ℝ, 0 < δ ∧ 0 < K ∧ 0 < α ∧ ∀ x : ℝ → Fin 4 → ℝ,
      IsSolution (squidI (Iss V)) x → ‖x 0 - eqPoint V‖ < δ →
        ∀ t, 0 ≤ t → ‖x t - eqPoint V‖ ≤ K * exp (-(α * t)) * ‖x 0 - eqPoint V‖ :=
  MathlibExt.Analysis.ODE.LinearizedStability.globalSolution_decay_of_hasFDerivAt
    (field_eqPoint V) (hasFDerivAt_field (squidI (Iss V)) (eqPoint V)) h

/-- **Necessity on the branch.** If the Jacobian at a branch point has a nonzero purely imaginary
eigenvalue `i ω`, then `Δ₃ = 0` there. -/
theorem hdet_eq_zero_of_imaginary_eigenvalue {V ω : ℝ} (hω : ω ≠ 0)
    (h : Complex.I * ω ∈ spectrum ℂ ((jac squid (eqPoint V)).map (algebraMap ℝ ℂ))) :
    (arrowAt V).hdet = 0 := by
  rw [jac_eqPoint] at h
  exact (arrowAt V).hdet_eq_zero_of_mem_spectrum hω h

/-- **A spectral Hopf candidate or a zero eigenvalue on the equilibrium branch.** There is a
branch voltage `V* ∈ (0, 15)` mV, with applied current `I* = I∞(V*)` and equilibrium `eqPoint V*`
of the squid system with current `I*`, such that either

* the Jacobian there satisfies the spectral Hopf conditions `IsSpectralHopfCandidate ω` (a simple
  pair `± i ω`, `ω > 0`, and every other eigenvalue in the open left half-plane), and for every
  `W ∈ [0, V*)` the branch equilibrium with current `I∞(W)` has a Hurwitz Jacobian, so `V*` is
  the first branch voltage in `[0, 15]` where the Jacobian stops being Hurwitz; or
* `0` is an eigenvalue of the Jacobian at `eqPoint V*`, i.e. `I∞'(V*) = 0`
  (`zero_mem_spectrum_jac_iff`); this alternative says nothing about the branch below `V*`.

Neither transversality nor fold nondegeneracy is shown. `exists_spectral_hopf_candidate` shows
that the first alternative holds. -/
theorem exists_spectral_hopf_candidate_or_zero_eigenvalue :
    ∃ V ∈ Ioo (0 : ℝ) 15, field (squidI (Iss V)) (eqPoint V) = 0 ∧
      (((∃ ω, (arrowAt V).IsSpectralHopfCandidate ω) ∧ jac squid (eqPoint V) = (arrowAt V).mat ∧
          ∀ W ∈ Ico 0 V, (jac squid (eqPoint W)).IsHurwitz) ∨
        (0 : ℂ) ∈ spectrum ℂ ((jac squid (eqPoint V)).map (algebraMap ℝ ℂ))) := by
  obtain ⟨V, hV, hcase⟩ := exists_hdet_eq_zero_or_coef₄_eq_zero
  refine ⟨V, hV, field_eqPoint V, ?_⟩
  rcases hcase with ⟨hH, h3, h4, hW⟩ | h4
  · refine Or.inl ⟨⟨_, (arrowAt V).isSpectralHopfCandidate_of_hdet_eq_zero
      (arrowAt_coef₁_pos V) h3 h4 hH⟩, jac_eqPoint V, fun W hWm => ?_⟩
    obtain ⟨w3, w4, wH⟩ := hW W hWm
    rw [jac_eqPoint]
    exact (arrowAt W).isHurwitz_of_hdet_pos (arrowAt_coef₁_pos W) w3 w4 wH
  · refine Or.inr ?_
    rw [jac_eqPoint, Arrow.zero_mem_spectrum_iff]
    exact h4


/-! ## I. The zero-eigenvalue alternative is a critical point of the steady-state I–V curve -/

/-- `HodgkinHuxley.hasDerivAt_steady` in the form of the Jacobian entries:
`y∞' = (α' (1 - y∞) - β' y∞) / (α + β)`. -/
private theorem hasDerivAt_steady_jac {α β : ℝ → ℝ} (hα : ContDiff ℝ 1 α)
    (hβ : ContDiff ℝ 1 β) (hα0 : ∀ V, 0 < α V) (hβ0 : ∀ V, 0 < β V) (V : ℝ) :
    HasDerivAt (steady α β)
      ((deriv α V * (1 - steady α β V) - deriv β V * steady α β V) / (α V + β V)) V := by
  have ha := (hα0 V).ne'
  have hb := (hβ0 V).ne'
  have hs := (add_pos (hα0 V) (hβ0 V)).ne'
  refine (hasDerivAt_steady (hα.differentiable one_ne_zero V).hasDerivAt
    (hβ.differentiable one_ne_zero V).hasDerivAt (hα0 V) (hβ0 V)).congr_deriv ?_
  simp only [steady]
  field_simp
  ring

/-- The constant coefficient of the characteristic quartic on the branch is
`coef₄ = k₁ k₂ k₃ · I∞'(V)`. So `0` is an eigenvalue at `eqPoint V` iff `I∞'(V) = 0`. -/
theorem coef₄_eq_deriv_Iss (V : ℝ) :
    (arrowAt V).coef₄ = (arrowAt V).k₁ * (arrowAt V).k₂ * (arrowAt V).k₃ * deriv Iss V := by
  have hm := hasDerivAt_steady_jac contDiff_alphaM contDiff_betaM alphaM_pos betaM_pos V
  have hh := hasDerivAt_steady_jac contDiff_alphaH contDiff_betaH alphaH_pos betaH_pos V
  have hn := hasDerivAt_steady_jac contDiff_alphaN contDiff_betaN alphaN_pos betaN_pos V
  have h : HasDerivAt Iss _ V :=
    (((((hm.pow 3).const_mul 120).mul hh).mul ((hasDerivAt_id' V).sub_const 115)).add
      (((hn.pow 4).const_mul 36).mul ((hasDerivAt_id' V).sub_const (-12)))).add
      (((hasDerivAt_id' V).sub_const squidEL).const_mul (3 / 10))
  have k1 := arrowAt_k₁_pos V
  have k2 := arrowAt_k₂_pos V
  have k3 := arrowAt_k₃_pos V
  rw [h.deriv]
  simp only [Arrow.coef₄, arrowAt, mInf, hInf, nInf, Pi.mul_apply, Pi.pow_apply] at k1 k2 k3 ⊢
  have k1' := k1.ne'
  have k2' := k2.ne'
  have k3' := k3.ne'
  norm_num
  field_simp
  ring

/-- `0` is an eigenvalue of the Jacobian at `eqPoint V` iff `I∞'(V) = 0`. -/
theorem zero_mem_spectrum_jac_iff (V : ℝ) :
    (0 : ℂ) ∈ spectrum ℂ ((jac squid (eqPoint V)).map (algebraMap ℝ ℂ)) ↔ deriv Iss V = 0 := by
  rw [jac_eqPoint, Arrow.zero_mem_spectrum_iff, coef₄_eq_deriv_Iss]
  have := mul_pos (mul_pos (arrowAt_k₁_pos V) (arrowAt_k₂_pos V)) (arrowAt_k₃_pos V)
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left this.ne'
  · intro h
    rw [h, mul_zero]

/-- **The spectral Hopf candidate, given monotonicity of the I–V curve on `[0, 15]`.** If
`I∞' > 0` on `[0, 15]` mV (the steady-state current is increasing there), the zero-eigenvalue
alternative of `exists_spectral_hopf_candidate_or_zero_eigenvalue` cannot occur: there is
`V* ∈ (0, 15)` with the spectral Hopf conditions at the equilibrium for
`I* = I∞(V*) ∈ (0, I∞(15))`, and the branch equilibria for every `I = I∞(W)`, `W ∈ [0, V*)`,
have Hurwitz Jacobians. -/
theorem exists_spectral_hopf_candidate_of_deriv_Iss_pos
    (hmono : ∀ V ∈ Icc (0 : ℝ) 15, 0 < deriv Iss V) :
    ∃ V ∈ Ioo (0 : ℝ) 15, Iss V ∈ Ioo 0 (Iss 15) ∧ field (squidI (Iss V)) (eqPoint V) = 0 ∧
      (∃ ω, (arrowAt V).IsSpectralHopfCandidate ω) ∧
        ∀ W ∈ Ico 0 V, (jac squid (eqPoint W)).IsHurwitz := by
  obtain ⟨V, hV, heq, hcase⟩ := exists_spectral_hopf_candidate_or_zero_eigenvalue
  have hsm : StrictMonoOn Iss (Icc 0 15) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 15) continuous_Iss.continuousOn fun x hx =>
      hmono x (interior_subset hx)
  have hI : Iss V ∈ Ioo 0 (Iss 15) := by
    refine ⟨?_, hsm ⟨hV.1.le, hV.2.le⟩ ⟨by norm_num, by norm_num⟩ hV.2⟩
    rw [← steadyCurrent_squid_zero]
    exact hsm ⟨le_rfl, by norm_num⟩ ⟨hV.1.le, hV.2.le⟩ hV.1
  rcases hcase with ⟨hH, -, hW⟩ | h0
  · exact ⟨V, hV, hI, heq, hH, hW⟩
  · exact absurd ((zero_mem_spectrum_jac_iff V).1 h0) (hmono V ⟨hV.1.le, hV.2.le⟩).ne'

/-- **The squid branch first stops being Hurwitz at a spectral Hopf candidate.** T256's
`steadyCurrentDeriv_squid_pos` gives `I∞' > 0` on `[-12, 115]` mV, which is the hypothesis of
`exists_spectral_hopf_candidate_of_deriv_Iss_pos`. So there is `V* ∈ (0, 15)` mV such that the
branch equilibria for the currents `I∞(W)`, `W ∈ [0, V*)`, have Hurwitz Jacobians and the
equilibrium for `I* = I∞(V*) ∈ (0, I∞(15))` satisfies the spectral Hopf conditions; in
particular `0` is not an eigenvalue there. Transversality is not shown, so `V*` is a Hopf
candidate, not a proved Hopf bifurcation. -/
theorem exists_spectral_hopf_candidate :
    ∃ V ∈ Ioo (0 : ℝ) 15, Iss V ∈ Ioo 0 (Iss 15) ∧ field (squidI (Iss V)) (eqPoint V) = 0 ∧
      (∃ ω, (arrowAt V).IsSpectralHopfCandidate ω) ∧
        ∀ W ∈ Ico 0 V, (jac squid (eqPoint W)).IsHurwitz :=
  exists_spectral_hopf_candidate_of_deriv_Iss_pos fun V hV => by
    change 0 < deriv (steadyCurrent squid) V
    rw [(hasDerivAt_steadyCurrent squid V).deriv]
    exact steadyCurrentDeriv_squid_pos ⟨by linarith [hV.1], by linarith [hV.2]⟩

end MathlibExt.Biology.Biophysics.HodgkinHuxleyCurrent
