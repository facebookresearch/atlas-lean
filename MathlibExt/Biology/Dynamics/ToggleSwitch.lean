/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import MathlibExt.LinearAlgebra.Matrix.MMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Gardner–Collins–Cantor genetic toggle switch

Two repressors `U` and `V` each repress the other's promoter. In the nondimensional form of
Gardner, Cantor and Collins (2000), with time measured in units of the (common) degradation
time, the concentrations `u = [U]` and `v = [V]` obey

  `du/dt = α₁ / (1 + v ^ β) - u`,
  `dv/dt = α₂ / (1 + u ^ γ) - v`,

with

* `α₁ > 0`, `α₂ > 0`: effective synthesis rates of `U` and `V`;
* `β, γ ∈ ℕ`, `β, γ ≥ 1`: Hill (cooperativity) exponents of repression of `U` by `V` and of
  `V` by `U`;
* state `(u, v) ∈ [0, ∞)²`.

This file fixes exactly this form (`uDot`, `vDot`, Hill repression `hill α n x = α / (1 + x ^ n)`).
An equilibrium is a point of the closed positive quadrant where both right-hand sides vanish
(`IsEquilibrium`).

## Linearization (every `β, γ`)

The Jacobian (`jacobian`, entries justified by `hasDerivAt_uDot_u` … `hasDerivAt_vDot_v`) is
`!![-1, h₁; h₂, -1]` with `h₁ = ∂_v (α₁ / (1 + v^β)) ≤ 0` and `h₂ = ∂_u (α₂ / (1 + u^γ)) ≤ 0`.
With the loop gain `P = h₁ h₂ ≥ 0` its complex spectrum is exactly `{-1 + √P, -1 - √P}`
(`eigenvalues_eq`). Hence, at a point of the quadrant, the Jacobian is Hurwitz
(`Matrix.IsHurwitz`: all eigenvalues have negative real part) iff `P < 1`, has saddle spectrum
(one positive, one negative eigenvalue, `HasSaddleSpectrum`) iff `P > 1`, and has the eigenvalue
`0` iff `P = 1`, which is exactly parallel nullcline directions (`nullclineTangentsParallel_iff`).
At an equilibrium these say that the equilibrium is linearly stable, a saddle, or a point where
the nullclines are tangent (`NullclinesTangent`, `nullclinesTangent_iff_of_isEquilibrium`); the
Jacobian predicates themselves do not require an equilibrium.

## Equilibria, saddle-node and bistability (`β = 1`, `γ = 2`)

Write `a = α₁`, `b = α₂`. Eliminating `v = b / (1 + u²)`, the equilibria are in bijection with the
real roots of the cubic `cubic a b u = u³ - a u² + (1 + b) u - a`, all of which are positive
(`isEquilibrium_iff`), and `1 - P = u · cubic' u / (a (1 + u²))` at an equilibrium. Hence:

* `ncard_equilibria_mem`: there are 1, 2 or 3 equilibria;
* `ncard_equilibria_eq_two_iff`: there are exactly 2 iff some equilibrium has tangent nullclines
  (a double root of the cubic, `P = 1`, eigenvalue `0`) and is not the cusp `3u = a`;
* `saddleNode_collision`: at such a tangency `(u₀, b₀)` two equilibria collide: for `b` on one side
  of `b₀` (fixed by the sign of `3 u₀ - a`) and close to `b₀` there are two equilibria
  `u₁ < u₀ < u₂` arbitrarily close to `u₀`, while on the other side a whole neighbourhood of `u₀`
  is free of equilibria (a saddle-node bifurcation in `b`);
* `three_equilibria`: with exactly three equilibria `u₁ < u₂ < u₃` (so `v₁ > v₂ > v₃`), the two
  outer ones are linearly stable and the middle one is a saddle;
* `ncard_equilibria_eq_three_iff_bistable`: exactly three equilibria iff two distinct linearly
  stable equilibria exist (bistability).

Other Hill exponents (the equilibrium polynomial then has degree `γ + 1` for `β = 1` and degree 5
for `β = γ = 2`; the mirror case `β = 2`, `γ = 1` follows by swapping `u` and `v` but is not
stated), the global phase portrait (basins, separatrix = stable manifold of the saddle) and the
continuous-time dynamics beyond linearization are not treated.

## References

* T. S. Gardner, C. R. Cantor and J. J. Collins, *Construction of a genetic toggle switch in
  Escherichia coli*, Nature 403 (2000) 339–342.
* S. H. Strogatz, *Nonlinear Dynamics and Chaos*, 2nd ed., Westview (2015), §3.1 and §8.1.
-/

@[expose] public section

open Set

namespace MathlibExt.Biology.Dynamics.ToggleSwitch

/-! ### The model -/

/-- Hill repression `α / (1 + x ^ n)`. -/
noncomputable def hill (α : ℝ) (n : ℕ) (x : ℝ) : ℝ := α / (1 + x ^ n)

/-- The derivative of `hill α n` on `x ≥ 0` (`hasDerivAt_hill`): `-α n x^(n-1) / (1 + x^n)²`. -/
noncomputable def hillDeriv (α : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  -(α * n * x ^ (n - 1)) / (1 + x ^ n) ^ 2

/-- Right-hand side of the `u` equation: `du/dt = α₁ / (1 + v ^ β) - u`. -/
noncomputable def uDot (α₁ : ℝ) (β : ℕ) (u v : ℝ) : ℝ := hill α₁ β v - u

/-- Right-hand side of the `v` equation: `dv/dt = α₂ / (1 + u ^ γ) - v`. -/
noncomputable def vDot (α₂ : ℝ) (γ : ℕ) (u v : ℝ) : ℝ := hill α₂ γ u - v

/-- An equilibrium of the toggle switch in the closed positive quadrant. -/
def IsEquilibrium (α₁ α₂ : ℝ) (β γ : ℕ) (u v : ℝ) : Prop :=
  0 ≤ u ∧ 0 ≤ v ∧ uDot α₁ β u v = 0 ∧ vDot α₂ γ u v = 0

/-- The set of equilibria. -/
def equilibria (α₁ α₂ : ℝ) (β γ : ℕ) : Set (ℝ × ℝ) :=
  {p | IsEquilibrium α₁ α₂ β γ p.1 p.2}

/-- The Jacobian of `(uDot, vDot)` at a point `(u, v)` of the closed quadrant (entries justified
by `hasDerivAt_uDot_u` … `hasDerivAt_vDot_v`); the formula is defined for all real `(u, v)`. -/
noncomputable def jacobian (α₁ α₂ : ℝ) (β γ : ℕ) (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1, hillDeriv α₁ β v; hillDeriv α₂ γ u, -1]

/-- The loop gain `P`: the product of the two off-diagonal Jacobian entries. -/
noncomputable def loopGain (α₁ α₂ : ℝ) (β γ : ℕ) (u v : ℝ) : ℝ :=
  hillDeriv α₁ β v * hillDeriv α₂ γ u

/-- The eigenvalues of the linearization: the complex spectrum of the Jacobian. -/
noncomputable def eigenvalues (α₁ α₂ : ℝ) (β γ : ℕ) (u v : ℝ) : Set ℂ :=
  spectrum ℂ ((jacobian α₁ α₂ β γ u v).map (algebraMap ℝ ℂ))

/-- The Jacobian at `(u, v)` has **saddle spectrum**: one eigenvalue with positive and one with
negative real part. At an equilibrium this makes the equilibrium a saddle; the predicate itself
only looks at the Jacobian and does not require `(u, v)` to be an equilibrium. -/
def HasSaddleSpectrum (α₁ α₂ : ℝ) (β γ : ℕ) (u v : ℝ) : Prop :=
  (∃ μ ∈ eigenvalues α₁ α₂ β γ u v, 0 < μ.re) ∧ ∃ μ ∈ eigenvalues α₁ α₂ β γ u v, μ.re < 0

/-- The nullcline directions at `(u, v)` are parallel: the tangent vector `(∂_v hill, 1)` of the
`u`-nullcline `u = α₁ / (1 + v ^ β)` at height `v` and the tangent vector `(1, ∂_u hill)` of the
`v`-nullcline `v = α₂ / (1 + u ^ γ)` at abscissa `u` are parallel. This does not require `(u, v)`
to lie on either nullcline; `NullclinesTangent` adds that. -/
def NullclineTangentsParallel (α₁ α₂ : ℝ) (β γ : ℕ) (u v : ℝ) : Prop :=
  !![hillDeriv α₁ β v, 1; 1, hillDeriv α₂ γ u].det = 0

/-- The nullclines are **tangent** at `(u, v)`: the point lies on both nullclines (`uDot = 0` and
`vDot = 0`) and their tangent vectors there are parallel (`NullclineTangentsParallel`). -/
def NullclinesTangent (α₁ α₂ : ℝ) (β γ : ℕ) (u v : ℝ) : Prop :=
  uDot α₁ β u v = 0 ∧ vDot α₂ γ u v = 0 ∧ NullclineTangentsParallel α₁ α₂ β γ u v

theorem hasDerivAt_hill (α : ℝ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (hill α n) (hillDeriv α n x) x := by
  have hne : (1 + x ^ n) ≠ 0 := by positivity
  have h := HasDerivAt.div (hasDerivAt_const x α)
    (HasDerivAt.add (hasDerivAt_const x (1 : ℝ)) (hasDerivAt_pow n x)) hne
  convert h using 1
  · funext y
    simp [hill, Pi.add_def]
  · simp only [hillDeriv, Pi.add_apply]
    field_simp
    ring

theorem hasDerivAt_uDot_u (α₁ α₂ : ℝ) (β γ : ℕ) (u v : ℝ) :
    HasDerivAt (fun u ↦ uDot α₁ β u v) (jacobian α₁ α₂ β γ u v 0 0) u := by
  simpa [uDot, jacobian, Pi.sub_def] using
    HasDerivAt.sub (hasDerivAt_const u (hill α₁ β v)) (hasDerivAt_id u)

theorem hasDerivAt_uDot_v (α₁ α₂ : ℝ) (β γ : ℕ) (u : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    HasDerivAt (fun v ↦ uDot α₁ β u v) (jacobian α₁ α₂ β γ u v 0 1) v := by
  simpa [uDot, jacobian, Pi.sub_def] using
    HasDerivAt.sub (hasDerivAt_hill α₁ β hv) (hasDerivAt_const v u)

theorem hasDerivAt_vDot_u (α₁ α₂ : ℝ) (β γ : ℕ) {u : ℝ} (hu : 0 ≤ u) (v : ℝ) :
    HasDerivAt (fun u ↦ vDot α₂ γ u v) (jacobian α₁ α₂ β γ u v 1 0) u := by
  simpa [vDot, jacobian, Pi.sub_def] using
    HasDerivAt.sub (hasDerivAt_hill α₂ γ hu) (hasDerivAt_const u v)

theorem hasDerivAt_vDot_v (α₁ α₂ : ℝ) (β γ : ℕ) (u v : ℝ) :
    HasDerivAt (fun v ↦ vDot α₂ γ u v) (jacobian α₁ α₂ β γ u v 1 1) v := by
  simpa [vDot, jacobian, Pi.sub_def] using
    HasDerivAt.sub (hasDerivAt_const v (hill α₂ γ u)) (hasDerivAt_id v)

theorem hillDeriv_nonpos {α : ℝ} (n : ℕ) {x : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ x) :
    hillDeriv α n x ≤ 0 := by
  unfold hillDeriv
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have : 0 ≤ α * n * x ^ (n - 1) := by positivity
  linarith

theorem loopGain_nonneg {α₁ α₂ : ℝ} (β γ : ℕ) {u v : ℝ} (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ loopGain α₁ α₂ β γ u v :=
  mul_nonneg_of_nonpos_of_nonpos (hillDeriv_nonpos β hα₁ hv) (hillDeriv_nonpos γ hα₂ hu)

/-! ### Linearization -/

section Linearization

variable {α₁ α₂ : ℝ} {β γ : ℕ} {u v : ℝ}

/-- The eigenvalues of the toggle-switch linearization are exactly `-1 ± √P`. -/
theorem eigenvalues_eq (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    eigenvalues α₁ α₂ β γ u v =
      {((-1 + √(loopGain α₁ α₂ β γ u v) : ℝ) : ℂ), ((-1 - √(loopGain α₁ α₂ β γ u v) : ℝ) : ℂ)} := by
  have hP := loopGain_nonneg β γ hα₁ hα₂ hu hv
  set s := √(loopGain α₁ α₂ β γ u v) with hs_def
  have hs : (s : ℂ) ^ 2 = (hillDeriv α₁ β v : ℂ) * hillDeriv α₂ γ u := by
    rw [← Complex.ofReal_pow, hs_def, Real.sq_sqrt hP, loopGain, Complex.ofReal_mul]
  ext μ
  rw [eigenvalues, Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_fin_two]
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Matrix.trace_fin_two,
    Matrix.det_fin_two, Matrix.map_apply, jacobian, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Complex.coe_algebraMap, mem_insert_iff, mem_singleton_iff]
  push_cast
  constructor
  · intro h
    have h2 : (μ - (-1 + s)) * (μ - (-1 - s)) = 0 := by linear_combination h - hs
    rcases mul_eq_zero.1 h2 with h3 | h3
    · left; linear_combination h3
    · right; linear_combination h3
  · rintro (rfl | rfl) <;> linear_combination hs

theorem isHurwitz_jacobian_iff (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (jacobian α₁ α₂ β γ u v).IsHurwitz ↔ loopGain α₁ α₂ β γ u v < 1 := by
  have hP := loopGain_nonneg β γ hα₁ hα₂ hu hv
  have hs := Real.sqrt_nonneg (loopGain α₁ α₂ β γ u v)
  change (∀ μ ∈ eigenvalues α₁ α₂ β γ u v, μ.re < 0) ↔ _
  simp only [eigenvalues_eq hα₁ hα₂ hu hv, mem_insert_iff, mem_singleton_iff,
    forall_eq_or_imp, forall_eq, Complex.ofReal_re]
  constructor
  · rintro ⟨h, -⟩
    have : √(loopGain α₁ α₂ β γ u v) < 1 := by linarith
    simpa using (Real.sqrt_lt' one_pos).1 this
  · intro h
    exact ⟨by linarith [(Real.sqrt_lt' one_pos).2 (by simpa using h)], by linarith⟩

theorem hasSaddleSpectrum_iff (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    HasSaddleSpectrum α₁ α₂ β γ u v ↔ 1 < loopGain α₁ α₂ β γ u v := by
  have hP := loopGain_nonneg β γ hα₁ hα₂ hu hv
  have hs := Real.sqrt_nonneg (loopGain α₁ α₂ β γ u v)
  simp only [HasSaddleSpectrum, eigenvalues_eq hα₁ hα₂ hu hv, mem_insert_iff, mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, Complex.ofReal_re]
  constructor
  · rintro ⟨h | h, -⟩
    · simpa using (Real.lt_sqrt zero_le_one).1 (by linarith)
    · linarith
  · intro h
    exact ⟨Or.inl (by linarith [(Real.lt_sqrt zero_le_one).2 (by simpa using h)]),
      Or.inr (by linarith)⟩

theorem zero_mem_eigenvalues_iff (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ∈ eigenvalues α₁ α₂ β γ u v ↔ loopGain α₁ α₂ β γ u v = 1 := by
  have hP := loopGain_nonneg β γ hα₁ hα₂ hu hv
  have hs := Real.sqrt_nonneg (loopGain α₁ α₂ β γ u v)
  rw [eigenvalues_eq hα₁ hα₂ hu hv]
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (h | h)
    · have h' : -1 + √(loopGain α₁ α₂ β γ u v) = 0 := by exact_mod_cast h.symm
      have : √(loopGain α₁ α₂ β γ u v) = 1 := by linarith
      rwa [Real.sqrt_eq_one] at this
    · have h' : -1 - √(loopGain α₁ α₂ β γ u v) = 0 := by exact_mod_cast h.symm
      linarith
  · intro h
    left
    rw [h, Real.sqrt_one]
    norm_num

theorem nullclineTangentsParallel_iff :
    NullclineTangentsParallel α₁ α₂ β γ u v ↔ loopGain α₁ α₂ β γ u v = 1 := by
  simp only [NullclineTangentsParallel, Matrix.det_fin_two_of, loopGain, mul_one]
  exact sub_eq_zero

/-- At an equilibrium the nullclines are tangent iff the loop gain is `1`, i.e. iff `0` is an
eigenvalue of the Jacobian (`zero_mem_eigenvalues_iff`). -/
theorem nullclinesTangent_iff_of_isEquilibrium (h : IsEquilibrium α₁ α₂ β γ u v) :
    NullclinesTangent α₁ α₂ β γ u v ↔ loopGain α₁ α₂ β γ u v = 1 := by
  rw [NullclinesTangent, ← nullclineTangentsParallel_iff]
  exact ⟨fun h' => h'.2.2, fun h' => ⟨h.2.2.1, h.2.2.2, h'⟩⟩

end Linearization

/-! ### The case `β = 1`, `γ = 2` -/

section Cubic

variable {a b : ℝ}

/-- The equilibrium cubic `u³ - a u² + (1 + b) u - a` of the `β = 1`, `γ = 2` toggle switch. -/
def cubic (a b u : ℝ) : ℝ := u ^ 3 - a * u ^ 2 + (1 + b) * u - a

/-- The derivative of `cubic a b`. -/
def cubicDeriv (a b u : ℝ) : ℝ := 3 * u ^ 2 - 2 * a * u + (1 + b)

theorem pos_of_cubic_eq_zero (ha : 0 < a) (hb : 0 < b) {u : ℝ} (h : cubic a b u = 0) :
    0 < u := by
  by_contra hu
  push Not at hu
  unfold cubic at h
  nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (neg_nonneg.2 hu)]

theorem continuous_cubic (a b : ℝ) : Continuous (cubic a b) := by
  unfold cubic
  fun_prop

theorem exists_cubic_eq_zero (ha : 0 < a) (hb : 0 < b) : ∃ u, cubic a b u = 0 := by
  have h0 : cubic a b 0 ≤ 0 := by simp [cubic]; linarith
  have h1 : 0 ≤ cubic a b (a + 1) := by
    simp only [cubic]
    nlinarith [sq_nonneg (a + 1)]
  obtain ⟨u, -, hu⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ a + 1)
    (continuous_cubic a b).continuousOn ⟨h0, h1⟩
  exact ⟨u, hu⟩

/-- Equilibria of the `β = 1`, `γ = 2` toggle switch are the points `(u, b / (1 + u²))` with
`u` a root of `cubic a b`. -/
theorem isEquilibrium_iff (ha : 0 < a) (hb : 0 < b) {u v : ℝ} :
    IsEquilibrium a b 1 2 u v ↔ cubic a b u = 0 ∧ v = b / (1 + u ^ 2) := by
  have hu2 : 0 < 1 + u ^ 2 := by positivity
  constructor
  · rintro ⟨hu, hv, h1, h2⟩
    simp only [uDot, vDot, hill, pow_one, sub_eq_zero] at h1 h2
    have hv1 : 0 < 1 + v := by linarith
    rw [div_eq_iff hv1.ne'] at h1
    refine ⟨?_, h2.symm⟩
    rw [div_eq_iff hu2.ne'] at h2
    unfold cubic
    linear_combination (-(u ^ 2) - 1) * h1 + u * h2
  · rintro ⟨h, rfl⟩
    have hu := pos_of_cubic_eq_zero ha hb h
    refine ⟨hu.le, by positivity, ?_, ?_⟩
    · simp only [uDot, hill, pow_one, sub_eq_zero]
      have : 0 < 1 + b / (1 + u ^ 2) := by positivity
      rw [div_eq_iff this.ne']
      field_simp
      unfold cubic at h
      linear_combination -h
    · simp [vDot, hill]

/-- At an equilibrium, `(1 - P) · a (1 + u²) = u · cubic' u`. -/
theorem one_sub_loopGain_mul (ha : 0 < a) (hb : 0 < b) {u v : ℝ}
    (h : IsEquilibrium a b 1 2 u v) :
    (1 - loopGain a b 1 2 u v) * (a * (1 + u ^ 2)) = u * cubicDeriv a b u := by
  obtain ⟨hc, rfl⟩ := (isEquilibrium_iff ha hb).1 h
  have hu := pos_of_cubic_eq_zero ha hb hc
  have hu2 : 0 < 1 + u ^ 2 := by positivity
  have hv1 : 0 < 1 + b / (1 + u ^ 2) := by positivity
  have hv1' : 1 + b / (1 + u ^ 2) = (1 + u ^ 2 + b) / (1 + u ^ 2) := by field_simp
  have hb' : (1 + u ^ 2 + b) ≠ 0 := by positivity
  simp only [loopGain, hillDeriv, pow_one, Nat.cast_one, Nat.cast_ofNat, Nat.sub_self, pow_zero,
    mul_one, Nat.add_one_sub_one, hv1']
  field_simp
  unfold cubic at hc
  unfold cubicDeriv
  have ha' : a = (u ^ 3 + (1 + b) * u) / (1 + u ^ 2) := by
    field_simp
    linear_combination -hc
  subst ha'
  field_simp
  ring

theorem isHurwitz_jacobian_iff_cubicDeriv (ha : 0 < a) (hb : 0 < b) {u v : ℝ}
    (h : IsEquilibrium a b 1 2 u v) :
    (jacobian a b 1 2 u v).IsHurwitz ↔ 0 < cubicDeriv a b u := by
  have hu := pos_of_cubic_eq_zero ha hb ((isEquilibrium_iff ha hb).1 h).1
  have hc : 0 < a * (1 + u ^ 2) := by positivity
  have key := one_sub_loopGain_mul ha hb h
  rw [isHurwitz_jacobian_iff ha.le hb.le h.1 h.2.1, ← sub_pos,
    ← mul_pos_iff_of_pos_right hc, key, mul_pos_iff_of_pos_left hu]

theorem hasSaddleSpectrum_iff_cubicDeriv (ha : 0 < a) (hb : 0 < b) {u v : ℝ}
    (h : IsEquilibrium a b 1 2 u v) :
    HasSaddleSpectrum a b 1 2 u v ↔ cubicDeriv a b u < 0 := by
  have hu := pos_of_cubic_eq_zero ha hb ((isEquilibrium_iff ha hb).1 h).1
  have hc : 0 < a * (1 + u ^ 2) := by positivity
  have key := one_sub_loopGain_mul ha hb h
  rw [hasSaddleSpectrum_iff ha.le hb.le h.1 h.2.1, ← sub_neg]
  constructor
  · intro h1
    by_contra h2
    push Not at h2
    nlinarith [mul_nonneg hu.le h2, mul_neg_of_neg_of_pos h1 hc]
  · intro h1
    by_contra h2
    push Not at h2
    nlinarith [mul_nonneg h2 hc.le, mul_neg_of_pos_of_neg hu h1]

theorem nullclinesTangent_iff_cubicDeriv (ha : 0 < a) (hb : 0 < b) {u v : ℝ}
    (h : IsEquilibrium a b 1 2 u v) :
    NullclinesTangent a b 1 2 u v ↔ cubicDeriv a b u = 0 := by
  have hu := pos_of_cubic_eq_zero ha hb ((isEquilibrium_iff ha hb).1 h).1
  have hc : 0 < a * (1 + u ^ 2) := by positivity
  have key := one_sub_loopGain_mul ha hb h
  rw [nullclinesTangent_iff_of_isEquilibrium h]
  constructor
  · intro hP
    rw [hP, sub_self, zero_mul] at key
    exact (mul_eq_zero.1 key.symm).resolve_left hu.ne'
  · intro hD
    rw [hD, mul_zero] at key
    linarith [(mul_eq_zero.1 key).resolve_right hc.ne']

/-- Two distinct roots `r, s` of `cubic a b` determine the third, `a - r - s` (Vieta). -/
theorem cubic_eq_of_roots {r s : ℝ} (hr : cubic a b r = 0) (hs : cubic a b s = 0) (hrs : r ≠ s)
    (u : ℝ) :
    cubic a b u = (u - r) * (u - s) * (u - (a - r - s)) ∧
      cubicDeriv a b u = (u - r) * (u - s) + (u - s) * (u - (a - r - s)) +
        (u - (a - r - s)) * (u - r) := by
  have h3 : r ^ 2 + r * s + s ^ 2 - a * (r + s) + (1 + b) = 0 := by
    have : (r - s) * (r ^ 2 + r * s + s ^ 2 - a * (r + s) + (1 + b)) = 0 := by
      unfold cubic at hr hs
      linear_combination hr - hs
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hrs)
  unfold cubic at hr
  unfold cubic cubicDeriv
  constructor
  · linear_combination (u - r) * h3 + hr
  · linear_combination h3

/-- A root `r` with `cubic' r = 0` is a double root: `cubic a b u = (u - r)² (u - (a - 2r))`. -/
theorem cubic_eq_of_double_root {r : ℝ} (hr : cubic a b r = 0) (hr' : cubicDeriv a b r = 0)
    (u : ℝ) : cubic a b u = (u - r) ^ 2 * (u - (a - 2 * r)) := by
  unfold cubic at hr ⊢
  unfold cubicDeriv at hr'
  linear_combination hr + (u - r) * hr'

/-- The equilibria are the image of the root set of the cubic. -/
theorem equilibria_eq_image (ha : 0 < a) (hb : 0 < b) :
    equilibria a b 1 2 = (fun u ↦ (u, b / (1 + u ^ 2))) '' {u | cubic a b u = 0} := by
  ext ⟨u, v⟩
  simp only [equilibria, mem_ofPred_eq, isEquilibrium_iff ha hb, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨u, h, rfl, rfl⟩
  · rintro ⟨w, hw, rfl, rfl⟩
    exact ⟨hw, rfl⟩

theorem ncard_equilibria (ha : 0 < a) (hb : 0 < b) :
    (equilibria a b 1 2).ncard = {u | cubic a b u = 0}.ncard := by
  rw [equilibria_eq_image ha hb]
  exact ncard_image_of_injective _ fun x y h ↦ (Prod.mk.inj h).1

/-- The root set of the cubic, given two distinct roots, is contained in the three Vieta roots. -/
theorem roots_subset {r s : ℝ} (hr : cubic a b r = 0) (hs : cubic a b s = 0) (hrs : r ≠ s) :
    {u | cubic a b u = 0} = {r, s, a - r - s} := by
  ext u
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  rw [(cubic_eq_of_roots hr hs hrs u).1]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (Or.inl (sub_eq_zero.1 h))
    · exact Or.inr (Or.inr (sub_eq_zero.1 h))
  · rintro (rfl | rfl | rfl) <;> ring

/-- **Number of equilibria.** The `β = 1`, `γ = 2` toggle switch has 1, 2 or 3 equilibria. -/
theorem ncard_equilibria_mem (ha : 0 < a) (hb : 0 < b) :
    (equilibria a b 1 2).ncard ∈ ({1, 2, 3} : Set ℕ) := by
  rw [ncard_equilibria ha hb]
  obtain ⟨r, hr⟩ := exists_cubic_eq_zero ha hb
  by_cases hone : ∀ s, cubic a b s = 0 → s = r
  · have : {u | cubic a b u = 0} = {r} := by
      ext s
      exact ⟨hone s, fun h ↦ h ▸ hr⟩
    simp [this]
  · push Not at hone
    obtain ⟨s, hs, hsr⟩ := hone
    rw [roots_subset hr hs hsr.symm]
    have h2 : 2 ≤ ({r, s, a - r - s} : Set ℝ).ncard := by
      rw [← ncard_pair hsr.symm]
      exact ncard_le_ncard (insert_subset_insert (by simp)) (toFinite _)
    have h3 : ({r, s, a - r - s} : Set ℝ).ncard ≤ 3 := by
      refine (ncard_insert_le _ _).trans ?_
      rw [show (3 : ℕ) = 2 + 1 from rfl]
      gcongr
      exact (ncard_insert_le _ _).trans (by simp)
    simp only [mem_insert_iff, mem_singleton_iff]
    omega

/-- **Saddle-node point.** There are exactly two equilibria iff some equilibrium has tangent
nullclines (equivalently a zero eigenvalue, a double root of the cubic) and is not the cusp
`3 u = a` (a triple root). -/
theorem ncard_equilibria_eq_two_iff (ha : 0 < a) (hb : 0 < b) :
    (equilibria a b 1 2).ncard = 2 ↔
      ∃ u v, IsEquilibrium a b 1 2 u v ∧ NullclinesTangent a b 1 2 u v ∧ 3 * u ≠ a := by
  rw [ncard_equilibria ha hb]
  constructor
  · intro h2
    obtain ⟨r, s, hrs, hS⟩ := ncard_eq_two.1 h2
    have hr : cubic a b r = 0 := by
      have : r ∈ {u | cubic a b u = 0} := by rw [hS]; simp
      exact this
    have hs : cubic a b s = 0 := by
      have : s ∈ {u | cubic a b u = 0} := by rw [hS]; simp
      exact this
    have ht : a - r - s ∈ ({r, s} : Set ℝ) := by
      rw [← hS]
      change cubic a b (a - r - s) = 0
      rw [(cubic_eq_of_roots hr hs hrs _).1]
      ring
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    -- the double root is `w`, the simple root is `w'`
    obtain ⟨w, w', hw, hw', hww', hD⟩ : ∃ w w', cubic a b w = 0 ∧ cubic a b w' = 0 ∧ w ≠ w' ∧
        cubicDeriv a b w = 0 := by
      rcases ht with ht | ht
      · refine ⟨r, s, hr, hs, hrs, ?_⟩
        rw [(cubic_eq_of_roots hr hs hrs r).2, ht]; ring
      · refine ⟨s, r, hs, hr, Ne.symm hrs, ?_⟩
        rw [(cubic_eq_of_roots hr hs hrs s).2, ht]; ring
    have hwe : IsEquilibrium a b 1 2 w (b / (1 + w ^ 2)) := (isEquilibrium_iff ha hb).2 ⟨hw, rfl⟩
    refine ⟨w, _, hwe, (nullclinesTangent_iff_cubicDeriv ha hb hwe).2 hD, ?_⟩
    intro hcusp
    -- a triple root would leave only one root
    rw [cubic_eq_of_double_root hw hD w', show a - 2 * w = w by linarith] at hw'
    have : (w' - w) ^ 3 = 0 := by linear_combination hw'
    exact hww' (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)).symm
  · rintro ⟨u, v, he, ht, hcusp⟩
    have hc := ((isEquilibrium_iff ha hb).1 he).1
    have hD := (nullclinesTangent_iff_cubicDeriv ha hb he).1 ht
    have hq : a - 2 * u ≠ u := fun h ↦ hcusp (by linarith)
    have hq0 : cubic a b (a - 2 * u) = 0 := by rw [cubic_eq_of_double_root hc hD]; ring
    rw [roots_subset hc hq0 hq.symm, show a - u - (a - 2 * u) = u by ring,
      insert_eq_of_mem (by simp), ncard_pair hq]

/-- Three roots `r < s < t` of the cubic: these are all the equilibria, the outer two are linearly
stable (Hurwitz Jacobian) and the middle one is a saddle (`HasSaddleSpectrum`). -/
theorem three_equilibria_of_lt (ha : 0 < a) (hb : 0 < b) {r s t : ℝ} (hr : cubic a b r = 0)
    (hs : cubic a b s = 0) (ht : cubic a b t = 0) (hrs : r < s) (hst : s < t) :
    equilibria a b 1 2 = {(r, b / (1 + r ^ 2)), (s, b / (1 + s ^ 2)), (t, b / (1 + t ^ 2))} ∧
      b / (1 + t ^ 2) < b / (1 + s ^ 2) ∧ b / (1 + s ^ 2) < b / (1 + r ^ 2) ∧
      (jacobian a b 1 2 r (b / (1 + r ^ 2))).IsHurwitz ∧
      HasSaddleSpectrum a b 1 2 s (b / (1 + s ^ 2)) ∧
      (jacobian a b 1 2 t (b / (1 + t ^ 2))).IsHurwitz := by
  have hq : t = a - r - s := by
    have : t ∈ ({r, s, a - r - s} : Set ℝ) := by
      rw [← roots_subset hr hs hrs.ne]; exact ht
    simp only [mem_insert_iff, mem_singleton_iff] at this
    rcases this with h | h | h
    · linarith
    · linarith
    · exact h
  have hfac := cubic_eq_of_roots hr hs hrs.ne
  have hDr : cubicDeriv a b r = (r - s) * (r - t) := by rw [(hfac r).2, ← hq]; ring
  have hDs : cubicDeriv a b s = (s - r) * (s - t) := by rw [(hfac s).2, ← hq]; ring
  have hDt : cubicDeriv a b t = (t - r) * (t - s) := by rw [(hfac t).2, ← hq]; ring
  have her : IsEquilibrium a b 1 2 r _ := (isEquilibrium_iff ha hb).2 ⟨hr, rfl⟩
  have hes : IsEquilibrium a b 1 2 s _ := (isEquilibrium_iff ha hb).2 ⟨hs, rfl⟩
  have het : IsEquilibrium a b 1 2 t _ := (isEquilibrium_iff ha hb).2 ⟨ht, rfl⟩
  have hr0 := pos_of_cubic_eq_zero ha hb hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [equilibria_eq_image ha hb, roots_subset hr hs hrs.ne, ← hq]
    simp only [image_insert_eq, image_singleton]
  · apply div_lt_div_of_pos_left hb (by positivity)
    nlinarith
  · apply div_lt_div_of_pos_left hb (by positivity)
    nlinarith
  · rw [isHurwitz_jacobian_iff_cubicDeriv ha hb her, hDr]
    nlinarith
  · rw [hasSaddleSpectrum_iff_cubicDeriv ha hb hes, hDs]
    nlinarith
  · rw [isHurwitz_jacobian_iff_cubicDeriv ha hb het, hDt]
    nlinarith

/-- **Bistable regime.** With exactly three equilibria `u₁ < u₂ < u₃` (so `v₁ > v₂ > v₃`), the
outer two are linearly stable (Hurwitz Jacobian) and the middle one is a saddle (one positive
eigenvalue, `HasSaddleSpectrum`). -/
theorem three_equilibria (ha : 0 < a) (hb : 0 < b) (h3 : (equilibria a b 1 2).ncard = 3) :
    ∃ u₁ u₂ u₃ : ℝ, u₁ < u₂ ∧ u₂ < u₃ ∧
      equilibria a b 1 2 =
        {(u₁, b / (1 + u₁ ^ 2)), (u₂, b / (1 + u₂ ^ 2)), (u₃, b / (1 + u₃ ^ 2))} ∧
      b / (1 + u₃ ^ 2) < b / (1 + u₂ ^ 2) ∧ b / (1 + u₂ ^ 2) < b / (1 + u₁ ^ 2) ∧
      (jacobian a b 1 2 u₁ (b / (1 + u₁ ^ 2))).IsHurwitz ∧
      HasSaddleSpectrum a b 1 2 u₂ (b / (1 + u₂ ^ 2)) ∧
      (jacobian a b 1 2 u₃ (b / (1 + u₃ ^ 2))).IsHurwitz := by
  rw [ncard_equilibria ha hb] at h3
  obtain ⟨x, y, z, hxy, hxz, hyz, hS⟩ := ncard_eq_three.1 h3
  have root : ∀ w ∈ ({x, y, z} : Set ℝ), cubic a b w = 0 := by
    intro w hw; rw [← hS] at hw; exact hw
  have hx := root x (by simp)
  have hy := root y (by simp)
  have hz := root z (by simp)
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact ⟨x, y, z, h1, h3, three_equilibria_of_lt ha hb hx hy hz h1 h3⟩
  · exact ⟨x, z, y, h2, h3, three_equilibria_of_lt ha hb hx hz hy h2 h3⟩
  · exact absurd (h1.trans h3) (not_lt.2 h2.le)
  · exact ⟨z, x, y, h2, h1, three_equilibria_of_lt ha hb hz hx hy h2 h1⟩
  · exact ⟨y, x, z, h1, h2, three_equilibria_of_lt ha hb hy hx hz h1 h2⟩
  · exact absurd (h3.trans h1) (not_lt.2 h2.le)
  · exact ⟨y, z, x, h3, h2, three_equilibria_of_lt ha hb hy hz hx h3 h2⟩
  · exact ⟨z, y, x, h3, h1, three_equilibria_of_lt ha hb hz hy hx h3 h1⟩

/-- **Bistability threshold.** There are exactly three equilibria iff there are two distinct
linearly stable equilibria (equilibria with Hurwitz Jacobian). -/
theorem ncard_equilibria_eq_three_iff_bistable (ha : 0 < a) (hb : 0 < b) :
    (equilibria a b 1 2).ncard = 3 ↔
      ∃ u₁ v₁ u₂ v₂, IsEquilibrium a b 1 2 u₁ v₁ ∧ IsEquilibrium a b 1 2 u₂ v₂ ∧ u₁ ≠ u₂ ∧
        (jacobian a b 1 2 u₁ v₁).IsHurwitz ∧ (jacobian a b 1 2 u₂ v₂).IsHurwitz := by
  constructor
  · intro h3
    obtain ⟨u₁, u₂, u₃, h12, h23, hset, -, -, hs₁, -, hs₃⟩ := three_equilibria ha hb h3
    have m₁ : (u₁, b / (1 + u₁ ^ 2)) ∈ equilibria a b 1 2 := by rw [hset]; simp
    have m₃ : (u₃, b / (1 + u₃ ^ 2)) ∈ equilibria a b 1 2 := by rw [hset]; simp
    exact ⟨u₁, _, u₃, _, m₁, m₃, (h12.trans h23).ne, hs₁, hs₃⟩
  · rintro ⟨u₁, v₁, u₂, v₂, he₁, he₂, hne, hs₁, hs₂⟩
    rw [isHurwitz_jacobian_iff_cubicDeriv ha hb he₁] at hs₁
    rw [isHurwitz_jacobian_iff_cubicDeriv ha hb he₂] at hs₂
    have hc₁ := ((isEquilibrium_iff ha hb).1 he₁).1
    have hc₂ := ((isEquilibrium_iff ha hb).1 he₂).1
    clear he₁ he₂
    wlog h : u₁ < u₂ generalizing u₁ u₂
    · exact this u₂ u₁ hne.symm hs₂ hs₁ hc₂ hc₁ (lt_of_le_of_ne (not_lt.1 h) hne.symm)
    have hfac := cubic_eq_of_roots hc₁ hc₂ hne
    have hD1 : cubicDeriv a b u₁ = (u₁ - u₂) * (u₁ - (a - u₁ - u₂)) := by rw [(hfac u₁).2]; ring
    have hD2 : cubicDeriv a b u₂ = (u₂ - u₁) * (u₂ - (a - u₁ - u₂)) := by rw [(hfac u₂).2]; ring
    rw [hD1] at hs₁
    rw [hD2] at hs₂
    have hq1 : u₁ < a - u₁ - u₂ := by nlinarith
    have hq2 : a - u₁ - u₂ < u₂ := by nlinarith
    rw [ncard_equilibria ha hb, roots_subset hc₁ hc₂ hne]
    exact ncard_eq_three.2 ⟨_, _, _, hne, hq1.ne, hq2.ne', rfl⟩

/-- **Saddle-node bifurcation in `b`.** Let `(u₀, v₀)` be an equilibrium at `b = b₀` with tangent
nullclines (a zero eigenvalue) that is not the cusp `3 u₀ = a`, and put `d = 3 u₀ - a ≠ 0`.

* For `b > 0` with `(b - b₀) d > 0` a fixed neighbourhood `|u - u₀| < η` contains no
  equilibrium.
* For `b > 0` with `(b₀ - b) d > 0` and `|b - b₀|` small, there are two equilibria
  `u₁ < u₀ < u₂`, one on each side of `u₀`, within any prescribed distance `δ` of `u₀`.

So as `b → b₀` from the second side two equilibria collide at `u₀` and then disappear. The
theorem does not say which of the two colliding equilibria is the saddle. -/
theorem saddleNode_collision (ha : 0 < a) {b₀ u₀ v₀ : ℝ} (hb₀ : 0 < b₀)
    (he : IsEquilibrium a b₀ 1 2 u₀ v₀) (ht : NullclinesTangent a b₀ 1 2 u₀ v₀)
    (hcusp : 3 * u₀ ≠ a) :
    (∃ η > 0, ∀ b u v, 0 < b → 0 < (b - b₀) * (3 * u₀ - a) → IsEquilibrium a b 1 2 u v →
      η ≤ |u - u₀|) ∧
    ∀ δ > 0, ∃ ε > 0, ∀ b, 0 < b → |b - b₀| < ε → 0 < (b₀ - b) * (3 * u₀ - a) →
      ∃ u₁ u₂, u₁ < u₀ ∧ u₀ < u₂ ∧ |u₁ - u₀| < δ ∧ |u₂ - u₀| < δ ∧
        IsEquilibrium a b 1 2 u₁ (b / (1 + u₁ ^ 2)) ∧
        IsEquilibrium a b 1 2 u₂ (b / (1 + u₂ ^ 2)) := by
  have hc0 := ((isEquilibrium_iff ha hb₀).1 he).1
  have hu0 := pos_of_cubic_eq_zero ha hb₀ hc0
  have hD := (nullclinesTangent_iff_cubicDeriv ha hb₀ he).1 ht
  set d := 3 * u₀ - a with hd_def
  have hd : d ≠ 0 := sub_ne_zero.2 hcusp
  have hdpos : 0 < |d| := abs_pos.2 hd
  have hdsq : |d| * |d| = d ^ 2 := by rw [abs_mul_abs_self, sq]
  -- the cubic near the double root
  have key : ∀ b u, cubic a b u = (u - u₀) ^ 2 * (d + (u - u₀)) + (b - b₀) * u := by
    intro b u
    have h := cubic_eq_of_double_root hc0 hD u
    unfold cubic at h ⊢
    linear_combination h
  -- `d (d + t) ≥ d² / 2` once `|t| ≤ |d| / 2`
  have hlow : ∀ t, |t| ≤ |d| / 2 → d ^ 2 / 2 ≤ d * (d + t) := by
    intro t htd
    have h1 : -(|d| * |t|) ≤ d * t := by rw [← abs_mul]; exact neg_abs_le _
    have h2 : |d| * |t| ≤ |d| * (|d| / 2) := mul_le_mul_of_nonneg_left htd hdpos.le
    nlinarith
  refine ⟨⟨|d| / 2, by positivity, ?_⟩, ?_⟩
  · intro b u v hb hside he'
    have hc := ((isEquilibrium_iff ha hb).1 he').1
    have hu := pos_of_cubic_eq_zero ha hb hc
    by_contra hlt
    push Not at hlt
    have h1 := hlow (u - u₀) hlt.le
    have h2 : 0 ≤ (u - u₀) ^ 2 * (d * (d + (u - u₀))) :=
      mul_nonneg (sq_nonneg _) (le_trans (by positivity) h1)
    have h3 : 0 < (b - b₀) * d * u := mul_pos hside hu
    have : d * cubic a b u = 0 := by rw [hc, mul_zero]
    rw [key] at this
    nlinarith
  · intro δ hδ
    set η := min (δ / 2) (|d| / 2) with hη_def
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    have hηδ : η ≤ δ / 2 := min_le_left _ _
    have hηd : η ≤ |d| / 2 := min_le_right _ _
    refine ⟨η ^ 2 * |d| / (2 * (u₀ + η)), by positivity, ?_⟩
    intro b hb hbε hside
    set g : ℝ → ℝ := fun u ↦ d * cubic a b u with hg
    have hgc : ContinuousOn g (Icc (u₀ - η) (u₀ + η)) :=
      (continuous_const.mul (continuous_cubic a b)).continuousOn
    have hg0 : g u₀ < 0 := by
      simp only [hg, key, sub_self]
      nlinarith [mul_pos hside hu0]
    have hgη : ∀ t, |t| = η → 0 < g (u₀ + t) := by
      intro t htη
      have h1 := hlow t (htη ▸ hηd)
      have ht2 : t ^ 2 = η ^ 2 := by rw [← sq_abs, htη]
      have hut : |u₀ + t| ≤ u₀ + η := by
        rw [← htη]; exact (abs_add_le _ _).trans (by rw [abs_of_pos hu0])
      have hpos : 0 < |d| * (u₀ + η) := by positivity
      have hbig : |d * ((b - b₀) * (u₀ + t))| < η ^ 2 * d ^ 2 / 2 := by
        rw [abs_mul, abs_mul]
        calc |d| * (|b - b₀| * |u₀ + t|) ≤ |d| * (|b - b₀| * (u₀ + η)) := by gcongr
          _ = |b - b₀| * (|d| * (u₀ + η)) := by ring
          _ < η ^ 2 * |d| / (2 * (u₀ + η)) * (|d| * (u₀ + η)) :=
            mul_lt_mul_of_pos_right hbε hpos
          _ = η ^ 2 * d ^ 2 / 2 := by
            rw [← hdsq]; field_simp
      have hneg := neg_abs_le (d * ((b - b₀) * (u₀ + t)))
      simp only [hg, key, add_sub_cancel_left]
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg t)]
    have hgl := hgη (-η) (by rw [abs_neg, abs_of_pos hη])
    have hgr := hgη η (abs_of_pos hη)
    rw [← sub_eq_add_neg] at hgl
    obtain ⟨u₁, ⟨hu₁l, hu₁r⟩, hgu₁⟩ := intermediate_value_Ioo' (by linarith : u₀ - η ≤ u₀)
      (hgc.mono (Icc_subset_Icc le_rfl (by linarith))) ⟨hg0, hgl⟩
    obtain ⟨u₂, ⟨hu₂l, hu₂r⟩, hgu₂⟩ := intermediate_value_Ioo (by linarith : u₀ ≤ u₀ + η)
      (hgc.mono (Icc_subset_Icc (by linarith) le_rfl)) ⟨hg0, hgr⟩
    have hc₁ : cubic a b u₁ = 0 := (mul_eq_zero.1 hgu₁).resolve_left hd
    have hc₂ : cubic a b u₂ = 0 := (mul_eq_zero.1 hgu₂).resolve_left hd
    refine ⟨u₁, u₂, hu₁r, hu₂l, ?_, ?_, (isEquilibrium_iff ha hb).2 ⟨hc₁, rfl⟩,
      (isEquilibrium_iff ha hb).2 ⟨hc₂, rfl⟩⟩
    · rw [abs_lt]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> linarith

end Cubic

end MathlibExt.Biology.Dynamics.ToggleSwitch
