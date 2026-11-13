/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monotone period function of an equivariant center (Gasull, Problem 16)

Gasull, Some open problems in low dimensional dynamical systems, Problem 16: is the period function
associated with the period annulus of the origin for `ż = i z + (z z̄)ⁿ z^{k+1}`, with `n` and `k`
positive integers, monotonically decreasing?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

@[expose] public section

namespace MathlibExt.Dynamics.EquivariantCenterPeriodFunctionAMR46Problem0016Wanted

/-!
Source: A. Gasull, Some open problems in low dimensional dynamical systems, SeMA J. 78 (2021),
arXiv:2012.02524, Problem 16. UnsolvedMath record UM-04700016 (`AMR-046-0016`), dataset
ulamai/UnsolvedMath v1.8.0.

Solutions are classical solutions `x : ℝ → ℂ` of `ż = F(z)`; `z` has period `T` if a solution
through `z` returns to `z` at time `T > 0` and not before (the minimal period, solutions being
unique). The period annulus is the connected component of the center `0` in the set made of `0` and
the points on periodic orbits, with `0` removed. The orbit of `z₁` is inside that of `z₂` when `z₁`
lies in the component of the complement of the orbit of `z₂` that contains `0`. Monotonically
decreasing is stated strictly (the outer orbit's period is smaller than the inner one's):
Gasull-Rojas reduce the equation to the quadratic reversible center (3) with `D = -k/(2(k + n))` and
show (Proposition 2.1 with Lemma 3.1) that the derivative of its period function has no zeros. Their
Theorem A also gives the limits `2π` at the center and `2(k + n)π/(k + 2n)` at the boundary of the
annulus.
-/

/-- The vector field `F(z) = i z + (z z̄) ^ n z ^ (k + 1)` on `ℂ`. -/
noncomputable def field (n k : ℕ) (z : ℂ) : ℂ :=
  Complex.I * z + (z * starRingEnd ℂ z) ^ n * z ^ (k + 1)

/-- `x` is a solution of `ż = F(z)` defined for all real times. -/
def IsSolution (n k : ℕ) (x : ℝ → ℂ) : Prop :=
  ∀ t, HasDerivAt x (field n k (x t)) t

/-- `z` lies on a periodic orbit of minimal period `T`: a solution through `z` at time `0` returns
to `z` at time `T > 0` and not before. -/
def HasPeriod (n k : ℕ) (z : ℂ) (T : ℝ) : Prop :=
  0 < T ∧ ∃ x, IsSolution n k x ∧ x 0 = z ∧ x T = z ∧ ∀ s ∈ Set.Ioo 0 T, x s ≠ z

/-- The orbit of `z`: the points of the solutions through `z`. -/
def orbit (n k : ℕ) (z : ℂ) : Set ℂ :=
  {w | ∃ x, IsSolution n k x ∧ x 0 = z ∧ ∃ t, x t = w}

/-- The period annulus of the center `0`: the points other than `0` in the connected component of
`0` in the set made of `0` and the points on periodic orbits. -/
def periodAnnulus (n k : ℕ) : Set ℂ :=
  connectedComponentIn {z | z = 0 ∨ ∃ T, HasPeriod n k z T} 0 \ {0}

/-- Gasull's question, with a positive answer: for all positive integers `n, k` the period function
of the period annulus of the origin of `ż = i z + (z z̄) ^ n z ^ (k + 1)` is monotonically
decreasing: if the orbit of `z₁` lies inside the orbit of `z₂` (in the component of its complement
containing the center), then the period of `z₂` is smaller than that of `z₁`. -/
def periodFunctionDecreasing : Prop :=
  ∀ n k : ℕ, 0 < n → 0 < k → ∀ (z₁ z₂ : ℂ) (T₁ T₂ : ℝ), z₁ ∈ periodAnnulus n k →
    z₂ ∈ periodAnnulus n k → z₁ ∈ connectedComponentIn (orbit n k z₂)ᶜ 0 →
      HasPeriod n k z₁ T₁ → HasPeriod n k z₂ T₂ → T₂ < T₁

/--
Resolved true: Gasull and Rojas (Theorem A) prove that for all positive integers `n` and `k` the
period function of the center at the origin of `ż = i z + a (z z̄)ⁿ z^{k+1}`, `a ≠ 0`, is
monotonically decreasing (here `a = 1`); the decrease is strict, since their proof shows that the
derivative of the period function has no zeros. Source: A. Gasull, Some open problems in low
dimensional dynamical systems, SeMA J. 78 (2021), arXiv:2012.02524, Problem 16; resolution: A.
Gasull and D. Rojas, Monotonous period function for equivariant differential equations with
homogeneous nonlinearities, Mediterr. J. Math. 22 (2025), article 112; arXiv:2411.12408, Theorem A:
the period function of the center at the origin of ż = iz + a(zz̄)ⁿz^{k+1}, with n and k positive
integers and 0 ≠ a ∈ ℂ, is monotonous decreasing; it starts at 2π at the origin and tends to 2(k +
n)π/(k + 2n) at the boundary of the period annulus; proof of Theorem B, Proposition 2.1 and Lemma
3.1: the derivative of the period function has no zeros, https://doi.org/10.1007/s00009-025-02879-2.
-/
public theorem_wanted periodFunctionDecreasing_holds : periodFunctionDecreasing

end MathlibExt.Dynamics.EquivariantCenterPeriodFunctionAMR46Problem0016Wanted
