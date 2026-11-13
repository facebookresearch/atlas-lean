/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The LP central path curvature integral is O(n^3.5 log(χ̄*_A + n)) (OWR 2/2005)

T. Tsuchiya (joint with R. D. C. Monteiro), Complexity analysis of interior-point algorithms and
geometric properties of the central trajectory for linear programming, Oberwolfach Report 2/2005,
pp. 121-124: for the primal-dual central trajectory `(x(ν), s(ν), y(ν))` of the LP `min cᵀx, Ax = b,
x ≥ 0` and its dual, with `κ(ν) = ‖ν ẋ(ν) ṡ(ν)‖^{1/2}` and `F(ν₀, ν₁) = ∫_{ν₁}^{ν₀} κ(ν)/ν dν`,
`F(∞, 0)` is finite and bounded by a constant depending on `(A, b, c)`; an interesting question is
whether there is an upper bound on `F(∞, 0)` depending only on `A`. We conjecture that `F(∞, 0) =
O(n^{3.5} log(χ̄*_A + n))`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.CentralPathCurvatureIntegralOWR783Problem004Wanted

/-!
Source: Oberwolfach Report 2/2005, Optimization and Applications (Oberwolfach, 2005), DOI
10.4171/OWR/2005/02, pp. 121-124 (T. Tsuchiya, joint with R. D. C. Monteiro). UnsolvedMath record
UM-30000172 (`OWR-783-004`), dataset ulamai/UnsolvedMath v1.8.0.

The report's standing assumption is that both programs have interior feasible solutions; `χ̄_A = max
{‖G⁻¹A‖ : G an m × m nonsingular submatrix of A}` presupposes that `A` has full row rank, which the
resolving paper assumes (A.1, A.2). Norms are Euclidean (operator norm: Mathlib's L2 operator norm
on matrices). The UnsolvedMath record writes `κ(ν) = ‖ν ẋ(ν) ∘ ṡ(ν)‖₁^{1/2}` with the `ℓ¹` norm, but
the report itself writes `κ(ν) = ‖ν ẋ(ν) ṡ(ν)‖^{1/2}` (p. 123) with the norm `‖·‖` of its `2`-norm
neighbourhood `N(β)` (p. 122), and Monteiro–Tsuchiya, who prove the bound for this `κ`, fix the
notation in §1: 'The Euclidean norm and the ∞-norm are denoted by ‖ · ‖ and ‖ · ‖∞'. With the `ℓ¹`
norm their theorem would give only `O(n^{3.75} log(χ̄*_A + n))`, since `‖v‖₁ ≤ √n ‖v‖₂`. `ẋ ṡ` is
the componentwise product and dots are derivatives in `ν`. The central path is given as any
functions `x, y, s` satisfying `x ∘ s = ν 1, Ax = b, Aᵀy + s = c, x, s > 0` for all `ν > 0` (the
solution is unique, so these are the central path). `F(∞, 0)` is the Lebesgue integral over `(0, ∞)`
of the nonnegative integrand taken in `ℝ≥0∞`, so no finiteness is assumed; `O(·)` is an absolute
constant `C`. The first question (a bound depending only on `A`) and the conjectured bound are
separate targets; the second implies the first.
-/

open MeasureTheory Set Matrix

open scoped Matrix.Norms.L2Operator in
/-- The condition number `χ̄_A = max {‖G⁻¹ A‖ : G an `m × m` nonsingular submatrix of `A`}` (the
Oberwolfach report's definition; Monteiro–Tsuchiya, Prop. 2.3(b)), with the operator norm induced
by the Euclidean norms. The submatrix `G` consists of the columns of `A` listed by an injection
`J : Fin m ↪ Fin n`. -/
noncomputable def chiBar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup {r | ∃ J : Fin m ↪ Fin n, IsUnit (A.submatrix id J).det ∧ r = ‖(A.submatrix id J)⁻¹ * A‖}

/-- The scaling-invariant condition number `χ̄*_A = inf {χ̄_{AD} : D positive diagonal}`. -/
noncomputable def chiBarStar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf {r | ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧ r = chiBar (A * Matrix.diagonal d)}

/-- `(x, y, s)` is the point with parameter `ν` of the primal-dual central path of the linear
program `min cᵀx, Ax = b, x ≥ 0` and its dual `max bᵀy, Aᵀy + s = c, s ≥ 0`: `x ∘ s = ν 1`,
`Ax = b`, `Aᵀy + s = c`, `x > 0`, `s > 0`. -/
def IsCentralPathPoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (ν : ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  (∀ i, x i * s i = ν) ∧ A *ᵥ x = b ∧ Aᵀ *ᵥ y + s = c ∧ (∀ i, 0 < x i) ∧ ∀ i, 0 < s i

/-- The Sonnevend–Stoer–Zhao curvature `κ(ν) = ‖ν ẋ(ν) ∘ ṡ(ν)‖^{1/2}` of a path `ν ↦ (x(ν), s(ν))`
(Euclidean norm, as in the report and Monteiro–Tsuchiya §1 and (7); `∘` the componentwise product,
dots the derivatives in `ν`). -/
noncomputable def curvature {n : ℕ} (x s : ℝ → Fin n → ℝ) (ν : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (∑ i, (ν * deriv x ν i * deriv s ν i) ^ 2))

/-- Standing assumptions of the problem (Monteiro–Tsuchiya, A.1–A.2): `A` has full row rank and
both programs have strictly feasible solutions. -/
def StandingAssumptions {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Prop :=
  A.rank = m ∧ (∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ A *ᵥ x = b) ∧
    ∃ (y : Fin m → ℝ) (s : Fin n → ℝ), (∀ i, 0 < s i) ∧ Aᵀ *ᵥ y + s = c

/-- First question: the curvature integral `F(∞, 0) = ∫₀^∞ κ(ν)/ν dν` of the central path is
bounded by a quantity depending only on `A` (not on `b`, `c`). The integral is the Lebesgue integral
of a nonnegative function in `ℝ≥0∞`, so no finiteness is presupposed. -/
def curvatureIntegralBoundedByA : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), A.rank = m → ∃ K : ℝ, ∀ (b : Fin m → ℝ)
    (c : Fin n → ℝ), StandingAssumptions A b c → ∀ (x s : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ),
      (∀ ν, 0 < ν → IsCentralPathPoint A b c ν (x ν) (y ν) (s ν)) →
        ∫⁻ ν in Ioi (0 : ℝ), ENNReal.ofReal (curvature x s ν / ν) ≤ ENNReal.ofReal K

/-- Second, more specific question (the conjecture of the report): there is an absolute constant
`C` with `F(∞, 0) ≤ C · n^{3.5} · log(χ̄*_A + n)` for every linear program satisfying the standing
assumptions, i.e. `F(∞, 0) = O(n^{3.5} log(χ̄*_A + n))`. -/
def curvatureIntegralBigO : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
    StandingAssumptions A b c → ∀ (x s : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ),
      (∀ ν, 0 < ν → IsCentralPathPoint A b c ν (x ν) (y ν) (s ν)) →
        ∫⁻ ν in Ioi (0 : ℝ), ENNReal.ofReal (curvature x s ν / ν) ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (7 / 2 : ℝ) * Real.log (chiBarStar A + n))

/--
Resolved true: by Monteiro–Tsuchiya's Theorem 2.4, `F(∞, 0)` is bounded by `C n^{3.5} log(χ̄*_A +
n)`, a quantity depending only on `A`. Source: Oberwolfach Report 2/2005, Optimization and
Applications (Oberwolfach, 2005), DOI 10.4171/OWR/2005/02, pp. 121-124 (T. Tsuchiya, joint with R.
D. C. Monteiro); resolution: R. D. C. Monteiro and T. Tsuchiya, A strong bound on the integral of
the central path curvature and its relationship with the iteration-complexity of primal-dual
path-following LP algorithms, Math. Program. 115 (2008), 105-149, DOI 10.1007/s10107-007-0141-5
(preprint Optimization Online 2005/09/1221), §2.1: assumptions A.1 (strictly feasible primal and
dual) and A.2 (rows of A linearly independent), curvature κ(ν) = ‖ν ẋ(ν) ṡ(ν)‖^{1/2} (7) with the
Euclidean norm, I(ν_f, ν_i) = ∫ κ(ν)/ν dν (10), Prop. 2.3(b) (χ̄_A = max ‖G⁻¹A‖ over m × m
nonsingular submatrices); Theorem 2.4: I(0, ∞) ≤ O(n^{3.5} log(χ̄*_A + n)) with χ̄*_A = inf {χ̄_{AD}
: D positive diagonal}; Lemma 2.1(ii): if κ vanishes somewhere it vanishes everywhere (the case
excluded by A.3, where the integral is 0),
https://optimization-online.org/wp-content/uploads/2005/09/1221.pdf.
-/
public theorem_wanted curvatureIntegralBoundedByA_holds : curvatureIntegralBoundedByA

/--
Resolved true: Monteiro and Tsuchiya prove `F(∞, 0) = I(0, ∞) ≤ O(n^{3.5} log(χ̄*_A + n))`, the
conjectured bound. Source: Oberwolfach Report 2/2005, Optimization and Applications (Oberwolfach,
2005), DOI 10.4171/OWR/2005/02, pp. 121-124 (T. Tsuchiya, joint with R. D. C. Monteiro); resolution:
R. D. C. Monteiro and T. Tsuchiya, A strong bound on the integral of the central path curvature and
its relationship with the iteration-complexity of primal-dual path-following LP algorithms, Math.
Program. 115 (2008), 105-149, DOI 10.1007/s10107-007-0141-5 (preprint Optimization Online
2005/09/1221), §2.1: assumptions A.1 (strictly feasible primal and dual) and A.2 (rows of A linearly
independent), curvature κ(ν) = ‖ν ẋ(ν) ṡ(ν)‖^{1/2} (7) with the Euclidean norm, I(ν_f, ν_i) = ∫
κ(ν)/ν dν (10), Prop. 2.3(b) (χ̄_A = max ‖G⁻¹A‖ over m × m nonsingular submatrices); Theorem 2.4:
I(0, ∞) ≤ O(n^{3.5} log(χ̄*_A + n)) with χ̄*_A = inf {χ̄_{AD} : D positive diagonal}; Lemma 2.1(ii):
if κ vanishes somewhere it vanishes everywhere (the case excluded by A.3, where the integral is 0),
https://optimization-online.org/wp-content/uploads/2005/09/1221.pdf.
-/
public theorem_wanted curvatureIntegralBigO_holds : curvatureIntegralBigO

end MathlibExt.Analysis.CentralPathCurvatureIntegralOWR783Problem004Wanted
