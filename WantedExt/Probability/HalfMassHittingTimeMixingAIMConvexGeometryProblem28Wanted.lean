/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mixing time is bounded by the hitting time of half-mass sets (AIM, Peres's Problem 9)

AIM workshop on algorithmic convex geometry, Problem 9 (Y. Peres): for lazy random walks on graphs
or reversible Markov chains, is there `c > 0` with `τ_TV(1/2) ≤ c · max {E_x T_A : x, π(A) ≥ 1/2}`?
Griffiths, Kang, Oliveira and Patel answered it: for lazy reversible chains `T(1/2)` is equivalent
to the mixing time `t_mix`, whose threshold `1/4` is stricter than the list's `1/2`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import MathlibExt.Probability.MarkovMixing

@[expose] public section

namespace MathlibExt.Probability.HalfMassHittingTimeMixingAIMConvexGeometryProblem28Wanted

/-!
Source: Problems from the AIM Workshop on Algorithmic Convex Geometry (compiled by N. Goyal),
Problem 9 (Y. Peres), https://aimath.org/WWN/convexgeometry/convexgeometry.pdf. UnsolvedMath record
UM-20001296 (`AIM-CONVEX_GEOMETRY-0028`), dataset ulamai/UnsolvedMath v1.8.0.

Chains are irreducible on a finite state space `Fin n`, with a stochastic matrix `P`, reversible
with respect to a probability vector `π` (detailed balance, so `π` is the stationary distribution),
and lazy in the paper's sense `P(x, x) ≥ 1/2`. The list measures mixing by `τ_TV(1/2)`, the least
`t` with `d_TV(P^t(x, ·), π) ≤ 1/2` for every start `x`. The target is stated in the notion of the
resolving theorem, Griffiths-Kang-Oliveira-Patel Theorem 1.9: the standard mixing time `t_mix`, the
least `t` with `|P^t(x, A) - π(A)| ≤ 1/4` for all `x` and `A`, i.e. `MathlibExt`'s `IsMixedAt P π t`
(total variation `tvDist` at most `1/4` from every start). The target asks for such a `t` with
`t ≤ c · T(1/2)`, which is `t_mix ≤ c · T(1/2)`; since a time at which every start is within `1/4`
is also within `1/2`, it is at least as strong as the list's `τ_TV(1/2) ≤ c · T(1/2)`. `T(1/2)` is
the maximum of `E_x[τ_A]` over states `x` and sets `A` with `π(A) ≥ 1/2`, where
`τ_A = min {s ≥ 0 | X_s ∈ A}`, computed as `∑_{t ≥ 0} P_x(τ_A > t)` in `[0, ∞]` with
`P_x(τ_A > t)` read off the chain killed on `A`. The list's remark quotes Aldous's bound with the
factor `μ(A)`; the question is the version restricted to sets of measure at least `1/2`.
-/

open MathlibExt.Probability.MarkovMixing
open scoped ENNReal

/-- The matrix `P` with every entry in a row or a column indexed by `A` replaced by `0`: the
transitions of the chain killed on entering `A`. -/
def killedOn {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (A : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun y z => if y ∈ A ∨ z ∈ A then 0 else P y z

/-- `P_x(τ_A > t)` for the chain with transition matrix `P` started at `x`, where
`τ_A = min {s | X_s ∈ A}`: the probability that `X_0, …, X_t` all lie outside `A`. -/
noncomputable def notYetHit {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (A : Finset (Fin n))
    (x : Fin n) (t : ℕ) : ℝ :=
  if x ∈ A then 0 else ∑ z, (killedOn P A ^ t) x z

/-- The expected hitting time `E_x[τ_A] = ∑_{t ≥ 0} P_x(τ_A > t)` (in `[0, ∞]`). -/
noncomputable def expectedHittingTime {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (A : Finset (Fin n)) (x : Fin n) : ℝ≥0∞ :=
  ∑' t, ENNReal.ofReal (notYetHit P A x t)

/-- `T(1/2) = max {E_x[τ_A] : x a state, A a set of states with π(A) ≥ 1/2}`. -/
noncomputable def halfMassHittingTime {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (π : Fin n → ℝ) : ℝ≥0∞ :=
  ⨆ (x : Fin n) (A : Finset (Fin n)) (_ : (1 : ℝ) / 2 ≤ ∑ y ∈ A, π y),
    expectedHittingTime P A x

/-- Peres's question (AIM algorithmic convex geometry list, Problem 9), answered yes in the form of
Griffiths-Kang-Oliveira-Patel Theorem 1.9: there is a universal `c > 0` such that every irreducible
finite Markov chain with transition matrix `P` that is reversible with respect to its stationary
distribution `π` and lazy (`P(x, x) ≥ 1/2`) has `t_mix ≤ c · T(1/2)`: some time `t ≤ c · T(1/2)`
has `d_TV(P^t(x, ·), π) ≤ 1/4` for every start `x` (`IsMixedAt P π t`). -/
def mixingTimeLeHalfMassHittingTime : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ),
    (∀ x y, 0 ≤ P x y) → (∀ x, ∑ y, P x y = 1) → (∀ x y, ∃ t : ℕ, 0 < (P ^ t) x y) →
    (∀ x, 0 ≤ π x) → ∑ x, π x = 1 → (∀ x y, π x * P x y = π y * P y x) →
    (∀ x, 1 / 2 ≤ P x x) →
    ∃ t : ℕ, (t : ℝ≥0∞) ≤ ENNReal.ofReal c * halfMassHittingTime P π ∧ IsMixedAt P π t

/--
Resolved true: there is a universal constant `c > 0` with `t_mix ≤ c · T(1/2)` for every
irreducible, reversible, lazy (`P(x, x) ≥ 1/2`) finite Markov chain. Griffiths-Kang-Oliveira-Patel
Theorem 1.9: 'There exists a universal constant c > 0 such that the following holds. Consider a
reversible, irreducible finite Markov chain with transition matrix P that is lazy in the sense that
P_xx ≥ 1/2 for all x in the state space. Then t_mix/c ≤ T(1/2) ≤ c t_mix', where (§1.3) `t_mix` is
the least `t` with `|P^t(x, A) - π(A)| ≤ 1/4` for all `x` and `A` and (§1) `T(α)` is the maximum of
`E_x[τ_A]` over `x` and `A` with `π(A) ≥ α`, `τ_A = min {t : X_t ∈ A}`; §1.3 presents the theorem as
answering this question of Peres, citing this problem list. Source: Problems from the AIM Workshop
on Algorithmic Convex Geometry (compiled by N. Goyal), Problem 9 (Y. Peres),
https://aimath.org/WWN/convexgeometry/convexgeometry.pdf; resolution: S. Griffiths, R. J. Kang, R.
I. Oliveira and V. Patel, Tight inequalities among set hitting times in Markov chains, Proc. Amer.
Math. Soc. 142 (2014), 3285-3298, arXiv:1209.0039, Theorem 1.9 (universal c > 0: for every
reversible, irreducible finite Markov chain with P(x, x) ≥ 1/2, t_mix/c ≤ T(1/2) ≤ c t_mix) and §1.3
(answering a question of Peres); T(α) and t_mix defined in §1 and §1.3,
https://doi.org/10.1090/S0002-9939-2014-12045-4.
-/
public theorem_wanted mixingTimeLeHalfMassHittingTime_holds : mixingTimeLeHalfMassHittingTime

end MathlibExt.Probability.HalfMassHittingTimeMixingAIMConvexGeometryProblem28Wanted
