/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Cohen–Grossberg theorem for competitive neural networks

Cohen and Grossberg (1983) study the competitive systems

  `x_i' = a_i(x_i) [b_i(x_i) - ∑_k c_ik d_k(x_k)]`,   `i = 1, …, n`  (Eq. (1)),

with a symmetric matrix `C = (c_ik)` of nonnegative interaction coefficients, amplification
functions `a_i > 0` on `(0, ∞)`, and nonnegative, nondecreasing, differentiable signal functions
`d_k` (hypotheses a)–d) of their Theorem 1; their c) asks `d_k ≥ 0` at every real argument, which
is assumed here only on the modeled ray `[0, ∞)`). Under the further hypotheses e) (each
`b_i(ξ) - c_ii d_i(ξ)` has negative upper limit as `ξ → ∞`) and f) (either `b_i(ξ) → ∞` as
`ξ → 0⁺`, or `b_i` has a finite limit at `0⁺` and `∫_0^ε dξ / a_i(ξ) = ∞`), solutions from
positive initial data stay positive and bounded (Lemma 1); the source calls them admissible
trajectories. The function

  `V(x) = -∑_i ∫_{λ_i}^{x_i} b_i(ξ) d_i'(ξ) dξ + (1/2) ∑_{j,k} c_jk d_j(x_j) d_k(x_k)`

(Eqs. (21)–(22), with lower limits `λ_i > 0` as in their Proposition 2) satisfies
`dV/dt = -∑_i a_i d_i' [b_i - ∑_k c_ik d_k]² ≤ 0` along solutions (Proposition 1); the chain-rule
computation of `dV/dt` here uses continuously differentiable `d_i`. By the LaSalle invariance
principle every admissible trajectory approaches the largest invariant set contained in the set
where `dV/dt = 0` (Theorem 1), whose points are equilibria when each `d_i` is strictly increasing
(Corollary 1); the source notes (p. 818) that this does not yet give convergence to a single
equilibrium. Its Theorem 3 does: if each `d_i` has an inhibitory signal threshold (Eq. (48)), no
level set of any `b_i` contains an open interval and the subsystem suprathreshold equilibrium
vectors are countable, then each admissible trajectory converges to an equilibrium point. The
source's piecewise-differentiable signal functions, the invariant-set conclusion of its
Theorem 1, its Sard-type corollaries and its Theorem 4 are not stated.

Sources: M. A. Cohen and S. Grossberg, "Absolute stability of global pattern formation and
parallel memory storage by competitive neural networks", IEEE Trans. Systems Man Cybernet.
SMC-13 (1983) 815–826, Eqs. (1), (21)–(22), (33)–(36), (47)–(48), Lemma 1, Propositions 1–2,
Theorems 1 and 3 and Corollary 1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

namespace WantedExt.Biology.Neuroscience.CohenGrossbergWanted

open Filter Topology MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- The vector field of the Cohen–Grossberg system (Eq. (1)):
`x_i' = a_i(x_i) [b_i(x_i) - ∑_k c_ik d_k(x_k)]`. -/
noncomputable def field (a b d : ι → ℝ → ℝ) (C : Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => a i (x i) * (b i (x i) - ∑ k, C i k * d k (x k))

/-- The Cohen–Grossberg Lyapunov function with lower limits `λ_i` (Eqs. (21)–(22) and
Proposition 2): `V(x) = -∑_i ∫_{λ_i}^{x_i} b_i d_i' + (1/2) ∑_{j,k} c_jk d_j(x_j) d_k(x_k)`. -/
noncomputable def lyapunov (b d : ι → ℝ → ℝ) (C : Matrix ι ι ℝ) (lowerLimit : ι → ℝ)
    (x : ι → ℝ) : ℝ :=
  -(∑ i, ∫ ξ in lowerLimit i..x i, b i ξ * deriv (d i) ξ) +
    (1 / 2) * ∑ j, ∑ k, C j k * d j (x j) * d k (x k)

/-- Hypotheses a)–d) of Theorem 1 of Cohen and Grossberg (1983): `C` is symmetric with
nonnegative entries; each `a_i` is continuous on `[0, ∞)` and positive on `(0, ∞)`; each `b_i`
is continuous on `(0, ∞)`; each `d_i` is nonnegative, differentiable and nondecreasing on
`[0, ∞)`. The source's c) states `d_i(ξ) ≥ 0` for every real `ξ`; here nonnegativity is assumed
only on the modeled ray `[0, ∞)`. -/
structure StandingHypotheses (a b d : ι → ℝ → ℝ) (C : Matrix ι ι ℝ) : Prop where
  symm : ∀ i j, C i j = C j i
  nonneg : ∀ i j, 0 ≤ C i j
  continuousOn_a : ∀ i, ContinuousOn (a i) (Set.Ici 0)
  pos_a : ∀ i ξ, 0 < ξ → 0 < a i ξ
  continuousOn_b : ∀ i, ContinuousOn (b i) (Set.Ioi 0)
  nonneg_d : ∀ i ξ, 0 ≤ ξ → 0 ≤ d i ξ
  differentiableOn_d : ∀ i, DifferentiableOn ℝ (d i) (Set.Ici 0)
  monotoneOn_d : ∀ i, MonotoneOn (d i) (Set.Ici 0)

/-- Hypotheses e) and f) of Theorem 1 of Cohen and Grossberg (1983, Eqs. (33)–(36)): for each
`i`, `b_i(ξ) - c_ii d_i(ξ)` is eventually at most some negative constant as `ξ → ∞` (negative
upper limit); and either `b_i(ξ) → ∞` as `ξ → 0⁺`, or `b_i` has a finite limit at `0⁺` and
`∫_0^ε dξ / a_i(ξ) = ∞` for some `ε > 0`. -/
structure BoundaryHypotheses (a b d : ι → ℝ → ℝ) (C : Matrix ι ι ℝ) : Prop where
  limsup_neg : ∀ i, ∃ c < 0, ∀ᶠ ξ in atTop, b i ξ - C i i * d i ξ ≤ c
  boundary : ∀ i, Tendsto (b i) (𝓝[>] 0) atTop ∨
    ((∃ L, Tendsto (b i) (𝓝[>] 0) (𝓝 L)) ∧
      ∃ ε > 0, ∫⁻ ξ in Set.Ioc 0 ε, ENNReal.ofReal (1 / a i ξ) = ⊤)

/-- **Positivity and boundedness** (Cohen and Grossberg 1983, Lemma 1). Assume hypotheses a)–d)
(`StandingHypotheses`) and e)–f) (`BoundaryHypotheses`). Let `x` be a forward solution of
Eq. (1) on `[0, ∞)` (derivative `field (x t)` within `[0, ∞)` at every `t ≥ 0`, one-sided at
`0`) with every coordinate of `x 0` positive. Then every coordinate of `x t` is positive for all
`t ≥ 0`, and the trajectory is bounded: there is `M` with `x t i ≤ M` for all `t ≥ 0` and all
`i`.

Source: Cohen and Grossberg (1983), Lemma 1. -/
theorem_wanted pos_and_bounded (a b d : ι → ℝ → ℝ) (C : Matrix ι ι ℝ)
    (hstd : StandingHypotheses a b d C) (hbdry : BoundaryHypotheses a b d C) (x : ℝ → ι → ℝ)
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (field a b d C (x t)) (Set.Ici 0) t)
    (hx0 : ∀ i, 0 < x 0 i) :
    (∀ t, 0 ≤ t → ∀ i, 0 < x t i) ∧ ∃ M, ∀ t, 0 ≤ t → ∀ i, x t i ≤ M

/-- **The Lyapunov identity** (Cohen and Grossberg 1983, Proposition 1, Eqs. (21)–(22), with
the lower limits of Proposition 2). Assume hypotheses a)–d) (`StandingHypotheses`) and that each
`d_i` is continuously differentiable on `(0, ∞)`. Let `λ_i > 0`, and let `x` be a solution of
Eq. (1) at time `t` (`x` has derivative `field (x t)` at `t`) with every coordinate of `x t`
positive. Then `t ↦ V(x t)` has derivative
`-∑_i a_i(x_i) d_i'(x_i) [b_i(x_i) - ∑_k c_ik d_k(x_k)]²` at `t`, and this derivative is `≤ 0`.

Source: Cohen and Grossberg (1983), Proposition 1. -/
theorem_wanted hasDerivAt_lyapunov (a b d : ι → ℝ → ℝ) (C : Matrix ι ι ℝ)
    (hstd : StandingHypotheses a b d C) (hd : ∀ i, ContDiffOn ℝ 1 (d i) (Set.Ioi 0))
    (lowerLimit : ι → ℝ) (hlow : ∀ i, 0 < lowerLimit i) (x : ℝ → ι → ℝ) (t : ℝ)
    (hx : HasDerivAt x (field a b d C (x t)) t) (hxt : ∀ i, 0 < x t i) :
    HasDerivAt (fun s => lyapunov b d C lowerLimit (x s))
        (-∑ i, a i (x t i) * deriv (d i) (x t i) *
          (b i (x t i) - ∑ k, C i k * d k (x t k)) ^ 2) t ∧
      -∑ i, a i (x t i) * deriv (d i) (x t i) *
          (b i (x t i) - ∑ k, C i k * d k (x t k)) ^ 2 ≤ 0

/-- **Convergence to an equilibrium** (Cohen and Grossberg 1983, Theorem 3, "Global Pattern
Formation": "Let all the hypotheses of Theorem 1 hold. Also suppose that no level sets of the
functions b_i contain an open interval and that the subsystem suprathreshold equilibrium vectors
are countable. Then each admissible trajectory converges to an equilibrium point."). Assume
hypotheses a)–d) (`StandingHypotheses`) and e)–f) (`BoundaryHypotheses`) of Theorem 1, and give
each `d_i` the inhibitory signal threshold `Γ_i ≥ 0` that the notion of a suprathreshold value
presupposes (Eq. (48)): `d_i(ξ) = 0` for `0 ≤ ξ ≤ Γ_i` and `d_i'(ξ) > 0` for `ξ > Γ_i`. Assume
that no level set of any `b_i` contains an open interval of `(0, ∞)`, and that for every set `U`
of indices the suprathreshold equilibrium vectors of the subsystem on `U` form a countable set:
the vectors `y`, zero off `U`, with `y_i > Γ_i` and
`a_i(y_i) [b_i(y_i) - ∑_{k ∈ U} c_ik d_k(y_k)] = 0` for every `i ∈ U`, that is, the equilibria
with every variable above its threshold of the system obtained from Eq. (1) by eliminating the
variables outside `U` (Sections V–VII). Let `x` be a forward solution of Eq. (1) on `[0, ∞)`
(derivative `field (x t)` within `[0, ∞)` at every `t ≥ 0`, one-sided at `0`) with every
coordinate of `x 0` positive, an admissible trajectory by Lemma 1. Then there is an equilibrium
`e` of Eq. (1), with every coordinate nonnegative and `field e = 0`, such that `x t → e` as
`t → ∞`.

Source: Cohen and Grossberg (1983), Theorem 3, with the thresholds of Eq. (48). -/
theorem_wanted tendsto_equilibrium (a b d : ι → ℝ → ℝ) (C : Matrix ι ι ℝ)
    (hstd : StandingHypotheses a b d C) (hbdry : BoundaryHypotheses a b d C)
    (Γ : ι → ℝ) (hΓ : ∀ i, 0 ≤ Γ i) (hsub : ∀ i ξ, 0 ≤ ξ → ξ ≤ Γ i → d i ξ = 0)
    (hsupra : ∀ i ξ, Γ i < ξ → 0 < deriv (d i) ξ)
    (hlevel : ∀ i (c u v : ℝ), 0 ≤ u → u < v → ∃ ξ ∈ Set.Ioo u v, b i ξ ≠ c)
    (hcount : ∀ U : Finset ι, Set.Countable {y : ι → ℝ |
      (∀ i ∈ U, Γ i < y i ∧ a i (y i) * (b i (y i) - ∑ k ∈ U, C i k * d k (y k)) = 0) ∧
        ∀ i ∉ U, y i = 0})
    (x : ℝ → ι → ℝ)
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (field a b d C (x t)) (Set.Ici 0) t)
    (hx0 : ∀ i, 0 < x 0 i) :
    ∃ e : ι → ℝ, (∀ i, 0 ≤ e i) ∧ field a b d C e = 0 ∧ Tendsto x atTop (𝓝 e)

end WantedExt.Biology.Neuroscience.CohenGrossbergWanted
