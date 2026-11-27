/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complex-balanced stochastic mass-action systems are non-explosive

A continuous-time Markov chain on a countable state space `σ` with jump rates `q(x, y) ≥ 0`
(`x ≠ y`) and total rates `q(x) = ∑_{y ≠ x} q(x, y) < ∞` is realized by its jump chain and
holding times: the jump chain `(Y_n)` is a Markov chain with transition probabilities
`q(x, y)/q(x)` (and stays put at absorbing states, `q(x) = 0`), and, given it, independent
exponential clocks `E_n` of rate `1` give the holding times `E_n / q(Y_n)` and the jump times
`T_n = ∑_{k < n} E_k / q(Y_k)`. The process is non-explosive if `T_n → ∞` almost surely.

**Theorem 2** (Anderson–Cappelletti–Koyama–Kurtz 2018). Suppose the rates satisfy Condition 1
(`0 ≤ q(x, y) < ∞`, `q(y) < ∞` for each `y`, `sup_y q(y, x) < ∞` for each `x`), and that a
probability distribution `π` is a constant solution of the forward equation,
`∑_{y ≠ x} π(y) q(y, x) = π(x) q(x)` for every `x` (equation (3)), with
`∑_x π(x) q(x) < ∞` (condition (13)). Then the process is non-explosive whenever the support of
the initial distribution is contained in the support of `π`.

**Theorem 3** (Anderson–Cappelletti–Koyama–Kurtz 2018). For any initial distribution,
complex-balanced stochastic mass-action systems are non-explosive.

For Theorem 3, a reaction network `N` on finitely many species `S` has reactions `y_r → y'_r` with
complexes in `ℕ^S` and rate constants `κ_r > 0`; its stochastic mass-action system is the chain
`StochasticCRNRegeneration.massAction N κ` of `Domains.Biology.Dynamics.StochasticCRNRegeneration`,
with the mass-action propensities `κ_r ∏_s x_s! / (x_s - y_{r,s})!` (`SystemsBiology.propensity`),
realized by its jump chain and holding times (`StochasticCRN.inputMeasure`,
`StochasticCRN.jumpTime`). The system is complex balanced if some `c` with all entries positive
satisfies `ReactionNetwork.IsComplexBalanced` (`Domains.Biology.Dynamics.ComplexBalanced`): at
every complex `z`, `∑_{r : y_r = z} κ_r c^{y_r} = ∑_{r : y'_r = z} κ_r c^{y_r}`; such a `c` is a
positive equilibrium, so this is the source's Definition 4. Theorem 3 is stated for every
initial state, which covers every initial distribution. This is the assumption that
`StochasticCRNRegeneration` records as unproved ("a drift bound is assumed").

Conventions. As in `Domains.Biology.Dynamics.StochasticCRNNonExplosion`, absorbing states
(total rate `0`) are padded with a fictitious self-loop of rate `1`: the chain stays put and the
holding time is a rate-`1` exponential clock. Jump times therefore count jump–hold clock epochs,
including the fictitious ones, and diverge almost surely from an absorbing state even though the
state never changes; this does not affect explosion. For Theorem 2 the countable-state chain uses
the generic jump–hold construction `StochasticCRNNonExplosion.JumpHold` (i.i.d. steps with the
jump kernel and rate-`1` exponential clocks), with the jump kernel given by the rates `q` and
holding rate `q(x)` (or `1` at an absorbing state); it is stated for every initial state in the
support of `π`, which covers every initial distribution supported there.

Sources: D. F. Anderson, D. Cappelletti, M. Koyama, T. G. Kurtz, "Non-explosivity of
stochastically modeled reaction networks that are complex balanced", Bull. Math. Biol. 80 (2018)
2561–2579, Sections 3–4, Condition 1, equations (3) and (13), Definitions 1, 3 and 4, Theorems 2
and 3 (arXiv:1708.09356).
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Dynamics.ComplexBalanced
public import Domains.Biology.Dynamics.StochasticCRNNonExplosion
public import Domains.Biology.Dynamics.StochasticCRNRegeneration
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace WantedExt.Biology.Biophysics.ComplexBalancedNonExplosionWanted

open MeasureTheory ProbabilityTheory Filter
open MathlibExt.Biology.Dynamics MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion

variable {σ : Type*} [DecidableEq σ]

/-- The total jump rate `q(x) = ∑_{y ≠ x} q(x, y)`. -/
noncomputable def totalRate (q : σ → σ → ℝ) (x : σ) : ℝ :=
  ∑' y, if y = x then 0 else q x y

/-- The holding rate: the total rate, or `1` when the total rate is `0`. When the off-diagonal row
`y ↦ q x y` is nonnegative and summable, a zero total means that `x` is absorbing, and the `1` is
a fictitious self-loop. In general a zero total need not mean that: a row that is not summable has
total `0`, and real entries such as `1` and `-1` cancel. -/
noncomputable def holdRate (q : σ → σ → ℝ) (x : σ) : ℝ :=
  if totalRate q x = 0 then 1 else totalRate q x

/-- The jump quotients of the rates: `q(x, y)/q(x)` for `y ≠ x`, and staying put (`1` at `y = x`,
`0` elsewhere) when the total rate `q(x)` is `0`. When the off-diagonal row `y ↦ q x y` is
nonnegative and summable, they are the transition probabilities of the jump chain. In general they
are raw quotients: for a row with off-diagonal entries `2` and `-1` the total is `1` and one
quotient is `-1`. -/
noncomputable def jumpProb (q : σ → σ → ℝ) (x y : σ) : ℝ :=
  if totalRate q x = 0 then (if y = x then 1 else 0)
  else (if y = x then 0 else q x y / totalRate q x)

/-- **A stationary weight with integrable rates prevents explosion** (Anderson–Cappelletti–
Koyama–Kurtz 2018, Theorem 2). Let `σ` be countable with measurable singletons and let the rates
`q` satisfy Condition 1: `q x y ≥ 0`; for every `x` the off-diagonal rates `y ↦ q x y` are
summable; and for every `x`, `y ↦ q y x` is bounded above. Let `π` be a probability distribution
(`π x ≥ 0`, `∑ π = 1`) that is a constant solution of the forward equation: for every `x`, the
family `y ↦ π y q y x` (`y ≠ x`) is summable with sum `π x q(x)`; and assume `x ↦ π x q(x)` is
summable. Let `P` be the jump kernel of the rates (`P x y = q(x, y)/q(x)` for `y ≠ x`, and
`P x x = 1` at an absorbing state, `jumpProb q`), and run the jump–hold chain
`StochasticCRNNonExplosion.JumpHold` with this kernel and holding rate `holdRate q` (the total
rate `q(x)`, padded to `1` at an absorbing state by a fictitious self-loop, so that the jump
times count jump–hold clock epochs, which diverge almost surely even from an absorbing state).
Then from every initial state `x₀` in the support of `π` (`π x₀ ≠ 0`) the chain is
non-explosive: almost surely its jump times tend to infinity.

Source: D. F. Anderson, D. Cappelletti, M. Koyama, T. G. Kurtz, "Non-explosivity of
stochastically modeled reaction networks that are complex balanced", Bull. Math. Biol. 80 (2018)
2561–2579, Theorem 2. -/
theorem_wanted ae_tendsto_jumpTime_of_stationary [Countable σ] [MeasurableSpace σ]
    [MeasurableSingletonClass σ] {q : σ → σ → ℝ} (hq : ∀ x y, 0 ≤ q x y)
    (hsum : ∀ x, Summable fun y => if y = x then 0 else q x y)
    (hbdd : ∀ x, BddAbove (Set.range fun y => q y x)) {π : σ → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hπ1 : HasSum π 1)
    (hfwd : ∀ x, HasSum (fun y => if y = x then 0 else π y * q y x) (π x * totalRate q x))
    (h13 : Summable fun x => π x * totalRate q x) (P : σ → PMF σ)
    (hP : ∀ x y, (P x y).toReal = jumpProb q x y) (x₀ : σ) (hx₀ : π x₀ ≠ 0) :
    ∀ᵐ ω ∂(JumpHold.inputMeasure P),
      Tendsto (JumpHold.jumpTime (holdRate q) x₀ ω) atTop atTop

open ComplexBalanced StochasticCRNRegeneration

variable {S ρ : Type*} [Fintype S] [Fintype ρ]

/-- **Complex-balanced stochastic mass-action systems are non-explosive** (Anderson–Cappelletti–
Koyama–Kurtz 2018, Theorem 3). Let `N` have finitely many species and reactions, let all rate
constants `κ r` be positive, and suppose the deterministic mass-action system is complex balanced
(`N.IsComplexBalanced κ c`) at some `c` with all entries positive. Then the stochastic
mass-action chain `massAction N κ` (`StochasticCRNRegeneration.massAction`, with absorbing
states padded by a rate-`1` fictitious self-loop) is non-explosive from every initial state `x₀`:
almost surely under its step law `inputMeasure`, its jump times `jumpTime x₀` tend to infinity.

Source: D. F. Anderson, D. Cappelletti, M. Koyama, T. G. Kurtz, "Non-explosivity of
stochastically modeled reaction networks that are complex balanced", Bull. Math. Biol. 80 (2018)
2561–2579, Theorem 3. -/
theorem_wanted ae_tendsto_jumpTime_of_isComplexBalanced (N : ReactionNetwork S ρ)
    {κ : ρ → ℝ} (hκ : ∀ r, 0 < κ r) {c : S → ℝ} (hc : ∀ s, 0 < c s)
    (hcb : N.IsComplexBalanced κ c) (x₀ : S → ℕ) :
    ∀ᵐ ω ∂(massAction N κ fun r => (hκ r).le).inputMeasure,
      Tendsto ((massAction N κ fun r => (hκ r).le).jumpTime x₀ ω) atTop atTop

end WantedExt.Biology.Biophysics.ComplexBalancedNonExplosionWanted
