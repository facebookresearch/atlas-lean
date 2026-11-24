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

For Theorem 3, a reaction network on finitely many species `S` has reactions `y_r → y'_r` with
complexes in `ℕ^S` and rate constants `κ_r > 0`; the stochastic mass-action intensity of `r` at
`x ∈ ℕ^S` is `κ_r ∏_s x_s! / (x_s - y_{r,s})!` (zero unless `x ≥ y_r`), and
`q(x, y)` is the sum of the intensities of the reactions with `x - y_r + y'_r = y`. The system is
complex balanced if some `c` with all entries positive satisfies, at every complex `z`,
`∑_{r : y_r = z} κ_r c^{y_r} = ∑_{r : y'_r = z} κ_r c^{y_r}`; such a `c` is a positive
equilibrium, so this is the source's Definition 4.

Conventions. Absorbing states are given a fictitious self-loop of rate `1`, which does not affect
explosion. Reactions with `y_r = y'_r` contribute only to the diagonal and are ignored, and
parallel reactions add their intensities, as in the source's `q(x, y)`. The initial distribution
is arbitrary in Theorem 3; in Theorem 2 it is any distribution supported in the support of `π`.

Sources: D. F. Anderson, D. Cappelletti, M. Koyama, T. G. Kurtz, "Non-explosivity of
stochastically modeled reaction networks that are complex balanced", Bull. Math. Biol. 80 (2018)
2561–2579, Sections 3–4, Condition 1, equations (3) and (13), Definitions 1, 3 and 4, Theorems 2
and 3 (arXiv:1708.09356).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace WantedExt.Biology.Biophysics.ComplexBalancedNonExplosionWanted

open MeasureTheory ProbabilityTheory Filter

variable {σ : Type*} [DecidableEq σ]

/-- The total jump rate `q(x) = ∑_{y ≠ x} q(x, y)`. -/
noncomputable def totalRate (q : σ → σ → ℝ) (x : σ) : ℝ :=
  ∑' y, if y = x then 0 else q x y

/-- The holding rate: the total rate, or `1` at an absorbing state (a fictitious self-loop). -/
noncomputable def holdRate (q : σ → σ → ℝ) (x : σ) : ℝ :=
  if totalRate q x = 0 then 1 else totalRate q x

/-- The transition probabilities of the jump chain: `q(x, y)/q(x)` for `y ≠ x`, and staying put
at an absorbing state. -/
noncomputable def jumpProb (q : σ → σ → ℝ) (x y : σ) : ℝ :=
  if totalRate q x = 0 then (if y = x then 1 else 0)
  else (if y = x then 0 else q x y / totalRate q x)

/-- `(Y, E)` under the probability measure `P` is a jump–hold realization of the chain with rates
`q`: each `Y n` is measurable; the finite-dimensional laws of `Y` are those of a Markov chain with
transition probabilities `jumpProb q` (and arbitrary initial law); the clocks `E n` are
independent, each exponential of rate `1`; and the clocks are independent of the jump chain. -/
def IsJumpHold [MeasurableSpace σ] (q : σ → σ → ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → σ) (E : ℕ → Ω → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ n, Measurable (Y n)) ∧
    (∀ (n : ℕ) (ys : Fin (n + 2) → σ),
      P {ω | ∀ i : Fin (n + 2), Y i ω = ys i} =
        P {ω | Y 0 ω = ys 0} *
          ∏ i : Fin (n + 1), ENNReal.ofReal (jumpProb q (ys i.castSucc) (ys i.succ))) ∧
    (∀ n, HasLaw (E n) (expMeasure 1) P) ∧ iIndepFun E P ∧
    IndepFun (fun ω n => E n ω) (fun ω n => Y n ω) P

/-- The `n`-th jump time `T_n = ∑_{k < n} E_k / holdRate (Y_k)`. -/
noncomputable def jumpTime (q : σ → σ → ℝ) {Ω : Type*} (Y : ℕ → Ω → σ) (E : ℕ → Ω → ℝ)
    (ω : Ω) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, E k ω / holdRate q (Y k ω)

/-- **A stationary weight with integrable rates prevents explosion** (Anderson–Cappelletti–
Koyama–Kurtz 2018, Theorem 2). Let `σ` be countable with measurable singletons and let the rates
`q` satisfy Condition 1: `q x y ≥ 0`; for every `x` the off-diagonal rates `y ↦ q x y` are
summable; and for every `x`, `y ↦ q y x` is bounded above. Let `π` be a probability distribution
(`π x ≥ 0`, `∑ π = 1`) that is a constant solution of the forward equation: for every `x`, the
family `y ↦ π y q y x` (`y ≠ x`) is summable with sum `π x q(x)`; and assume `x ↦ π x q(x)` is
summable. Then every jump–hold realization whose initial state lies almost surely in the support
of `π` (`π (Y 0) ≠ 0` almost surely) is non-explosive: almost surely the jump times tend to
infinity.

Source: D. F. Anderson, D. Cappelletti, M. Koyama, T. G. Kurtz, Bull. Math. Biol. 80 (2018)
2561–2579, Theorem 2. -/
theorem_wanted ae_tendsto_jumpTime_of_stationary [Countable σ] [MeasurableSpace σ]
    [MeasurableSingletonClass σ] {q : σ → σ → ℝ} (hq : ∀ x y, 0 ≤ q x y)
    (hsum : ∀ x, Summable fun y => if y = x then 0 else q x y)
    (hbdd : ∀ x, BddAbove (Set.range fun y => q y x)) {π : σ → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hπ1 : HasSum π 1)
    (hfwd : ∀ x, HasSum (fun y => if y = x then 0 else π y * q y x) (π x * totalRate q x))
    (h13 : Summable fun x => π x * totalRate q x) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : ℕ → Ω → σ} {E : ℕ → Ω → ℝ} (hY : IsJumpHold q P Y E)
    (hsupp : ∀ᵐ ω ∂P, π (Y 0 ω) ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (jumpTime q Y E ω) atTop atTop

open MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*} [Fintype S] [Fintype ρ]

/-- The stochastic mass-action intensity `κ_r ∏_s x_s (x_s - 1) ⋯ (x_s - y_{r,s} + 1)` of
reaction `r` at `x` (zero unless `x ≥ src r`). -/
noncomputable def intensity (N : ReactionNetwork S ρ) (κ : ρ → ℝ) (r : ρ) (x : S → ℕ) : ℝ :=
  κ r * ∏ s, ((x s).descFactorial (N.src r s) : ℝ)

/-- The jump rates of the stochastic mass-action system: `q(x, y)` is the sum of the intensities
of the reactions `r` with `x - src r + prod r = y` (only reactions with `src r ≤ x` have positive
intensity). -/
noncomputable def massActionRate (N : ReactionNetwork S ρ) (κ : ρ → ℝ) (x y : S → ℕ) : ℝ :=
  ∑ r, if x - N.src r + N.prod r = y then intensity N κ r x else 0

/-- The deterministic mass-action system is complex balanced at `c`: at every complex `z`, the
total rate of reactions leaving `z` equals the total rate of reactions arriving at `z`, with
reaction rates `κ_r c^{src r}`. -/
def IsComplexBalancedAt (N : ReactionNetwork S ρ) (κ : ρ → ℝ) (c : S → ℝ) : Prop :=
  ∀ z : S → ℕ, ∑ r ∈ Finset.univ.filter (fun r => N.src r = z), κ r * ∏ s, c s ^ N.src r s =
    ∑ r ∈ Finset.univ.filter (fun r => N.prod r = z), κ r * ∏ s, c s ^ N.src r s

/-- **Complex-balanced stochastic mass-action systems are non-explosive** (Anderson–Cappelletti–
Koyama–Kurtz 2018, Theorem 3). Let `N` have finitely many species and reactions, let all rate
constants `κ r` be positive, and suppose the deterministic mass-action system is complex balanced
at some `c` with all entries positive. Then every jump–hold realization of the stochastic
mass-action system, with an arbitrary initial distribution, is non-explosive: almost surely its
jump times tend to infinity.

Source: D. F. Anderson, D. Cappelletti, M. Koyama, T. G. Kurtz, Bull. Math. Biol. 80 (2018)
2561–2579, Theorem 3. -/
theorem_wanted ae_tendsto_jumpTime_of_isComplexBalanced (N : ReactionNetwork S ρ)
    {κ : ρ → ℝ} (hκ : ∀ r, 0 < κ r) {c : S → ℝ} (hc : ∀ s, 0 < c s)
    (hcb : IsComplexBalancedAt N κ c) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → S → ℕ} {E : ℕ → Ω → ℝ} (hY : IsJumpHold (massActionRate N κ) P Y E) :
    ∀ᵐ ω ∂P, Tendsto (jumpTime (massActionRate N κ) Y E ω) atTop atTop

end WantedExt.Biology.Biophysics.ComplexBalancedNonExplosionWanted
