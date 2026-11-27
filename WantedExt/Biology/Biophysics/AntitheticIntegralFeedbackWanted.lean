/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Antithetic integral feedback achieves stochastic set-point tracking

An open-loop stochastic reaction network on `d` species `X_1, …, X_d` has reactions
`k = 1, …, K` with stoichiometry vectors `ζ_k ∈ ℤ^d` and propensities `λ_k : ℕ^d → [0, ∞)`
(positive only where the jump stays in `ℕ^d`). The antithetic controller adds two species
`Z_1`, `Z_2` and the reactions
`∅ → Z_1` (propensity `μ`, reference), `∅ → Z_2` (propensity `θ X_ℓ`, measurement),
`Z_1 + Z_2 → ∅` (propensity `η Z_1 Z_2`, comparison), `∅ → X_1` (propensity `k Z_1`,
actuation). The closed-loop network is ergodic if, from every initial state, the distribution of
`(X(t), Z(t))` converges to a stationary distribution `π` as `t → ∞`.

**Theorem 1** (Briat–Gupta–Khammash 2016). If, for some values of the parameters, the closed-loop
network is ergodic and has uniformly bounded first- and second-order moments, then
`E[X_ℓ(t)] → μ/θ` as `t → ∞`.

**Theorem 2** (Briat–Gupta–Khammash 2016). Suppose the open-loop network is unimolecular,
`λ_k(x) = ∑_i w_{ki} x_i + w_{k0}` with `w_{k0} ≥ 0`, and its state space `𝒮 ⊆ ℕ^d` is
irreducible. Let `S` be the `d × K` matrix with columns `ζ_k` and `W = (w_{ki})`. Assume `SW` is
Hurwitz stable, the output controllability condition `[(SW)^{-1}]_{ℓ1} ≠ 0` holds, and the
set-point is accessible: there are `c > 0` and `v` with positive entries such that every entry of
`vᵀ(SW + c I)` is negative and `μ/θ > vᵀ S w_0/(c v_ℓ)`. Then for every `k, η > 0` the closed loop
is ergodic and `E[X_ℓ(t)] → μ/θ`; the source also displays the limits
`E[X(t)] → μ (SW)^{-1} e_1/(θ [(SW)^{-1}]_{ℓ1})` and `E[Z_1(t)] → -μ/(θ [(SW)^{-1}]_{ℓ1})`.

The displayed limits drop the terms `S w_0` and `k` of the stationary first-moment equations
`0 = SW m + S w_0 + k z e_1`, `m_ℓ = μ/θ` (for `m = lim E[X(t)]`, `z = lim E[Z_1(t)]`), so they
are correct only when `S w_0 = 0` and `k = 1`. For the birth-death network `∅ → X_1` at rate `1`,
`X_1 → ∅` at rate `X_1` (`SW = -1`, `S w_0 = 1`), with `μ = 3`, `θ = 1`, `k = 1`, the equations
give `m = 3` and `z = 2`, while the displayed formula gives `z = 3`. The theorem below states the
limits that solve those equations:
`z = -(μ/θ + ((SW)^{-1} S w_0)_ℓ)/(k [(SW)^{-1}]_{ℓ1})` and
`m = -(SW)^{-1} (S w_0 + k z e_1)`.

Encoding. The closed-loop Markov chain on `ℕ^d × ℕ × ℕ` is realized by its jump chain and
exponential holding times, as in the source's Markov process; the state at time `t` is the state
after the last jump time `≤ t`. Ergodicity requires non-explosion and pointwise convergence of the
time-`t` law to a stationary law `π` (stationary meaning that the time-`t` law stays `π` from the
initial law `π`) from every initial state of the closed-loop state space; uniqueness of `π` among
stationary laws on that space follows. Moments are bounded uniformly in `t ≥ 0`. All controller
parameters `μ, θ, η, k` are positive. The actuated species is `X_1`, indexed `0` here. In
Theorem 2 the closed-loop state space is `𝒮 × ℕ × ℕ`: `𝒮` is required to be closed under the
open-loop reactions and under the actuation `X_1 → X_1 + 1`, so every closed-loop trajectory
started there stays there and the unimolecular form of the propensities is used only on states
the closed loop can reach.

Sources: C. Briat, A. Gupta, M. Khammash, "Antithetic integral feedback ensures robust perfect
adaptation in noisy biomolecular networks", Cell Systems 2 (2016) 15–26, controller (2),
Theorem 1 (General Network Case) and Theorem 2 (Unimolecular Network Case) (arXiv:1410.6064).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Relation
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace WantedExt.Biology.Biophysics.AntitheticIntegralFeedbackWanted

open MeasureTheory ProbabilityTheory Filter Topology Matrix

section JumpHold

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

/-- `(Y, E)` under `P` is a jump–hold realization of the chain with rates `q`: `P` is a
probability measure; each `Y n` is measurable; the probability that `Y` starts with a given path
is that of its first state times the factors `ENNReal.ofReal (jumpProb q y y')` of its steps, so
that `Y` is a Markov chain with transition probabilities `jumpProb q` (and arbitrary initial law)
when every off-diagonal row of `q` is nonnegative and summable; the clocks `E n` are independent
and exponential of rate `1`; and the clocks are independent of `Y`. -/
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

open Classical in
/-- The state at time `t`: `Y n` for the first `n` with `T_n ≤ t < T_{n+1}` (and `Y 0` if there
is none, which happens only after an explosion). -/
noncomputable def stateAt (q : σ → σ → ℝ) {Ω : Type*} (Y : ℕ → Ω → σ) (E : ℕ → Ω → ℝ)
    (ω : Ω) (t : ℝ) : σ :=
  if h : ∃ n, jumpTime q Y E ω n ≤ t ∧ t < jumpTime q Y E ω (n + 1) then Y (Nat.find h) ω
  else Y 0 ω

/-- `π` is a stationary law: it is a probability distribution, and every jump–hold realization
with initial law `π` is non-explosive and has law `π` at every time `t ≥ 0`. -/
def IsStationaryLaw [MeasurableSpace σ] (q : σ → σ → ℝ) (π : σ → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ HasSum π 1 ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → σ) (E : ℕ → Ω → ℝ),
      IsJumpHold q P Y E → (∀ y, (P {ω | Y 0 ω = y}).toReal = π y) →
        (∀ᵐ ω ∂P, Tendsto (jumpTime q Y E ω) atTop atTop) ∧
          ∀ t, 0 ≤ t → ∀ y, (P {ω | stateAt q Y E ω t = y}).toReal = π y

/-- The chain with rates `q` is ergodic on the state space `Λ`: there is a stationary law `π`
such that every jump–hold realization started at a state `x₀ ∈ Λ` is non-explosive and its law at
time `t` converges pointwise to `π` as `t → ∞`. -/
def IsErgodic [MeasurableSpace σ] (q : σ → σ → ℝ) (Λ : Set σ) : Prop :=
  ∃ π : σ → ℝ, IsStationaryLaw q π ∧
    ∀ x₀ ∈ Λ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → σ)
      (E : ℕ → Ω → ℝ), IsJumpHold q P Y E → (∀ᵐ ω ∂P, Y 0 ω = x₀) →
        (∀ᵐ ω ∂P, Tendsto (jumpTime q Y E ω) atTop atTop) ∧
          ∀ y, Tendsto (fun t => (P {ω | stateAt q Y E ω t = y}).toReal) atTop (𝓝 (π y))

end JumpHold

variable {d K : ℕ}

/-- An open-loop stochastic reaction network on the `d + 1` species `X_1, …, X_{d+1}` (indexed
by `Fin (d + 1)`), with stoichiometry vectors `ζ j` and propensities `prop j`: nonnegative, and
positive only at states where the jump stays in `ℕ^{d+1}`. -/
structure OpenLoop (d K : ℕ) where
  /-- The stoichiometry vector of reaction `j`. -/
  ζ : Fin K → Fin (d + 1) → ℤ
  /-- The propensity of reaction `j`. -/
  prop : Fin K → (Fin (d + 1) → ℕ) → ℝ
  prop_nonneg : ∀ j x, 0 ≤ prop j x
  admissible : ∀ j x, 0 < prop j x → ∀ i, 0 ≤ (x i : ℤ) + ζ j i

/-- The state `x + v`, truncated at `0` in each coordinate. -/
def shift (x : Fin (d + 1) → ℕ) (v : Fin (d + 1) → ℤ) : Fin (d + 1) → ℕ :=
  fun i => ((x i : ℤ) + v i).toNat

/-- The jump rates of the closed loop on states `(x, z₁, z₂)`: the open-loop reactions, the
reference `∅ → Z_1` (rate `μ`), the measurement `∅ → Z_2` (rate `θ x_ℓ`), the comparison
`Z_1 + Z_2 → ∅` (rate `η z₁ z₂`) and the actuation `∅ → X_1` (rate `k z₁`). -/
noncomputable def closedLoopRate (net : OpenLoop d K) (μ θ η k : ℝ) (ℓ : Fin (d + 1))
    (p p' : (Fin (d + 1) → ℕ) × ℕ × ℕ) : ℝ :=
  (∑ j, if p' = (shift p.1 (net.ζ j), p.2) then net.prop j p.1 else 0) +
    (if p' = (p.1, p.2.1 + 1, p.2.2) then μ else 0) +
    (if p' = (p.1, p.2.1, p.2.2 + 1) then θ * p.1 ℓ else 0) +
    (if p' = (p.1, p.2.1 - 1, p.2.2 - 1) then η * p.2.1 * p.2.2 else 0) +
    (if p' = (Function.update p.1 0 (p.1 0 + 1), p.2) then k * p.2.1 else 0)

/-- The realization has uniformly bounded first- and second-order moments: there is `M < ∞` with
`E[X_i(t)²] ≤ M`, `E[Z_1(t)²] ≤ M` and `E[Z_2(t)²] ≤ M` for all `t ≥ 0` and all `i` (which bounds
the first and mixed second moments). -/
def HasBoundedMoments (q : ((Fin (d + 1) → ℕ) × ℕ × ℕ) → ((Fin (d + 1) → ℕ) × ℕ × ℕ) → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → (Fin (d + 1) → ℕ) × ℕ × ℕ)
    (E : ℕ → Ω → ℝ) : Prop :=
  ∃ M : ENNReal, M < ⊤ ∧ ∀ t, 0 ≤ t →
    (∀ i, ∫⁻ ω, ((stateAt q Y E ω t).1 i : ENNReal) ^ 2 ∂P ≤ M) ∧
    ∫⁻ ω, ((stateAt q Y E ω t).2.1 : ENNReal) ^ 2 ∂P ≤ M ∧
    ∫⁻ ω, ((stateAt q Y E ω t).2.2 : ENNReal) ^ 2 ∂P ≤ M

/-- **Set-point tracking under ergodicity** (Briat–Gupta–Khammash 2016, Theorem 1). Let `net` be
an open-loop network (propensities nonnegative, and positive only where the jump stays in
`ℕ^{d+1}`), let `μ, θ, η, k > 0`, and let `ℓ` be the regulated species. Suppose the
closed loop is ergodic on a state space `Λ`. Then every jump–hold realization of the closed loop
started at a state of `Λ` with uniformly bounded first- and second-order moments satisfies
`E[X_ℓ(t)] → μ/θ` as `t → ∞`.

Source: C. Briat, A. Gupta, M. Khammash, Cell Systems 2 (2016) 15–26, Theorem 1. -/
theorem_wanted tendsto_expectation_of_isErgodic (net : OpenLoop d K) {μ θ η k : ℝ}
    (hμ : 0 < μ) (hθ : 0 < θ) (hη : 0 < η) (hk : 0 < k) (ℓ : Fin (d + 1))
    {Λ : Set ((Fin (d + 1) → ℕ) × ℕ × ℕ)} (herg : IsErgodic (closedLoopRate net μ θ η k ℓ) Λ)
    {x₀ : (Fin (d + 1) → ℕ) × ℕ × ℕ} (hx₀ : x₀ ∈ Λ) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : ℕ → Ω → (Fin (d + 1) → ℕ) × ℕ × ℕ} {E : ℕ → Ω → ℝ}
    (hY : IsJumpHold (closedLoopRate net μ θ η k ℓ) P Y E) (hY₀ : ∀ᵐ ω ∂P, Y 0 ω = x₀)
    (hmom : HasBoundedMoments (closedLoopRate net μ θ η k ℓ) P Y E) :
    Tendsto (fun t => ∫ ω, ((stateAt (closedLoopRate net μ θ η k ℓ) Y E ω t).1 ℓ : ℝ) ∂P)
      atTop (𝓝 (μ / θ))

/-- One open-loop step: a reaction with positive propensity at `x` fires. -/
def OpenLoop.Step (net : OpenLoop d K) (x y : Fin (d + 1) → ℕ) : Prop :=
  ∃ j, 0 < net.prop j x ∧ y = shift x (net.ζ j)

/-- The stoichiometry matrix `S`, whose column `j` is `ζ j`. -/
def OpenLoop.stoichMatrix (net : OpenLoop d K) : Matrix (Fin (d + 1)) (Fin K) ℝ :=
  fun i j => (net.ζ j i : ℝ)

/-- `A` is Hurwitz stable: every complex eigenvalue of `A` has negative real part. -/
def IsHurwitz {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) : Prop :=
  ∀ (z : ℂ) (v : m → ℂ), v ≠ 0 → (A.map (↑)) *ᵥ v = z • v → z.re < 0

/-- The stationary mean of `Z_1`: `-(μ/θ + (A⁻¹ b)_ℓ)/(k A⁻¹ ℓ 0)`, the value of `z` for which
the solution `m` of `0 = A m + b + k z e_1` has `m_ℓ = μ/θ` (with `b = S w₀`). -/
noncomputable def limZ1 (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (b : Fin (d + 1) → ℝ)
    (μ θ k : ℝ) (ℓ : Fin (d + 1)) : ℝ :=
  -(μ / θ + (A⁻¹ *ᵥ b) ℓ) / (k * A⁻¹ ℓ 0)

/-- The stationary mean of `X`: `-A⁻¹ (b + k z e_1)`, the solution `m` of
`0 = A m + b + k z e_1` (with `b = S w₀` and `e_1` the actuated species, index `0`). -/
noncomputable def limX (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (b : Fin (d + 1) → ℝ)
    (k z : ℝ) : Fin (d + 1) → ℝ :=
  -(A⁻¹ *ᵥ (b + (k * z) • Pi.single 0 1))

/-- **Antithetic control of unimolecular networks** (Briat–Gupta–Khammash 2016, Theorem 2). Let
`net` be an open-loop network (propensities nonnegative, and positive only where the jump stays
in `ℕ^{d+1}`) with state space `𝒮 ⊆ ℕ^{d+1}`: nonempty, closed under open-loop
steps and under the actuation (adding one molecule of `X_1`, index `0`), so that `𝒮 × ℕ × ℕ` is
closed under every closed-loop transition, and irreducible (every state of `𝒮` reaches every
other by open-loop steps). Suppose
`net` is unimolecular on `𝒮`: `prop j x = ∑_i W j i * x i + w₀ j` for `x ∈ 𝒮`, with `w₀ j ≥ 0`.
Let `S` be the stoichiometry matrix and `A = S W`. Assume `A` is Hurwitz stable, the output
controllability condition `A⁻¹ ℓ 0 ≠ 0` holds, and the set-point `μ/θ` (with `μ, θ > 0`) is
accessible: some `c > 0` and `v` with positive entries have `(vᵀ (A + c I))_j < 0` for every `j`
and `vᵀ S w₀ / (c v_ℓ) < μ/θ`. Then for all `η, k > 0` the closed loop is ergodic on `𝒮 × ℕ × ℕ`,
and every jump–hold realization of it started in `𝒮 × ℕ × ℕ` satisfies `E[X_ℓ(t)] → μ/θ`,
`E[X(t)] → limX A (S w₀) k z` coordinatewise and `E[Z_1(t)] → z` with
`z = limZ1 A (S w₀) μ θ k ℓ = -(μ/θ + (A⁻¹ S w₀)_ℓ)/(k A⁻¹ ℓ 0)` and
`limX A (S w₀) k z = -A⁻¹ (S w₀ + k z e_1)`, the solution of the stationary first-moment equations
`0 = A m + S w₀ + k z e_1`, `m_ℓ = μ/θ`. (The source's displayed limits omit `S w₀` and `k`; they
agree with these when `S w₀ = 0` and `k = 1`.)

Source: C. Briat, A. Gupta, M. Khammash, Cell Systems 2 (2016) 15–26, Theorem 2. -/
theorem_wanted isErgodic_and_tendsto_of_unimolecular (net : OpenLoop d K)
    {𝒮 : Set (Fin (d + 1) → ℕ)} (hne : 𝒮.Nonempty)
    (hclosed : ∀ x ∈ 𝒮, ∀ y, net.Step x y → y ∈ 𝒮)
    (hact : ∀ x ∈ 𝒮, Function.update x 0 (x 0 + 1) ∈ 𝒮)
    (hirr : ∀ x ∈ 𝒮, ∀ y ∈ 𝒮, Relation.ReflTransGen net.Step x y)
    (W : Matrix (Fin K) (Fin (d + 1)) ℝ) (w₀ : Fin K → ℝ) (hw₀ : ∀ j, 0 ≤ w₀ j)
    (hlin : ∀ j, ∀ x ∈ 𝒮, net.prop j x = ∑ i, W j i * x i + w₀ j)
    (hHur : IsHurwitz (net.stoichMatrix * W)) (ℓ : Fin (d + 1))
    (hctrl : (net.stoichMatrix * W)⁻¹ ℓ 0 ≠ 0) {μ θ : ℝ} (hμ : 0 < μ) (hθ : 0 < θ)
    (hacc : ∃ c : ℝ, 0 < c ∧ ∃ v : Fin (d + 1) → ℝ, (∀ i, 0 < v i) ∧
      (∀ j, (v ᵥ* (net.stoichMatrix * W + c • (1 : Matrix _ _ ℝ))) j < 0) ∧
      v ⬝ᵥ (net.stoichMatrix *ᵥ w₀) / (c * v ℓ) < μ / θ)
    {η k : ℝ} (hη : 0 < η) (hk : 0 < k) :
    IsErgodic (closedLoopRate net μ θ η k ℓ) (𝒮 ×ˢ Set.univ) ∧
      ∀ x₀ ∈ 𝒮 ×ˢ (Set.univ : Set (ℕ × ℕ)), ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (Y : ℕ → Ω → (Fin (d + 1) → ℕ) × ℕ × ℕ) (E : ℕ → Ω → ℝ),
        IsJumpHold (closedLoopRate net μ θ η k ℓ) P Y E → (∀ᵐ ω ∂P, Y 0 ω = x₀) →
          Tendsto (fun t => ∫ ω, ((stateAt (closedLoopRate net μ θ η k ℓ) Y E ω t).1 ℓ : ℝ) ∂P)
            atTop (𝓝 (μ / θ)) ∧
          (∀ i, Tendsto
            (fun t => ∫ ω, ((stateAt (closedLoopRate net μ θ η k ℓ) Y E ω t).1 i : ℝ) ∂P)
            atTop (𝓝 (limX (net.stoichMatrix * W) (net.stoichMatrix *ᵥ w₀) k
              (limZ1 (net.stoichMatrix * W) (net.stoichMatrix *ᵥ w₀) μ θ k ℓ) i))) ∧
          Tendsto (fun t => ∫ ω, ((stateAt (closedLoopRate net μ θ η k ℓ) Y E ω t).2.1 : ℝ) ∂P)
            atTop (𝓝 (limZ1 (net.stoichMatrix * W) (net.stoichMatrix *ᵥ w₀) μ θ k ℓ))

end WantedExt.Biology.Biophysics.AntitheticIntegralFeedbackWanted
