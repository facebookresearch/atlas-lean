/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Law of large numbers for the SIR epidemic on a random graph with given degrees

Janson, Luczak and Windridge (2014) study the Markovian SIR epidemic on the configuration-model
multigraph `G*` with a given degree sequence `d_1, …, d_n` (a uniformly random perfect matching
of the half-edges), and on the uniform simple graph `G` with these degrees (`G*` conditioned on
having no loops or multiple edges). Each edge from an infective to a susceptible vertex
transmits at rate `β`, and infectives recover at rate `ρ`. Revealing the matching as the
epidemic runs gives the same law of the vertex counts as fixing the graph first, which is the
form used here. With `n_{S,k}` the number of initially susceptible vertices of degree `k`, they
assume (D1)–(D6): `n_S/n → α_S > 0`, `n_I/n → α_I`, `n_R/n → α_R`; `n_{S,k}/n_S → p_k` for
every `k`, for a probability law `(p_k)` with mean `λ ∈ (0, ∞)`, and the mean degree of the
susceptibles tends to `λ`; `∑ d_i/n → μ > 0` and the total degrees of the initially susceptible,
infective and recovered vertices, divided by `n`, tend to `μ_S`, `μ_I` and `μ_R`; the largest
degree of an initial infective is `o(n)`; and `p_1 > 0` or `ρ > 0` or `μ_R > 0`. For the simple
graph they add (G1): `∑ d_i² = O(n)`. With
`v_S(θ) = α_S ∑ p_k θ^k`, `h_S(θ) = α_S ∑ k p_k θ^k`, `h_X(θ) = μ θ²`,
`h_R(θ) = μ_R θ + (μ ρ / β) θ (1 - θ)`, `h_I = h_X - h_S - h_R` and `p_I = h_I / h_X`, their
Theorems 2.6–2.7 give, when `μ_I > 0`: a unique `θ_∞ ∈ (0, 1)` with `h_I(θ_∞) = 0`; a unique
solution of `θ' = -β θ p_I(θ)`, `θ_0 = 1`, decreasing to `θ_∞`; and convergence in probability,
uniformly in time, of `S_t/n`, `I_t/n`, `R_t/n` and the number `X_{S,t}/n` of susceptible
half-edges to `v_S(θ_t)`, `Î_t`, `R̂_t = 1 - v_S(θ_t) - Î_t` and `h_S(θ_t)`, where
`Î' = β h_I h_S / h_X - ρ Î`, `Î_0 = α_I`; and `S_∞/n → v_S(θ_∞)`. Their Theorems 2.9–2.10
treat few initial infectives (`α_I = μ_I = 0`): with
`R₀ = (β / (ρ + β)) (α_S / μ) ∑ (k - 1) k p_k`, the outbreak infects `o_p(n)` vertices if
`R₀ ≤ 1`, while if `R₀ > 1` the number of susceptibles falls below `n s₀` with probability
bounded away from `0`, for every `s₀ ∈ (v_S(θ_∞), α_S)`. On the multigraph these hold without
(G1) (the remark after Theorem 2.9); when `(p_k)` has no second moment, `R₀ = ∞` and the epidemic
is supercritical (end of Section 7), so `R₀` is taken with values in `[0, ∞]`.

The statements below cover these conclusions for the vertex counts and the susceptible
half-edges; the source's convergence of the free infective and recovered half-edge counts, which
depend on the revealed matching, is not stated. The chain is the continuous-time Markov chain of
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`; vertex states are coded
`0` (susceptible), `1` (infective) and `2` (recovered).

Sources: S. Janson, M. Luczak and P. Windridge, "Law of large numbers for the SIR epidemic on a
random graph with given degrees", Random Structures Algorithms 45 (2014) 726–763, conditions
(D1)–(D6) and (G1), Eqs. (2.11)–(2.24), Theorems 2.6, 2.7, 2.9 and 2.10 (arXiv:1308.5493).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace WantedExt.Biology.Epidemiology.ConfigurationModelSIRWanted

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal ENNReal

/-! ### The random graphs -/

/-- The half-edges of the degree sequence `d`: vertex `i` carries `d i` of them. -/
abbrev HalfEdge {n : ℕ} (d : Fin n → ℕ) : Type := Σ i : Fin n, Fin (d i)

/-- The perfect matchings of the half-edges: fixed-point-free involutions. -/
abbrev Matching {n : ℕ} (d : Fin n → ℕ) : Type :=
  {σ : Equiv.Perm (HalfEdge d) // ∀ h, σ h ≠ h ∧ σ (σ h) = h}

/-- The multiplicity matrix of the multigraph of a matching: `mult σ i j` is the number of
half-edges at `i` matched to a half-edge at `j` (the number of edges between `i ≠ j`). -/
def mult {n : ℕ} {d : Fin n → ℕ} (σ : Matching d) (i j : Fin n) : ℕ :=
  (univ.filter fun h : HalfEdge d => h.1 = i ∧ (σ.1 h).1 = j).card

/-- The multigraph of a matching is simple: no loops and no multiple edges. -/
def IsSimple {n : ℕ} {d : Fin n → ℕ} (σ : Matching d) : Prop :=
  (∀ i, mult σ i i = 0) ∧ ∀ i j, mult σ i j ≤ 1

/-! ### The epidemic on a fixed multigraph -/

/-- The total rate of a single transition `x → y` of the SIR epidemic on the multigraph with
multiplicities `M`: a susceptible vertex `i` becomes infective at rate `β ∑_j M i j` over the
infective vertices `j`, and an infective vertex recovers at rate `ρ`. -/
noncomputable def jumpRate {n : ℕ} (M : Fin n → Fin n → ℕ) (β ρ : ℝ) (x y : Fin n → Fin 3) :
    ℝ :=
  ∑ i, ((if x i = 0 ∧ y = Function.update x i 1 then
      β * ∑ j, (if x j = 1 then (M i j : ℝ) else 0) else 0) +
    (if x i = 1 ∧ y = Function.update x i 2 then ρ else 0))

/-- The rate matrix of the SIR epidemic on the multigraph `M`: off the diagonal the
single-transition rates, and on the diagonal minus the total rate out of the state. It is a
rate matrix (`IsRateMatrix`) whenever `β, ρ ≥ 0`. -/
noncomputable def sirRateMatrix {n : ℕ} (M : Fin n → Fin n → ℕ) (β ρ : ℝ) :
    Matrix (Fin n → Fin 3) (Fin n → Fin 3) ℝ :=
  fun x y => if y = x then -∑ z ∈ univ.erase x, jumpRate M β ρ x z else jumpRate M β ρ x y

/-- The number of vertices in state `c` (`0` susceptible, `1` infective, `2` recovered). -/
def count {n : ℕ} (c : Fin 3) (x : Fin n → Fin 3) : ℕ :=
  (univ.filter fun i => x i = c).card

/-- The number `X_S` of susceptible half-edges: the total degree of the susceptible vertices. -/
def susceptibleHalfEdges {n : ℕ} (d : Fin n → ℕ) (x : Fin n → Fin 3) : ℕ :=
  ∑ i ∈ univ.filter (fun i => x i = 0), d i

open Classical in
/-- The probability that the epidemic path started from `x₀` lies in `E`, for the random graph
of the degree sequence `d`: the configuration multigraph `G*` (`simple = false`, a uniform
matching) or the uniform simple graph `G` (`simple = true`, a uniform matching conditioned on a
simple multigraph). When no matching qualifies (an odd total degree, or `simple = true` and no
matching gives a simple multigraph), the denominator is `0` and Lean's `x / 0 = 0` convention
makes the value `0` for every `E`. (`hQ` records that each epidemic rate matrix is a rate
matrix.) -/
noncomputable def epidemicProb {n : ℕ} (d : Fin n → ℕ) (simple : Bool) (β ρ : ℝ)
    (hQ : ∀ σ : Matching d, IsRateMatrix (sirRateMatrix (mult σ) β ρ)) (x₀ : Fin n → Fin 3)
    (E : (ℝ≥0 → Fin n → Fin 3) → Prop) : ℝ :=
  (∑ σ : Matching d, if simple → IsSimple σ then
      (ctmcInputMeasure (hQ σ)).real
        {ω | E fun t => ctmcPath (sirRateMatrix (mult σ) β ρ) x₀ ω t} else 0) /
    ((univ.filter fun σ : Matching d => simple → IsSimple σ).card : ℝ)

/-! ### The degree conditions and the limit functions -/

/-- The number of initially susceptible vertices of degree `k`. -/
def numSDeg {n : ℕ} (d : Fin n → ℕ) (x₀ : Fin n → Fin 3) (k : ℕ) : ℕ :=
  (univ.filter fun i => x₀ i = 0 ∧ d i = k).card

/-- The total degree of the initial vertices in state `c`. -/
def degreeSum {n : ℕ} (d : Fin n → ℕ) (x₀ : Fin n → Fin 3) (c : Fin 3) : ℕ :=
  ∑ i ∈ univ.filter (fun i => x₀ i = c), d i

/-- The largest degree of an initially infective vertex (`0` if there is none). -/
def maxInfectiveDegree {n : ℕ} (d : Fin n → ℕ) (x₀ : Fin n → Fin 3) : ℕ :=
  (univ.filter fun i => x₀ i = 1).sup d

/-- The degree conditions (D1)–(D6) of Janson, Luczak and Windridge (2014) for a sequence of
degree sequences `d n` and initial states `x₀ n` on `n` vertices, with limits `α_S, α_I, α_R`,
degree law `p` of mean `λ`, and degree-sum limits `μ, μ_S, μ_I, μ_R`; also the total degree is
even, as a perfect matching of the half-edges requires. -/
structure Conditions (d : (n : ℕ) → Fin n → ℕ) (x₀ : (n : ℕ) → Fin n → Fin 3) (p : ℕ → ℝ)
    (αS αI αR lam μ μS μI μR ρ : ℝ) : Prop where
  /-- Each total degree is even. -/
  even : ∀ n, Even (∑ i, d n i)
  /-- (D1) The fractions of initially susceptible, infective and recovered vertices converge,
  the first to a positive limit. -/
  αS_pos : 0 < αS
  d1S : Tendsto (fun n : ℕ => (count 0 (x₀ n) : ℝ) / n) atTop (𝓝 αS)
  d1I : Tendsto (fun n : ℕ => (count 1 (x₀ n) : ℝ) / n) atTop (𝓝 αI)
  d1R : Tendsto (fun n : ℕ => (count 2 (x₀ n) : ℝ) / n) atTop (𝓝 αR)
  /-- (D2) The degree distribution of the susceptibles converges to the probability law `p`,
  of mean `λ ∈ (0, ∞)`. -/
  p_nonneg : ∀ k, 0 ≤ p k
  hasSum_p : HasSum p 1
  hasSum_mean : HasSum (fun k : ℕ => (k : ℝ) * p k) lam
  lam_pos : 0 < lam
  d2 : ∀ k, Tendsto (fun n : ℕ => (numSDeg (d n) (x₀ n) k : ℝ) / count 0 (x₀ n)) atTop
    (𝓝 (p k))
  /-- (D3) The mean degree of the susceptibles converges to `λ`. -/
  d3 : Tendsto (fun n : ℕ => (degreeSum (d n) (x₀ n) 0 : ℝ) / count 0 (x₀ n)) atTop (𝓝 lam)
  /-- (D4) The degree sums, divided by `n`, converge. -/
  μ_pos : 0 < μ
  d4 : Tendsto (fun n : ℕ => (∑ i, d n i : ℝ) / n) atTop (𝓝 μ)
  d4S : Tendsto (fun n : ℕ => (degreeSum (d n) (x₀ n) 0 : ℝ) / n) atTop (𝓝 μS)
  d4I : Tendsto (fun n : ℕ => (degreeSum (d n) (x₀ n) 1 : ℝ) / n) atTop (𝓝 μI)
  d4R : Tendsto (fun n : ℕ => (degreeSum (d n) (x₀ n) 2 : ℝ) / n) atTop (𝓝 μR)
  /-- (D5) The largest degree of an initial infective is `o(n)`. -/
  d5 : Tendsto (fun n : ℕ => (maxInfectiveDegree (d n) (x₀ n) : ℝ) / n) atTop (𝓝 0)
  /-- (D6) `p_1 > 0`, or `ρ > 0`, or `μ_R > 0`. -/
  d6 : 0 < p 1 ∨ 0 < ρ ∨ 0 < μR

/-- The condition (G1): `∑ d_i² = O(n)`. -/
def SquareSumBound (d : (n : ℕ) → Fin n → ℕ) : Prop :=
  ∃ C : ℝ, ∀ n, (∑ i, (d n i : ℝ) ^ 2) ≤ C * n

/-- `v_S(θ) = α_S ∑_k p_k θ^k` (Eq. (2.11)). -/
noncomputable def vS (αS : ℝ) (p : ℕ → ℝ) (θ : ℝ) : ℝ := αS * ∑' k, p k * θ ^ k

/-- `h_S(θ) = θ v_S'(θ) = α_S ∑_k k p_k θ^k` (Eq. (2.12)). -/
noncomputable def hS (αS : ℝ) (p : ℕ → ℝ) (θ : ℝ) : ℝ := αS * ∑' k : ℕ, (k : ℝ) * p k * θ ^ k

/-- `h_I(θ) = μ θ² - h_S(θ) - μ_R θ - (μ ρ / β) θ (1 - θ)` (Eqs. (2.13)–(2.15)). -/
noncomputable def hI (αS μ μR β ρ : ℝ) (p : ℕ → ℝ) (θ : ℝ) : ℝ :=
  μ * θ ^ 2 - hS αS p θ - (μR * θ + μ * ρ / β * θ * (1 - θ))

/-- The infective pressure `p_I(θ) = h_I(θ) / (μ θ²)` (Eq. (2.18)). -/
noncomputable def pI (αS μ μR β ρ : ℝ) (p : ℕ → ℝ) (θ : ℝ) : ℝ :=
  hI αS μ μR β ρ p θ / (μ * θ ^ 2)

/-- `θ` solves `θ' = -β θ p_I(θ)` on `[0, ∞)` with `θ_0 = 1` (Eq. (2.19)). -/
def IsThetaSolution (αS μ μR β ρ : ℝ) (p : ℕ → ℝ) (θ : ℝ → ℝ) : Prop :=
  θ 0 = 1 ∧ ∀ t, 0 ≤ t →
    HasDerivWithinAt θ (-β * θ t * pI αS μ μR β ρ p (θ t)) (Set.Ici 0) t

/-- The solution `Î_t = e^{-ρ t} α_I + ∫_0^t e^{-ρ (t - s)} β h_I(θ_s) h_S(θ_s) / h_X(θ_s) ds`
of `Î' = β h_I h_S / h_X - ρ Î`, `Î_0 = α_I` (Eq. (2.20)). -/
noncomputable def infectiveLimit (αS αI μ μR β ρ : ℝ) (p : ℕ → ℝ) (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-ρ * t) * αI + ∫ s in (0 : ℝ)..t, Real.exp (-ρ * (t - s)) *
    (β * hI αS μ μR β ρ p (θ s) * hS αS p (θ s) / (μ * θ s ^ 2))

/-- `R₀ = (β / (ρ + β)) (α_S / μ) ∑_k (k - 1) k p_k` (Eq. (2.23)), with values in `[0, ∞]`:
the terms `(k - 1) k p_k` are nonnegative for a degree law `p ≥ 0`, so the sum is `∞` exactly when
`(p_k)` has no second moment, and then `R₀ = ∞` (Janson, Luczak and Windridge 2014, end of
Section 7); when the second moment is finite, `R₀` is the real number of Eq. (2.23). Both claims
about `R₀` assume that the prefactor `β / (ρ + β) · (α_S / μ)` is positive, as it is when `β > 0`,
`ρ ≥ 0`, `α_S > 0` and `μ > 0`; otherwise `ENNReal.ofReal` sends it to `0`, and `R₀ = 0` for
every `p`, since `0 · ∞ = 0` in `ℝ≥0∞`. -/
noncomputable def R0 (αS μ β ρ : ℝ) (p : ℕ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (β / (ρ + β) * (αS / μ)) * ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) - 1) * k * p k)

/-- The number `S_∞` of vertices that are still susceptible at the end of the epidemic (the
counts of susceptibles never increase). -/
noncomputable def finalSusceptible {n : ℕ} (path : ℝ≥0 → Fin n → Fin 3) : ℕ :=
  ⨅ t, count 0 (path t)

/-! ### The theorems -/

/-- **The limit equations** (Janson, Luczak and Windridge 2014, Theorem 2.6(a)–(b)). Assume the
degree conditions (D1)–(D6) (`Conditions`, with limits `α_S, α_I, α_R`, degree law `p` of mean
`λ`, and degree-sum limits `μ, μ_S, μ_I, μ_R`), `β > 0`, `ρ ≥ 0` and `μ_I > 0`. Then (a) there
is a unique `θ_∞ ∈ (0, 1)` with `h_I(θ_∞) = 0`; moreover `h_I > 0` on `(θ_∞, 1]` and `h_I < 0`
on `(0, θ_∞)`; and (b) there is a solution `θ` of `θ' = -β θ p_I(θ)`, `θ_0 = 1` on `[0, ∞)`, any
two such solutions agree on `[0, ∞)`, and it takes values in `(θ_∞, 1]`, is antitone on
`[0, ∞)` and tends to `θ_∞`.

Source: Janson, Luczak and Windridge (2014), Theorem 2.6. -/
theorem_wanted limit_equations (d : (n : ℕ) → Fin n → ℕ) (x₀ : (n : ℕ) → Fin n → Fin 3)
    (p : ℕ → ℝ) (αS αI αR lam μ μS μI μR β ρ : ℝ)
    (hcond : Conditions d x₀ p αS αI αR lam μ μS μI μR ρ) (hβ : 0 < β) (hρ : 0 ≤ ρ)
    (hμI : 0 < μI) :
    ∃ θinf : ℝ, θinf ∈ Set.Ioo 0 1 ∧ hI αS μ μR β ρ p θinf = 0 ∧
      (∀ θ ∈ Set.Ioc θinf 1, 0 < hI αS μ μR β ρ p θ) ∧
      (∀ θ ∈ Set.Ioo 0 θinf, hI αS μ μR β ρ p θ < 0) ∧
      (∀ θ' ∈ Set.Ioo (0 : ℝ) 1, hI αS μ μR β ρ p θ' = 0 → θ' = θinf) ∧
      ∃ θ : ℝ → ℝ, IsThetaSolution αS μ μR β ρ p θ ∧
        (∀ θ' : ℝ → ℝ, IsThetaSolution αS μ μR β ρ p θ' → Set.EqOn θ' θ (Set.Ici 0)) ∧
        (∀ t, 0 ≤ t → θ t ∈ Set.Ioc θinf 1) ∧ AntitoneOn θ (Set.Ici 0) ∧
        Tendsto θ atTop (𝓝 θinf)

/-- **Law of large numbers for the epidemic** (Janson, Luczak and Windridge 2014,
Theorems 2.6(c)–(d) and 2.7). Assume the degree conditions (D1)–(D6) (`Conditions`), `β > 0`,
`ρ ≥ 0` and `μ_I > 0`, and for the simple graph (`simple = true`) also (G1)
(`SquareSumBound`). Let `θ` solve `θ' = -β θ p_I(θ)`, `θ_0 = 1`, let `θ_∞ ∈ (0, 1)` be the
zero of `h_I`, and let `Î` be the solution of Eq. (2.20) (`infectiveLimit`). Then for every
`ε > 0`, the probability that for some `t ≥ 0` one of `|S_t/n - v_S(θ_t)|`, `|I_t/n - Î_t|`,
`|R_t/n - (1 - v_S(θ_t) - Î_t)|`, `|X_{S,t}/n - h_S(θ_t)|` exceeds `ε` tends to `0`, and the
probability that `|S_∞/n - v_S(θ_∞)| > ε` tends to `0`, for the epidemic on the configuration
multigraph (`simple = false`) or on the uniform simple graph (`simple = true`). (`hQ` records
that each epidemic rate matrix is a rate matrix.)

Source: Janson, Luczak and Windridge (2014), Theorems 2.6 and 2.7. -/
theorem_wanted tendsto_epidemicProb_deviation (d : (n : ℕ) → Fin n → ℕ)
    (x₀ : (n : ℕ) → Fin n → Fin 3) (p : ℕ → ℝ) (αS αI αR lam μ μS μI μR β ρ : ℝ)
    (hcond : Conditions d x₀ p αS αI αR lam μ μS μI μR ρ) (hβ : 0 < β) (hρ : 0 ≤ ρ)
    (hμI : 0 < μI) (simple : Bool) (hG1 : simple = true → SquareSumBound d)
    (hQ : ∀ n (σ : Matching (d n)), IsRateMatrix (sirRateMatrix (mult σ) β ρ))
    (θ : ℝ → ℝ) (hθ : IsThetaSolution αS μ μR β ρ p θ) (θinf : ℝ)
    (hθinf : θinf ∈ Set.Ioo 0 1) (hzero : hI αS μ μR β ρ p θinf = 0) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => epidemicProb (d n) simple β ρ (hQ n) (x₀ n) fun path => ∃ t : ℝ≥0,
        ε < |(count 0 (path t) : ℝ) / n - vS αS p (θ t)| ∨
        ε < |(count 1 (path t) : ℝ) / n - infectiveLimit αS αI μ μR β ρ p θ t| ∨
        ε < |(count 2 (path t) : ℝ) / n -
          (1 - vS αS p (θ t) - infectiveLimit αS αI μ μR β ρ p θ t)| ∨
        ε < |(susceptibleHalfEdges (d n) (path t) : ℝ) / n - hS αS p (θ t)|) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => epidemicProb (d n) simple β ρ (hQ n) (x₀ n) fun path =>
        ε < |(finalSusceptible path : ℝ) / n - vS αS p θinf|) atTop (𝓝 0)

/-- **Small outbreaks below threshold** (Janson, Luczak and Windridge 2014, Theorems 2.9(i)
and 2.10). Assume the degree conditions (D1)–(D6) (`Conditions`), `β > 0`, `ρ ≥ 0`,
`α_I = μ_I = 0`, that for every `n ≥ 1` some initially infective vertex has nonzero degree, and
for the simple graph (`simple = true`) also (G1) (`SquareSumBound`). If `R₀ ≤ 1` (so in
particular `(p_k)` has a finite second moment; `R₀` takes values in `[0, ∞]`), then for every
`ε > 0` the probability that more than `ε n` of the initially susceptible vertices ever get
infected (`n_S - S_∞ > ε n`) tends to `0`, on the configuration multigraph (`simple = false`) or
on the uniform simple graph (`simple = true`). (`hQ` records that each epidemic rate matrix is a
rate matrix.)

Source: Janson, Luczak and Windridge (2014), Theorems 2.9 and 2.10. -/
theorem_wanted tendsto_epidemicProb_large_of_R0_le_one (d : (n : ℕ) → Fin n → ℕ)
    (x₀ : (n : ℕ) → Fin n → Fin 3) (p : ℕ → ℝ) (αS αR lam μ μS μR β ρ : ℝ)
    (hcond : Conditions d x₀ p αS 0 αR lam μ μS 0 μR ρ)
    (hβ : 0 < β) (hρ : 0 ≤ ρ) (hinf : ∀ n, 0 < n → ∃ i, x₀ n i = 1 ∧ 0 < d n i)
    (simple : Bool) (hG1 : simple = true → SquareSumBound d)
    (hQ : ∀ n (σ : Matching (d n)), IsRateMatrix (sirRateMatrix (mult σ) β ρ))
    (hR0 : R0 αS μ β ρ p ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => epidemicProb (d n) simple β ρ (hQ n) (x₀ n) fun path =>
      ε * n < (count 0 (x₀ n) : ℝ) - finalSusceptible path) atTop (𝓝 0)

/-- **Large outbreaks above threshold** (Janson, Luczak and Windridge 2014, Theorems 2.9(ii)(a),
(ii)(c) and 2.10). Assume the degree conditions (D1)–(D6) (`Conditions`), `β > 0`, `ρ ≥ 0`,
`α_I = μ_I = 0`, that for every `n ≥ 1` some initially infective vertex has nonzero degree, and
for the simple graph (`simple = true`) also (G1) (`SquareSumBound`). If `R₀ > 1` in `[0, ∞]`
(including `R₀ = ∞`, when `(p_k)` has no second moment), then there is
a unique `θ_∞ ∈ (0, 1)` with `h_I(θ_∞) = 0`, `h_I > 0` on `(θ_∞, 1)` and `h_I < 0` on
`(0, θ_∞)`; and for every `s₀ ∈ (v_S(θ_∞), v_S(1))` there are `c > 0` and, for all large `n`,
probability at least `c` that the number of susceptibles falls to at most `n s₀` at some time
`t > 0` (a large outbreak), on the configuration multigraph (`simple = false`) or on the uniform
simple graph (`simple = true`). (`hQ` records that each epidemic rate matrix is a rate matrix.)

Source: Janson, Luczak and Windridge (2014), Theorems 2.9 and 2.10. -/
theorem_wanted eventually_epidemicProb_large_of_one_lt_R0 (d : (n : ℕ) → Fin n → ℕ)
    (x₀ : (n : ℕ) → Fin n → Fin 3) (p : ℕ → ℝ) (αS αR lam μ μS μR β ρ : ℝ)
    (hcond : Conditions d x₀ p αS 0 αR lam μ μS 0 μR ρ)
    (hβ : 0 < β) (hρ : 0 ≤ ρ) (hinf : ∀ n, 0 < n → ∃ i, x₀ n i = 1 ∧ 0 < d n i)
    (simple : Bool) (hG1 : simple = true → SquareSumBound d)
    (hQ : ∀ n (σ : Matching (d n)), IsRateMatrix (sirRateMatrix (mult σ) β ρ))
    (hR0 : 1 < R0 αS μ β ρ p) :
    ∃ θinf : ℝ, θinf ∈ Set.Ioo 0 1 ∧ hI αS μ μR β ρ p θinf = 0 ∧
      (∀ θ ∈ Set.Ioo θinf 1, 0 < hI αS μ μR β ρ p θ) ∧
      (∀ θ ∈ Set.Ioo 0 θinf, hI αS μ μR β ρ p θ < 0) ∧
      (∀ θ' ∈ Set.Ioo (0 : ℝ) 1, hI αS μ μR β ρ p θ' = 0 → θ' = θinf) ∧
      ∀ s₀ ∈ Set.Ioo (vS αS p θinf) (vS αS p 1), ∃ c > 0, ∀ᶠ n : ℕ in atTop,
        c ≤ epidemicProb (d n) simple β ρ (hQ n) (x₀ n) fun path =>
          ∃ t : ℝ≥0, 0 < t ∧ (count 0 (path t) : ℝ) ≤ n * s₀

end WantedExt.Biology.Epidemiology.ConfigurationModelSIRWanted
