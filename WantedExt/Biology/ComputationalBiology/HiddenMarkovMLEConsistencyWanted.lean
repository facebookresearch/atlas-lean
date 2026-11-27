/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Consistency of maximum likelihood for finite hidden Markov models

Baum and Petrie (1966) state that for a stationary hidden Markov model whose hidden chain and
observations take values in finite sets, the maximum likelihood estimator is consistent, with the
parameter identified only up to the equivalence of parameters that induce the same law of the
observations (for example, relabelling the hidden states). Douc, Moulines and Rydén (2004,
Theorem 1) prove strong consistency in a general setting under assumptions (A1)–(A5), where (A5)
is identifiability. In the finite positive model below their regularity assumptions reduce to
positivity, continuity and compactness, but these do not imply (A5): two distinct parameters with
the same weights give the same observation law. Without (A5) the estimator converges only to the
equivalence class of the true parameter (`tendsto_infDist_equivClass`); convergence to the
parameter itself needs (A5) as the separate hypothesis `hid` of `tendsto_mle_of_identifiable`.
Their Theorem 1 is stated for a conditional likelihood; their Section 4 compares it with the
stationary likelihood used here.

The model here: hidden states `Fin r`, symbols `Fin K`, a parameter set `Θ` that is a nonempty
compact subset of `ℝ^p`, and maps `θ ↦ (P_θ, e_θ, π_θ)` continuous on `Θ`, where `P_θ` is a
transition matrix and `e_θ` an emission matrix with all entries positive on `Θ`, and `π_θ` is a
stationary distribution of `P_θ`. Each `θ` gives the hidden Markov model
`Cslib.MachineLearning.Sequence.HiddenMarkov.HMM` with initial weights `π_θ`, transitions `P_θ`
and emissions `e_θ`, and its `likelihood` of the observations `y_0, …, y_n` is

  `p̄_θ(y_0, …, y_n) = ∑_{x_0, …, x_n} π_θ(x_0) e_θ(x_0, y_0)
    ∏_{i=1}^n P_θ(x_{i-1}, x_i) e_θ(x_i, y_i)`.

The observations `Y_0, Y_1, …` form the stationary observation process of `θ*`: their law `Q` on
`ℕ → Fin K` has these cylinder probabilities at `θ = θ*`. The log-likelihood of the first
`n + 1` observations is `𝓛_n(θ) = log p̄_θ(Y_0, …, Y_n)` (the full stationary joint likelihood),
and an estimator is any sequence of measurable maps, the `n`-th a function of `Y_0, …, Y_n` only,
choosing a maximizer of `𝓛_n` over `Θ`. Two parameters are equivalent when they give the same
observation law.

Not recorded here: asymptotic normality (Douc, Moulines and Rydén 2004, Theorem 4), whose
statement for the full parameter set needs a characterization of the equivalence classes beyond
the chart-restricted form; and the models with continuous observations.

Sources: L. E. Baum and T. Petrie, "Statistical inference for probabilistic functions of finite
state Markov chains", Annals of Mathematical Statistics 37 (1966) 1554–1563,
doi:10.1214/aoms/1177699147; R. Douc, É. Moulines and T. Rydén, "Asymptotic properties of the
maximum likelihood estimator in autoregressive models with Markov regime", Annals of Statistics
32 (2004) 2254–2304, doi:10.1214/009053604000000021, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.HiddenMarkovMLEConsistencyWanted

open MeasureTheory Filter Topology
open Cslib.MachineLearning.Sequence.HiddenMarkov (HMM likelihood)

/-- **Finite hidden Markov model family.** On `r` hidden states and `K` symbols, over a parameter
set `Θ ⊆ ℝ^p`: transition weights `P θ`, emission weights `e θ` and initial weights `π θ`, which
may be any reals (all zero, for example). `HMMFamily.Regular` assumes that on `Θ` they are
positive transition and emission probabilities and a stationary initial probability vector,
continuous in `θ`. -/
structure HMMFamily (p r K : ℕ) where
  /-- The parameter set. -/
  Θ : Set (EuclideanSpace ℝ (Fin p))
  /-- Transition weights `P_θ(x, x')`; transition probabilities on `Θ` under `HMMFamily.Regular`. -/
  P : EuclideanSpace ℝ (Fin p) → Fin r → Fin r → ℝ
  /-- Emission weights `e_θ(x, y)`; emission probabilities on `Θ` under `HMMFamily.Regular`. -/
  e : EuclideanSpace ℝ (Fin p) → Fin r → Fin K → ℝ
  /-- Initial weights `π_θ(x)`; a stationary probability vector of `P_θ` on `Θ` under
  `HMMFamily.Regular`. -/
  π : EuclideanSpace ℝ (Fin p) → Fin r → ℝ

/-- The **standing assumptions**: `Θ` is nonempty and compact; on `Θ` the maps are continuous,
all transition and emission probabilities are positive, rows sum to `1`, and `π_θ` is a
stationary probability vector of `P_θ`. -/
structure HMMFamily.Regular {p r K : ℕ} (M : HMMFamily p r K) : Prop where
  /-- `Θ` is nonempty. -/
  nonempty : M.Θ.Nonempty
  /-- `Θ` is compact. -/
  compact : IsCompact M.Θ
  /-- `θ ↦ P_θ(x, x')` is continuous on `Θ`. -/
  contP : ∀ x x', ContinuousOn (fun θ => M.P θ x x') M.Θ
  /-- `θ ↦ e_θ(x, y)` is continuous on `Θ`. -/
  conte : ∀ x y, ContinuousOn (fun θ => M.e θ x y) M.Θ
  /-- `θ ↦ π_θ(x)` is continuous on `Θ`. -/
  contπ : ∀ x, ContinuousOn (fun θ => M.π θ x) M.Θ
  /-- Transition probabilities are positive on `Θ`. -/
  P_pos : ∀ θ ∈ M.Θ, ∀ x x', 0 < M.P θ x x'
  /-- Emission probabilities are positive on `Θ`. -/
  e_pos : ∀ θ ∈ M.Θ, ∀ x y, 0 < M.e θ x y
  /-- Transition rows sum to `1`. -/
  P_sum : ∀ θ ∈ M.Θ, ∀ x, ∑ x', M.P θ x x' = 1
  /-- Emission rows sum to `1`. -/
  e_sum : ∀ θ ∈ M.Θ, ∀ x, ∑ y, M.e θ x y = 1
  /-- `π_θ` is nonnegative. -/
  π_nonneg : ∀ θ ∈ M.Θ, ∀ x, 0 ≤ M.π θ x
  /-- `π_θ` has total mass `1`. -/
  π_sum : ∀ θ ∈ M.Θ, ∑ x, M.π θ x = 1
  /-- `π_θ` is stationary for `P_θ`. -/
  π_stationary : ∀ θ ∈ M.Θ, ∀ x', ∑ x, M.π θ x * M.P θ x x' = M.π θ x'

/-- The raw `HMM` structure built from the parameter weights `M.π θ`, `M.P θ`, and `M.e θ`. When
`M` is regular (`M.Regular`) and `θ ∈ M.Θ`, these weights are stochastic with stationary initial
law `M.π θ`, and `likelihood (M.toHMM θ) y n` is the stationary observation probability
`p̄_θ(y_0, …, y_n)`. -/
def HMMFamily.toHMM {p r K : ℕ} (M : HMMFamily p r K) (θ : EuclideanSpace ℝ (Fin p)) :
    HMM (Fin r) (Fin K) ℝ where
  init := M.π θ
  trans := M.P θ
  emit := M.e θ

/-- Cylinder-measure identity equating the real-valued cylinder measures
`Q.real {ω | ∀ i : Fin (n + 1), ω i = y i}` to `likelihood (M.toHMM θ) y n` for every `n` and
every sequence `y`. When `M` is regular (`M.Regular`), `θ ∈ M.Θ`, and `Q` is a probability
measure, this expresses that `Q` is the stationary observation law of `θ`. -/
def HMMFamily.IsObsLaw {p r K : ℕ} (M : HMMFamily p r K) (θ : EuclideanSpace ℝ (Fin p))
    (Q : Measure (ℕ → Fin K)) : Prop :=
  ∀ (n : ℕ) (y : ℕ → Fin K),
    Q.real {ω | ∀ i : Fin (n + 1), ω i = y i} = likelihood (M.toHMM θ) y n

/-- Raw likelihood equality: `likelihood (M.toHMM θ) y n = likelihood (M.toHMM θ') y n` for every
`n` and every observation sequence `y`. When `M` is regular (`M.Regular`) and `θ, θ' ∈ M.Θ`, this
expresses equality of the stationary observation laws of `θ` and `θ'`. -/
def HMMFamily.Equiv {p r K : ℕ} (M : HMMFamily p r K) (θ θ' : EuclideanSpace ℝ (Fin p)) :
    Prop :=
  ∀ (n : ℕ) (y : ℕ → Fin K), likelihood (M.toHMM θ) y n = likelihood (M.toHMM θ') y n

/-- **Log-likelihood.** `𝓛_n(θ) = log p̄_θ(Y_0, …, Y_n)` of the first `n + 1` observations, the
logarithm of `likelihood (M.toHMM θ) ω n`. `Real.log` sends `0` to `0` (not `-∞`) and `x < 0` to
`log |x|`; on `Θ` under `HMMFamily.Regular` the likelihood is positive. -/
noncomputable def HMMFamily.logLik {p r K : ℕ} (M : HMMFamily p r K)
    (θ : EuclideanSpace ℝ (Fin p)) (n : ℕ) (ω : ℕ → Fin K) : ℝ :=
  Real.log (likelihood (M.toHMM θ) ω n)

/-- **Maximum likelihood estimator.** Each `θhat n` depends only on the first `n + 1`
observations (two observation sequences that agree up to index `n` get the same estimate), is
measurable, takes values in `Θ`, and maximizes `𝓛_n` over `Θ`. -/
def HMMFamily.IsMLE {p r K : ℕ} (M : HMMFamily p r K)
    (θhat : ℕ → (ℕ → Fin K) → EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ n, (∀ ω ω' : ℕ → Fin K, (∀ i ≤ n, ω i = ω' i) → θhat n ω = θhat n ω') ∧
    Measurable (θhat n) ∧ ∀ ω, θhat n ω ∈ M.Θ ∧
      ∀ θ ∈ M.Θ, M.logLik θ n ω ≤ M.logLik (θhat n ω) n ω

/-- **Consistency up to equivalence** (Baum and Petrie 1966): for a regular finite hidden Markov
family (nonempty compact `Θ`; continuous `P_θ`, `e_θ`, `π_θ` on `Θ`; positive transition and
emission probabilities; `π_θ` a stationary probability vector), a true parameter `θ* ∈ Θ`, its
stationary observation law `Q` (a probability measure) and any maximum likelihood estimator
`θhat`, almost surely the distance from `θhat n` to the set of parameters in `Θ` equivalent to
`θ*` tends to `0`.

Source: Baum and Petrie (1966); Douc, Moulines and Rydén (2004), Theorem 1. -/
public theorem_wanted tendsto_infDist_equivClass {p r K : ℕ} (M : HMMFamily p r K)
    (hM : M.Regular) (θstar : EuclideanSpace ℝ (Fin p)) (hθ : θstar ∈ M.Θ)
    (Q : Measure (ℕ → Fin K)) [IsProbabilityMeasure Q] (hQ : M.IsObsLaw θstar Q)
    (θhat : ℕ → (ℕ → Fin K) → EuclideanSpace ℝ (Fin p)) (hθhat : M.IsMLE θhat) :
    ∀ᵐ ω ∂Q, Tendsto (fun n => Metric.infDist (θhat n ω) {θ ∈ M.Θ | M.Equiv θ θstar}) atTop
      (𝓝 0)

/-- **Strong consistency under identifiability** (Douc, Moulines and Rydén 2004, Theorem 1, in
the finite positive model): for a regular finite hidden Markov family (nonempty compact `Θ`;
continuous `P_θ`, `e_θ`, `π_θ` on `Θ`; positive transition and emission probabilities; `π_θ` a
stationary probability vector), a true parameter `θ* ∈ Θ` that is identifiable in `Θ` (every
`θ ∈ Θ` equivalent to `θ*` equals `θ*`), its stationary observation law `Q` (a probability
measure) and any maximum likelihood estimator `θhat`, almost surely `θhat n → θ*`.

Source: Douc, Moulines and Rydén (2004), Theorem 1. -/
public theorem_wanted tendsto_mle_of_identifiable {p r K : ℕ} (M : HMMFamily p r K)
    (hM : M.Regular) (θstar : EuclideanSpace ℝ (Fin p)) (hθ : θstar ∈ M.Θ)
    (hid : ∀ θ ∈ M.Θ, M.Equiv θ θstar → θ = θstar)
    (Q : Measure (ℕ → Fin K)) [IsProbabilityMeasure Q] (hQ : M.IsObsLaw θstar Q)
    (θhat : ℕ → (ℕ → Fin K) → EuclideanSpace ℝ (Fin p)) (hθhat : M.IsMLE θhat) :
    ∀ᵐ ω ∂Q, Tendsto (fun n => θhat n ω) atTop (𝓝 θstar)

end WantedExt.Biology.ComputationalBiology.HiddenMarkovMLEConsistencyWanted
