/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fast and slow die-out of the SIS epidemic on a finite graph

On a finite connected graph `G` with `n` vertices and adjacency matrix `A`, the SIS (contact)
process is the continuous-time Markov chain on the sets `X ⊆ V` of infected vertices in which a
healthy vertex becomes infected at rate `β` times its number of infected neighbours and an
infected vertex recovers at rate `δ = 1`; the extinction time `τ` is the hitting time of `∅`.
Ganesh, Massoulié and Towsley (2005) showed:

* (Theorem 3.1) if `β ρ(A) < 1`, then `P(X(t) ≠ ∅) ≤ √(n |X(0)|) exp ((β ρ(A) - 1) t)` and
  `E τ ≤ (log n + 1) / (1 - β ρ(A))`;
* (Theorem 4.1) if `β η(m) > 1`, where `η(m)` is the least ratio `E(S, Sᶜ) / |S|` over the
  nonempty vertex sets `S` with `|S| ≤ m` (`m ≤ n / 2`), then with `r = 1 / (β η(m))` the
  extinction time exceeds `⌊r^(-(m-1))⌋ / (2m)` with probability at least
  `((1 - r) / e) (1 + O(r^m))`.

The `O(r^m)` term of Theorem 4.1 is not quantified in the source. It is stated here with the
explicit uniform constant that the source's argument gives: `1 - K r^m` with
`K = sup_{x ≥ 1} x² c^(x-1)`, `c = e^(1/2) / 2` (from a Chernoff bound on the sojourn times),
for `m ≥ 2`. The chain is the continuous-time Markov chain of
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`.

Sources: A. Ganesh, L. Massoulié and D. Towsley, "The effect of network topology on the spread
of epidemics", Proc. IEEE INFOCOM 2005, vol. 2, 1455–1466, Section 2, Theorem 3.1
(Eqs. (2)–(3)), Eq. (4) and Theorem 4.1 (Eqs. (6)–(7)).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.HittingTime
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace WantedExt.Biology.Epidemiology.GraphSISExtinctionTimeWanted

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The total rate of a single transition `S → T` of the SIS process on `G` with infection rate
`β` and recovery rate `δ`: `δ` if `T = S \ {i}` for some `i ∈ S`, and
`β · #{j ∈ S | j ~ i}` if `T = S ∪ {i}` for some `i ∉ S`. -/
noncomputable def jumpRate (G : SimpleGraph V) (β δ : ℝ) (S T : Finset V) : ℝ :=
  ∑ i, ((if i ∈ S ∧ T = S.erase i then δ else 0) +
    (if i ∉ S ∧ T = insert i S then β * ((S.filter (G.Adj i)).card : ℝ) else 0))

/-- The rate matrix of the SIS process on `G`: off the diagonal the single-transition rates,
and on the diagonal minus the total rate out of the state. It is a rate matrix
(`IsRateMatrix`) whenever `β, δ ≥ 0`. -/
noncomputable def sisRateMatrix (G : SimpleGraph V) (β δ : ℝ) :
    Matrix (Finset V) (Finset V) ℝ :=
  fun S T => if T = S then -∑ U ∈ univ.erase S, jumpRate G β δ S U else jumpRate G β δ S T

open Classical in
/-- The spectral radius `ρ(A)` of the adjacency matrix of `G`, as a real number. -/
noncomputable def adjSpectralRadius (G : SimpleGraph V) : ℝ :=
  (spectralRadius ℂ ((G.adjMatrix ℝ).map (algebraMap ℝ ℂ))).toReal

open Classical in
/-- The number `E(S, Sᶜ)` of edges of `G` between `S` and its complement. -/
noncomputable def cutSize (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((univ ×ˢ univ).filter fun p : V × V => p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2).card

/-- The generalized isoperimetric constant `η(G, m)` of Ganesh, Massoulié and Towsley (2005,
Eq. (4)): defined via `sInf` of `E(S, Sᶜ) / |S|` over nonempty vertex sets `S` with `|S| ≤ m`.
When `V` is nonempty and `1 ≤ m`, this finite nonempty set attains its minimum; when no admissible
subset exists (for example `m = 0`), Lean's real infimum convention `sInf ∅ = 0` yields `0`. -/
noncomputable def isoperimetric (G : SimpleGraph V) (m : ℕ) : ℝ :=
  sInf ((fun S : Finset V => (cutSize G S : ℝ) / S.card) '' {S | 0 < S.card ∧ S.card ≤ m})

/-- The constant `K = sup_{x ≥ 1} x² c^(x-1)` with `c = e^(1/2) / 2`, which makes the error
term of Theorem 4.1 explicit. -/
noncomputable def dieOutConstant : ℝ :=
  sSup ((fun x : ℝ => x ^ 2 * (Real.exp (1 / 2) / 2) ^ (x - 1)) '' Set.Ici 1)

/-- **Fast die-out, survival probability** (Ganesh, Massoulié and Towsley 2005, Theorem 3.1,
Eq. (2)). Let `G` be a finite connected graph on `n` vertices with adjacency spectral radius
`ρ(A)`, let `β > 0` with `β ρ(A) < 1`, and run the SIS process with infection rate `β` and
recovery rate `1` from the set `X₀` (`hQ` records that its rate matrix is a rate matrix). Then
for every `t ≥ 0`, `P(X(t) ≠ ∅) ≤ √(n |X₀|) exp ((β ρ(A) - 1) t)`.

Source: A. Ganesh, L. Massoulié and D. Towsley, "The effect of network topology on the spread of
epidemics", in *Proceedings of IEEE INFOCOM 2005*, vol. 2, pp. 1455–1466, Theorem 3.1,
doi:10.1109/INFCOM.2005.1498374. -/
theorem_wanted prob_ne_empty_le (G : SimpleGraph V) (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (hρ : β * adjSpectralRadius G < 1) (hQ : IsRateMatrix (sisRateMatrix G β 1))
    (X₀ : Finset V) (t : ℝ≥0) :
    (ctmcInputMeasure hQ).real {ω | ctmcPath (sisRateMatrix G β 1) X₀ ω t ≠ ∅} ≤
      Real.sqrt (Fintype.card V * X₀.card) * Real.exp ((β * adjSpectralRadius G - 1) * t)

/-- **Fast die-out, expected extinction time** (Ganesh, Massoulié and Towsley 2005,
Theorem 3.1, Eq. (3)). Let `G` be a finite connected graph on `n` vertices with adjacency
spectral radius `ρ(A)`, let `β > 0` with `β ρ(A) < 1`, and run the SIS process with infection
rate `β` and recovery rate `1` from any set `X₀` (`hQ` records that its rate matrix is a rate
matrix). Then the expected extinction time satisfies `E τ ≤ (log n + 1) / (1 - β ρ(A))`.

Source: A. Ganesh, L. Massoulié and D. Towsley, "The effect of network topology on the spread of
epidemics", in *Proceedings of IEEE INFOCOM 2005*, vol. 2, pp. 1455–1466, Theorem 3.1,
doi:10.1109/INFCOM.2005.1498374. -/
theorem_wanted lintegral_extinctionTime_le (G : SimpleGraph V) (hG : G.Connected) (β : ℝ)
    (hβ : 0 < β) (hρ : β * adjSpectralRadius G < 1) (hQ : IsRateMatrix (sisRateMatrix G β 1))
    (X₀ : Finset V) :
    ∫⁻ ω, ctmcHittingTime (sisRateMatrix G β 1) X₀ {∅} ω ∂(ctmcInputMeasure hQ) ≤
      ENNReal.ofReal ((Real.log (Fintype.card V) + 1) / (1 - β * adjSpectralRadius G))

/-- **Slow die-out** (Ganesh, Massoulié and Towsley 2005, Theorem 4.1, Eq. (6), with the error
term made explicit). Let `G` be a finite connected graph on `n` vertices, let `2 ≤ m ≤ n / 2`,
let `β > 0` with `β η(G, m) > 1`, and put `r = 1 / (β η(G, m))`. Run the SIS process with
infection rate `β` and recovery rate `1` from any nonempty set `X₀` (`hQ` records that its rate
matrix is a rate matrix). Then the extinction time `τ` satisfies
`P(τ > ⌊(β η(G, m))^(m-1)⌋ / (2m)) ≥ ((1 - r) / e) (1 - K r^m)`, where
`K = sup_{x ≥ 1} x² (e^(1/2) / 2)^(x-1)` (`dieOutConstant`).

Source: A. Ganesh, L. Massoulié and D. Towsley, "The effect of network topology on the spread of
epidemics", in *Proceedings of IEEE INFOCOM 2005*, vol. 2, pp. 1455–1466, Theorem 4.1,
doi:10.1109/INFCOM.2005.1498374. -/
theorem_wanted prob_extinctionTime_gt_ge (G : SimpleGraph V) (hG : G.Connected) (m : ℕ)
    (hm : 2 ≤ m) (hmn : m ≤ Fintype.card V / 2) (β : ℝ) (hβ : 0 < β)
    (hη : 1 < β * isoperimetric G m) (hQ : IsRateMatrix (sisRateMatrix G β 1))
    (X₀ : Finset V) (hX₀ : X₀.Nonempty) :
    (1 - 1 / (β * isoperimetric G m)) / Real.exp 1 *
        (1 - dieOutConstant * (1 / (β * isoperimetric G m)) ^ m) ≤
      (ctmcInputMeasure hQ).real {ω |
        ENNReal.ofReal (⌊(β * isoperimetric G m) ^ (m - 1)⌋₊ / (2 * m)) <
          ctmcHittingTime (sisRateMatrix G β 1) X₀ {∅} ω}

end WantedExt.Biology.Epidemiology.GraphSISExtinctionTimeWanted
