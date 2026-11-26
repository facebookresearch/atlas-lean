/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Process.Stopping
public import MathlibExt.Probability.BrownianHittingTime
public import MathlibExt.Probability.Process.BrownianStrongMarkovMapISupEqMapAbs

/-!
# Wanted: the strong Markov property of Brownian motion and its consequences

The strong Markov property of real Brownian motion (Mathlib's `IsBrownianReal`) at a stopping time
of its natural filtration, and the two consequences that Le Gall's ENS notes derive from it right
away: the reflection principle (the law of the running maximum is in
`MathlibExt.Probability.Process.BrownianStrongMarkovMapISupEqMapAbs`) and the law of the hitting
time of a level. The statements assume that every path is continuous, as in the notes, so that
suprema over `[0, t]` and hitting times are the classical ones. The repository proves the simple
Markov property for processes with independent increments
(`MathlibExt.Probability.IndependentIncrementsMarkovProperty`) and Mathlib proves the weak Markov
property of pre-Brownian motion (`ProbabilityTheory.IsPreBrownianReal.indepFun_shift`).

## References

* J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires* (ENS lecture notes),
  Théorème 14.5.1, Théorème 14.5.2 and Corollaire 14.5.3.
* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 2,
  section "The strong Markov property of Brownian motion".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExt.Probability.BrownianStrongMarkovWanted

/-- **Strong Markov property of Brownian motion.** Let `B` be a Brownian motion with continuous
paths and measurable coordinates, and `T` a stopping time of its natural filtration with
`P(T < ∞) > 0`. Conditionally on `{T < ∞}`, the process `B^{(T)}_t = B_{T + t} - B_T` is a
Brownian motion independent of the σ-algebra `F_T` of events prior to `T` (Le Gall, ENS notes
*Intégration, Probabilités et Processus Aléatoires*, Théorème 14.5.1; Le Gall, GTM 274,
Chapter 2, section "The strong Markov property of Brownian motion"). -/
theorem_wanted IsBrownianReal.strongMarkov {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t ↦ B t ω) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (Filtration.natural B fun t ↦ (hBm t).stronglyMeasurable) T)
    (hfin : P {ω | T ω ≠ ⊤} ≠ 0) :
    IsBrownianReal (fun t ω ↦ B ((T ω).untopA + t) ω - B (T ω).untopA ω)
        (P[|{ω | T ω ≠ ⊤}]) ∧
      Indep (MeasurableSpace.comap
          (fun ω (t : ℝ≥0) ↦ B ((T ω).untopA + t) ω - B (T ω).untopA ω) inferInstance)
        hT.measurableSpace (P[|{ω | T ω ≠ ⊤}])

/-- **Reflection principle.** For a Brownian motion `B` with continuous paths,
`S_t = sup_{s ≤ t} B s`, `t > 0`, `a ≥ 0` and `b ≤ a`, `P(S_t ≥ a, B_t ≤ b) = P(B_t ≥ 2a - b)`
(Le Gall, ENS notes *Intégration, Probabilités et Processus Aléatoires*, Théorème 14.5.2, proved
by applying the strong Markov property at the hitting time of `a`). -/
theorem_wanted IsBrownianReal.reflection_principle {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t ↦ B t ω) {t : ℝ≥0} (ht : 0 < t) {a b : ℝ} (ha : 0 ≤ a)
    (hba : b ≤ a) :
    P {ω | a ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, B s ω ∧ B t ω ≤ b} = P {ω | 2 * a - b ≤ B t ω}

end MathlibExt.Probability.BrownianStrongMarkovWanted
