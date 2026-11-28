/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace WantedExt.Biology.CriticalBirthDeathSampleWanted

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Independent uniforms for each vertex of the binary genealogical tree: event clock,
birth/death choice, and sampling mark. Vertices use the binary-heap enumeration rooted at `0`. -/
abbrev BirthDeathNoise := (ℕ × Fin 3) → unitInterval

/-- The product law of the event clocks, event choices, and independent sampling marks. -/
noncomputable def noiseLaw : Measure BirthDeathNoise :=
  Measure.infinitePi (fun _ : ℕ × Fin 3 => (volume : Measure unitInterval))

/-- An empty genealogy is `none`; `some H` has `H.length + 1` extant leaves in planar order.
When both daughter branches survive, their boundary divergence has depth `h`. -/
def joinGenealogies (h : ℝ) : Option (List ℝ) → Option (List ℝ) → Option (List ℝ)
  | none, right => right
  | left, none => left
  | some left, some right => some (left ++ [h] ++ right)

/-- A rate-`r` critical birth–death genealogy observed after `h` units, with Bernoulli-`q`
sampling of surviving leaves. The next event has exponential rate `2 * r` and is a birth or
death with equal probability. Birth creates two independent ordered daughter branches.
At the generation cutoff, unresolved branches are omitted. -/
noncomputable def truncatedGenealogy (u : BirthDeathNoise) (r q : ℝ) :
    ℕ → ℕ → ℝ → Option (List ℝ)
  | 0, _, _ => none
  | d + 1, a, h =>
      let lifetime := -Real.log (u (a, 0) : ℝ) / (2 * r)
      if h < lifetime then
        if (u (a, 2) : ℝ) < q then some [] else none
      else if (u (a, 1) : ℝ) < 1 / 2 then
        joinGenealogies (h - lifetime)
          (truncatedGenealogy u r q d (2 * a + 1) (h - lifetime))
          (truncatedGenealogy u r q d (2 * a + 2) (h - lifetime))
      else none

/-- The eventual finite genealogy of the nonexplosive birth–death tree. The value `none` on
noise configurations without an eventual genealogy fixes the value on the exceptional set. -/
noncomputable def genealogy (r q h : ℝ) (u : BirthDeathNoise) : Option (List ℝ) := by
  classical
  exact if hs : ∃ g, ∃ d₀ : ℕ, ∀ d ≥ d₀, truncatedGenealogy u r q d 0 h = g then
    hs.choose else none

/-- Number of sampled extant leaves. -/
def sampleCount : Option (List ℝ) → ℕ
  | none => 0
  | some H => H.length + 1

/-- The birth–death law conditioned on exactly `n` sampled extant individuals. -/
noncomputable def conditionedLaw (r q h : ℝ) (n : ℕ) : Measure BirthDeathNoise :=
  noiseLaw[|{u | sampleCount (genealogy r q h u) = n}]

/-- Consecutive divergence depths, divided by the time-scaling factor `N`.
Index `i : Fin (n - 1)` represents the pair of leaves numbered `i.val + 1` and `i.val + 2`.
The default is used only outside the event of sample size `n`. -/
noncomputable def nodeDepths (r q h N : ℝ) (n : ℕ) (u : BirthDeathNoise) :
    Fin (n - 1) → ℝ :=
  fun i => ((genealogy r q h u).getD []).getD i.val 0 / N

/-- The coalescent point process `∑ k = 1, …, n - 1, δ_(k/n,H_k)`. -/
noncomputable def coalescentPointProcess (n : ℕ) (H : Fin (n - 1) → ℝ) :
    Measure (ℝ × ℝ) :=
  ∑ i : Fin (n - 1), Measure.dirac (((i.val + 1 : ℕ) : ℝ) / n, H i)

/-- The fixed-origin node-depth law with density
`p / (1 + p * x)^2 * (1 + p * t) / (p * t)` on `(0,t)`. -/
noncomputable def nodeDepthLaw (p t : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => if x ∈ Set.Ioo 0 t then
    ENNReal.ofReal (p / (1 + p * x) ^ 2 * ((1 + p * t) / (p * t))) else 0)

/-- **Achaz–Delaporte–Lambert, Theorem 2.1.** Start a planar critical birth–death tree with
birth and death rates `1` at time `N * t` before observation, independently sample its extant
individuals with probability `p / N`, divide times by `N`, and condition on sample size `n`.
For `N,t > 0`, `0 < p < N`, and `n ≥ 1`, the consecutive divergence depths are mutually
independent with the common density `p / (1 + p*x)^2 * (1 + p*t) / (p*t)` on `(0,t)`.
Their joint law equals that of the full extant genealogy of a rate-`p` critical birth–death
tree at time `t`, conditioned on `n` extant individuals. In particular, it is independent of
`N`; the coalescent point process is obtained by `coalescentPointProcess`.

Source: G. Achaz, C. Delaporte and A. Lambert, "Mutational pattern of a sample from a critical
branching population", Journal of Mathematical Biology 73 (2016), 627–664, Theorem 2.1 and
Remark 2.2, https://doi.org/10.1007/s00285-015-0964-2;
preprint https://doi.org/10.48550/arXiv.1407.7720, Section 1.2. -/
public theorem_wanted nodeDepths_iid (N p t : ℝ) (n : ℕ) (hN : 0 < N) (hp : 0 < p)
    (hpN : p < N) (ht : 0 < t) (hn : 1 ≤ n) :
    iIndepFun (fun i : Fin (n - 1) => fun u => nodeDepths 1 (p / N) (N * t) N n u i)
      (conditionedLaw 1 (p / N) (N * t) n) ∧
    (∀ i : Fin (n - 1),
      HasLaw (fun u => nodeDepths 1 (p / N) (N * t) N n u i) (nodeDepthLaw p t)
        (conditionedLaw 1 (p / N) (N * t) n)) ∧
    Measure.map (nodeDepths 1 (p / N) (N * t) N n)
        (conditionedLaw 1 (p / N) (N * t) n) =
      Measure.map (nodeDepths p 1 t 1 n) (conditionedLaw p 1 t n)

end WantedExt.Biology.CriticalBirthDeathSampleWanted
