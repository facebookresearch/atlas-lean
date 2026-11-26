/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.GraphonCounting
public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.GraphonSampling
public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.LimitTheorem

/-!
# Graph limits: compactness and uniqueness (wanted)

Central theorems of the theory of dense graph limits, stated on the repository's homomorphism
densities (`homDensity`, `graphonHomDensity`), cut norms (`cutNorm`, `graphonCutNorm`) and cut
distance (`cutDistance`), with graphons in the sense of the existing `IsGraphon` (jointly
measurable, symmetric, values in `[0, 1]`). The finite counting lemma and the Frieze–Kannan weak
regularity lemma are proved in `MathlibExt.Combinatorics.SimpleGraph.GraphLimits`, and the
Lovász–Szegedy limit theorem in `MathlibExt.Combinatorics.SimpleGraph.GraphLimits.LimitTheorem`.

Sources:
* L. Lovász and B. Szegedy, *Limits of dense graph sequences*, J. Combin. Theory Ser. B 96 (2006),
  933-957, arXiv:math/0408173.
* C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, *Convergent sequences of dense
  graphs I: Subgraph frequencies, metric properties and testing*, Adv. Math. 219 (2008), 1801-1851,
  arXiv:math/0702004.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.GraphLimitsWanted

open MathlibExt.Combinatorics.SimpleGraph.GraphLimits
open MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted (IsGraphon)
open Filter Topology

/-- **Compactness of the graphon space.** Every sequence of graphons has a subsequence converging
in the cut distance to a graphon: after identifying graphons at cut distance `0`, the space of
`[0, 1]`-valued graphons with `δ_□` is compact (Lovász and Szegedy, *Szemerédi's lemma for the
analyst*, Geom. Funct. Anal. 17 (2007), as quoted in Borgs–Chayes–Lovász–Sós–Vesztergombi,
*Convergent sequences of dense graphs I* (2008), Proposition 3.6 with `I = [0, 1]`; stated here
in sequential form). -/
public theorem_wanted exists_subseq_tendsto_cutDistance (W : ℕ → ℝ → ℝ → ℝ)
    (hW : ∀ n, IsGraphon (W n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ W' : ℝ → ℝ → ℝ, IsGraphon W' ∧
      Tendsto (fun n => cutDistance (W (φ n)) W') atTop (𝓝 0)

/-- **Left convergence is cut-distance convergence.** For graphons `Wₙ, W` with values in `[0, 1]`,
`t(F, Wₙ) → t(F, W)` for every simple graph `F` if and only if `δ_□(Wₙ, W) → 0`
(Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs I* (2008),
Theorem 3.8, final statement, with `I = [0, 1]`). -/
public theorem_wanted tendsto_graphonHomDensity_iff_tendsto_cutDistance
    {W : ℕ → ℝ → ℝ → ℝ} {W' : ℝ → ℝ → ℝ} (hW : ∀ n, IsGraphon (W n)) (hW' : IsGraphon W') :
    (∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      Tendsto (fun n => graphonHomDensity F (W n)) atTop (𝓝 (graphonHomDensity F W'))) ↔
    Tendsto (fun n => cutDistance (W n) W') atTop (𝓝 0)

/-- **Uniqueness of the limit.** Two graphons with values in `[0, 1]` are at cut distance `0` if and
only if they have the same homomorphism density for every simple graph
(Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs I* (2008),
Corollary 3.10, for graphons in `W_[0,1]`). -/
public theorem_wanted cutDistance_eq_zero_iff {U W : ℝ → ℝ → ℝ} (hU : IsGraphon U)
    (hW : IsGraphon W) :
    cutDistance U W = 0 ↔
      ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
        graphonHomDensity F U = graphonHomDensity F W

end MathlibExt.Combinatorics.SimpleGraph.GraphLimitsWanted
