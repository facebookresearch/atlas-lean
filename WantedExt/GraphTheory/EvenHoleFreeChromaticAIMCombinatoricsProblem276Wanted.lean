/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# χ ≤ 2ω - 1 for even-hole-free graphs (AIM perfect graph conjecture, Conjecture 3)

AIM workshop The perfect graph conjecture, problem list, section Even-hole-free graphs, Conjecture 3
(Hoàng): if `G` is an even-hole-free graph then `χ(G) ≤ 2ω(G) - 1`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

namespace MathlibExt.GraphTheory.EvenHoleFreeChromaticAIMCombinatoricsProblem276Wanted

/-!
Source: AIM workshop The perfect graph conjecture, problem list,
https://aimath.org/WWN/perfectgraph/perfectgraph.pdf, section G.4 Even-hole-free graphs, Conjecture
3 (Hoàng). UnsolvedMath record UM-20001151 (`AIM-COMBINATORICS-0276`), dataset ulamai/UnsolvedMath
v1.8.0.

Graphs are finite, simple and nonempty (so `ω ≥ 1`); even-hole-free means no induced copy of
`cycleGraph (2k)` with `k ≥ 2`, as in the module of Conjecture 4. `χ` is Mathlib's `chromaticNumber`
(in `ℕ∞`) and `ω` is `cliqueNum`. The answer combines two printed premises and nothing else: the
list's own sentence that Conjecture 4 implies Conjecture 3, and Chudnovsky and Seymour's theorem
1.1, which is Conjecture 4.
-/

/-- Hoàng's conjecture (AIM, The perfect graph conjecture, Conjecture 3): every finite nonempty
even-hole-free graph `G` (no induced copy of `cycleGraph (2 k)` with `k ≥ 2`) satisfies
`χ(G) ≤ 2 ω(G) - 1`. -/
def hoangEvenHoleFreeChromaticBound : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
    (∀ k : ℕ, 2 ≤ k → ¬ (SimpleGraph.cycleGraph (2 * k)).IsIndContained G) →
    G.chromaticNumber ≤ ((2 * G.cliqueNum - 1 : ℕ) : ℕ∞)

/--
Resolved true: the problem list notes that Conjecture 4 (every even-hole-free graph has a
bisimplicial vertex) gives every induced subgraph `H` a vertex of degree at most `2ω(H) - 2`, hence
`χ(G) ≤ 2ω(G) - 1`; Chudnovsky and Seymour proved Conjecture 4 (their 1.1: every non-null
even-hole-free graph has a bisimplicial vertex). Source: AIM workshop The perfect graph conjecture,
problem list, https://aimath.org/WWN/perfectgraph/perfectgraph.pdf, section G.4 Even-hole-free
graphs, Conjecture 3 (Hoàng); resolution: M. Chudnovsky and P. Seymour, Even-hole-free graphs still
have bisimplicial vertices, J. Combin. Theory Ser. B 161 (2023), 331-381, arXiv:1909.10967, with the
problem list's own derivation of Conjecture 3 from Conjecture 4, Chudnovsky-Seymour statement 1.1
(Conjecture 4: every non-null even-hole-free graph has a bisimplicial vertex, 'conjectured in [4]',
[4] = J. Ramirez-Alfonsin and B. Reed (eds.), Perfect Graphs, Wiley, 2001, p. 130); problem list,
section G.4 (p. 14), after Conjecture 4: 'Conjecture 4 implies Conjecture 3 which in turn implies
Conjecture 2. Let G be an even-hole-free graph. Conjecture 4 implies that each induced subgraph H of
G has a vertex of degree at most 2ω(H) - 2, and therefore χ(G) ≤ 2ω(G) - 1',
https://doi.org/10.1016/j.jctb.2023.02.009.
-/
public theorem_wanted hoangEvenHoleFreeChromaticBound_holds : hoangEvenHoleFreeChromaticBound

end MathlibExt.GraphTheory.EvenHoleFreeChromaticAIMCombinatoricsProblem276Wanted
