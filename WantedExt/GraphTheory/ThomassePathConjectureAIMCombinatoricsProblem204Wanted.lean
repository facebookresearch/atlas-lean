/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Thomassé's path conjecture fails for every girth g ≥ 4 (AIM Caccetta-Häggkvist, Conj. 6.34)

AIM workshop The Caccetta-Häggkvist conjecture, problem list, Conjecture 6.34 (Thomassé): every
digraph `D` has a path of length `δ⁺_D (g - 1)`, where `g` is the girth of `D`. Note: this is open
for `g = 3`, and implies Caccetta-Häggkvist.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.GraphTheory.ThomassePathConjectureAIMCombinatoricsProblem204Wanted

/-!
Source: AIM workshop The Caccetta-Häggkvist conjecture, problem list (B. Sullivan, A summary of
problems and results related to the Caccetta-Häggkvist conjecture),
https://aimath.org/WWN/caccetta/caccetta.pdf, Conjecture 6.34 (Thomassé). UnsolvedMath record
UM-20001079 (`AIM-COMBINATORICS-0204`), dataset ulamai/UnsolvedMath v1.8.0.

Digraphs are Mathlib's `Digraph V` on a finite type `V`; a directed cycle with `m + 1` vertices is
an injective cyclic sequence with consecutive arcs (`m = 0` a loop, `m = 1` a pair of opposite
arcs), so girth `g ≥ 4` excludes loops and opposite arcs. A path of length `l` has `l` arcs and `l +
1` distinct vertices. `δ⁺` is the minimum out-degree. The conjecture is one statement about all
digraphs (`g` is the digraph's girth), so its negation says only that some digraph fails. Following
the note (open for `g = 3`), the target splits it girth by girth and says the bound holds for some
girth `g ≥ 4`; its refutation is Cheng and Keevash's statement that the bound fails for every girth
`g ≥ 4`. This is stronger than the negation of the conjecture, a documented strengthening that
matches the published result (one counterexample digraph alone would be a finite object).
-/

/-- The digraph `G` has a directed cycle through `m + 1` distinct vertices: an injective
`c : Fin (m + 1) → V` with an arc from `c i` to `c (i + 1)` for every `i`, indices taken mod
`m + 1`. For `m = 0` this is a loop, for `m = 1` a pair of opposite arcs. -/
def HasDirCycle {V : Type} (G : Digraph V) (m : ℕ) : Prop :=
  ∃ c : Fin (m + 1) → V, Function.Injective c ∧ ∀ i : Fin (m + 1), G.Adj (c i) (c (i + 1))

/-- The digraph `G` has girth `g`: it has a directed cycle with `g` vertices (so `g ≥ 1`) and no
directed cycle with fewer vertices. -/
def HasGirth {V : Type} (G : Digraph V) (g : ℕ) : Prop :=
  1 ≤ g ∧ HasDirCycle G (g - 1) ∧ ∀ m : ℕ, m + 1 < g → ¬ HasDirCycle G m

/-- The digraph `G` has a directed path with `l` arcs: distinct vertices `p 0, …, p l` with an arc
from `p i` to `p (i + 1)` for every `i < l`. -/
def HasDirPath {V : Type} (G : Digraph V) (l : ℕ) : Prop :=
  ∃ p : Fin (l + 1) → V, Function.Injective p ∧ ∀ i : Fin l, G.Adj (p i.castSucc) (p i.succ)

/-- Thomassé's path bound for girth `g`: every finite digraph `G` of girth `g` has a directed path
with `δ⁺ (g - 1)` arcs, where `δ⁺ = min_v |{w | v → w}|` is its minimum out-degree. -/
def ThomasseBoundForGirth (g : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : Digraph V), HasGirth G g →
    HasDirPath G ((⨅ v : V, {w : V | G.Adj v w}.ncard) * (g - 1))

/-- Thomassé's conjecture holds for at least one girth `g ≥ 4` (the AIM note leaves `g = 3`
open). -/
def thomassePathBoundForSomeGirthAtLeastFour : Prop :=
  ∃ g : ℕ, 4 ≤ g ∧ ThomasseBoundForGirth g

/--
Resolved false for every girth `g ≥ 4`: Bai and Manoussakis gave counterexamples to Thomassé's
conjecture for every even `g ≥ 4`, and Cheng and Keevash (Proposition 2) constructed, for every `g ≥
2` and `δ ≥ 1`, a digraph of girth `g` with minimum out-degree at least `δ` whose directed paths all
have length at most `gδ/2 + g - 2` (`g` even) or `(g + 1)δ/2 + g - 3` (`g` odd); for `δ ≥ 3` this is
below `δ(g - 1)`. The case `g = 3` stays open, as the AIM note says. Source: AIM workshop The
Caccetta-Häggkvist conjecture, problem list (B. Sullivan, A summary of problems and results related
to the Caccetta-Häggkvist conjecture), https://aimath.org/WWN/caccetta/caccetta.pdf, Conjecture 6.34
(Thomassé); resolution: Y. Cheng and P. Keevash, On the length of directed paths in digraphs, SIAM
J. Discrete Math. 38 (2024), 3134-3139, arXiv:2402.16776; Y. Bai and Y. Manoussakis, On the number
of vertex-disjoint cycles in digraphs, SIAM J. Discrete Math. 33 (2019), 2444-2451 (every even g ≥
4), Cheng-Keevash, abstract and Proposition 2: for every g ≥ 2 and δ ≥ 1 there is a digraph of girth
g with δ⁺ ≥ δ all of whose directed paths have length at most gδ/2 + g - 2 (g even) or (g + 1)δ/2 +
g - 3 (g odd), which is less than δ(g - 1) once δ ≥ 3 and g ≥ 4; 'Thomassé's conjecture is false for
every g ≥ 4', https://doi.org/10.1137/24M1648375.
-/
public theorem_wanted thomassePathBoundForSomeGirthAtLeastFour_refuted :
    ¬ thomassePathBoundForSomeGirthAtLeastFour

end MathlibExt.GraphTheory.ThomassePathConjectureAIMCombinatoricsProblem204Wanted
