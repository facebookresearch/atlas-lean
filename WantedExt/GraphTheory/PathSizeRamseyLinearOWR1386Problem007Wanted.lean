/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Size-Ramsey numbers of paths (Oberwolfach Reports 48/2006)

Oberwolfach workshop Combinatorics, Probability and Computing (2006), Y. Kohayakawa (with V. Rödl
and E. Tengan), Problem 1 of Erdős, Faudree, Rousseau and Schelp (1978): is it true that `r̂(P_n)/n
→ ∞` and `r̂(P_n)/n² → 0`, where `r̂(P_n)` is the size-Ramsey number of the path on `n` vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.PathSizeRamseyLinearOWR1386Problem007Wanted

/-!
Source: Y. Kohayakawa (with V. Rödl and E. Tengan), in Combinatorics, Probability and Computing,
Oberwolfach Reports 3 (2006), no. 48, p. 2914, Problem 1, DOI 10.4171/OWR/2006/48. UnsolvedMath
record UM-30000603 (`OWR-1386-007`), dataset ulamai/UnsolvedMath v1.8.0.

`r̂(P_n)` is the least number of edges of a graph `G` with `G → (P_n)₂`; the two limits are stated
without it: `r̂(P_n)/n → ∞` says that for every `C` and all large `n` every graph arrowing `P_n` has
more than `C n` edges, and `r̂(P_n)/n² → 0` that for every `ε > 0` and all large `n` some graph
arrowing `P_n` has at most `ε n²` edges. Graphs live on `Fin m` for arbitrary `m`; copies need not
be induced.
-/

open Filter

/-- The edges of `G` that the colouring `c` gives colour `b`, as a graph on the vertices of `G`. -/
def colourClass {V : Type*} (G : SimpleGraph V) (c : Sym2 V → Bool) (b : Bool) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = b}

/-- `G → P_n`: every 2-colouring of the edges of `G` has a monochromatic copy (not necessarily
induced) of the path `P_n` on `n` vertices. -/
def ArrowsPath {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ c : Sym2 V → Bool, ∃ b, (SimpleGraph.pathGraph n).IsContained (colourClass G c b)

/-- Part (a), Erdős, Faudree, Rousseau and Schelp: `r̂(P_n) / n → ∞`, where `r̂(P_n)` is the least
number of edges of a graph `G` with `G → P_n`; that is, for every `C` and all large `n`, every graph
`G → P_n` has more than `C n` edges. -/
def sizeRamseyPathSuperlinear : Prop :=
  ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ (m : ℕ) (G : SimpleGraph (Fin m)), ArrowsPath G n →
    C * n < G.edgeSet.ncard

/-- Part (b): `r̂(P_n) / n² → 0`; that is, for every `ε > 0` and all large `n` some graph
`G → P_n` has at most `ε n²` edges. -/
def sizeRamseyPathSubquadratic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ (m : ℕ) (G : SimpleGraph (Fin m)), ArrowsPath G n ∧
    (G.edgeSet.ncard : ℝ) ≤ ε * n ^ 2

/--
Resolved false: Beck proved `r̂(P_n) ≤ c n` for an absolute constant `c`, as the source records
right after the problem, so `r̂(P_n)/n` stays bounded. Source: Y. Kohayakawa (with V. Rödl and E.
Tengan), in Combinatorics, Probability and Computing, Oberwolfach Reports 3 (2006), no. 48, p. 2914,
Problem 1, DOI 10.4171/OWR/2006/48; resolution: J. Beck, On size Ramsey number of paths, trees, and
circuits. I, J. Graph Theory 7 (1983), 115-129, as quoted in the source (p. 2914): Beck proved
r̂(P_n) ≤ c n for an absolute constant c; explicit linear-size Ramsey graphs for paths are due to
Alon and Chung, https://doi.org/10.1002/jgt.3190070115.
-/
public theorem_wanted sizeRamseyPathSuperlinear_refuted : ¬ sizeRamseyPathSuperlinear

/--
Resolved true: Beck's bound `r̂(P_n) ≤ c n`, recorded in the source right after the problem, gives
`r̂(P_n)/n² ≤ c / n → 0`. Source: Y. Kohayakawa (with V. Rödl and E. Tengan), in Combinatorics,
Probability and Computing, Oberwolfach Reports 3 (2006), no. 48, p. 2914, Problem 1, DOI
10.4171/OWR/2006/48; resolution: J. Beck, On size Ramsey number of paths, trees, and circuits. I, J.
Graph Theory 7 (1983), 115-129, as quoted in the source (p. 2914): Beck proved r̂(P_n) ≤ c n for an
absolute constant c; explicit linear-size Ramsey graphs for paths are due to Alon and Chung,
https://doi.org/10.1002/jgt.3190070115.
-/
public theorem_wanted sizeRamseyPathSubquadratic_holds : sizeRamseyPathSubquadratic

end MathlibExt.GraphTheory.PathSizeRamseyLinearOWR1386Problem007Wanted
