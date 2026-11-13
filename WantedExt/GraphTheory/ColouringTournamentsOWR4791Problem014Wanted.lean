/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Colouring tournaments, statements 7 and 8 (Oberwolfach Reports 1/2011)

Oberwolfach workshop Combinatorics (2011), P. Seymour, Colouring tournaments, statements 7 and 8:
(7) for every `k` there is `c` such that a tournament in which every out-neighbourhood has chromatic
number at most `k` has chromatic number at most `c`; (8) for `H = Δ(T₂, T₂, T₂)` and every `ε > 0`
there is `c > 0` such that every `H`-free tournament `G` has a transitive subset of size at least
`c|V(G)|^{1-ε}`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

namespace MathlibExt.GraphTheory.ColouringTournamentsOWR4791Problem014Wanted

/-!
Source: P. Seymour (joint work with E. Berger, K. Choromanski, M. Chudnovsky, J. Fox, M. Loebl, A.
Scott and S. Thomassé), Colouring tournaments, in Combinatorics, Oberwolfach Reports 8 (2011), no.
1, pp. 25-28, statements 7 and 8, pp. 27-28, DOI 10.4171/OWR/2011/01. UnsolvedMath record
UM-30001657 (`OWR-4791-014`), dataset ulamai/UnsolvedMath v1.8.0.

As in the source, a tournament is a finite digraph with exactly one edge between any two distinct
vertices (`Digraph`, no loops); `X` is transitive if the subtournament on `X` has no directed cycle
(no closed directed walk inside `X`); a `k`-colouring is a partition into at most `k` transitive
sets (colour classes of a map `col : X → Fin k` on the set itself, so the empty set is
`0`-colourable). The out-neighbourhood condition of statement 7 is `k`-colourability of the
subtournament induced on `{u | v → u}`. In statement 8, `Δ(P, Q, R)` is the tournament with a
trisection `(A, B, C)`, `A ⇒ B ⇒ C ⇒ A`, whose parts induce `P, Q, R`, and `T₂` is the transitive
tournament on two vertices; `G` contains `H` if `H` is isomorphic to a subtournament of `G`.
Statement 8 is stated for nonempty tournaments: for the empty tournament `|V|^{1-ε}` is `0^{1-ε}`,
and at `ε = 1` Lean's `0 ^ 0 = 1` would make the empty tournament a spurious counterexample.
-/

/-- `G` is a tournament: no loops, and for distinct `u, v` exactly one of the edges `uv`, `vu`. -/
def IsTournament {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ ∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u)

/-- `X` is transitive in `G`: the subtournament induced on `X` has no directed cycle (no closed
directed walk `c 0 → c 1 → ⋯ → c k → c 0` inside `X`). -/
def IsTransitiveSet {V : Type*} (G : Digraph V) (X : Set V) : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → V), (∀ i, c i ∈ X) → ¬ ∀ i, G.Adj (c i) (c (finRotate (k + 1) i))

/-- The subtournament of `G` induced on `X` admits a `k`-colouring: `X` is the union of at most `k`
transitive subsets, the colour classes of some `col : X → Fin k` (so `∅` is `0`-colourable). -/
def IsColourableOn {V : Type*} (G : Digraph V) (X : Set V) (k : ℕ) : Prop :=
  ∃ col : X → Fin k, ∀ i : Fin k, IsTransitiveSet G {v | ∃ h : v ∈ X, col ⟨v, h⟩ = i}

/-- Statement 7 of Seymour's abstract (Oberwolfach Report 1/2011, pp. 27-28): for every `k` there is
`c` such that every tournament in which the out-neighbourhood of each vertex has chromatic number at
most `k` has chromatic number at most `c`. -/
def localToGlobalColouring : Prop :=
  ∀ k : ℕ, ∃ c : ℕ, ∀ (V : Type) [Finite V] (G : Digraph V), IsTournament G →
    (∀ v, IsColourableOn G {u | G.Adj v u} k) → IsColourableOn G Set.univ c

/-- The tournament `Δ(T₂, T₂, T₂)` on `Fin 3 × Fin 2`: the parts `{i} × Fin 2` induce the transitive
tournament `T₂` (`(i, 0) → (i, 1)`), and every vertex of part `i` dominates every vertex of part
`i + 1` (mod `3`), so the parts form a trisection `A ⇒ B ⇒ C ⇒ A`. -/
def deltaT2T2T2 : Digraph (Fin 3 × Fin 2) where
  Adj x y := (x.1 = y.1 ∧ x.2 < y.2) ∨ y.1 = x.1 + 1

/-- `G` contains `H`: `H` is isomorphic to a subtournament of `G` (an injective map preserving and
reflecting edges). -/
def Contains {V W : Type*} (G : Digraph V) (H : Digraph W) : Prop :=
  ∃ φ : W → V, Function.Injective φ ∧ ∀ x y, H.Adj x y ↔ G.Adj (φ x) (φ y)

/-- Statement 8 of Seymour's abstract (Oberwolfach Report 1/2011, p. 28): for every `ε > 0` there is
`c > 0` such that every nonempty `Δ(T₂, T₂, T₂)`-free tournament `G` has a transitive subset of size
at least `c |V(G)|^{1-ε}`. -/
def nearLinearTransitiveSubsets : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V),
    IsTournament G → ¬ Contains G deltaT2T2T2 →
      ∃ X : Finset V, IsTransitiveSet G (X : Set V) ∧ c * (Fintype.card V : ℝ) ^ (1 - ε) ≤ X.card

/--
Resolved true: Harutyunyan, Le, Thomassé and Wu (Theorem 6) prove that there is a function `f` such
that every tournament whose out-neighbourhoods all have chromatic number at most `t` has chromatic
number at most `f(t)`. Source: P. Seymour (joint work with E. Berger, K. Choromanski, M. Chudnovsky,
J. Fox, M. Loebl, A. Scott and S. Thomassé), Colouring tournaments, in Combinatorics, Oberwolfach
Reports 8 (2011), no. 1, pp. 25-28, statements 7 and 8, pp. 27-28, DOI 10.4171/OWR/2011/01;
resolution: A. Harutyunyan, T.-N. Le, S. Thomassé and H. Wu, Coloring tournaments: from local to
global, J. Combin. Theory Ser. B 138 (2019), 166-171, DOI 10.1016/j.jctb.2019.01.005,
arXiv:1702.01607, Theorem 6: there is a function f such that every t-local tournament T (every
out-neighbourhood has chromatic number at most t) has chromatic number at most f(t); the abstract
states that this answers a question of Berger et al., https://arxiv.org/abs/1702.01607.
-/
public theorem_wanted localToGlobalColouring_holds : localToGlobalColouring

/--
Resolved true: Choromanski, Chudnovsky and Seymour prove that `Δ(T₂, T₂, T₂)`, their `Δ(2, 2, 2)`,
is a pseudo-hero (Theorem 1.5 with `k = l = 2`); by their 5.1 every `Δ(2, 2, 2)`-free tournament `G`
with `|G| > 1` has a transitive subset of size at least `c |G| / log |G|`, and by 1.7 its
Erdős-Hajnal supremum is `ξ(Δ(2, 2, 2)) = 1`, i.e. every exponent `1 - ε < 1` is attained, which is
statement 8. Source: P. Seymour (joint work with E. Berger, K. Choromanski, M. Chudnovsky, J. Fox,
M. Loebl, A. Scott and S. Thomassé), Colouring tournaments, in Combinatorics, Oberwolfach Reports 8
(2011), no. 1, pp. 25-28, statements 7 and 8, pp. 27-28, DOI 10.4171/OWR/2011/01; resolution: K.
Choromanski, M. Chudnovsky and P. Seymour, Tournaments with near-linear transitive subsets, J.
Combin. Theory Ser. B 109 (2014), 228-249, DOI 10.1016/j.jctb.2014.06.007, Theorem 1.5: a tournament
is a pseudo-hero if and only if it is a pseudo-celebrity (there are c > 0 and d ≥ 0 with α(G) ≥
c|G|/(log|G|)^d for every H-free tournament G with |G| > 1, α(G) the largest transitive subset), and
a strongly-connected tournament with more than one vertex is a pseudo-hero if it equals Δ(2, k, l)
for some k, l ≥ 2 (k standing for T_k); 5.1: for all k, l ≥ 2 there is c > 0 such that every Δ(2, k,
l)-free tournament G with |G| > 1 satisfies α(G) ≥ c|G|/log(|G|); 1.7: a pseudo-hero H satisfies
ξ(H) = 1, where ξ(H) is the supremum of the ε for which some c > 0 gives α(G) ≥ c|G|^ε for every
H-free G; author's copy https://web.math.princeton.edu/~pds/papers/pseudo/paper.pdf,
https://doi.org/10.1016/j.jctb.2014.06.007.
-/
public theorem_wanted nearLinearTransitiveSubsets_holds : nearLinearTransitiveSubsets

end MathlibExt.GraphTheory.ColouringTournamentsOWR4791Problem014Wanted
