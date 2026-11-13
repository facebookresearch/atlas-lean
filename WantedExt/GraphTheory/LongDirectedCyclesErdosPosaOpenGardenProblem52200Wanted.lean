/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Erdős-Pósa property for long directed cycles (Open Problem Garden 52200)

Open Problem Garden, Erdős-Posa property for long directed cycles (F. Havet and A. K. Maia): let `ℓ
≥ 2`. For every `n ≥ 0` there is `t_n = t_n(ℓ)` such that every digraph `D` either has `n` pairwise
disjoint directed cycles of length at least `ℓ`, or has a set `T` of at most `t_n` vertices such
that `D - T` has no directed cycle of length at least `ℓ`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GraphTheory.LongDirectedCyclesErdosPosaOpenGardenProblem52200Wanted

/-!
Source: Open Problem Garden, Erdős-Posa property for long directed cycles (node 52200; F. Havet and
A. K. Maia), http://www.openproblemgarden.org/op/erdos_posa_property_for_long_directed_cycles.
UnsolvedMath record UM-00003274 (`OPG-52200`), dataset ulamai/UnsolvedMath v1.8.0.

Digraphs are finite (`Fintype V`), Mathlib `Digraph`s; disjoint means vertex-disjoint. A directed
cycle of length `m` is a list of `m` distinct vertices with arcs `c i → c (i + 1)`, indices modulo
`m`; as `ℓ ≥ 2` (as on the source page) only cycles with at least two vertices count. The statement
takes the form in which Amiri's dissertation states and proves it (Conjecture 4.1.1: one function
`f`, hitting sets of size at most `f (k + ℓ)`); with `t_n(ℓ) = f (n + ℓ)` it gives the source's
statement.
-/

/-- `c` lists the vertices of a directed cycle of `D` of length `m`: the vertices `c 0, …, c (m-1)`
are distinct and `c i → c (i + 1)` is an arc for every `i`, indices taken modulo `m`. -/
def IsDirectedCycle {V : Type} (D : Digraph V) {m : ℕ} (c : Fin m → V) : Prop :=
  Function.Injective c ∧ ∀ i, D.Adj (c i) (c (finRotate m i))

/-- The Erdős-Pósa property for long directed cycles, in the form of Amiri's Conjecture 4.1.1: there
is a function `f` such that for all `ℓ ≥ 2` and `k`, every finite digraph either has `k` pairwise
vertex-disjoint directed cycles of length at least `ℓ`, or has a set `S` of at most `f (k + ℓ)`
vertices meeting every directed cycle of length at least `ℓ`. -/
def longDirectedCyclesErdosPosa : Prop :=
  ∃ f : ℕ → ℕ, ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ k : ℕ, ∀ (V : Type) [Fintype V] (D : Digraph V),
    (∃ (m : Fin k → ℕ) (c : ∀ i, Fin (m i) → V), (∀ i, ℓ ≤ m i ∧ IsDirectedCycle D (c i)) ∧
        ∀ i j, i ≠ j → Disjoint (Set.range (c i)) (Set.range (c j))) ∨
      ∃ S : Finset V, S.card ≤ f (k + ℓ) ∧
        ∀ (m : ℕ) (c : Fin m → V), ℓ ≤ m → IsDirectedCycle D c → ∃ i, c i ∈ S

/--
Resolved true: the Erdős-Pósa property for directed cycles of length at least `ℓ` is proved in
Amiri's doctoral dissertation (TU Berlin 2017), which presents its Theorem 4.3.1 on strongly
connected digraphs as answering this conjecture (its Conjecture 4.1.1, in exactly the form stated
here); Kawarabayashi and Kreutzer had stated the result as a consequence of their directed grid
theorem (the case `ℓ = 2` is Younger's conjecture, proved by Reed, Robertson, Seymour and Thomas; `ℓ
= 3` was proved by Havet and Maia). Source: Open Problem Garden, Erdős-Posa property for long
directed cycles (node 52200; F. Havet and A. K. Maia),
http://www.openproblemgarden.org/op/erdos_posa_property_for_long_directed_cycles; resolution: S.
Akhoondian Amiri, Structural Graph Theory Meets Algorithms: Covering and Connectivity Problems in
Graphs, doctoral dissertation, Technische Universität Berlin, 2017 (examiners S. Kreutzer, M.
Pilipczuk, D. M. Thilikos); K. Kawarabayashi and S. Kreutzer, The directed grid theorem, Proc. 47th
ACM STOC (2015), 655-664, doi:10.1145/2746539.2746586; arXiv:1411.5681, Amiri, Section 4.1: Theorem
4.3.1 (strongly connected digraphs with the Erdős-Pósa property) 'eventually answers the following
conjecture positively. Conjecture 4.1.1. There exists a function f : N → N such that for every ℓ, k
∈ N, every directed graph G either has k vertex disjoint cycles each of length at least ℓ, or there
is a set of vertices S ⊆ V(G) such that G − S does not contain a cycle of length at least ℓ and |S|
≤ f(k + ℓ). In fact we provide the function f'; Theorem 4.3.2 and Section 4.5 ('By Theorem 4.3.2, a
single ℓ-cycle has the Erdős-Pósa property'); the same proof in unrefereed form: S. Akhoondian
Amiri, K. Kawarabayashi, S. Kreutzer and P. Wollan, The Erdős-Pósa property for directed graphs,
arXiv:1603.02504, Theorem 4.3 and Section 5.1; Kawarabayashi-Kreutzer, Introduction (arXiv v3, p.
4): 'our grid theorem implies the following stronger result than Reed et al. in 1996 [42] (see also
[39]): for every l and every integer n ≥ 0, there exists an integer t_n = t_n(l) such that for every
digraph G, either G has n pairwise vertex disjoint directed cycles of length at least l or there
exists a set T of at most t_n vertices such that G − T has no directed cycle of length at least l',
https://depositonce.tu-berlin.de/bitstream/11303/7262/4/akhoondian_saeed.pdf.
-/
public theorem_wanted longDirectedCyclesErdosPosa_holds : longDirectedCyclesErdosPosa

end MathlibExt.GraphTheory.LongDirectedCyclesErdosPosaOpenGardenProblem52200Wanted
