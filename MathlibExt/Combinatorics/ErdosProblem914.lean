/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/914.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the definition of the conjecture and the statement that it holds.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Equitable
import MathlibExt.Combinatorics.SimpleGraph.HajnalSzemeredi

/-!
# Clique factors and equal-sized colour classes

For a graph on `r * m` vertices, `conjecture_holds` gives a partition into cliques of size `r`
under the Hajnal–Szemerédi minimum-degree bound, and an equitable colouring with `m` colours
under the complementary maximum-degree bound.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem914Wanted

/-- **Erdős Problem 914 on clique factors and equitable colourings.** The proposition asserts
that for all integers $r \ge 2$ and $m \ge 1$ and every finite simple graph $G$ with exactly $rm$
vertices, (a) if every vertex of $G$ has degree at least $m(r - 1)$, then $G$ contains $m$
pairwise disjoint cliques of $r$ vertices each, and (b) if every vertex of $G$ has degree at most
$m - 1$, then $G$ has a proper colouring with $m$ colours in which every colour class has exactly
$r$ vertices. -/
def conjecture : Prop :=
  (∀ {r m : ℕ}, 2 ≤ r → 1 ≤ m → ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V = r * m → m * (r - 1) ≤ G.minDegree →
    ∃ K : Fin m → Finset V, (∀ i, G.IsNClique r (K i)) ∧
      Pairwise fun i j => Disjoint (K i) (K j)) ∧
  (∀ {r m : ℕ}, 2 ≤ r → 1 ≤ m → ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V = r * m → G.maxDegree ≤ m - 1 →
    ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r)

private theorem exists_coloring_card_eq {r m : ℕ} {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = r * m)
    (hdeg : G.maxDegree < m) :
    ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r := by
  obtain ⟨C, heq⟩ := SimpleGraph.HajnalSzemerediWanted.exists_equitable_coloring_of_maxDegree_lt
    G m hdeg
  let size (i : Fin m) := (C.colorClass i).ncard
  have hsum : ∑ i, size i = r * m := by
    rw [← hcard]
    simp only [size, SimpleGraph.Coloring.colorClass, Set.ncard_eq_toFinset_card',
      Set.toFinset_ofPred]
    exact (Finset.card_eq_sum_card_fiberwise (f := ⇑C) (fun _ _ => Finset.mem_univ _)).symm
  have hequitable : Set.EquitableOn (Finset.univ : Finset (Fin m)) size :=
    fun {_ _} _ _ => heq _ _
  have hm : 0 < m := Nat.zero_lt_of_lt hdeg
  -- Every class has at least the integer average, and the class sizes already sum to the total.
  have hlower (i : Fin m) (hi : i ∈ Finset.univ) : r ≤ size i := by
    simpa [hsum, Nat.mul_div_cancel _ hm] using Finset.EquitableOn.le hequitable hi
  have htotal : ∑ _ : Fin m, r = ∑ i, size i := by simp [hsum, Nat.mul_comm]
  exact ⟨C, fun i => ((Finset.sum_eq_sum_iff_of_le hlower).mp htotal i (Finset.mem_univ i)).symm⟩

/--
**Hajnal–Szemerédi theorem in clique-factor and equitable-colouring form.** For all integers
$r \ge 2$ and $m \ge 1$ and every finite simple graph $G$ with exactly $rm$ vertices, (a) if every
vertex of $G$ has degree at least $m(r - 1)$, then $G$ contains $m$ pairwise disjoint cliques of
$r$ vertices each, and (b) if every vertex of $G$ has degree at most $m - 1$, then $G$ has a
proper colouring with $m$ colours in which every colour class has exactly $r$ vertices.

This resolves Erdős Problem 914 affirmatively: part (a) was proved by Corrádi and Hajnal for
$r = 3$ and by Hajnal and Szemerédi for all $r$, and part (b) is its equitable-colouring
reformulation, obtained by applying (a) to the complement of $G$.

Source: A. Hajnal and E. Szemerédi, Proof of a conjecture of P. Erdős
(1970), 601–623, https://mathscinet.ams.org/mathscinet-getitem?mr=297607; External Lean proof of
Erdős Problem 914, plby/lean-proofs at commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos914.lean.
Moved from `OpenConjectures/Combinatorics/ErdosProblem914`.
-/
public theorem conjecture_holds : conjecture := by
  classical
  constructor
  · intro r m _ hm V _ G _ hcard hmin
    have hmax : Gᶜ.maxDegree ≤ m - 1 := by
      apply Gᶜ.maxDegree_le_of_forall_degree_le
      intro v
      rw [G.degree_compl, hcard]
      have hv := hmin.trans (G.minDegree_le_degree v)
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm m r] at hv
      omega
    obtain ⟨C, hsize⟩ := exists_coloring_card_eq Gᶜ hcard (by omega)
    refine ⟨fun i => (C.colorClass i).toFinset, fun i => ⟨?_, ?_⟩, ?_⟩
    · simpa using C.isIndepSet_colorClass i
    · exact (Set.ncard_eq_toFinset_card' _).symm.trans (hsize i)
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro v hvi hvj
      exact hij ((Set.mem_toFinset.mp hvi).symm.trans (Set.mem_toFinset.mp hvj))
  · intro r m _ hm V _ G _ hcard hmax
    exact exists_coloring_card_eq G hcard (by omega)

end MathlibExt.Combinatorics.ErdosProblem914Wanted
