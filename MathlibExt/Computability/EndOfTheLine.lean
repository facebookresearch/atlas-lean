/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin

/-!
# The END-OF-THE-LINE principle

Papadimitriou's class PPAD ("polynomial parity argument, directed version") collects the total
search problems whose totality follows from one combinatorial principle: *a directed graph in
which every vertex has in-degree and out-degree at most `1`, and which has a source, has a sink
or another source.* Daskalakis, Goldberg and Papadimitriou (SIAM J. Comput. 2009, Section 3.1)
define PPAD as the class of total search problems polynomial-time reducible to
END-OF-THE-LINE: given circuits `S` and `P` on `{0,1}ⁿ` with `P(0ⁿ) = 0ⁿ ≠ S(0ⁿ)`, find `x`
with `P(S(x)) ≠ x` or `S(P(x)) ≠ x ≠ 0ⁿ`. The graph has an edge `x → y` exactly when
`S(x) = y` and `P(y) = x`.

This module proves the principle behind that definition for an arbitrary finite vertex type
and arbitrary maps `S`, `P` (the "successor candidate" and "predecessor candidate"): the
search problem is total. It also identifies the two kinds of solutions with sinks and with
sources of the graph. Circuits, encodings and polynomial-time reductions, and hence the class
PPAD itself, are not formalised here.

## References

* C. H. Papadimitriou, "On the complexity of the parity argument and other inefficient proofs
  of existence", J. Comput. System Sci. 48(3) (1994), 498–532.
* C. Daskalakis, P. W. Goldberg, C. H. Papadimitriou, "The complexity of computing a Nash
  equilibrium", SIAM J. Comput. 39(1) (2009), 195–259, Section 3.1.
-/

@[expose] public section

namespace MathlibExt.Computability.EndOfTheLine

variable {V : Type*}

/-- **The END-OF-THE-LINE graph.** For maps `S P : V → V` there is an edge `x → y` exactly
when `S x = y` and `P y = x` (Daskalakis, Goldberg and Papadimitriou, SIAM J. Comput. 2009,
Section 3.1). Every vertex has at most one out-neighbour (`S x`) and at most one in-neighbour
(`P x`). -/
def Adj (S P : V → V) (x y : V) : Prop := S x = y ∧ P y = x

instance [DecidableEq V] (S P : V → V) (x y : V) : Decidable (Adj S P x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Out-degree at most one.** In the END-OF-THE-LINE graph two out-neighbours of a vertex
coincide: both equal `S x`. -/
theorem Adj.out_unique {S P : V → V} {x y z : V} (hy : Adj S P x y) (hz : Adj S P x z) :
    y = z :=
  hy.1.symm.trans hz.1

/-- **In-degree at most one.** In the END-OF-THE-LINE graph two in-neighbours of a vertex
coincide: both equal `P x`. -/
theorem Adj.in_unique {S P : V → V} {x y z : V} (hy : Adj S P y x) (hz : Adj S P z x) :
    y = z :=
  hy.2.symm.trans hz.2

/-- **Sinks of the END-OF-THE-LINE graph.** A vertex `x` has no outgoing edge if and only if
`P (S x) ≠ x`. -/
theorem forall_not_adj_iff {S P : V → V} {x : V} :
    (∀ y, ¬ Adj S P x y) ↔ P (S x) ≠ x := by
  constructor
  · intro h hx
    exact h (S x) ⟨rfl, hx⟩
  · rintro h y ⟨rfl, hy⟩
    exact h hy

/-- **Sources of the END-OF-THE-LINE graph.** A vertex `x` has no incoming edge if and only if
`S (P x) ≠ x`. -/
theorem forall_not_adj_to_iff {S P : V → V} {x : V} :
    (∀ y, ¬ Adj S P y x) ↔ S (P x) ≠ x := by
  constructor
  · intro h hx
    exact h (P x) ⟨hx, rfl⟩
  · rintro h y ⟨hy, rfl⟩
    exact h hy

/-- **Every END-OF-THE-LINE instance has a sink.** Under the hypotheses of `exists_solution`,
some vertex `x` has `P (S x) ≠ x`, that is, has no outgoing edge (`forall_not_adj_iff`).
Proof: otherwise `P ∘ S = id`, so `S` is injective, hence surjective on the finite set `V`;
then `o = S y` gives `y = P o = o` and `S o = o`, a contradiction. This is the parity lemma
"a directed graph with in- and out-degrees at most one that has a source has a sink" quoted in
Daskalakis, Goldberg and Papadimitriou (2009), Section 3.1. -/
theorem exists_sink [Finite V] (S P : V → V) (o : V) (hP : P o = o) (hS : S o ≠ o) :
    ∃ x, ∀ y, ¬ Adj S P x y := by
  by_contra h
  simp only [not_exists, forall_not_adj_iff, not_not] at h
  have hinj : Function.Injective S := fun a b hab => by
    rw [← h a, ← h b, hab]
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hinj) o
  have hyo : y = o := by rw [← h y, hy, hP]
  exact hS (hyo ▸ hy)

/-- **END-OF-THE-LINE is total.** Let `V` be finite and `S P : V → V` with a standard vertex
`o` satisfying `P o = o ≠ S o` (so `o` is a source with an outgoing edge to `S o` whenever
`P (S o) = o`). Then some `x` satisfies `P (S x) ≠ x` (a sink) or `S (P x) ≠ x` with `x ≠ o`
(a source other than `o`).

This is the existence statement behind the definition of END-OF-THE-LINE and of PPAD in
C. Daskalakis, P. W. Goldberg, C. H. Papadimitriou, "The complexity of computing a Nash
equilibrium", SIAM J. Comput. 39(1) (2009), 195–259, Section 3.1, where `V = {0,1}ⁿ` and
`o = 0ⁿ`. In fact the first alternative always occurs (`exists_sink`). -/
theorem exists_solution [Finite V] (S P : V → V) (o : V) (hP : P o = o) (hS : S o ≠ o) :
    ∃ x, P (S x) ≠ x ∨ (S (P x) ≠ x ∧ x ≠ o) := by
  obtain ⟨x, hx⟩ := exists_sink S P o hP hS
  exact ⟨x, Or.inl (forall_not_adj_iff.mp hx)⟩

end MathlibExt.Computability.EndOfTheLine
