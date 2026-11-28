/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Finite.Lattice

/-!
# Least Herbrand model of a definite logic program

A definite clause `A₀ ← A₁, …, Aₙ` has one head atom `A₀` and a finite list of body atoms. This
file works with a set `P` of ground definite clauses over a type `α` of ground atoms, such as the
set of ground instances of the clauses of a definite logic program. The type `α` plays the role
of the Herbrand base, and a Herbrand interpretation is a set `I : Set α` of ground atoms, those
taken to be true.

## Main definitions

- `DefiniteClause α`: a definite clause with head `head : α` and body `body : List α`.
- `IsModel P I`: the Herbrand interpretation `I` is a model of `P`.
- `immediateConsequence P`: the immediate consequence operator `T_P`, as an order homomorphism
  of `Set α`.
- `leastModel P`: the intersection `M_P` of all Herbrand models of `P`.

## Main results

- `isModel_iff_immediateConsequence_subset`: `I` is a model of `P` if and only if
  `T_P(I) ⊆ I`.
- `ωScottContinuous_immediateConsequence`: `T_P` is ω-continuous, because clause bodies are
  finite.
- `leastModel_characterization`: Herbrand models are closed under intersections, `M_P` is the
  least Herbrand model of `P`, and `M_P = lfp T_P = ⋃ₙ T_Pⁿ(∅)`.

## References

- M. H. van Emden and R. A. Kowalski, The semantics of predicate logic as a programming language,
  *J. ACM* 23(4) (1976), 733–742: the model-intersection property (Section 5), the theorem that
  the Herbrand models are the interpretations closed under `T_P` (Section 7) and
  `⋃ₙ T_Pⁿ(∅) = M_P` (Section 8).
- H. Strass (based on slides by M. Thielscher), *Least Herbrand Models*, Lecture 5 of
  Foundations of Logic Programming, TU Dresden, 2026: the model intersection property and its
  corollary, Lemmas 4.32 and 4.33, Theorem 4.22 (Kleene's fixpoint theorem) and Theorem 4.34.
- J. W. Lloyd, *Foundations of Logic Programming*, 2nd ed., Springer, 1987.
-/

@[expose] public section

namespace Cslib.LogicProgramming

open OmegaCompletePartialOrder

variable {α : Type*}

/-- **Definite clause.** A definite clause $A_0 \leftarrow A_1, \dots, A_n$ ($n \ge 0$) over a type
$\alpha$ of atoms consists of its head, the atom $A_0$, and its body, the finite list
$[A_1, \dots, A_n]$ of atoms. A clause with empty body is a fact. -/
structure DefiniteClause (α : Type*) where
  /-- The head $A_0$ of the clause $A_0 \leftarrow A_1, \dots, A_n$. -/
  head : α
  /-- The body $[A_1, \dots, A_n]$ of the clause $A_0 \leftarrow A_1, \dots, A_n$. -/
  body : List α

/-- **Herbrand model of a set of ground definite clauses.** Let $P$ be a set of ground definite
clauses over a type $\alpha$ of ground atoms. A Herbrand interpretation $I \subseteq \alpha$, the
set of ground atoms taken to be true, is a model of $P$ if $A_0 \in I$ for every clause
$A_0 \leftarrow A_1, \dots, A_n$ of $P$ with $A_1, \dots, A_n \in I$. -/
def IsModel (P : Set (DefiniteClause α)) (I : Set α) : Prop :=
  ∀ c ∈ P, (∀ b ∈ c.body, b ∈ I) → c.head ∈ I

/-- **Immediate consequence operator.** For a set $P$ of ground definite clauses over a type
$\alpha$ of ground atoms, the operator $T_P$ maps a Herbrand interpretation $I \subseteq \alpha$ to
the set of heads $A_0$ of the clauses $A_0 \leftarrow A_1, \dots, A_n$ of $P$ with
$A_1, \dots, A_n \in I$. It is monotone, so it is an order homomorphism of the subsets of
$\alpha$. -/
def immediateConsequence (P : Set (DefiniteClause α)) : Set α →o Set α where
  toFun I := {a | ∃ c ∈ P, c.head = a ∧ ∀ b ∈ c.body, b ∈ I}
  monotone' _ _ hIJ _ := fun ⟨c, hc, ha, hb⟩ ↦ ⟨c, hc, ha, fun b hb' ↦ hIJ (hb b hb')⟩

/-- **Least Herbrand model.** For a set $P$ of ground definite clauses over a type $\alpha$ of
ground atoms, $M_P$ is the intersection of all Herbrand models of $P$: a ground atom lies in $M_P$
exactly when it lies in every Herbrand model of $P$. -/
def leastModel (P : Set (DefiniteClause α)) : Set α :=
  ⋂₀ {I | IsModel P I}

/-- **Herbrand models are the pre-fixed points of the immediate consequence operator.** For a set
$P$ of ground definite clauses over a type $\alpha$ of ground atoms, a Herbrand interpretation
$I \subseteq \alpha$ is a model of $P$ if and only if $T_P(I) \subseteq I$. (van Emden and
Kowalski, *J. ACM* 23(4) (1976), Section 7, Theorem; H. Strass, *Least Herbrand Models*, Lecture 5
of Foundations of Logic Programming, TU Dresden, 2026, Lemma 4.32.) -/
theorem isModel_iff_immediateConsequence_subset {P : Set (DefiniteClause α)} {I : Set α} :
    IsModel P I ↔ immediateConsequence P I ⊆ I := by
  refine ⟨?_, fun h c hc hb ↦ h ⟨c, hc, rfl, hb⟩⟩
  rintro h _ ⟨c, hc, rfl, hb⟩
  exact h c hc hb

/-- **The immediate consequence operator is ω-continuous.** For a set $P$ of ground definite
clauses over a type $\alpha$ of ground atoms, $T_P$ is monotone and preserves unions of increasing
sequences: if $I_0 \subseteq I_1 \subseteq \cdots$ are Herbrand interpretations, then
$T_P(\bigcup_n I_n) = \bigcup_n T_P(I_n)$. This holds because clause bodies are finite.
(H. Strass, *Least Herbrand Models*, Lecture 5 of Foundations of Logic Programming, TU Dresden,
2026, Lemma 4.33.) -/
theorem ωScottContinuous_immediateConsequence (P : Set (DefiniteClause α)) :
    ωScottContinuous (immediateConsequence P) := by
  refine ωScottContinuous.of_map_ωSup_of_orderHom fun c ↦ le_antisymm ?_ <|
    ωSup_le _ _ fun i ↦ (immediateConsequence P).monotone (le_ωSup c i)
  classical
  rintro _ ⟨cl, hcl, rfl, hb⟩
  obtain ⟨n, hn⟩ := c.monotone.directed_le.exists_mem_subset_of_finset_subset_biUnion
    (s := cl.body.toFinset) fun b hb' ↦ hb b (List.mem_toFinset.mp hb')
  exact le_ωSup (c.map (immediateConsequence P)) n
    ⟨cl, hcl, rfl, fun b hb' ↦ hn (List.mem_toFinset.mpr hb')⟩

/-- **Least Herbrand model of a definite logic program.** Let $P$ be a set of ground definite
clauses over a type $\alpha$ of ground atoms, such as the set of ground instances of the clauses of
a definite logic program. Let $M_P$ be the intersection of all Herbrand models of $P$ and $T_P$ the
immediate consequence operator of $P$.

1. **Least model.** The intersection of any family of Herbrand models of $P$ is a Herbrand model
   of $P$. Hence $M_P$ is a Herbrand model of $P$ contained in every Herbrand model of $P$: it is
   the unique least Herbrand model of $P$.
2. **Fixed-point characterization.** $M_P$ is the least fixed point of $T_P$, and
   $M_P = \bigcup_{i \ge 0} T_P^i(\emptyset)$.

(van Emden and Kowalski, *J. ACM* 23(4) (1976), Sections 5, 7 and 8; H. Strass, *Least Herbrand
Models*, Lecture 5 of Foundations of Logic Programming, TU Dresden, 2026, the model intersection
property with its corollary, and Theorem 4.34.) -/
theorem leastModel_characterization (P : Set (DefiniteClause α)) :
    (∀ S : Set (Set α), (∀ I ∈ S, IsModel P I) → IsModel P (⋂₀ S)) ∧
      IsLeast {I | IsModel P I} (leastModel P) ∧
      leastModel P = OrderHom.lfp (immediateConsequence P) ∧
      leastModel P = ⋃ n, (immediateConsequence P)^[n] ∅ := by
  have hinter : ∀ S : Set (Set α), (∀ I ∈ S, IsModel P I) → IsModel P (⋂₀ S) :=
    fun S hS c hc hb I hI ↦ hS I hI c hc fun b hb' ↦ hb b hb' I hI
  have hleast : IsLeast {I | IsModel P I} (leastModel P) :=
    ⟨hinter _ fun _ ↦ id, fun _ hI ↦ Set.sInter_subset_of_mem hI⟩
  have hlfp : leastModel P = OrderHom.lfp (immediateConsequence P) :=
    hleast.unique <| by
      simpa only [isModel_iff_immediateConsequence_subset] using
        (immediateConsequence P).isLeast_lfp_le
  refine ⟨hinter, hleast, hlfp, ?_⟩
  rw [hlfp, fixedPoints.lfp_eq_sSup_iterate _ (ωScottContinuous_immediateConsequence P)]
  rfl

end Cslib.LogicProgramming
