/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalAlgebra
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Consistency, semijoin programs and ear removal

A schema assigns each relation name a finite set of attributes. Instances use the named
relational algebra: `Expr.Conforms` requires each stored row to be defined exactly on its
relation's scheme. The common value domain is the natural numbers. The union of the schemes,
not an ambient set of unused attributes, is the heading of the full join.

Beeri, Fagin, Maier and Yannakakis, *On the Desirability of Acyclic Database Schemes*,
J. ACM 30 (1983), Theorem 3.4 (p. 488), connect pairwise-to-global consistency (7),
full reducers (8) and join trees (9) with the success of Graham's algorithm (4).
The ear-deletion rule here is Algorithm 6.4.4 of Abiteboul, Hull and Vianu,
*Foundations of Databases*, §6.4; their Theorem 6.4.5 uses this form of reduction.
-/

@[expose] public section

namespace Cslib.Databases
namespace AcyclicSchema

variable {N A : Type*} [DecidableEq A]

/-- **Full natural join.** A row belongs to the join of a finite family of relations when it
is defined exactly on the union of their schemes and its restriction to every scheme belongs
to the corresponding relation. All restrictions come from this one row. -/
def fullJoin [Fintype N] (sch : N → Finset A) (I : N → Finset (Tuple A ℕ)) : Set (Tuple A ℕ) :=
  {t | t.IsOver (Finset.univ.biUnion sch) ∧ ∀ i, t.restrict (sch i) ∈ I i}

/-- **Finiteness of the full join.** Even though the scalar domain is infinite, the full join
of finitely many finite extents is finite: a join row is determined by its local restrictions. -/
theorem finite_fullJoin [Fintype N] (sch : N → Finset A) (I : N → Finset (Tuple A ℕ)) :
    (fullJoin sch I).Finite := by
  let parts : fullJoin sch I → ∀ i, ↥(I i) := fun t i => ⟨_, t.property.2 i⟩
  apply Finite.of_injective parts
  intro t u he
  apply Subtype.ext
  funext a
  by_cases ha : a ∈ Finset.univ.biUnion sch
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    have h := congrArg (fun x : ↥(I i) => x.val a) (congrFun he i)
    simpa [parts, hi] using h
  · exact (t.property.1.eq_none ha).trans (u.property.1.eq_none ha).symm

section Consistency

variable [Fintype A]

/-- **Pairwise consistency.** For every ordered pair of relation names, projecting the natural
join of their extents onto the first scheme recovers the entire first extent. -/
def PairwiseConsistent (sch : N → Finset A) (I : N → Finset (Tuple A ℕ)) : Prop :=
  ∀ i j, project (sch i) (join (I i) (I j)) = I i

/-- **Global consistency.** The image of the full join under restriction to each relation's
scheme is exactly that relation's extent. This permits empty extents and an empty full join. -/
def GloballyConsistent [Fintype N] (sch : N → Finset A) (I : N → Finset (Tuple A ℕ)) : Prop :=
  ∀ i, Tuple.restrict (sch i) '' fullJoin sch I = (I i : Set (Tuple A ℕ))

/-- **Semijoin as a filter.** If every row of the left relation is over the scheme $S$, then a
row is in the projection of the binary natural join onto $S$ exactly when it is a left row and
is compatible with some right row. -/
theorem mem_project_join_iff {S : Finset A} {r s : Finset (Tuple A ℕ)} (hr : IsOver S r)
    {t : Tuple A ℕ} : t ∈ project S (join r s) ↔ t ∈ r ∧ ∃ u ∈ s, t.Compatible u := by
  constructor
  · rintro ht
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v, hv, u, hu, hc, rfl⟩ := mem_join.mp hw
    rw [Tuple.restrict_merge_left (hr v hv)]
    exact ⟨hv, u, hu, hc⟩
  · rintro ⟨ht, u, hu, hc⟩
    exact Finset.mem_image.mpr ⟨_, mem_join.mpr ⟨t, ht, u, hu, hc, rfl⟩,
      Tuple.restrict_merge_left (hr t ht)⟩

section Programs

variable [DecidableEq N] (sch : N → Finset A)

/-- **One semijoin command.** For an ordered pair $(i,j)$ replace relation $i$ by the
projection of its join with relation $j$ onto the scheme of $i$. All other extents are unchanged. -/
def semijoinStep (I : N → Finset (Tuple A ℕ)) (ij : N × N) : N → Finset (Tuple A ℕ) :=
  Function.update I ij.1 (project (sch ij.1) (join (I ij.1) (I ij.2)))

/-- **Running a semijoin program.** A finite list of ordered pairs of relation names is executed
from left to right. Each command reads the extents left by the preceding commands. -/
def runSemijoins (P : List (N × N)) (I : N → Finset (Tuple A ℕ)) : N → Finset (Tuple A ℕ) :=
  P.foldl (semijoinStep sch) I

variable {sch} {I : N → Finset (Tuple A ℕ)}

theorem conforms_semijoinStep (hI : Expr.Conforms sch I) (ij : N × N) :
    Expr.Conforms sch (semijoinStep sch I ij) := by
  intro k
  by_cases hk : k = ij.1
  · subst k
    simpa only [semijoinStep, Function.update_self] using
      isOver_project (isOver_join (hI ij.1) (hI ij.2)) Finset.subset_union_left
  · simpa only [semijoinStep, Function.update_of_ne hk] using hI k

/-- **Semijoin invariance of the full join.** If the extents conform to their schemes, updating
one of them by a semijoin leaves the set of full join rows unchanged. -/
theorem fullJoin_semijoinStep [Fintype N] (hI : Expr.Conforms sch I) (ij : N × N) :
    fullJoin sch (semijoinStep sch I ij) = fullJoin sch I := by
  ext t
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, fun k => ?_⟩
    by_cases hk : k = ij.1
    · subst k
      exact ((mem_project_join_iff (hI ij.1)).mp (by simpa [semijoinStep] using h ij.1)).1
    · simpa [semijoinStep, hk] using h k
  · rintro ⟨ht, h⟩
    refine ⟨ht, fun k => ?_⟩
    by_cases hk : k = ij.1
    · subst k
      rw [semijoinStep, Function.update_self]
      refine (mem_project_join_iff (hI ij.1)).mpr ⟨h _, _, h ij.2, fun a => ?_⟩
      by_cases hi : a ∈ sch ij.1 <;> by_cases hj : a ∈ sch ij.2 <;> simp [hi, hj]
    · simpa [semijoinStep, hk] using h k

/-- **Semijoin programs preserve answers.** Running any finite semijoin program on conforming
relations preserves their full natural join, including when that join is empty. -/
theorem fullJoin_runSemijoins [Fintype N] (hI : Expr.Conforms sch I) (P : List (N × N)) :
    fullJoin sch (runSemijoins sch P I) = fullJoin sch I := by
  induction P generalizing I with
  | nil => rfl
  | cons ij P ih => exact (ih (conforms_semijoinStep hI ij)).trans (fullJoin_semijoinStep hI ij)

theorem runSemijoins_eq_of_pairwise (hI : PairwiseConsistent sch I) (P : List (N × N)) :
    runSemijoins sch P I = I := by
  induction P with
  | nil => rfl
  | cons ij P ih =>
    have h : semijoinStep sch I ij = I := by simp [semijoinStep, hI ij.1 ij.2]
    change runSemijoins sch P (semijoinStep sch I ij) = I
    rwa [h]

/-- **Full semijoin reducer.** There is one finite semijoin program for the schema such that,
for every conforming finite instance, its execution leaves globally consistent extents. -/
def HasFullReducer [Fintype N] (sch : N → Finset A) : Prop :=
  ∃ P : List (N × N), ∀ I, Expr.Conforms sch I → GloballyConsistent sch (runSemijoins sch P I)

/-- **A full reducer implies local-to-global consistency.** On a schema admitting a full
reducer, every pairwise consistent conforming instance is globally consistent: each command
of the reducer leaves that instance fixed. -/
theorem globallyConsistent_of_hasFullReducer [Fintype N] (h : HasFullReducer sch)
    (hI : Expr.Conforms sch I) (hp : PairwiseConsistent sch I) : GloballyConsistent sch I := by
  obtain ⟨P, hP⟩ := h
  simpa only [runSemijoins_eq_of_pairwise hp P] using hP I hI

end Programs

end Consistency

/-- **Join tree.** An undirected tree on the relation names is a join tree if any attribute
shared by the endpoints of a simple path belongs to every scheme on the path. Thus adjacent
schemes need not intersect: their edge can have the empty label. -/
def HasJoinTree (sch : N → Finset A) : Prop :=
  ∃ T : SimpleGraph N, T.IsTree ∧ ∀ i j (p : T.Walk i j), p.IsPath →
    ∀ k ∈ p.support, sch i ∩ sch j ⊆ sch k

section EarRemoval

variable [DecidableEq N] (sch : N → Finset A)

/-- **GYO ear.** A remaining scheme $i$ is an ear if it meets no other remaining scheme, or
one other remaining scheme $j$ contains every attribute shared by $i$ with any other remaining
scheme. The first alternative applies also to the last remaining scheme. -/
def IsEar (F : Finset N) (i : N) : Prop :=
  i ∈ F ∧ ((∀ k ∈ F.erase i, Disjoint (sch i) (sch k)) ∨
    ∃ j ∈ F.erase i, ∀ k ∈ F.erase i, sch i ∩ sch k ⊆ sch j)

/-- **GYO ear deletion.** One transition removes precisely one ear of the current family; the
attributes of the new hypergraph are the union of its surviving schemes. -/
def EarStep (F G : Finset N) : Prop := ∃ i, IsEar sch F i ∧ G = F.erase i

/-- **Empty output of GYO.** Starting with all relation names, every finite sequence of ear
deletions ending in a family with no ear ends in the empty family. This quantifies over all
maximal runs, not just one favourable choice of ears. -/
def GYOEmpties [Fintype N] : Prop :=
  ∀ F, Relation.ReflTransGen (EarStep sch) Finset.univ F → (∀ i, ¬ IsEar sch F i) → F = ∅

/-- **Existence of a terminal GYO output.** From each finite family there is a finite sequence
of ear deletions to a family with no ear. Each deletion strictly decreases the family size. -/
theorem exists_terminal_earRemoval (F : Finset N) :
    ∃ G, Relation.ReflTransGen (EarStep sch) F G ∧ ∀ i, ¬ IsEar sch G i := by
  classical
  by_cases h : ∃ i, IsEar sch F i
  · obtain ⟨i, hi⟩ := h
    obtain ⟨G, hG, hstop⟩ := exists_terminal_earRemoval (F.erase i)
    exact ⟨G, hG.head ⟨i, hi, rfl⟩, hstop⟩
  · exact ⟨F, .refl, fun i hi => h ⟨i, hi⟩⟩
termination_by F.card
decreasing_by exact Finset.card_erase_lt_of_mem hi.1

end EarRemoval

end AcyclicSchema
end Cslib.Databases
