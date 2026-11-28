/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CORE STABLE PARTITION EXISTENCE in hedonic games: definitions

Source:
C. Ballester, "NP-completeness in hedonic games", Games and Economic Behavior 49 (2004), 1-30,
doi:10.1016/j.geb.2003.10.003;
G. J. Woeginger, "Core stability in hedonic coalition formation", SOFSEM 2013, Lecture Notes in
Computer Science 7741, 33-50, doi:10.1007/978-3-642-35843-2_4 (Definition 2.1 and
Theorem 3.2, restating Ballester's result under the individually rational encoding).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Partition.Finpartition

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HedonicCoreStablePartition

/-- An instance: the number `n` of players (players `0, …, n - 1`) and, for each player `p`,
the list of pairs `(S, r)` of a listed coalition `S` (a list of players) and its rank `r`. -/
abbrev HedonicCoreStablePartitionInstance := ℕ × List (List (List ℕ × ℕ))

/-- The coalitions listed by player `p`, with their ranks. -/
def listing (i : HedonicCoreStablePartitionInstance) (p : ℕ) : List (List ℕ × ℕ) :=
  i.2.getD p []

/-- Well-formedness of an instance: one listing per player; every coalition listed by `p`
consists of players and contains `p`; `p` lists no coalition twice; `p` lists `{p}`; and every
coalition listed by `p` has rank at most that of `{p}`. -/
def WellFormed (i : HedonicCoreStablePartitionInstance) : Prop :=
  i.2.length = i.1 ∧
    ∀ p < i.1, (∀ c ∈ listing i p, p ∈ c.1 ∧ ∀ q ∈ c.1, q < i.1) ∧
      ((listing i p).map fun c => c.1.toFinset).Nodup ∧
      ∃ c ∈ listing i p, c.1.toFinset = {p} ∧ ∀ c' ∈ listing i p, c'.2 ≤ c.2

/-- Player `p` strictly prefers coalition `S` to coalition `T`: `p` lists `S`, and either does
not list `T` or lists it with a larger (worse) rank. -/
def Prefers (i : HedonicCoreStablePartitionInstance) (p : Fin i.1) (S T : Finset (Fin i.1)) :
    Prop :=
  ∃ c ∈ listing i p, c.1.toFinset = S.image Fin.val ∧
    ∀ c' ∈ listing i p, c'.1.toFinset = T.image Fin.val → c.2 < c'.2

/-- `Π` is core stable: no nonempty coalition `S` has every member `p` strictly preferring `S`
to `Π(p)`. -/
def IsCoreStable (i : HedonicCoreStablePartitionInstance)
    (P : Finpartition (Finset.univ : Finset (Fin i.1))) : Prop :=
  ∀ S : Finset (Fin i.1), S.Nonempty → ∃ p ∈ S, ¬ Prefers i p S (P.part p)

/-- The game has a core stable partition. -/
def HedonicCoreStablePartitionFeasible (i : HedonicCoreStablePartitionInstance) : Prop :=
  ∃ P : Finpartition (Finset.univ : Finset (Fin i.1)), IsCoreStable i P

open Classical in
/-- CORE STABLE PARTITION EXISTENCE as a decision problem over bitstrings. -/
noncomputable def hedonicCoreStablePartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HedonicCoreStablePartitionInstance) x with
  | some i => decide (WellFormed i ∧ HedonicCoreStablePartitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HedonicCoreStablePartition
