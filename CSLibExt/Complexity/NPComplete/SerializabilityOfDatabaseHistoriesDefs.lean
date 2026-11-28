/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIALIZABILITY OF DATABASE HISTORIES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR33] SERIALIZABILITY OF DATABASE
HISTORIES;
C. H. Papadimitriou, "The serializability of concurrent database updates", Journal of the ACM
26 (1979), 631-653, doi:10.1145/322154.322158.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SerializabilityOfDatabaseHistories

/-- An instance: the number of variables `k`, the transactions as pairs
`(S(R_t), S(W_t))` of variable lists, and the history `H` as a list of operations. -/
abbrev SerializabilityOfDatabaseHistoriesInstance :=
  ℕ × List (List ℕ × List ℕ) × List (ℕ × Bool)

/-- The number `n` of transactions. -/
def numTxns (i : SerializabilityOfDatabaseHistoriesInstance) : ℕ := i.2.1.length

/-- The read set of transaction `t` in the augmented history: the instance's for `t < n`, every
variable for the final transaction `n + 1`, and nothing otherwise (the initial transaction `n`
reads nothing). -/
def readSet (i : SerializabilityOfDatabaseHistoriesInstance) (t : ℕ) : List ℕ :=
  if t < numTxns i then (i.2.1.getD t ([], [])).1
  else if t = numTxns i + 1 then List.range i.1 else []

/-- The write set of transaction `t` in the augmented history: the instance's for `t < n`, every
variable for the initial transaction `n`, and nothing otherwise (the final transaction `n + 1`
writes nothing). -/
def writeSet (i : SerializabilityOfDatabaseHistoriesInstance) (t : ℕ) : List ℕ :=
  if t < numTxns i then (i.2.1.getD t ([], [])).2
  else if t = numTxns i then List.range i.1 else []

/-- The augmented history: the initial transaction, then `h`, then the final transaction. -/
def augment (i : SerializabilityOfDatabaseHistoriesInstance) (h : List (ℕ × Bool)) :
    List (ℕ × Bool) :=
  (numTxns i, false) :: (numTxns i, true) :: (h ++ [(numTxns i + 1, false), (numTxns i + 1, true)])

/-- `R_j` reads `x` from `W_t` in the history `h`: `x ∈ S(R_j)`, and scanning the augmented
history backwards from `R_j`, the first write symbol whose write set contains `x` is `W_t`. -/
def ReadsFrom (i : SerializabilityOfDatabaseHistoriesInstance) (h : List (ℕ × Bool))
    (j t x : ℕ) : Prop :=
  x ∈ readSet i j ∧
    (((augment i h).take ((augment i h).idxOf (j, false))).reverse.find?
      fun o => o.2 && decide (x ∈ writeSet i o.1)) = some (t, true)

/-- The live transactions of `h`: those reached from the final transaction `n + 1` by repeatedly
passing from a live `T_j` to every `T_t` such that `R_j` reads some variable from `W_t`. -/
def Live (i : SerializabilityOfDatabaseHistoriesInstance) (h : List (ℕ × Bool)) (t : ℕ) :
    Prop :=
  Relation.ReflTransGen (fun j t' => ∃ x, ReadsFrom i h j t' x) (numTxns i + 1) t

/-- `h` is a history for `n` transactions: a permutation of `R_0, W_0, …, R_{n-1}, W_{n-1}` (no
repeated operation, `2n` operations, all of transactions `< n`) in which each `R_t` occurs
before `W_t`. -/
def IsHistory (n : ℕ) (h : List (ℕ × Bool)) : Prop :=
  h.Nodup ∧ h.length = 2 * n ∧ (∀ o ∈ h, o.1 < n) ∧
    ∀ t < n, h.idxOf (t, false) < h.idxOf (t, true)

/-- `h` is serial: each `R_t` immediately precedes `W_t`. -/
def IsSerial (n : ℕ) (h : List (ℕ × Bool)) : Prop :=
  ∀ t < n, h.idxOf (t, true) = h.idxOf (t, false) + 1

/-- Well-formedness of an instance: `0 < n`, every read and write set lists variables `< k`, and
`H` is a history for the `n` transactions. -/
def WellFormed (i : SerializabilityOfDatabaseHistoriesInstance) : Prop :=
  0 < numTxns i ∧ (∀ s ∈ i.2.1, (∀ x ∈ s.1, x < i.1) ∧ ∀ x ∈ s.2, x < i.1) ∧
    IsHistory (numTxns i) i.2.2

/-- Some serial history `H'` for the same transactions is equivalent to `H`: the same live
transactions, and every live `R_j` reads each variable from the same `W_t` in both. -/
def SerializabilityOfDatabaseHistoriesFeasible (i : SerializabilityOfDatabaseHistoriesInstance) :
    Prop :=
  ∃ h' : List (ℕ × Bool), IsHistory (numTxns i) h' ∧ IsSerial (numTxns i) h' ∧
    (∀ t, Live i i.2.2 t ↔ Live i h' t) ∧
    ∀ j t x, Live i i.2.2 j → (ReadsFrom i i.2.2 j t x ↔ ReadsFrom i h' j t x)

open Classical in
/-- SERIALIZABILITY OF DATABASE HISTORIES as a decision problem over bitstrings. -/
noncomputable def serializabilityOfDatabaseHistoriesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SerializabilityOfDatabaseHistoriesInstance) x with
  | some i => decide (WellFormed i ∧ SerializabilityOfDatabaseHistoriesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SerializabilityOfDatabaseHistories
