/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIALIZABILITY OF DATABASE HISTORIES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR33] SERIALIZABILITY OF DATABASE
HISTORIES;
C. H. Papadimitriou, "The serializability of concurrent database updates", Journal of the ACM
26 (1979), 631-653, doi:10.1145/322154.322158.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SerializabilityOfDatabaseHistories

/-!
# SERIALIZABILITY OF DATABASE HISTORIES is NP-complete

INSTANCE: a set `V` of database variables, a collection `T` of transactions `(R_i, W_i)`,
`1 ≤ i ≤ n`, where `R_i` and `W_i` are subsets of `V` (the read set and the write set), and a
history `H` for `T`: a permutation of all the `R_i` and `W_i` in which each `R_i` occurs before
the corresponding `W_i`. QUESTION: is there a serial history `H'` for `T` (each `R_i` immediately
followed by `W_i`) that is equivalent to `H`, i.e., has the same set of live transactions and,
for each live read, the same writer it reads from?

The definitions are Papadimitriou's (Section 2), which Garey and Johnson follow. The augmented
history adds a transaction `T_{n+1}` before `H` that reads nothing and writes every variable,
and a transaction `T_{n+2}` after `H` that reads every variable and writes nothing. `R_j` reads
`x` from `W_i` if `x ∈ S(R_j)` and `W_i` is the latest write symbol before `R_j` in the augmented
history whose write set contains `x`. `T_{n+2}` is live; if a live `R_j` reads a variable from
`W_i`, then `T_i` is live; no other transaction is live. Two histories are equivalent iff they
have the same live transactions and every live `R_j` reads each `x` from the same `W_i`
(Papadimitriou's Proposition 1, the characterization Garey and Johnson state). A history is
serial if each `R_i` immediately precedes `W_i`.

Transactions are numbered `0, …, n - 1`; `n` and `n + 1` are the added initial and final
transactions. Variables are `0, …, k - 1`. An operation is `(t, false)` for `R_t` and
`(t, true)` for `W_t`, and a history is a list of operations.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SERIALIZABILITY OF DATABASE HISTORIES is NP-complete.** Source: Garey and Johnson
(1979), [SR33]; Papadimitriou (1979), Theorem 1. -/
public theorem_wanted serializabilityOfDatabaseHistories_npComplete :
    serializabilityOfDatabaseHistoriesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L serializabilityOfDatabaseHistoriesDec

end MetaMathlibExt.Complexity.NPComplete.SerializabilityOfDatabaseHistories
