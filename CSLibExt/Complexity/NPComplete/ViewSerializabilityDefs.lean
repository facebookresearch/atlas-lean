/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VIEW SERIALIZABILITY: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300,
doi:10.1016/0196-6774(83)90028-7, Section 3 (view serializability, "having the same complexity
breakdown as the original notion" of serializability, which is NP-complete; credited to
Yannakakis, "Serializability by locking", manuscript (1982));
M. Yannakakis, "Serializability by locking", J. ACM 31 (1984), 227-244, doi:10.1145/62.322425;
C. H. Papadimitriou, "The serializability of concurrent database updates", J. ACM 26 (1979),
631-653, doi:10.1145/322154.322158 (the semantics of schedules).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiversionSerializabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ViewSerializability

open MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
  (Value Schedule MultiversionSerializabilityInstance WellFormed action standard values
    finalValue serial)

/-- The values that the reads of transaction `t` obtain in `S` under the standard
interpretation, in schedule order. -/
def readValues (S : Schedule) (t : ℕ) : List Value :=
  ((List.range S.length).filter fun p => (action S p).1 == t && !(action S p).2.2).map
    fun p => (values S (standard S)).getD p (.init 0)

/-- Some serial schedule of the `n` transactions agrees with `S` on the final value of every
variable and on the value of every read. -/
def ViewSerializabilityFeasible (i : MultiversionSerializabilityInstance) : Prop :=
  ∃ π : List ℕ, π.Perm (List.range i.1) ∧
    (∀ x : ℕ, finalValue i.2 (standard i.2) x =
      finalValue (serial i.2 π) (standard (serial i.2 π)) x) ∧
    ∀ t : ℕ, readValues i.2 t = readValues (serial i.2 π) t

open Classical in
/-- VIEW SERIALIZABILITY as a decision problem over bitstrings. -/
noncomputable def viewSerializabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiversionSerializabilityInstance) x with
  | some i => decide (WellFormed i ∧ ViewSerializabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ViewSerializability
