/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.URMBridge
public import MathlibExt.Computability.TuringMachine.Recursive.Equiv

@[expose] public section

/-!
# Church–Turing equivalences: the proved URM ⇒ TM direction

The Church–Turing thesis (Sipser, *Introduction to the Theory of Computation*,
3rd ed., §3.3; Soare, *Recursively Enumerable Sets and Degrees*, Ch. I) says that
every intuitively computable function is computable by a Turing machine, and
that all standard models of computation (Turing machines, URM / register
machines, lambda calculus, counter machines, RAM machines) compute the same
class of functions. One direction of the equivalence between URM machines and
multi-stack Turing machines is proved here: every URM-computable total
function is computed by a `FinTM2` machine, and every URM-decidable /
URM-recognizable predicate is decidable / recognizable by a `FinTM2` machine.
The converse direction (every partial recursive function is URM-computable)
is a compiler construction and is registered as a wanted theorem in
`WantedExt/TheoryOfComputation/PartrecToURM.lean`; the lambda-calculus,
counter-machine and RAM-machine equivalences are registered in
`WantedExt/TheoryOfComputation/LambdaCalculusEquivalence.lean`,
`WantedExt/TheoryOfComputation/CounterMachineEquivalence.lean` and
`WantedExt/TheoryOfComputation/RAMMachineEquivalence.lean`.
-/

set_option autoImplicit false

namespace Cslib.Decidability

open MetaMathlibExt.TM2Recursive (tm2Computable_of_computable)

/-- **A URM-computable total function is computed by a multi-stack Turing machine.**
Source: Sipser, *Introduction to the Theory of Computation*, 3rd ed., §3.1 (Church–Turing thesis) and §3.3 (equivalence of models). -/
theorem urmComputable_to_tm2 {f : ℕ → ℕ}
    (h : Cslib.URM.Computable 1 fun inputs ↦ Part.some (f (inputs 0))) :
    Nonempty (Turing.TM2Computable Computability.encodeNat Computability.encodeNat f) := by
  have hpart : Partrec (fun n : ℕ ↦ Part.some (f n)) :=
    Cslib.URM.partrec_of_computable h
  exact tm2Computable_of_computable hpart

/-- **A URM-decidable predicate is decidable by a multi-stack Turing machine.**
Source: Sipser, *Introduction to the Theory of Computation*, 3rd ed.,
§3.1 (Church–Turing thesis). -/
theorem urmDecidable_to_tm2Decidable {P : ℕ → Prop} (h : Cslib.URM.Decidable P) :
    TM2Decidable P :=
  h.tm2Decidable

/-- **A URM-recognizable predicate is recognizable by a multi-stack Turing machine.**
Source: Sipser, *Introduction to the Theory of Computation*, 3rd ed.,
§3.1 (Church–Turing thesis). -/
theorem urmRecognizable_to_tm2Recognizable {P : ℕ → Prop} (h : Cslib.URM.Recognizable P) :
    TM2Recognizable P :=
  h.tm2Recognizable

end Cslib.Decidability
