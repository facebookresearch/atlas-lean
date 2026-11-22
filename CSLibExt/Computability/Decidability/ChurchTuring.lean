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
multi-stack Turing machines is proved: every URM-computable total
function is computed by a `FinTM2` machine, and every URM-decidable /
URM-recognizable predicate is decidable / recognizable by a `FinTM2` machine.
The three declarations here are compatibility aliases of the canonical results in
`URMBridge`; their proofs and the translation to Turing machines live there.
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

/-- **A URM-computable total function is computed by a multi-stack Turing machine.**
This is an alias of `Cslib.URM.Computable.tm2Computable` from `URMBridge.lean`, kept under
the Church–Turing name.
Source: Sipser, *Introduction to the Theory of Computation*, 3rd ed., Chapter 3 (the
Church–Turing thesis and the equivalence of models). -/
alias urmComputable_to_tm2 := Cslib.URM.Computable.tm2Computable

/-- **A URM-decidable predicate is decidable by a multi-stack Turing machine.**
This is an alias of `Cslib.URM.Decidable.tm2Decidable` from `URMBridge.lean`, kept under
the Church–Turing name.
Source: Sipser, *Introduction to the Theory of Computation*, 3rd ed.,
Chapter 3 (the Church–Turing thesis). -/
alias urmDecidable_to_tm2Decidable := Cslib.URM.Decidable.tm2Decidable

/-- **A URM-recognizable predicate is recognizable by a multi-stack Turing machine.**
This is an alias of `Cslib.URM.Recognizable.tm2Recognizable` from `URMBridge.lean`, kept
under the Church–Turing name.
Source: Sipser, *Introduction to the Theory of Computation*, 3rd ed.,
Chapter 3 (the Church–Turing thesis). -/
alias urmRecognizable_to_tm2Recognizable := Cslib.URM.Recognizable.tm2Recognizable

end Cslib.Decidability
