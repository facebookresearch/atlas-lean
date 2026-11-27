/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.StlcExtended.Semantics
public import CSLibExt.Languages.TypeSafety

/-!
# Type safety for the extended simply typed lambda calculus

Multi-step type safety for closed terms of the calculus with unit, products, sums, booleans and
`let`: every term reachable from a closed term is a value or reduces further (`final_or_step`),
equivalently no reachable term is stuck (`not_stuck`).

Both statements are instances of the relation-level type-safety schema of
`CSLibExt.Languages.TypeSafety` on the terms of a fixed type in the empty context, with values as
the final states and the trivial typing predicate. The trivial predicate is preserved because
`Step` relates terms of the same type (preservation by construction), so the content of both
statements is progress (`Step.progress`) at every reachable term, together with the intrinsic
closure of `Step` under typing.

## References

* R. Harper, *Practical Foundations for Programming Languages*, 2nd ed., Cambridge University
  Press, 2016: Theorem 6.2 (preservation) and Theorem 6.4 (progress), the pattern followed by
  Theorem 10.1 and Theorem 11.1 for products and sums.
* P. Sewell, *Semantics of Programming Languages*, lecture notes, University of Cambridge
  Computer Science Tripos Part IB, 2025–26: Theorem 25 (type safety).
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.StlcExtended

universe u

/-- **Closed terms reduce only to values or reducible terms.** If $t$ is a term of type $A$ in
the empty context and $t$ reduces in any number of call-by-value steps to $t'$, then $t'$ is a
value or reduces further. The proof applies progress at $t'$, which has type $A$ because
reduction preserves types by construction. -/
theorem final_or_step {Base : Type u} {A : Ty Base} {t t' : Tm [] A} (h : Steps t t') :
    Value t' ∨ ∃ t'', Step t' t'' := by
  exact TypeSafety.final_or_step_of_reflTransGen Step Value (fun _ (_ : Unit) => True)
    (fun {s} {_} _ => Step.progress s) (fun _ _ _ _ _ => trivial) (A := ()) trivial h

/-- **Closed terms never reach a stuck term.** If $t$ is a term of type $A$ in the empty context
and $t$ reduces in any number of call-by-value steps to $t'$, then $t'$ is not stuck: it is not
the case that $t'$ is a normal form of `Step` and not a value. -/
theorem not_stuck {Base : Type u} {A : Ty Base} {t t' : Tm [] A} (h : Steps t t') :
    ¬ (¬ Value t' ∧ Relation.Normal Step t') := by
  exact TypeSafety.not_stuck_of_reflTransGen Step Value (fun _ (_ : Unit) => True)
    (fun {s} {_} _ => Step.progress s) (fun _ _ _ _ _ => trivial) (A := ()) trivial h

end Cslib.Languages.LambdaCalculus.StlcExtended
