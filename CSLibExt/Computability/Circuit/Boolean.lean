/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Circuit.Basic

/-!
# Boolean circuit basis

NOT and positive-arity AND/OR gates, as used in CLRS4 section 34.3,
printed pages 1065-1068. The signature and interpretation use the canonical
CSLib straight-line program and circuit types.
-/

@[expose] public section

namespace Cslib.Circuits

/-- **Boolean gates.** The Boolean gates are a NOT gate and, for each natural number $a$, an AND
gate and an OR gate indexed by $a$, which stand for gates with $a + 1$ inputs. The numbers of
inputs are assigned by the Boolean signature, so there is no AND or OR gate with zero inputs. -/
inductive BooleanGate where
  | not
  | and (arityMinusOne : Nat)
  | or (arityMinusOne : Nat)
  deriving Repr, DecidableEq

/-- **Boolean signature.** The Boolean signature has the Boolean gates as its operation symbols,
where NOT has arity $1$ and, for each natural number $a$, the AND gate and the OR gate indexed by
$a$ have arity $a + 1$. In particular, no AND or OR gate takes zero inputs. -/
def booleanSignature : Signature where
  Op := BooleanGate
  Arity
    | .not => 1
    | .and a => a + 1
    | .or a => a + 1

/-- **Boolean interpretation.** The Boolean interpretation evaluates the gates of the Boolean
signature on the truth values $\{\mathrm{false}, \mathrm{true}\}$: NOT sends its input $x$ to
$\lnot x$, and for each natural number $a$, the AND gate and the OR gate with inputs
$x_0, \dots, x_a$ return $(\cdots((\mathrm{true} \land x_0) \land x_1) \cdots) \land x_a$ and
$(\cdots((\mathrm{false} \lor x_0) \lor x_1) \cdots) \lor x_a$ respectively, that is, the
conjunction and the disjunction of the inputs. -/
def booleanInterpretation : Interpretation booleanSignature Bool
  | .not, f => !(f ⟨0, by decide⟩)
  | .and a, f => Fin.foldl (a + 1) (fun acc k => acc && f k) true
  | .or a, f => Fin.foldl (a + 1) (fun acc k => acc || f k) false

/-- **Boolean NOT.** Under the Boolean interpretation, the NOT gate applied to a truth value $x$
returns its negation $\lnot x$. -/
@[simp] theorem booleanInterpretation_not (f : Fin 1 → Bool) :
    booleanInterpretation .not f = !(f 0) := rfl

/-- **Boolean AND as a left fold.** For every natural number $a$ and truth values
$x_0, \dots, x_a$, the Boolean interpretation of the AND gate with $a + 1$ inputs, applied to
$x_0, \dots, x_a$, returns $(\cdots((\mathrm{true} \land x_0) \land x_1) \cdots) \land x_a$,
folding conjunction over the inputs from left to right starting from true. -/
theorem booleanInterpretation_and (a : Nat) (f : Fin (a + 1) → Bool) :
    booleanInterpretation (.and a) f =
      Fin.foldl (a + 1) (fun acc k => acc && f k) true := rfl

/-- **Boolean OR as a left fold.** For every natural number $a$ and truth values
$x_0, \dots, x_a$, the Boolean interpretation of the OR gate with $a + 1$ inputs, applied to
$x_0, \dots, x_a$, returns $(\cdots((\mathrm{false} \lor x_0) \lor x_1) \cdots) \lor x_a$,
folding disjunction over the inputs from left to right starting from false. -/
theorem booleanInterpretation_or (a : Nat) (f : Fin (a + 1) → Bool) :
    booleanInterpretation (.or a) f =
      Fin.foldl (a + 1) (fun acc k => acc || f k) false := rfl

end Cslib.Circuits
