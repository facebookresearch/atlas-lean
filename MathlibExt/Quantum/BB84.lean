/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod

/-!
# BB84 intercept-resend error rate

In the BB84 protocol with an intercept-resend attack, the
sifted rounds (Bob's basis equals Alice's) have error
exactly when Eve measured in the wrong basis and flipped
the bit: 4 of the 16 uniform sifted combinations, a rate of
`1/4`. Counts are stated over the five uniform booleans
`(a, e, ba, be, bb)`.
-/

@[expose] public section

/-- BB84 intercept-resend outcomes (core of QCI-50). Alice
sends bit `a` in basis `ba` (false = Z, true = X); Eve measures
in basis `be` obtaining `e`, resends; Bob measures in basis
`bb` obtaining `r`. The (deterministic given bases) resent bit
is `e`; Bob's result is wrong when bases align (`bb = ba`) but
Eve chose wrong (`be ≠ ba`) and her outcome flipped the bit:
modeled by the standard table: error iff `bb = ba ∧ be ≠ ba ∧ e ≠ a`,
with `e` uniform. Counting form below. -/
def bb84Error (a e : Bool) (ba be bb : Bool) : Bool :=
  (bb == ba) && (be != ba) && (e != a)

/-- Over uniform Eve outcomes and basis choices, exactly
1/4 of the 32 equally likely `(a, e, ba, be, bb)` combinations
with sifted bases (`bb = ba`) produce an error: precisely 4 of
the 16 sifted combinations. Sifted error count: -/
theorem bb84_sifted_errors :
    (Finset.univ.filter (fun p : Bool × Bool × Bool × Bool × Bool =>
      bb84Error p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
        && (p.2.2.2.2 == p.2.2.1))).card = 4 := by
  decide

/-- Total sifted combinations: 16 of 32 have `bb = ba` after
also fixing... stated as the full count of sifted tuples: -/
theorem bb84_sifted_total :
    (Finset.univ.filter (fun p : Bool × Bool × Bool × Bool × Bool =>
      p.2.2.2.2 == p.2.2.1)).card = 16 := by
  decide

/-- Hence the sifted error rate is `4/16 = 1/4` (kept here as
the two counts). No error when Eve measures in Alice's basis: -/
theorem bb84_no_error_when_eve_correct (a e : Bool) (ba bb : Bool)
    (hbe : bb = ba) :
    bb84Error a e ba ba bb = false := by
  have _ := hbe
  unfold bb84Error
  simp

end
