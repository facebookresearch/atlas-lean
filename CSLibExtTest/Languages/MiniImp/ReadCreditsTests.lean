/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.ReadCredits

import all CSLibExt.Languages.MiniImp.ReadCost
import all CSLibExt.Languages.MiniImp.Exec
import all CSLibExt.Languages.MiniImp.Semantics
import all CSLibExt.Languages.MiniImp.Syntax
import all Cslib.Algorithms.Lean.TimeM

/-!
# Read-credit rules and interpreter checks

Compiling this module executes and asserts the fixed twenty-case corpus.
Finite observations supplement the universal successful-run proofs.

In a normal checkout, build this client with:
lake --wfail build CSLibExtTest.Languages.MiniImp.ReadCreditsTests
Replay its imported and local constants in a fresh kernel environment with:
lake env leanchecker --fresh CSLibExtTest.Languages.MiniImp.ReadCreditsTests
-/

public section

namespace CSLibExt.Languages.MiniImp.ReadCreditsTests

/-- Skip has the same exact credit assertion at entry and exit. -/
private theorem skipRule (P : State → Nat → Prop) : ReadCredits P .skip P :=
  ReadCredits.skip P

/-- Read into a scalar distinct from the counter, then decrement the counter.
The deliberately false syntax annotation is ghost data. -/
private def countdown (xs : Array Nat) (dest : String) : Stmt :=
  .while (.le (.lit 1) (.var "i")) (fun _ => False)
    (.seq (.read dest xs (.lit 0)) (.assign "i" (.sub (.var "i") (.lit 1))))

/-- Decrement consumes no credits and establishes the counter invariant. -/
private theorem decrementCredits :
    ReadCredits (fun s k => s "i" - 1 ≤ k)
      (.assign "i" (.sub (.var "i") (.lit 1))) (fun s k => s "i" ≤ k) := by
  apply ReadCredits.consequence (h := ReadCredits.assign (Q := fun s k => s "i"
    ≤ k))
  · intro s k h
    simpa only [State.update, evalA, ite_true] using h
  · intro s k h
    exact h

/-- The read and assignment rules compose with the remaining credits. -/
private theorem bodyCredits (xs : Array Nat) (dest : String)
    (hxs : 0 < xs.size) (hd : dest ≠ "i") :
    ReadCredits (fun s k => s "i" ≤ k ∧ beval (.le (.lit 1) (.var "i")) s)
      (.seq (.read dest xs (.lit 0)) (.assign "i" (.sub (.var "i") (.lit 1))))
      (fun s k => s "i" ≤ k) := by
  apply ReadCredits.seq (R := fun s k => s "i" - 1 ≤ k) _ decrementCredits
  apply ReadCredits.consequence
    (h := ReadCredits.read (Q := fun s k => s "i" - 1 ≤ k))
  · intro s k h
    have hk : 1 ≤ k := by
      change s "i" ≤ k ∧ 1 ≤ s "i" at h
      omega
    refine ⟨hk, hxs, ?_⟩
    simp only [State.update, ite_eq_right (Ne.symm hd)]
    omega
  · intro s k h
    exact h

/-- The rule-using countdown consumer exits with a zero counter and spends
at most the initial credits, for every unrestricted initial state. -/
private theorem countdownCredits (xs : Array Nat) (dest : String)
    (hxs : 0 < xs.size) (hd : dest ≠ "i") :
    ReadCredits (fun s k => s "i" ≤ k) (countdown xs dest) (fun s _ => s "i" =
      0) := by
  apply ReadCredits.consequence
    (h := ReadCredits.while (A := fun _ => False) (bodyCredits xs dest hxs hd))
  · intro s k h
    exact h
  · intro s k h
    change s "i" ≤ k ∧ ¬ 1 ≤ s "i" at h
    omega

/-- Successful canonical interpreter runs inherit the concrete time bound
and final scalar property from the new compositional judgment. -/
private theorem countdownExec (xs : Array Nat) (dest : String)
    (hxs : 0 < xs.size) (hd : dest ≠ "i") {s t : State} {fuel k : Nat}
    (hcredit : s "i" ≤ k) (hret : (execReads fuel (countdown xs dest) s).ret =
      some t) :
    (execReads fuel (countdown xs dest) s).time ≤ k ∧ t "i" = 0 :=
  ReadCredits.execReads (countdownCredits xs dest hxs hd) hcredit hret

/-- The consumer also projects to the existing ordinary Hoare judgment. -/
private theorem countdownHoare (xs : Array Nat) (dest : String)
    (hxs : 0 < xs.size) (hd : dest ≠ "i") :
    Hoare (fun s => ∃ k, s "i" ≤ k) (countdown xs dest)
      (fun t => ∃ _k : Nat, t "i" = 0) :=
  ReadCredits.hoare (countdownCredits xs dest hxs hd)

/-- The conditional API verifies the same two branches exercised at runtime. -/
private theorem conditionalCredits :
    ReadCredits (fun _ k => 1 ≤ k)
      (.if_ (.le (.lit 1) (.var "i")) (.read "r" #[7] (.lit 0))
        (.assign "r" (.lit 11))) (fun _ _ => True) := by
  apply ReadCredits.if_
  · apply ReadCredits.consequence (h := ReadCredits.read (Q := fun _ _ => True))
    · intro s k h
      exact ⟨h.1, by change 0 < 1; decide, trivial⟩
    · intro s k h
      exact h
  · apply ReadCredits.consequence (h := ReadCredits.assign (Q := fun _ _ =>
    True))
    · intro s k h
      trivial
    · intro s k h
      exact h

/-- Natural subtraction alone would conceal this overspend at zero credits. -/
private theorem readZeroRefutes :
    ¬ ReadCredits (fun _ k => k = 0) (.read "r" #[7] (.lit 0)) (fun _ _ => True)
      := by
  intro h
  have hn := (h (fun _ => 0) 0 _ 1 rfl (ReadSteps.read (by decide))).1
  omega

/-- Sequencing two reads at one credit refutes a max-cost or reset-credit rule.
  -/
private theorem sequenceOneRefutes :
    ¬ ReadCredits (fun _ k => k = 1)
      (.seq (.read "r" #[7] (.lit 0)) (.read "z" #[13] (.lit 0)))
      (fun _ _ => True) := by
  intro h
  have hn := (h (fun _ => 0) 1 _ 2 rfl
    (ReadSteps.seq (ReadSteps.read (by decide))
      (ReadSteps.read (by change 0 < 1; decide)))).1
  omega

/-- The later invalid read has no successful derivation. The success-only
judgment may therefore hold at zero credits despite a charged failed prefix. -/
private theorem failedPrefixCredits :
    ReadCredits (fun _ k => k = 0)
      (.seq (.read "r" #[7] (.lit 0)) (.read "z" #[13] (.lit 1)))
      (fun _ _ => False) := by
  intro s k t n hP h
  cases h with
  | seq _ h₂ =>
      cases h₂ with
      | read hb => exact False.elim (Nat.lt_irrefl 1 hb)

/-- Assertions can demand exactly zero credits; no upward closure is built in.
  -/
private theorem exactCreditsSkip :
    ReadCredits (fun _ k => k = 0) .skip (fun _ k => k = 0) :=
  skipRule _

/-- A zero-credit successful skip falsifies a positive-credit postcondition. -/
private theorem positiveCreditsSkipRefutes :
    ¬ ReadCredits (fun _ k => k = 0) .skip (fun _ k => 0 < k) := by
  intro h
  have hn := (h (fun _ => 0) 0 _ 0 rfl ReadSteps.skip).2
  exact Nat.lt_irrefl 0 hn

/-- One finite interpreter input and its pre-frozen scalar/count observation. -/
private structure Case where
  name : String
  code : Stmt
  initial : Nat × Nat × Nat
  credits : Nat
  fuel : Nat
  expectedTime : Nat
  expectedFinal : Option (Nat × Nat × Nat)

/-- The three named scalars are initialized explicitly; all other names are
  zero. -/
private def initialState (values : Nat × Nat × Nat) : State :=
  fun x => if x = "i" then values.1 else if x = "r" then values.2.1
    else if x = "z" then values.2.2 else 0

/-- Observe the actual canonical instrumented interpreter, including failure
  costs. -/
private def observe (c : Case) : Nat × Option (Nat × Nat × Nat) :=
  let result := execReads c.fuel c.code (initialState c.initial)
  (result.time, result.ret.map fun s => (s "i", s "r", s "z"))

-- BEGIN FINITE CORPUS
/-- The finite corpus covers both successes and failures; expectations are
  fixed. -/
private def cases : List Case := [
  { name := "loop-zero",
    code :=
      countdown #[7] "r",
    initial := (0, 99, 88), credits := 0, fuel := 1,
    expectedTime := 0, expectedFinal := some (0, 99, 88) },
  { name := "loop-one-exact",
    code :=
      countdown #[7] "r",
    initial := (1, 99, 88), credits := 1, fuel := 3,
    expectedTime := 1, expectedFinal := some (0, 7, 88) },
  { name := "loop-three-exact",
    code :=
      countdown #[42] "r",
    initial := (3, 99, 88), credits := 3, fuel := 5,
    expectedTime := 3, expectedFinal := some (0, 42, 88) },
  { name := "loop-two-surplus-varied-destination",
    code :=
      countdown #[0, 42] "z",
    initial := (2, 99, 88), credits := 3, fuel := 4,
    expectedTime := 2, expectedFinal := some (0, 99, 0) },
  { name := "loop-zero-fuel",
    code :=
      countdown #[7] "r",
    initial := (0, 99, 88), credits := 0, fuel := 0,
    expectedTime := 0, expectedFinal := none },
  { name := "loop-insufficient-fuel",
    code :=
      countdown #[7] "r",
    initial := (3, 99, 88), credits := 3, fuel := 3,
    expectedTime := 1, expectedFinal := none },
  { name := "read-zero-credit",
    code :=
      .read "r" #[7] (.lit 0),
    initial := (0, 99, 88), credits := 0, fuel := 1,
    expectedTime := 1, expectedFinal := some (0, 7, 88) },
  { name := "read-one-credit",
    code :=
      .read "r" #[7] (.lit 0),
    initial := (0, 99, 88), credits := 1, fuel := 1,
    expectedTime := 1, expectedFinal := some (0, 7, 88) },
  { name := "read-surplus-credit",
    code :=
      .read "r" #[7] (.lit 0),
    initial := (0, 99, 88), credits := 3, fuel := 1,
    expectedTime := 1, expectedFinal := some (0, 7, 88) },
  { name := "two-reads-one-credit",
    code :=
      .seq (.read "r" #[7] (.lit 0)) (.read "z" #[13] (.lit 0)),
    initial := (0, 99, 88), credits := 1, fuel := 2,
    expectedTime := 2, expectedFinal := some (0, 7, 13) },
  { name := "two-reads-exact-credit",
    code :=
      .seq (.read "r" #[7] (.lit 0)) (.read "z" #[13] (.lit 0)),
    initial := (0, 99, 88), credits := 2, fuel := 2,
    expectedTime := 2, expectedFinal := some (0, 7, 13) },
  { name := "if-taken",
    code :=
      .if_ (.le (.lit 1) (.var "i")) (.read "r" #[7] (.lit 0)) (.assign "r"
        (.lit 11)),
    initial := (1, 99, 88), credits := 1, fuel := 2,
    expectedTime := 1, expectedFinal := some (1, 7, 88) },
  { name := "if-untaken",
    code :=
      .if_ (.le (.lit 1) (.var "i")) (.read "r" #[7] (.lit 0)) (.assign "r"
        (.lit 11)),
    initial := (0, 99, 88), credits := 0, fuel := 2,
    expectedTime := 0, expectedFinal := some (0, 11, 88) },
  { name := "read-last-index",
    code :=
      .read "r" #[2, 5] (.lit 1),
    initial := (0, 99, 88), credits := 1, fuel := 1,
    expectedTime := 1, expectedFinal := some (0, 5, 88) },
  { name := "read-invalid-index",
    code :=
      .read "r" #[7] (.lit 1),
    initial := (0, 99, 88), credits := 0, fuel := 1,
    expectedTime := 0, expectedFinal := none },
  { name := "read-empty-array",
    code :=
      .read "r" #[] (.lit 0),
    initial := (0, 99, 88), credits := 0, fuel := 1,
    expectedTime := 0, expectedFinal := none },
  { name := "later-failure-prefix",
    code :=
      .seq (.read "r" #[7] (.lit 0)) (.read "z" #[13] (.lit 1)),
    initial := (0, 99, 88), credits := 0, fuel := 2,
    expectedTime := 1, expectedFinal := none },
  { name := "always-true-fuel-exhaustion",
    code :=
      .while .tru (fun _ => False) (.read "r" #[7] (.lit 0)),
    initial := (0, 99, 88), credits := 0, fuel := 3,
    expectedTime := 2, expectedFinal := none },
  { name := "subtraction-truncates",
    code :=
      .assign "r" (.sub (.lit 0) (.lit 3)),
    initial := (0, 99, 88), credits := 0, fuel := 1,
    expectedTime := 0, expectedFinal := some (0, 0, 88) },
  { name := "division-zero",
    code :=
      .assign "z" (.div (.lit 5) (.lit 0)),
    initial := (0, 99, 88), credits := 0, fuel := 1,
    expectedTime := 0, expectedFinal := some (0, 99, 0) }]
-- END FINITE CORPUS

/-- A concrete successful countdown instantiates the rule proof and bridge on
its actual `.ret` identity, with the same input used in the finite corpus. -/
private theorem concreteConsumer :
    (execReads 3 (countdown #[7] "r") (initialState (1, 99, 88))).time ≤ 1 ∧
      (((initialState (1, 99, 88)).update "r" 7).update "i" 0) "i" = 0 := by
  apply countdownExec #[7] "r" (by decide) (by decide)
    (s := initialState (1, 99, 88)) (fuel := 3) (k := 1)
  · change 1 ≤ 1
    decide
  · rfl

/-- This false observation is well typed and must fail during execution. -/
private def falseSingleReadTime : Option Bool :=
  (cases.find? (fun c => decide (c.name = "read-zero-credit"))).map fun c =>
    (observe
    c).1 == 0

/-- This well-typed false observation would accept an incorrect sequence rule.
  -/
private def falseTwoReadBudget : Option Bool :=
  (cases.find? (fun c => decide (c.name = "two-reads-one-credit"))).map fun c =>
    (observe c).1 ≤ 1

/-- Emit actual scalar/count data before checking the frozen expectation. -/
private def checkCase (c : Case) (wrong : Bool) : IO Bool := do
  let actual := observe c
  IO.println s!"{c.name}|{actual.1}|{repr actual.2}|credits={c.credits}"
  let expected := if wrong && decide (c.name = "loop-three-exact") then some (0,
    43, 88)
    else c.expectedFinal
  let ok := actual.1 == c.expectedTime && actual.2 == expected
  if !ok then
    IO.eprintln s!"MISMATCH|{c.name}|expected={c.expectedTime},{repr expected}"
  return ok

/-- Missing control inputs are errors, distinct from the intended semantic
  rejection. -/
private def checkNegative (name : String) (observation : Option Bool) : IO
  UInt32 := do
  match observation with
  | none => throw (IO.userError s!"missing control input: {name}")
  | some value =>
      IO.println s!"CONTROL|{name}|{value}"
      return if value then 0 else 1

/-- Execute the canonical interpreter on the complete fixed corpus. Negative
modes retain the same compiled source and intentionally reject false
  observations. -/
def runChecks (mode : String) : IO UInt32 := do
  if decide (mode = "false-single-read-time") then
    return ← checkNegative mode falseSingleReadTime
  if decide (mode = "false-two-read-budget") then
    return ← checkNegative mode falseTwoReadBudget
  if !(decide (mode = "positive")) && !(decide (mode = "wrong-same-source"))
    then
    throw (IO.userError s!"unknown control mode: {mode}")
  let mut passed := 0
  for c in cases do
    if ← checkCase c (decide (mode = "wrong-same-source")) then
      passed := passed + 1
  IO.println s!"CASES|{cases.length}|PASS|{passed}"
  return if passed == cases.length && cases.length == 20 then 0 else 1

end CSLibExt.Languages.MiniImp.ReadCreditsTests

open CSLibExt.Languages.MiniImp.ReadCreditsTests in
#eval (do
  let status ← runChecks "positive"
  if status != 0 then
    throw (IO.userError "Read-credit runtime corpus failed")
  : IO Unit)
