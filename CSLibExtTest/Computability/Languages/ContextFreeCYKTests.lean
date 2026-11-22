/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.CYK
meta import CSLibExt.Computability.Languages.ContextFree.CYK

/-!
# Tests for the CYK recognizer

* `anbn`: `S → A X | A B`, `X → S B`, `A → true`, `B → false`, in Chomsky normal form, generates
  `trueⁿ falseⁿ` for `n ≥ 1`. The recognizer accepts `[true, false]` and
  `[true, true, false, false]` and rejects `[]`, `[true, false, false]` and `[false, true]`; by
  `cykAccepts_iff` these are statements about the language.
* `epsAB`: `S → ε | A B`, `A → true`, `B → false` generates `{[], [true, false]}`, so the empty
  word is accepted through `S → ε`.
-/

@[expose] public section

namespace Cslib.Language.CYKTests

/-- `S → A X | A B`, `X → S B`, `A → true`, `B → false`, with `S, X, A, B = 0, 1, 2, 3`. -/
def anbn : ContextFreeGrammar Bool where
  NT := Fin 4
  initial := 0
  rules := {⟨0, [.nonterminal 2, .nonterminal 1]⟩, ⟨0, [.nonterminal 2, .nonterminal 3]⟩,
    ⟨1, [.nonterminal 0, .nonterminal 3]⟩, ⟨2, [.terminal true]⟩, ⟨3, [.terminal false]⟩}

instance : DecidableEq anbn.NT := inferInstanceAs (DecidableEq (Fin 4))
instance : Fintype anbn.NT := inferInstanceAs (Fintype (Fin 4))

theorem anbn_isChomskyNormalForm : IsChomskyNormalForm anbn := by
  unfold IsChomskyNormalForm
  decide

example : cykAccepts anbn [true, false] = true := by decide
example : cykAccepts anbn [true, true, false, false] = true := by decide
example : cykAccepts anbn [] = false := by decide
example : cykAccepts anbn [true, false, false] = false := by decide
example : cykAccepts anbn [false, true] = false := by decide

example : [true, true, false, false] ∈ anbn.language :=
  (cykAccepts_iff anbn_isChomskyNormalForm).1 (by decide)

example : [true, false, false] ∉ anbn.language := fun h => by
  have := (cykAccepts_iff anbn_isChomskyNormalForm).2 h
  revert this
  decide

/-- `S → ε | A B`, `A → true`, `B → false`, with `S, A, B = 0, 1, 2`. -/
def epsAB : ContextFreeGrammar Bool where
  NT := Fin 3
  initial := 0
  rules := {⟨0, []⟩, ⟨0, [.nonterminal 1, .nonterminal 2]⟩, ⟨1, [.terminal true]⟩,
    ⟨2, [.terminal false]⟩}

instance : DecidableEq epsAB.NT := inferInstanceAs (DecidableEq (Fin 3))
instance : Fintype epsAB.NT := inferInstanceAs (Fintype (Fin 3))

theorem epsAB_isChomskyNormalForm : IsChomskyNormalForm epsAB := by
  unfold IsChomskyNormalForm
  decide

example : [] ∈ epsAB.language := (cykAccepts_iff epsAB_isChomskyNormalForm).1 (by decide)
example : cykAccepts epsAB [true, false] = true := by decide
example : cykAccepts epsAB [true, false, true, false] = false := by decide

end Cslib.Language.CYKTests

namespace Cslib.Language.CYKTests

-- These bounded word predicates follow the productions above; no universal
-- language-characterization theorem is being asserted by the runtime tests.
private meta def anbnExpected (w : List Bool) : Bool :=
  let n := (w.takeWhile id).length
  n > 0 && w == List.replicate n true ++ List.replicate n false

private meta def epsABExpected (w : List Bool) : Bool :=
  w.isEmpty || w == [true, false]

private meta def checkAcceptance (name : String) (accept oracle : List Bool → Bool)
    (w : List Bool) : IO Unit := do
  let actual := accept w
  let expected := oracle w
  unless actual == expected do
    throw (IO.userError s!"CYK {name} word={w} expected={expected} actual={actual}")

private meta def boolWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolWords n).flatMap fun w => [false :: w, true :: w]

private meta def generatedWords : Plausible.Rand (List (List Bool)) :=
  (List.range 1000).mapM fun _ => do
    let n ← Plausible.Random.randBound Nat 0 12 (by decide)
    (List.range n.val).mapM fun _ => Plausible.Random.rand Bool

private abbrev singletonTerminal : ContextFreeGrammar Bool where
  NT := Unit
  initial := ()
  rules := {⟨(), [.terminal true]⟩}

private abbrev noRules : ContextFreeGrammar Bool where
  NT := Unit
  initial := ()
  rules := ∅


#eval show IO Unit from do
  unless @decide (IsChomskyNormalForm singletonTerminal)
      (by unfold IsChomskyNormalForm singletonTerminal; infer_instance) &&
      @decide (IsChomskyNormalForm noRules)
      (by unfold IsChomskyNormalForm noRules; infer_instance) do throw (IO.userError "boundary grammar CNF")
  for w in [[], [true], [false], [true, true], [true, false]] do
    checkAcceptance "singleton" (cykAccepts singletonTerminal) (· == [true]) w
    checkAcceptance "noRules" (cykAccepts noRules) (fun _ => false) w
  IO.println "S2 CYK boundary probe: both full normal-form predicates; 10 checks PASS"

private theorem singletonTerminal_normal : IsChomskyNormalForm singletonTerminal := by
  unfold IsChomskyNormalForm
  decide

private theorem noRules_normal : IsChomskyNormalForm noRules := by
  unfold IsChomskyNormalForm
  decide

example : [true] ∈ singletonTerminal.language :=
  (cykAccepts_iff singletonTerminal_normal).1 (by decide)

example : [] ∉ noRules.language := fun h => by
  have := (cykAccepts_iff noRules_normal).2 h
  revert this
  decide

private meta def runAcceptanceTests (acceptAnbn acceptEps : List Bool → Bool) : IO Unit := do
  let exhaustive := (List.range 9).flatMap boolWords
  let generated := (generatedWords.run ⟨mkStdGen 2026110402⟩).1
  let fixed := [[], [true], [false], [true, false], [true, true, false, false],
    [true, false, false], [false, true], [true, false, true, false],
    List.replicate 6 true ++ List.replicate 6 false, List.replicate 12 false]
  let lengths := (List.range 13).map fun n => (generated.filter (·.length == n)).length
  unless exhaustive.length == 511 && exhaustive.eraseDups.length == 511 &&
      (List.range 9).all (fun n => (exhaustive.filter (·.length == n)).length == 2^n) &&
      generated.length == 1000 && lengths.all (· > 0) do
    throw (IO.userError "CYK corpus coverage")
  for (kind, words) in [("fixed", fixed), ("exhaustive", exhaustive),
      ("generated", generated)] do
    for (name, accept, oracle) in [("anbn", acceptAnbn, anbnExpected),
        ("epsAB", acceptEps, epsABExpected)] do
      let mut accepted := 0
      for w in words do
        unless w.length ≤ 12 do throw (IO.userError "CYK word bound")
        checkAcceptance name accept oracle w
        if oracle w then accepted := accepted + 1
      unless accepted > 0 && accepted < words.length do
        throw (IO.userError s!"CYK {name} {kind} missing acceptance/rejection branch")
      IO.println s!"S2 CYK {name} {kind} checks={words.length} accepted={accepted}"
  IO.println s!"S2 CYK seed=2026110402 sharedDraws={generated.length} retries=0 discards=0"
  IO.println s!"S2 CYK generated lengths={lengths} trueBits={generated.flatten.count true}"

#eval runAcceptanceTests (cykAccepts anbn) (cykAccepts epsAB)

end Cslib.Language.CYKTests
