/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.CookLevin
meta import CSLibExt.Computability.CookLevin

@[expose] public section

set_option autoImplicit false

open Cslib.CookLevin

#check PolyManyOneRed
#check CNF
#check CNFSat
#check encodeCNF
#check decodeCNF
#check decodeCNF_eq_some_iff
#check encodeCNF_injective
#check encodeCNF_length
#check SATLang
#check satDec

example : CNFSat [[(0, true)]] := by
  refine ⟨fun _ => true, fun C h => ?_⟩
  have hC : C = [(0, true)] := by
    simpa only [List.mem_singleton] using h
  subst C
  exact ⟨0, true, by simp, rfl⟩

example : ¬ CNFSat [[(0, true)], [(0, false)]] := by
  rintro ⟨v, hv⟩
  obtain ⟨x1, b1, m1, e1⟩ := hv [(0, true)] (by simp)
  obtain ⟨x2, b2, m2, e2⟩ := hv [(0, false)] (by simp)
  have hm1 : x1 = 0 ∧ b1 = true := by
    simpa only [List.mem_singleton, Prod.mk.injEq] using m1
  have hm2 : x2 = 0 ∧ b2 = false := by
    simpa only [List.mem_singleton, Prod.mk.injEq] using m2
  obtain ⟨rfl, rfl⟩ := hm1
  obtain ⟨rfl, rfl⟩ := hm2
  rw [e1] at e2
  exact Bool.noConfusion e2

example : decodeCNF (encodeCNF []) = some [] := by simp

example : decodeCNF
    (encodeCNF [[(0, true), (5, false)], [], [(2, true)]]) =
      some [[(0, true), (5, false)], [], [(2, true)]] := by simp

example : decodeCNF [] = none := rfl
example : decodeCNF [true] = none := rfl
example : decodeCNF [false, true] = none := rfl
example : decodeNatPrefix [true, false, false] = none := rfl
example : decodeLit (encodeNatPrefix 3) = none := by
  unfold decodeLit
  rw [show decodeNatPrefix (encodeNatPrefix 3) =
      some (3, []) by
    simpa using decodeNatPrefix_encodeNatPrefix_append 3 []]
  rfl

example : encodeClause [] = [false] := rfl

example (n : Nat) (b : Bool) : encodeLit (n, b) =
    encodeNatPrefix n ++ [b] := rfl

example (φ ψ : CNF) (h : encodeCNF φ =
    encodeCNF ψ) : φ = ψ :=
  encodeCNF_injective h

example (input : List Bool) (φ : CNF) :
    decodeCNF input = some φ ↔ input = encodeCNF φ :=
  decodeCNF_eq_some_iff input φ

example : decodeClause
    (encodeClause [(2, false)] ++ [true]) =
      some ([(2, false)], [true]) := by simp

namespace CookLevinRuntimeTests

private meta def checkDecoding (decode : List Bool → Option CNF) (label : String)
    (input : List Bool) (expected : Option CNF) : IO Unit := do
  let actual := decode input
  if let some formula := actual then
    unless input == encodeCNF formula do
      throw (IO.userError s!"CNF complete {label} input={input} decoded={formula}")
  unless actual == expected do
    throw (IO.userError s!"CNF result {label} input={input} expected={expected} actual={actual}")

private meta def checkRawEncodings : IO Unit := do
  -- The name guards are reused from Complexity/SatTokenizerTests.lean.
  let cases : List (String × List Bool × Option CNF) :=
    [("empty input", [], none), ("truncated count", [true], none),
     ("empty formula", [false], some []),
     ("empty clause", [true, false, false], some [[]]),
     ("trailing bit", [false, true], none),
     ("invalid name", [true, false, true, false, true, false, false, true], none),
     ("missing polarity", [true, false, true, false] ++ encodeNatPrefix 3, none),
     ("noncanonical name", [true, false, true, false, true, true, true, false, false, true],
       none),
     ("canonical name", [true, false, true, false, true, true, false, false],
       some [[(1, false)]])]
  for (label, input, expected) in cases do checkDecoding decodeCNF label input expected
  unless decodeCNFAux [false, true] == some ([], [true]) do
    throw (IO.userError "CNF prefix parser suffix")
  let accepted := (cases.filter (·.2.2.isSome)).length
  IO.println s!"S2 CNF raw checks={cases.length} some={accepted} none={cases.length - accepted}"
  IO.println "S2 CNF prefixSuffixChecks=1"

#eval checkRawEncodings

private meta def fixedFormulas : List CNF :=
  [[], [[]], [[(0, true), (5, false)], [], [(2, true)]],
   [[(1, false), (1, false)], [(1, false), (1, false)], []],
   [[(7, true), (8, false), (255, true), (256, false)]],
   List.replicate 3 [(0, true), (7, false), (0, true), (7, false)]]

private meta def generatedFormulas : Plausible.Rand (List CNF) :=
  (List.range 1000).mapM fun _ => do
    let clauses ← Plausible.Random.randBound Nat 0 3 (by decide)
    (List.range clauses.val).mapM fun _ => do
      let literals ← Plausible.Random.randBound Nat 0 4 (by decide)
      (List.range literals.val).mapM fun _ => do
        let index ← Plausible.Random.randBound Nat 0 7 (by decide)
        let polarity ← Plausible.Random.rand Bool
        return (index.val, polarity)

private meta def checkFormula (formula : CNF) : IO Unit := do
  let input := encodeCNF formula
  checkDecoding decodeCNF "round trip" input (some formula)
  for suffix in [[true], [false]] do
    checkDecoding decodeCNF "nonempty suffix" (input ++ suffix) none
  checkDecoding decodeCNF "truncated" input.dropLast none

private meta def checkFixedFormulas : IO Unit := do
  let mut properPrefixes := 0
  for formula in fixedFormulas do
    checkFormula formula
    let input := encodeCNF formula
    -- dropLast was already checked by checkFormula.
    for n in List.range (input.length - 1) do
      checkDecoding decodeCNF "proper prefix" (input.take n) none
      properPrefixes := properPrefixes + 1
  IO.println s!"S2 CNF fixed formulas={fixedFormulas.length} baseChecks={4 * fixedFormulas.length}"
  IO.println s!"S2 CNF additionalProperPrefixChecks={properPrefixes}"

#eval checkFixedFormulas

private meta def runGeneratedDecodingTests : IO Unit := do
  let formulas := (generatedFormulas.run ⟨mkStdGen 2026110404⟩).1
  let clauses := formulas.flatten
  let literals := clauses.flatten
  let clauseCounts := (List.range 4).map fun n => (formulas.filter (·.length == n)).length
  let literalCounts := (List.range 5).map fun n => (clauses.filter (·.length == n)).length
  let indices := (List.range 8).map fun n => (literals.filter (·.1 == n)).length
  let positive := (literals.filter (·.2)).length
  let duplicateClauses := (formulas.filter fun f => f.any (fun c => f.count c > 1)).length
  let duplicateLiterals := (clauses.filter fun c => c.any (fun l => c.count l > 1)).length
  unless formulas.length == 1000 && clauseCounts.all (· > 0) &&
      literalCounts.all (· > 0) && indices.all (· > 0) &&
      positive > 0 && positive < literals.length && duplicateClauses > 0 &&
      duplicateLiterals > 0 do throw (IO.userError "CNF generator coverage")
  for formula in formulas do
    unless formula.length ≤ 3 && formula.all (fun c =>
        c.length ≤ 4 && c.all (fun l => l.1 ≤ 7)) do
      throw (IO.userError "CNF generator bounds")
    checkFormula formula
  IO.println s!"S2 CNF seed=2026110404 generated={formulas.length} checks={4 * formulas.length}"
  IO.println s!"S2 CNF retries=0 discards=0 clauseCounts={clauseCounts} literalCounts={literalCounts}"
  IO.println s!"S2 CNF indices={indices} positive={positive} negative={literals.length - positive}"
  IO.println s!"S2 CNF duplicateClauses={duplicateClauses} duplicateLiterals={duplicateLiterals}"

#eval runGeneratedDecodingTests

end CookLevinRuntimeTests
