/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibExt.Combinatorics.Words.DumontThomasNumeration

namespace MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail

private def letterMap : Bool → List Bool
  | false => [true, false]
  | true => [false, false]

private def path : ℕ → List Bool × Bool
  | 0 => ([], true)
  | _ + 1 => ([true], false)

private theorem letterMap_isSubstitution : IsSubstitution letterMap := by
  refine ⟨fun a => by cases a <;> decide, false, Filter.tendsto_atTop_atTop.mpr ?_⟩
  intro n
  refine ⟨n, fun k hk => ?_⟩
  have hlen (a : Bool) : (letterMap a).length = 2 := by cases a <;> rfl
  simpa [morphIterate_length_of_uniform hlen] using hk.trans (Nat.lt_two_pow_self (n := k)).le

end MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail

namespace MetaMathlibExt.substitutionAutomaton_admissibleSequence.Tests

open morphIterate_getElem_eq_substitutionAutomaton_tail

private theorem path_isLetterAdmissible : IsLetterAdmissibleSequence letterMap false path 1 := by
  refine ⟨fun i hi => ?_, ⟨[], rfl⟩⟩
  obtain rfl : i = 0 := by omega
  exact ⟨[false], rfl⟩

-- The first digit skips a block of length two. Reversing the digits selects a different letter.
example : (morphIterate letterMap 2 [false])[2]? =
    substitutionAutomaton letterMap false [1, 0] := by
  exact morphIterate_getElem_eq_substitutionAutomaton_tail
    letterMap letterMap_isSubstitution 2 (by decide) false path path_isLetterAdmissible

-- A single pair can have an empty word. Its digit still makes a transition.
example : substitutionAutomaton letterMap false [0] = some true := by
  have hadm : IsLetterAdmissibleSequence letterMap false path 0 :=
    ⟨isAdmissibleSequence_zero _ _, ⟨[false], rfl⟩⟩
  exact substitutionAutomaton_admissibleSequence
    letterMap letterMap_isSubstitution 1 (by decide) false path hadm 0 (by decide)

-- The first digit reaches the intermediate letter, and the next digit changes it.
example : substitutionAutomaton letterMap false [1] = some false ∧
    substitutionAutomaton letterMap false [1, 0] = some true := by
  have h := substitutionAutomaton_admissibleSequence
    letterMap letterMap_isSubstitution 2 (by decide) false path path_isLetterAdmissible
  exact ⟨h 1 (by decide), h 0 (by decide)⟩

end MetaMathlibExt.substitutionAutomaton_admissibleSequence.Tests

namespace MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail

-- At depth zero the terminal word is unchanged and the only summand is `|m₀|`.
example : (∑ j ∈ Finset.range (0 + 1), (morphIterate letterMap j [true]).length) <
    (morphIterate letterMap 0 [true, false]).length :=
  admissibleSequence_weightedLength_lt letterMap letterMap_isSubstitution
    (fun _ => ([true], false)) 0 (isAdmissibleSequence_zero _ _)

-- Two transitions: `m₁a₁` is a full image, while `m₀a₀` is a proper prefix.
example : (∑ j ∈ Finset.range (2 + 1), (morphIterate letterMap j (path j).1).length) <
    (morphIterate letterMap 2 [true, false]).length := by
  apply admissibleSequence_weightedLength_lt letterMap letterMap_isSubstitution path 2
  intro i hi
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · exact ⟨[false], rfl⟩
  · exact ⟨[], rfl⟩

example : substitutionAutomaton letterMap false [1, 0] = some true ∧
    substitutionAutomaton letterMap false [0, 1] = some false ∧
    substitutionAutomaton letterMap false [1, 2] = none := by
  decide

end MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail

namespace MetaMathlibExt.letterAdmissibleSequence_eq_of_weightedLength_eq.Tests

open morphIterate_getElem_eq_substitutionAutomaton_tail

private def onePair : ℕ → List Bool × Bool
  | 0 => ([true], false)
  | _ + 1 => ([], false)

private def onePair' : ℕ → List Bool × Bool := fun _ => ([true], false)

-- At depth zero the prefix is nonempty and the two tails need not agree.
example : onePair 0 = onePair' 0 ∧ onePair 1 ≠ onePair' 1 := by
  have hs : IsLetterAdmissibleSequence letterMap false onePair 0 :=
    ⟨isAdmissibleSequence_zero _ _, ⟨[], rfl⟩⟩
  have hs' : IsLetterAdmissibleSequence letterMap false onePair' 0 :=
    ⟨isAdmissibleSequence_zero _ _, ⟨[], rfl⟩⟩
  have hw : (∑ j ∈ Finset.range (0 + 1), (morphIterate letterMap j (onePair j).1).length) = 1 ∧
      (∑ j ∈ Finset.range (0 + 1), (morphIterate letterMap j (onePair' j).1).length) = 1 := by
    decide
  exact ⟨letterAdmissibleSequence_eq_of_weightedLength_eq letterMap letterMap_isSubstitution 0
    false onePair onePair' hs hs' (hw.1.trans hw.2.symm) 0 (by decide), by decide⟩

private def pathWithTail (i : ℕ) : List Bool × Bool :=
  if i ≤ 1 then path i else ([], false)

-- At depth one the top word has length one but contributes two to the weight.
-- The top letter is false; the lower letter is true. The second tail is different.
example : path 0 = pathWithTail 0 ∧ path 1 = pathWithTail 1 ∧ path 2 ≠ pathWithTail 2 := by
  have hs : IsLetterAdmissibleSequence letterMap false path 1 := by
    refine ⟨fun i hi => ?_, ⟨[], rfl⟩⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[false], rfl⟩
  have hs' : IsLetterAdmissibleSequence letterMap false pathWithTail 1 := by
    refine ⟨fun i hi => ?_, ⟨[], rfl⟩⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[false], rfl⟩
  have hw : (∑ j ∈ Finset.range (1 + 1), (morphIterate letterMap j (path j).1).length) = 2 ∧
      (∑ j ∈ Finset.range (1 + 1), (morphIterate letterMap j (pathWithTail j).1).length) = 2 := by
    decide
  have h := letterAdmissibleSequence_eq_of_weightedLength_eq (η := letterMap)
    (hη := letterMap_isSubstitution) (k := 1) (b := false) (s := path) (s' := pathWithTail)
    (hs := hs) (hs' := hs') (hsum := hw.1.trans hw.2.symm)
  exact ⟨h 0 (by decide), h 1 (by decide), by decide⟩

end MetaMathlibExt.letterAdmissibleSequence_eq_of_weightedLength_eq.Tests

namespace MetaMathlibExt.seedAutomaton_neutral_padding.Tests

private def double : Unit → List Unit := fun _ => [(), ()]

private theorem unitPoint : IsPeriodicPointWithGrowingSeed double (fun _ => ()) 1 := by
  have hgrow : Filter.Tendsto (fun k => (morphIterate double k [()]).length)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun n => ⟨n, fun k hk => ?_⟩
    have hlen (a : Unit) : (double a).length = 2 := rfl
    simpa [morphIterate_length_of_uniform hlen] using hk.trans (Nat.lt_two_pow_self (n := k)).le
  have hper : IsTwoSidedPeriodicPoint double (fun _ => ()) 1 :=
    ⟨le_rfl, fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨⟨fun _ => List.cons_ne_nil _ _, (), hgrow⟩, ⟨hper, ?_⟩, hgrow, hgrow⟩
  intro q hq
  exact (show IsTwoSidedPeriodicPoint double (fun _ => ()) q from hq).one_le

-- Insert two padding blocks after either sign, keeping the nonempty suffix.
example : seedAutomaton double () () [0, 0, 0, 1] = some () ∧
    seedAutomaton double () () [1, 1, 1, 0] = some () := by
  have hzero := (seedAutomaton_neutral_padding (η := double) (u := fun _ => ())
    (p := 1) (hu := unitPoint) (v := [1]) (i := 2)).1 (by decide)
  have hone := (seedAutomaton_neutral_padding double (fun _ => ()) 1 unitPoint [0] 2).2
    (by decide)
  exact ⟨hzero.trans rfl, hone.trans rfl⟩

private def fibonacci (a : Fin 2) : List (Fin 2) := if a = 0 then [0, 1] else [0]

-- From the negative Fibonacci seed, two copies of `01` return to the seed; `10` is rejected.
example : lastLetterDigits fibonacci 2 1 = [0, 1] ∧
    seedAutomaton fibonacci 1 0 (1 :: ((List.replicate 2 (lastLetterDigits fibonacci 2 1)).flatten
      ++ [0])) = some 0 ∧
    seedAutomaton fibonacci 1 0 [1, 1, 0, 0] = none := by
  decide

end MetaMathlibExt.seedAutomaton_neutral_padding.Tests

namespace MetaMathlibExt.tail_injective_and_strictMono.Tests

open morphIterate_getElem_eq_substitutionAutomaton_tail
open substitutionAutomaton_admissibleSequence.Tests (path_isLetterAdmissible)

private def smallerTop : ℕ → List Bool × Bool
  | 0 => ([false], false)
  | _ + 1 => ([], true)

private def largerBottom : ℕ → List Bool × Bool := fun _ => ([true], false)

-- The top digit decides even though the bottom digits compare the other way.
example : ([0, 1] : List ℕ) < [1, 0] := by
  have hs : IsLetterAdmissibleSequence letterMap false smallerTop 1 := by
    refine ⟨fun i hi => ?_, ⟨[false], rfl⟩⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[], rfl⟩
  exact (tail_injective_and_strictMono letterMap letterMap_isSubstitution 2 (by decide)
    false smallerTop path hs path_isLetterAdmissible).2.mp (by decide)

-- With a shared top digit, the bottom digit breaks the tie: [1, 0] < [1, 1].
example : (∑ j ∈ Finset.range 2, (morphIterate letterMap j (path j).1).length) <
    ∑ j ∈ Finset.range 2, (morphIterate letterMap j (largerBottom j).1).length := by
  have hs : IsLetterAdmissibleSequence letterMap false largerBottom 1 :=
    ⟨fun _ _ => ⟨[], rfl⟩, ⟨[], rfl⟩⟩
  exact (tail_injective_and_strictMono letterMap letterMap_isSubstitution 2 (by decide)
    false path largerBottom path_isLetterAdmissible hs).2.mpr (by decide)

-- At depth one, equality of the retained digit determines the weight, not the unused pairs.
example : (∑ j ∈ Finset.range 1, (morphIterate letterMap j (path j).1).length) =
    ∑ j ∈ Finset.range 1, (morphIterate letterMap j (path 0).1).length := by
  have hs : IsLetterAdmissibleSequence letterMap false path 0 :=
    ⟨isAdmissibleSequence_zero _ _, ⟨[false], rfl⟩⟩
  have hs' : IsLetterAdmissibleSequence letterMap false (fun _ => path 0) 0 :=
    ⟨isAdmissibleSequence_zero _ _, ⟨[false], rfl⟩⟩
  exact (tail_injective_and_strictMono letterMap letterMap_isSubstitution 1 (by decide)
    false path (fun _ => path 0) hs hs').1.mpr rfl

end MetaMathlibExt.tail_injective_and_strictMono.Tests

namespace MetaMathlibExt.dumontThomasRep_quotient_remainder_pos.Tests

private def ternary (a : Bool) : List Bool := [a, !a, a]

private def alternating (i : ℤ) : Bool := decide (i % 2 = 1)

private def onePath (_ : ℕ) : List Bool × Bool := ([false], true)

private def fivePath : ℕ → List Bool × Bool
  | 0 => ([true, false], true)
  | _ + 1 => ([false], true)

private theorem onePath_admissible :
    IsLetterAdmissibleSequence ternary (alternating 0) onePath 0 :=
  ⟨isAdmissibleSequence_zero _ _, ⟨[false], rfl⟩⟩

private theorem one_rep : IsDumontThomasRep ternary alternating 1 1 [0, 1] :=
  Or.inr (Or.inr (Or.inl
    ⟨1, 1, onePath, by decide, rfl, dvd_refl _, onePath_admissible, by decide, by decide, rfl⟩))

-- Odd-length images preserve the alternating word on both sides of the origin. For N = 5,
-- the first digit skips a block of three; the last skips two letters in the image of `true`.
example : IsDumontThomasRep ternary alternating 1 5 [0, 1, 2] := by
  have hs : IsLetterAdmissibleSequence ternary (alternating 0) fivePath 1 := by
    refine ⟨fun i hi => ?_, ⟨[false], rfl⟩⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[], rfl⟩
  exact Or.inr (Or.inr (Or.inl
    ⟨5, 2, fivePath, by decide, rfl, by decide, hs, by decide, by decide, rfl⟩))

-- Independent positive-quotient check: the weighted positions are q = 1 and r = 2;
-- the quotient seed is `true`, not the original seed `false`.
example : (∑ j ∈ Finset.range (2 - 1), (morphIterate ternary j (fivePath (j + 1)).1).length) = 1 ∧
    (∑ j ∈ Finset.range 1, (morphIterate ternary j (fivePath j).1).length) = 2 ∧
    (morphIterate ternary 1 [alternating 1])[2]? = some (alternating 5) ∧
    IsDumontThomasRep ternary alternating 1 1 [0, 1] ∧
    IsLetterAdmissibleSequence ternary (alternating 1) fivePath 0 :=
  ⟨by decide, by decide, by decide, one_rep, isAdmissibleSequence_zero _ _, ⟨[], rfl⟩⟩

-- Independent zero-quotient check: there are no retained digits and r = 1.
example : (∑ j ∈ Finset.range (1 - 1), (morphIterate ternary j (onePath (j + 1)).1).length) = 0 ∧
    (∑ j ∈ Finset.range 1, (morphIterate ternary j (onePath j).1).length) = 1 ∧
    (morphIterate ternary 1 [alternating 0])[1]? = some (alternating 1) ∧
    IsDumontThomasRep ternary alternating 1 0 [0] ∧
    IsLetterAdmissibleSequence ternary (alternating 0) onePath 0 :=
  ⟨by decide, by decide, by decide, isDumontThomasRep_zero _ _ _, onePath_admissible⟩

-- Compute the singleton extension and both sides of iterate composition independently.
example : morphExtend ternary [true] = [true, false, true] ∧
    morphIterate ternary 2 [true] = [true, false, true, false, true, false, true, false, true] ∧
    morphIterate ternary 1 (morphIterate ternary 1 [true]) =
      [true, false, true, false, true, false, true, false, true] := by decide

open seedAutomaton_neutral_padding.Tests (double unitPoint)

-- Apply the public theorem on an actual period-one point, with a zero quotient.
example : IsDumontThomasRep double (fun _ => ()) 1 0 [0] := by
  let s : ℕ → List Unit × Unit := fun _ => ([()], ())
  have hs : IsLetterAdmissibleSequence double () s 0 :=
    ⟨isAdmissibleSequence_zero _ _, ⟨[], rfl⟩⟩
  exact (dumontThomasRep_quotient_remainder_pos (η := double) (u := fun _ => ())
    (p := 1) (hu := unitPoint) (N := 1) (k := 1) (s := s) (hN := by decide)
    (hk := dvd_refl _) (hs := hs) (htop := by decide) (hpre := by decide)).2.1

end MetaMathlibExt.dumontThomasRep_quotient_remainder_pos.Tests
