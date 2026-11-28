/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PermutationWordleFirstCorrectOne
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Permutation
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- An independent list simulation: rotate the entries at incorrect positions and put
-- them back into the same slots in the guess.
private def nextList (secret guess : List ℕ) : List ℕ :=
  let wrong := guess.zipIdx.filter (fun (a, i) => some a != secret[i]?)
  let moves := (wrong.map Prod.snd).zip ((wrong.map Prod.fst).rotateRight)
  guess.zipIdx.map fun (a, i) => ((moves.find? (fun p => p.1 == i)).map Prod.snd).getD a

example : ((List.range 4).permutations'.filter fun π =>
    let g₀ := List.range 4
    let g₁ := nextList π g₀
    let g₂ := nextList π g₁
    (g₀.zip π).any (fun (a, b) => a == b) && (g₀ != π) && (g₁ != π) && (g₂ == π)).length =
      4 := by decide

private theorem checkNextGuess {m n : ℕ} (S : (k : ℕ) → Equiv.Perm (Fin k))
    (π : Equiv.Perm (Fin n)) (g next : Fin n → Fin n) (e : Fin m ↪o Fin n)
    (missed : ∀ i, (∃ j, e j = i) ↔ g i ≠ π i)
    (shifted : ∀ j, next (e j) = g (e ((S m).symm j)))
    (locked : ∀ i, g i = π i → next i = g i) : permWordleNextGuess S π g = next := by
  funext i
  by_cases hi : g i = π i
  · exact (permWordleNextGuess_of_eq S π g i hi).trans (locked i hi).symm
  · obtain ⟨j, rfl⟩ := (missed i).mpr hi
    exact (permWordleNextGuess_apply_orderEmbedding S π g e missed j).trans (shifted j).symm

-- The nonconsecutive mismatch set {0,1,3,4} shrinks to {1,4}; position 2
-- stays locked throughout. Both replies are checked entry by entry.
example :
    let π : Equiv.Perm (Fin 5) := Equiv.swap 0 4 * Equiv.swap 1 3
    let S := cyclicShiftLeftStrategy 5
    (∀ i, permWordleGuess S π 0 i = π i ↔ i = 2) ∧
      (∀ i, permWordleGuess S π 1 i ≠ π i ↔ i = 1 ∨ i = 4) ∧
      permWordleGuess S π 2 = ⇑π := by
  intro π S
  let a : Fin 4 ↪o Fin 5 := OrderEmbedding.ofStrictMono ![0, 1, 3, 4] (by decide)
  let b : Fin 2 ↪o Fin 5 := OrderEmbedding.ofStrictMono ![1, 4] (by decide)
  let reply : Fin 5 → Fin 5 := ![4, 0, 2, 1, 3]
  have h₀ : ∀ i, id i = π i ↔ i = 2 := by decide +revert
  have h₁ : ∀ i, reply i ≠ π i ↔ i = 1 ∨ i = 4 := by decide +revert
  have second : permWordleGuess S π 1 = reply := by
    rw [permWordleGuess_succ S π 0, permWordleGuess.eq_1]
    clear h₀ h₁
    apply checkNextGuess S π id reply a <;> decide +revert
  have third : permWordleGuess S π 2 = ⇑π := by
    rw [permWordleGuess_succ S π 1, second]
    clear h₀ h₁ second
    apply checkNextGuess S π reply π b <;> decide +revert
  rw [permWordleGuess.eq_1, second]
  exact ⟨h₀, h₁, third⟩

-- Even the identity at length four (not a four-cycle) gives the same count.
private def identityAtFour (m : ℕ) : Equiv.Perm (Fin m) := if m = 4 then 1 else finRotate m

-- A two-point support solves on the second guess and stays solved on the third.
example :
    let π : Equiv.Perm (Fin 4) := Equiv.swap 0 2
    (∀ i, permWordleGuess identityAtFour π 0 i = π i ↔ i = 1 ∨ i = 3) ∧
      permWordleGuess identityAtFour π 1 = ⇑π ∧ permWordleGuess identityAtFour π 2 = ⇑π := by
  intro π
  let e : Fin 2 ↪o Fin 4 := OrderEmbedding.ofStrictMono ![0, 2] (by decide)
  have h₀ : ∀ i, id i = π i ↔ i = 1 ∨ i = 3 := by decide +revert
  have second : permWordleGuess identityAtFour π 1 = ⇑π := by
    rw [permWordleGuess_succ identityAtFour π 0, permWordleGuess.eq_1]
    clear h₀
    apply checkNextGuess identityAtFour π id π e <;> decide +revert
  have third : permWordleGuess identityAtFour π 2 = ⇑π := by
    rw [permWordleGuess_succ identityAtFour π 1, second]
    exact funext fun i => permWordleNextGuess_of_eq identityAtFour π π i rfl
  rw [permWordleGuess.eq_1]
  exact ⟨h₀, second, third⟩

example :
    (Nat.card {π : Equiv.Perm (Fin 4) //
      PermWordleSolvedIn identityAtFour π 3 ∧ PermWordleFirstCorrectAt identityAtFour π 1} : ℚ) =
      4 := by
  have h (m : ℕ) (hm : m < 4) : identityAtFour m = finRotate m := by
    simp [identityAtFour, hm.ne]
  rw [card_solvedIn_three_firstCorrectAt_one 4 (by decide) identityAtFour h]
  norm_num
