/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal complete finite transition tables and exact source word bindings. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationD6A5Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationD6A5Block01

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The finite original-source representatives in the D6A5 cover. -/
def y322D6A5RepresentativeWord : Fin 32 → List (Fin 8) :=
![
    [],
    [
      6],
    [
      6, 0],
    [
      6, 0, 1],
    [
      6, 0, 4],
    [
      6, 0, 1, 2],
    [
      6, 0, 1, 4],
    [
      6, 0, 1, 2, 3],
    [
      6, 0, 1, 2, 4],
    [
      6, 0, 1, 4, 0],
    [
      6, 0, 1, 2, 3, 4],
    [
      6, 0, 1, 2, 4, 0],
    [
      6, 0, 1, 4, 0, 6],
    [
      6, 0, 1, 2, 3, 4, 0],
    [
      6, 0, 1, 2, 4, 0, 1],
    [
      6, 0, 1, 2, 4, 0, 6],
    [
      6, 0, 1, 2, 3, 4, 0, 1],
    [
      6, 0, 1, 2, 3, 4, 0, 6],
    [
      6, 0, 1, 2, 4, 0, 1, 6],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 2],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 6],
    [
      6, 0, 1, 2, 4, 0, 1, 6, 0],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 2, 6],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 6, 0],
    [
      6, 0, 1, 2, 4, 0, 1, 6, 0, 4],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 2, 6, 0],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 6, 0, 4],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 2, 6, 0, 1],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 2, 6, 0, 4],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 2, 6, 0, 1, 4],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 2, 6, 0, 1, 4, 0],
    [
      6, 0, 1, 2, 3, 4, 0, 1, 2, 6, 0, 1, 4, 0, 6]]

/-- The exact finite target of each original-source right-generator transition. -/
def y322D6A5TargetData : Fin 192 → Fin 32 :=
![
  0, 0, 0, 0, 0, 1, 2, 1, 1, 1, 1, 0, 1, 3, 2, 2, 4, 2, 3, 2, 5, 3, 6, 3, 4, 6, 4, 4, 2, 4, 5,
  5, 3, 7, 8, 5, 9, 4, 8, 6, 3, 6, 7, 7, 7, 5, 10, 7, 11, 8, 6, 10, 5, 8, 6, 9, 11, 9, 9, 12,
  13, 10, 10, 8, 7, 10, 8, 14, 9, 13, 11, 15, 12, 12, 15, 12, 12, 9, 10, 16, 13, 11, 13, 17, 14,
  11, 14, 16, 14, 18, 15, 18, 12, 17, 15, 11, 16, 13, 19, 14, 16, 20, 17, 20, 17, 15, 17, 13,
  21, 15, 18, 20, 18, 14, 19, 19, 16, 19, 19, 22, 23, 17, 22, 18, 20, 16, 18, 21, 21, 23, 24,
  21, 25, 22, 20, 22, 22, 19, 20, 23, 25, 21, 26, 23, 24, 24, 24, 26, 21, 24, 22, 27, 23, 25,
  28, 25, 26, 26, 28, 24, 23, 26, 27, 25, 27, 27, 29, 27, 28, 29, 26, 28, 25, 28, 30, 28, 29,
  29, 27, 29, 29, 30, 30, 30, 30, 31, 31, 31, 31, 31, 31, 30]

/-- Select the literal transition by its representative and source generator. -/
def y322D6A5Index (i : Fin 32) (g : Fin 6) : Fin 192 :=
  ⟨i.val * 6 + g.val, by omega⟩

/-- The source generator labels of this actual parabolic. -/
def y322D6A5Generator : Fin 6 → Fin 8 :=
  ![0, 1, 2, 3, 4, 6]

/-- Select the exact literal input word of a finite parabolic transition. -/
def y322D6A5Input (i : Fin 192) : List (Fin 8) :=
  match i.val / 128 with
  | 0 => y322D6A5Block00Input ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩
  | _ => y322D6A5Block01Input ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩

/-- Select the exact literal output word of a finite parabolic transition. -/
def y322D6A5Output (i : Fin 192) : List (Fin 8) :=
  match i.val / 128 with
  | 0 => y322D6A5Block00Output ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩
  | _ => y322D6A5Block01Output ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩

/-- Every selected transition coefficient has its actual original-source group equality. -/
theorem y322D6A5Value (i : Fin 192) :
    y322PositiveWord (y322D6A5Input i) = y322PositiveWord (y322D6A5Output i) := by
  have h : i.val / 128 = 0 ∨ i.val / 128 = 1 := by omega
  rcases h with h | h
  · simp only [y322D6A5Input, y322D6A5Output, h]
    exact y322D6A5Block00Value _
  · simp only [y322D6A5Input, y322D6A5Output, h]
    exact y322D6A5Block01Value _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- This checks exact word assembly, without assuming any reflection representation is faithful.
/-- Each finite input is exactly its actual representative-generator-target inverse word. -/
theorem y322D6A5Input_eq (i : Fin 32) (g : Fin 6) :
    y322D6A5Input (y322D6A5Index i g) =
      y322D6A5RepresentativeWord i ++ [y322D6A5Generator g] ++
        (y322D6A5RepresentativeWord (y322D6A5TargetData (y322D6A5Index i g))).reverse := by
  revert i g
  decide +kernel

/-- The base representative is literally the empty source word. -/
theorem y322D6A5RepresentativeWord_zero : y322D6A5RepresentativeWord 0 = [] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Literal source labels are checked before actual subgroup membership is derived.
/-- Every literal coefficient uses only its declared source parabolic generators. -/
theorem y322D6A5Coefficient_allowed (i : Fin 192) :
    ∀ v ∈ y322D6A5Output i, v.val < 5 := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Literal source labels are checked before actual subgroup membership is derived.
/-- Every literal representative uses only its declared source parabolic generators. -/
theorem y322D6A5Representative_allowed (i : Fin 32) :
    ∀ v ∈ y322D6A5RepresentativeWord i, v.val < 5 ∨ v.val = 6 := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
