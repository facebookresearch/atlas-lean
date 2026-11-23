/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.KaprekarProjectiveDoubling
import Mathlib.Tactic.IntervalCases

open MetaMathlibExt

/-! ## The projective order of 2 -/

-- `2 ≡ -1 (mod 3)`, so `λ(3) = 1`.
example : projectiveOrderTwo 3 = 1 :=
  projectiveOrderTwo_eq_of (by omega) (by decide) (by decide)

-- `2 ^ 2 = 4 ≡ -1 (mod 5)`, so `λ(5) = 2`.
example : projectiveOrderTwo 5 = 2 :=
  projectiveOrderTwo_eq_of (by omega) (by decide) (by decide)

-- Modulo `15`, the first power of `2` that is `±1` is `2 ^ 4 = 16 ≡ 1`.
example : projectiveOrderTwo 15 = 4 :=
  projectiveOrderTwo_eq_of (by omega) (by decide) (by decide)

-- Modulo the even number `2` no power `2 ^ m` with `m > 0` is `±1`, so `λ(2)` is the junk
-- value `0`.
example : projectiveOrderTwo 2 = 0 := by
  rw [projectiveOrderTwo, Nat.sInf_eq_zero]
  refine Or.inr (Set.eq_empty_of_forall_notMem fun m ⟨hm, h⟩ => ?_)
  rw [show (2 : ZMod 2) = 0 from rfl, zero_pow hm.ne'] at h
  revert h
  decide

/-! ## Doubling on pairs of projective classes -/

-- In base `11`, where `λ(11) = 5`, every pair of distinct nonzero projective classes returns to
-- itself after at most five doublings.
example (S : Finset (Finset (ZMod 11)))
    (hS : S.card = 2 ∧ ∀ C ∈ S, ∃ x : ZMod 11, x ≠ 0 ∧ C = {x, -x}) :
    Function.minimalPeriod
      (fun T : Finset (Finset (ZMod 11)) => T.image fun C => C.image (· * 2)) S ≤ 5 :=
  projectiveOrderTwo_examples.2.2.1 ▸
    (projective_doubling_minimalPeriod_le_projectiveOrderTwo 11 (by decide) (by omega) S hS).2

-- In base `7`, the pair `{[1], [3]}` runs through `{[2], [1]}` and `{[3], [2]}` before it
-- returns, so its minimal period is exactly `λ(7) = 3`: the bound is attained.
example :
    Function.minimalPeriod
      (fun T : Finset (Finset (ZMod 7)) => T.image fun C => C.image (· * 2))
      {{1, -1}, {3, -3}} = 3 := by
  have hS : ({{1, -1}, {3, -3}} : Finset (Finset (ZMod 7))).card = 2 ∧
      ∀ C ∈ ({{1, -1}, {3, -3}} : Finset (Finset (ZMod 7))),
        ∃ x : ZMod 7, x ≠ 0 ∧ C = {x, -x} := by
    refine ⟨by decide, fun C hC => ?_⟩
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨3, by decide, (Finset.mem_singleton.mp hC)⟩
  obtain ⟨hpos, hle⟩ :=
    projective_doubling_minimalPeriod_le_projectiveOrderTwo 7 (by decide) (by omega) _ hS
  rw [projectiveOrderTwo_examples.1] at hle
  have hiter := Function.iterate_minimalPeriod
    (f := fun T : Finset (Finset (ZMod 7)) => T.image fun C => C.image (· * 2))
    (x := {{1, -1}, {3, -3}})
  interval_cases h : Function.minimalPeriod
      (fun T : Finset (Finset (ZMod 7)) => T.image fun C => C.image (· * 2))
      {{1, -1}, {3, -3}}
  · revert hiter
    decide
  · revert hiter
    decide
  · rfl

-- Classes of non-units take part too: in base `9`, doubling fixes `[3] = {3, 6}`, and the pair
-- `{[1], [3]}` returns to itself after `λ(9) = 3` doublings.
example :
    ({3, -3} : Finset (ZMod 9)).image (· * 2) = {3, -3} ∧
      (fun T : Finset (Finset (ZMod 9)) => T.image fun C => C.image (· * 2))^[3]
        {{1, -1}, {3, -3}} = {{1, -1}, {3, -3}} := by
  decide
