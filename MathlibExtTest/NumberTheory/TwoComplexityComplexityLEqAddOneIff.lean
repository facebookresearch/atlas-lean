/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoComplexityComplexityLEqAddOneIff

open MathlibExt.NumberTheory.TwoComplexityWanted

-- Enumerate values obtainable with exactly k copies of 2 by splitting k at the root.
-- The fuel decreases at each split, and fuel at least k suffices.
private def buildValues : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, k =>
    if k = 1 then [2] else
      (List.range k).flatMap fun a =>
        (buildValues fuel a).flatMap fun x =>
          (buildValues fuel (k - a)).flatMap fun y => [x + y, x * y]

private theorem mem_buildValues {k n fuel : ℕ} (h : CanBuild 2 k n) (hf : k ≤ fuel) :
    n ∈ buildValues fuel k := by
  induction h generalizing fuel with
  | base =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [buildValues]
  | @add a b x y hx hy ihx ihy | @mul a b x y hx hy ihx ihy =>
    have ha := hx.one_le
    have hb := hy.one_le
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [buildValues, ite_eq_right (by omega : a + b ≠ 1)]
    refine List.mem_flatMap.mpr ⟨a, List.mem_range.mpr (by omega), ?_⟩
    rw [Nat.add_sub_cancel_left]
    refine List.mem_flatMap.mpr ⟨x, ihx (by omega), ?_⟩
    exact List.mem_flatMap.mpr ⟨y, ihy (by omega), by simp⟩

private theorem complexity_eq_of_enumeration {n k : ℕ} (h : CanBuild 2 k n)
    (hsmall : ∀ i : Fin k, n ∉ buildValues k i.val) : complexityL 2 n = k := by
  refine le_antisymm (complexityL_min_le h) ?_
  by_contra! hlt
  exact hsmall ⟨_, hlt⟩ (mem_buildValues (complexityL_spec ⟨k, h⟩) hlt.le)

private theorem buildFour : CanBuild 2 2 4 := CanBuild.base.mul CanBuild.base

private theorem buildSixteen : CanBuild 2 4 16 := buildFour.mul buildFour

-- Independent checks at m = 4: an interior two-power sum and the equal-exponent endpoint.
example : complexityL 2 18 = 5 ∧ (∃ t : ℕ, 1 ≤ t ∧ t ≤ 4 ∧ 18 = 2 ^ 4 + 2 ^ t) :=
  ⟨complexity_eq_of_enumeration (buildSixteen.add CanBuild.base) (by decide),
    ⟨1, by decide, by decide, by decide⟩⟩

example : complexityL 2 32 = 5 ∧ (∃ t : ℕ, 1 ≤ t ∧ t ≤ 4 ∧ 32 = 2 ^ 4 + 2 ^ t) :=
  ⟨complexity_eq_of_enumeration (buildSixteen.mul CanBuild.base) (by decide),
    ⟨4, by decide, by decide, by decide⟩⟩

-- 28 is in the same interval, but the six-copy build is minimal and no exponent works.
example : complexityL 2 28 = 6 ∧ (¬ ∃ t : ℕ, 1 ≤ t ∧ t ≤ 4 ∧ 28 = 2 ^ 4 + 2 ^ t) := by
  have h6 : CanBuild 2 3 6 := buildFour.add CanBuild.base
  have h28 : CanBuild 2 6 28 := ((h6.mul CanBuild.base).add CanBuild.base).mul CanBuild.base
  refine ⟨complexity_eq_of_enumeration h28 (by decide), ?_⟩
  rintro ⟨t, -, ht, he⟩
  have hnone : ∀ i : Fin 5, 28 ≠ 2 ^ 4 + 2 ^ i.val := by decide
  exact hnone ⟨t, by omega⟩ he

-- A client can recover the endpoint witness from the public classification.
example (h : complexityL 2 32 = 5) : ∃ t : ℕ, 1 ≤ t ∧ t ≤ 4 ∧ 32 = 2 ^ 4 + 2 ^ t :=
  (complexityL_eq_add_one_iff 4 32 (by decide) (by decide) (by decide) (by decide)).mp h
