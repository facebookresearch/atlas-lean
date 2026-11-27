/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.GameTheory.ChocolateBarNSProperty
import MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtFoldlXor

open MetaMathlibExt

-- For the constant-one function the threshold supplied by the theorem must be zero.
example : ∃ m : ℕ, m = 0 ∧ (fun _ : ℕ ↦ 1) = (Set.Ici m).indicator (1 : ℕ → ℕ) := by
  obtain ⟨m, _, hm⟩ := (indicator_Ici_even_iff_hasNSProperty monotone_const
    (fun _ ↦ le_rfl) ⟨0, rfl⟩).mpr (hasNSProperty_const 1)
  refine ⟨m, ?_, hm⟩
  by_contra hn
  simpa [Set.indicator, hn] using congrFun hm 0

-- A positive even threshold gives a nonconstant function with the NS property.
example : HasNSProperty (fun z : ℕ ↦ if 4 ≤ z then 1 else 0) := by
  have hmono : Monotone (fun z : ℕ ↦ if 4 ≤ z then 1 else 0) := by
    intro a b hab
    dsimp only
    split_ifs <;> omega
  apply (indicator_Ici_even_iff_hasNSProperty hmono (fun z ↦ by split_ifs <;> decide)
    ⟨4, rfl⟩).mp
  exact ⟨4, ⟨2, rfl⟩, by funext z; simp [Set.indicator]⟩

-- The odd threshold three separates two inputs in the same block of length two.
example : ¬ HasNSProperty ((Set.Ici 3).indicator (1 : ℕ → ℕ)) := by
  intro hns
  have hpair := hns.2 2 3 1 (by decide) (by decide)
  simp [Set.indicator] at hpair

-- Inputs in the same block of eight have quotients by four in the same block of four.
example {a b : ℕ} (h : a / 8 = b / 8) : a / 4 / 4 = b / 4 / 4 :=
  (hasNSProperty_div_two_pow (m := 2) (by decide)).2 a b 3 (by decide) h

-- Exponent zero gives the identity, so positivity of the exponent is necessary.
example : ¬ HasNSProperty (fun x : ℕ ↦ x / 2 ^ 0) := by
  intro h
  have hpair := h.2 0 1 1 (by decide) rfl
  exact absurd hpair (by decide)

-- At cutoff zero, every function qualifies regardless of its values at positive inputs.
example (h : ℕ → ℕ) : HasNSProperty (fun x ↦ if x ≤ 0 then h x else h 0) := by
  apply hasNSProperty_extend_const
  · intro a b hab hb
    have : a = b := by omega
    simp [this]
  · intro a b i ha hb _ _
    simp [Nat.le_zero.mp ha, Nat.le_zero.mp hb]

-- The dyadic block {2, 3} straddles the cutoff of this nonconstant extension.
example : HasNSProperty (fun x : ℕ ↦ if x ≤ 2 then x / 2 else 1) := by
  have hh := hasNSProperty_div_two_pow (m := 1) (by decide)
  exact hasNSProperty_extend_const 2 (fun x ↦ x / 2)
    (fun _ _ hab _ ↦ hh.1 hab) (fun a b i _ _ ↦ hh.2 a b i)

-- The cutoff nine lies strictly between the two values of the halving function.
example : min (23 / 2) 9 / 4 = min (16 / 2) 9 / 4 :=
  (hasNSProperty_div_two_pow (m := 1) (by decide)).min_div_two_pow_eq
    (z := 16) (z' := 23) (k := 3) (by decide) (by decide) 9

-- At k = 1 the output divisor is one, so the truncated values themselves agree.
example {h : ℕ → ℕ} (hh : HasNSProperty h) {z z' : ℕ} (hz : z' / 2 = z / 2) (y : ℕ) :
    min (h z') y = min (h z) y := by
  simpa only [Nat.sub_self, pow_zero, Nat.div_one] using
    hh.min_div_two_pow_eq (k := 1) Nat.one_pos hz y

-- At width three, clamping the first coordinate swaps the witnesses zero and one.
example : {c : ℕ | ∃ w < 3, c = 3 ^^^ w} =
    {c | ∃ w < 3, c = min 1 (w / 2) ^^^ 2 ^^^ w} := by
  let f : Fin 2 → ℕ → ℕ := ![fun w ↦ w / 2, fun _ ↦ 2]
  have hf : ∀ t, HasNSProperty (f t) := Fin.forall_fin_two.mpr
    ⟨hasNSProperty_div_two_pow (m := 1) (by decide), hasNSProperty_const 2⟩
  have hx : ∀ t, (![1, 2] : Fin 2 → ℕ) t ≤ f t 3 := by decide
  simpa [f, List.ofFn_succ] using image_foldl_xor_eq_image_min hf hx

-- The target three requires a coordinate move; neither smaller width attains it.
example :
    ∃ i, ∃ u < (![1, 4] : Fin 2 → ℕ) i,
      3 = (List.ofFn (Function.update ![1, 4] i u)).foldl (· ^^^ ·) 0 ^^^ 2 := by
  obtain h | ⟨w, hw, he⟩ := exists_of_lt_foldl_xor (f := fun _ _ ↦ 4)
    (x := ![1, 4]) (z := 2) (c := 3) (fun _ ↦ hasNSProperty_const 4) (by decide) (by decide)
  · exact h
  · obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
    all_goals revert he; decide

-- At width zero, the remaining coordinate is clamped. Lowering only the coordinate gives two.
example : ∃ w < 2, 0 = min 1 (w / 2) ^^^ w := by
  obtain ⟨i, u, hu, he⟩ | h := exists_of_lt_foldl_xor
    (f := fun _ : Fin 1 ↦ fun w ↦ w / 2) (x := ![1]) (z := 2) (c := 0)
    (fun _ ↦ hasNSProperty_div_two_pow (m := 1) (by decide)) (by decide) (by decide)
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hu0 : u = 0 := by simpa using hu
    subst u
    revert he
    decide
  · simpa [List.ofFn_succ] using h

-- With no coordinates, any smaller target is attained by a width move.
example {c z : ℕ} (hc : c < z) : ∃ w < z, c = w := by
  obtain ⟨i, _⟩ | h := exists_of_lt_foldl_xor (m := 0) (f := fun i ↦ i.elim0)
    (x := fun i ↦ i.elim0) (z := z) (c := c) (fun i ↦ i.elim0) (fun i ↦ i.elim0)
    (by simpa using hc)
  · exact i.elim0
  · simpa using h
