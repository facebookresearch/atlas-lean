/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GaussPrimitiveRoots
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Gauss's theorem on the primitive roots modulo `p^ℓ`

* The definitions on concrete residues: `unitReduceSq 5` sends `7` to
  `2`, so `7 ∈ P_2` modulo `25` and `8 ∉ P_2`; `ord_{25}(7) = 4`,
  `ord_5(2) = 4`, and `mulOrdMod` is `0` off the units.
* Theorem 2 and Corollary 1 at `p = 5`, `g = 2`: the exceptional
  shift is `m = 1`, since `2 + 1 · 5 = 7` has order `4` modulo `25`;
  every other shift, such as `17`, is a primitive root of `25`.
* Theorem 1 at `p = 3`, `g = 2` and `p = 7`, `g = 3`; Theorem 3 at
  `p = 7`, `g = 3`, `k = 1`; Lemmas 3 and 4 at `p = 7`.
* The lifting criterion at `p = 5`, `h = 2`: `2 ^ 4 = 16 ≢ 1` modulo
  `25`, so `2` is a primitive root of every `5^ℓ`, `ℓ ≥ 2`; and the
  failure at `p = 2`: `3` is not a primitive root of `8`.
-/

@[expose] public section

namespace MathlibExtTest.NumberTheory.GaussPrimitiveRoots

open MathlibExt.NumberTheory.GaussPrimitiveRoots

/-! ### The definitions on concrete residues -/

theorem unitReduceSq_seven :
    unitReduceSq 5 (ZMod.unitOfCoprime 7 (by norm_num)) =
      ZMod.unitOfCoprime 2 (by norm_num) := by
  decide

theorem seven_mem_liftFiber :
    ZMod.unitOfCoprime 7 (by norm_num) ∈
      liftFiber 5 (ZMod.unitOfCoprime 2 (by norm_num)) := by
  change unitReduceSq 5 _ = unitReduceSq 5 _
  decide

theorem eight_not_mem_liftFiber :
    ZMod.unitOfCoprime 8 (by norm_num) ∉
      liftFiber 5 (ZMod.unitOfCoprime 2 (by norm_num)) := by
  change ¬ unitReduceSq 5 _ = unitReduceSq 5 _
  decide

theorem orderOf_seven :
    orderOf (ZMod.unitOfCoprime 7 (by norm_num) : (ZMod (5 ^ 2))ˣ) = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)

theorem orderOf_two :
    orderOf (ZMod.unitOfCoprime 2 (by norm_num) : (ZMod 5)ˣ) = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)

theorem mulOrdMod_twentyFive_seven : mulOrdMod (5 ^ 2) 7 = 4 := by
  rw [mulOrdMod, dite_eq_left (by norm_num), orderOf_seven]

theorem mulOrdMod_five_two : mulOrdMod 5 2 = 4 := by
  rw [mulOrdMod, dite_eq_left (by norm_num), orderOf_two]

/-- Off the units, `mulOrdMod` is the junk value `0`. -/
theorem mulOrdMod_six_two : mulOrdMod 6 2 = 0 := by
  rw [mulOrdMod, dite_eq_right (by norm_num)]

/-! ### Primitive roots of `3`, `5` and `7` -/

theorem isPrimitiveRoot_two_three :
    IsPrimitiveRoot ((2 : ℕ) : ZMod 3) (Nat.totient 3) := by
  rw [Nat.totient_prime (by norm_num)]
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by decide) ?_
  intro l hl0 hl
  interval_cases l
  decide

theorem isPrimitiveRoot_two_five :
    IsPrimitiveRoot ((2 : ℕ) : ZMod 5) (Nat.totient 5) := by
  rw [Nat.totient_prime (by norm_num)]
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by decide) ?_
  intro l hl0 hl
  interval_cases l <;> decide

theorem isPrimitiveRoot_three_seven :
    IsPrimitiveRoot ((3 : ℕ) : ZMod 7) (Nat.totient 7) := by
  rw [Nat.totient_prime (by norm_num)]
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by decide) ?_
  intro l hl0 hl
  interval_cases l <;> decide

/-! ### Lemma 1 and Theorem 2 at `p = 5`, `a = 2` -/

/-- Lemma 1 at `p = 5`, `a = 2`, `k = 3`. -/
example : mulOrdMod (5 ^ 2) 17 = 4 ∨ mulOrdMod (5 ^ 2) 17 = 20 := by
  have h := order_add_mul_prime_eq_or_mul 5 (by norm_num) (by norm_num) 2 3
    (by norm_num)
  rwa [mulOrdMod_five_two] at h

/-- The shift of Theorem 2 for `a = 2` modulo `5` is `m = 1`. -/
example (m : ZMod 5) (hm : mulOrdMod (5 ^ 2) (2 + m.val * 5) = mulOrdMod 5 2) :
    m = 1 := by
  obtain ⟨m₀, -, huniq⟩ :=
    existsUnique_order_add_mul_prime_eq 5 (by norm_num) (by norm_num) 2
      (by norm_num)
  have h1 : mulOrdMod (5 ^ 2) (2 + (1 : ZMod 5).val * 5) = mulOrdMod 5 2 :=
    mulOrdMod_twentyFive_seven.trans mulOrdMod_five_two.symm
  rw [huniq m hm, huniq 1 h1]

/-- The fiber form of Theorem 2 picks out `7` in `P_2` modulo `25`. -/
example (x : (ZMod (5 ^ 2))ˣ)
    (hx : x ∈ liftFiber 5 (ZMod.unitOfCoprime 2 (by norm_num)) ∧
      orderOf x = orderOf (unitReduceSq 5 x)) :
    x = ZMod.unitOfCoprime 7 (by norm_num) := by
  obtain ⟨x₀, -, huniq⟩ := existsUnique_mem_liftFiber_order_eq 5 (by norm_num)
    (by norm_num) (ZMod.unitOfCoprime 2 (by norm_num))
  refine (huniq x hx).trans (huniq _ ⟨seven_mem_liftFiber, ?_⟩).symm
  rw [unitReduceSq_seven, orderOf_seven, orderOf_two]

/-! ### Corollary 1 at `p = 5`, `g = 2` -/

/-- `7 = 2 + 1 · 5` is not a primitive root of `25`: `7 ^ 4 ≡ 1`. -/
theorem not_isPrimitiveRoot_seven :
    ¬ IsPrimitiveRoot (((2 + (1 : ZMod 5).val * 5 : ℕ) : ZMod (5 ^ 2)))
      (Nat.totient (5 ^ 2)) := fun h => by
  have h4 : ((2 + (1 : ZMod 5).val * 5 : ℕ) : ZMod (5 ^ 2)) ^ 4 = 1 := by
    decide
  exact absurd ((h.pow_eq_one_iff_dvd 4).mp h4) (by decide)

/-- Every shift `2 + k · 5` with `k ≠ 1` is a primitive root of `25`,
and `k = 1` is the unique exceptional shift of Corollary 1. -/
theorem isPrimitiveRoot_two_add_mul_five (k : ZMod 5) :
    IsPrimitiveRoot (((2 + k.val * 5 : ℕ) : ZMod (5 ^ 2)))
      (Nat.totient (5 ^ 2)) ↔ k ≠ 1 := by
  obtain ⟨m₀, ⟨-, hprim⟩, -⟩ :=
    existsUnique_not_primitiveRoot_add_mul_prime 5 (by norm_num) (by norm_num)
      2 isPrimitiveRoot_two_five
  have hm₀ : m₀ = 1 :=
    by_contra fun h => not_isPrimitiveRoot_seven (hprim 1 (Ne.symm h))
  subst hm₀
  exact ⟨fun h hk => not_isPrimitiveRoot_seven (hk ▸ h), hprim k⟩

/-- `17 = 2 + 3 · 5` is a primitive root of `25`. -/
example : IsPrimitiveRoot (((2 + (3 : ZMod 5).val * 5 : ℕ) : ZMod (5 ^ 2)))
    (Nat.totient (5 ^ 2)) :=
  (isPrimitiveRoot_two_add_mul_five 3).mpr (by decide)

/-- The fiber form of Corollary 1 at `p = 5`, `g = 2`. -/
example : ∃! x, x ∈ liftFiber 5 (ZMod.unitOfCoprime 2 (by norm_num)) ∧
    orderOf x = 5 - 1 :=
  existsUnique_mem_liftFiber_order_eq_sub_one 5 (by norm_num) (by norm_num) 2
    isPrimitiveRoot_two_five

/-! ### Theorems 1 and 3 -/

/-- Theorem 1 at `p = 3`, `g = 2`. -/
example : ∃ k : ℕ, ∀ ℓ : ℕ, 2 ≤ ℓ →
    IsPrimitiveRoot (((2 + k * 3 : ℕ) : ZMod (3 ^ ℓ))) (Nat.totient (3 ^ ℓ)) :=
  exists_primitiveRoot_add_mul_prime_pow 3 (by norm_num) (by norm_num) 2
    isPrimitiveRoot_two_three

/-- Theorem 1 at `p = 7`, `g = 3`. -/
example : ∃ k : ℕ, ∀ ℓ : ℕ, 2 ≤ ℓ →
    IsPrimitiveRoot (((3 + k * 7 : ℕ) : ZMod (7 ^ ℓ))) (Nat.totient (7 ^ ℓ)) :=
  exists_primitiveRoot_add_mul_prime_pow 7 (by norm_num) (by norm_num) 3
    isPrimitiveRoot_three_seven

/-- Theorem 3 at `p = 7`, `g = 3`, `k = 1`, `ℓ = 3`: `3^7 + 7` is a
primitive root of `343`. -/
example : IsPrimitiveRoot (((3 ^ 7 + 1 * 7 : ℕ) : ZMod (7 ^ 3)))
    (Nat.totient (7 ^ 3)) :=
  primitiveRoot_pow_add_mul_prime_pow 7 (by norm_num) (by norm_num) 3 1
    isPrimitiveRoot_three_seven (by norm_num) 3 (by norm_num)

/-! ### The lifting criterion at `p = 5`, `h = 2` -/

/-- `2 ^ 4 = 16 ≢ 1 (mod 25)`, so `2` is a primitive root of every
`5^ℓ` with `ℓ ≥ 2`. -/
example (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    IsPrimitiveRoot ((2 : ℕ) : ZMod (5 ^ ℓ)) (Nat.totient (5 ^ ℓ)) :=
  isPrimitiveRoot_prime_pow 5 (by norm_num) (by norm_num) 2
    isPrimitiveRoot_two_five (by decide) ℓ hℓ

/-- The hypothesis `p ≠ 2` cannot be dropped: `3` satisfies the other
hypotheses at `p = 2`, but `3 ^ 2 = 1` modulo `8`, so `3` is not a
primitive root of `8`. -/
example : ¬ IsPrimitiveRoot ((3 : ℕ) : ZMod 8) (Nat.totient 8) := by
  intro h
  have h2 := h.dvd_of_pow_eq_one 2 (by decide)
  rw [show Nat.totient 8 = 4 by decide] at h2
  omega

/-! ### Lemmas 3 and 4 at `p = 7` -/

/-- Lemma 3 for the squaring map modulo `49`. -/
example (a : (ZMod (7 ^ 2))ˣ) :
    powMonoidHom 2 '' liftFiber 7 a ⊆ liftFiber 7 (a ^ 2) :=
  monoidHom_image_liftFiber_subset 7 (by norm_num) (by norm_num)
    (powMonoidHom 2) a

/-- Lemma 4 for `n = 5` modulo `49`: `5` is coprime to `7` and to every
order dividing `φ(49) = 42`. -/
example (a : (ZMod (7 ^ 2))ˣ) :
    Set.InjOn (fun x => x ^ 5) (liftFiber 7 a) ∧
      (fun x => x ^ 5) '' liftFiber 7 a = liftFiber 7 (a ^ 5) ∧
      ∀ b ∈ liftFiber 7 a, orderOf (b ^ 5) = orderOf b := by
  have hcard : Fintype.card (ZMod (7 ^ 2))ˣ = 42 := by
    rw [ZMod.card_units_eq_totient]
    decide
  exact pow_injectiveOn_liftFiber_and_order_eq 7 (by norm_num) (by norm_num) a 5
    (by norm_num) (Nat.Coprime.coprime_dvd_right (hcard ▸ orderOf_dvd_card)
      (by norm_num))

/-! ### Axioms -/

#print axioms order_add_mul_prime_eq_or_mul
#print axioms existsUnique_order_add_mul_prime_eq
#print axioms existsUnique_mem_liftFiber_order_eq
#print axioms exists_primitiveRoot_add_mul_prime_pow
#print axioms existsUnique_not_primitiveRoot_add_mul_prime
#print axioms existsUnique_mem_liftFiber_order_eq_sub_one
#print axioms primitiveRoot_pow_add_mul_prime_pow
#print axioms monoidHom_image_liftFiber_subset
#print axioms pow_injectiveOn_liftFiber_and_order_eq
#print axioms isPrimitiveRoot_prime_pow

end MathlibExtTest.NumberTheory.GaussPrimitiveRoots
