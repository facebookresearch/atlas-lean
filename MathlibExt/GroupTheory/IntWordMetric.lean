/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Group.WordMetric

/-!
# The word metric of the infinite cyclic group

The infinite cyclic group `Multiplicative ℤ` with the generator `ofAdd 1` has word length
`|ofAdd n| = |n|`, so its word metric is the usual metric `|m - n|` of `ℤ`. This is the basic
infinite example for word metrics, growth and hyperbolicity of groups.

## Main definitions

* `Group.Generators.intGenerators`: the generating family `{ofAdd 1}` of `Multiplicative ℤ`.

## Main results

* `Group.Generators.wordLength_intGenerators`: `|ofAdd n| = |n|`.
-/

@[expose] public section

namespace Group.Generators

/-- **The standard generator of the infinite cyclic group.** The generating family of
`Multiplicative ℤ` consisting of the single element `ofAdd 1`. -/
def intGenerators : Generators (Multiplicative ℤ) Unit where
  val _ := Multiplicative.ofAdd 1
  closure_eq_top := by
    refine eq_top_iff.mpr fun g _ => ?_
    have hg : g = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd g) := by
      rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
    rw [hg]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self ())) _

private lemma abs_toAdd_wordProd_le (l : List (Unit × Bool)) :
    |Multiplicative.toAdd (intGenerators.wordProd l)| ≤ l.length := by
  induction l with
  | nil => simp [wordProd_nil]
  | cons a l ih =>
    obtain ⟨u, b⟩ := a
    rw [wordProd_cons, List.length_cons, toAdd_mul]
    push_cast
    have : |Multiplicative.toAdd (cond b (intGenerators.val u) (intGenerators.val u)⁻¹)| = 1 := by
      cases b <;> simp [intGenerators]
    calc _ ≤ |Multiplicative.toAdd (cond b (intGenerators.val u) (intGenerators.val u)⁻¹)| +
          |Multiplicative.toAdd (intGenerators.wordProd l)| := abs_add_le _ _
      _ ≤ _ := by rw [this]; linarith

private lemma wordLength_ofAdd_natCast_le (k : ℕ) :
    intGenerators.wordLength (Multiplicative.ofAdd (k : ℤ)) ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : intGenerators.wordLength (Multiplicative.ofAdd (1 : ℤ)) ≤ 1 := by
      simpa [intGenerators, wordProd_singleton] using
        intGenerators.wordLength_wordProd_le [((), true)]
    calc intGenerators.wordLength (Multiplicative.ofAdd ((k + 1 : ℕ) : ℤ))
        = intGenerators.wordLength (Multiplicative.ofAdd (k : ℤ) * Multiplicative.ofAdd 1) := by
          push_cast; rfl
      _ ≤ _ := intGenerators.wordLength_mul_le _ _
      _ ≤ k + 1 := by omega

/-- **Word length in the infinite cyclic group.** With respect to the generator `ofAdd 1`, the word
length of `ofAdd n` in `Multiplicative ℤ` is `|n|`. -/
theorem wordLength_intGenerators (n : ℤ) :
    intGenerators.wordLength (Multiplicative.ofAdd n) = n.natAbs := by
  apply le_antisymm
  · rcases Int.natAbs_eq n with h | h
    · calc _ = intGenerators.wordLength (Multiplicative.ofAdd (n.natAbs : ℤ)) := by rw [← h]
        _ ≤ _ := wordLength_ofAdd_natCast_le _
    · calc _ = intGenerators.wordLength (Multiplicative.ofAdd (n.natAbs : ℤ))⁻¹ := by
            rw [← ofAdd_neg, ← h]
        _ = _ := wordLength_inv _ _
        _ ≤ _ := wordLength_ofAdd_natCast_le _
  · obtain ⟨l, hl, he⟩ := intGenerators.exists_isGeodesic (Multiplicative.ofAdd n)
    have h := abs_toAdd_wordProd_le l
    rw [he, toAdd_ofAdd] at h
    rw [← he, show intGenerators.wordLength (intGenerators.wordProd l) = l.length from hl]
    have : (n.natAbs : ℤ) ≤ l.length := by rw [Int.natCast_natAbs]; exact h
    omega

end Group.Generators
