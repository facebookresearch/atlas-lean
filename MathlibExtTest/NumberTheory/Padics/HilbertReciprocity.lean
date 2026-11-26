/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Padics.HilbertReciprocity
import MathlibExt.NumberTheory.Padics.TernaryIsotropic

open IsDedekindDomain NumberField

namespace HilbertReciprocityTest

/-- Consumer with the original binders and hypotheses. -/
theorem exactSource
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      (∀ v, v ∈ S ↔
        ¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
          z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2
            - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0) ∧
      Even (S.card + if (a < 0 ∧ b < 0) then 1 else 0) :=
  Rat.hilbertReciprocity_even_card_not_ternary_isotropic a b ha hb

/-- For `a = b = -1` the witness set is exactly the place over `2`: each odd place is
isotropic (`Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two`), and the sign term makes
the count odd, so the set is not empty. -/
example : ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
    (∀ v, v ∈ S ↔
      ¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) (-1)) * x ^ 2
          - (algebraMap ℚ (v.adicCompletion ℚ) (-1)) * y ^ 2 = 0) ∧
      S.card = 1 ∧ ∀ v ∈ S, (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = 2 := by
  obtain ⟨S, hS, hEven⟩ := exactSource (-1) (-1) (by norm_num) (by norm_num)
  have hsub : ∀ v ∈ S, (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = 2 := by
    intro v hv
    by_contra hq2
    apply (hS v).mp hv
    have : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
    obtain ⟨z, x, y, hnt, h⟩ :=
      Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two _ hq2 (-1) (-1) (by simp) (by simp)
    let e := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
    refine ⟨e z, e x, e y, fun ⟨hz, hx, hy⟩ ↦ hnt ⟨by simpa using hz, by simpa using hx,
      by simpa using hy⟩, ?_⟩
    have he := congrArg e h
    simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_zero] at he
    simp only [map_neg, map_one]
    linear_combination he
  have hle : S.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦
    Rat.HeightOneSpectrum.primesEquiv.injective
      (Nat.Primes.coe_nat_injective ((hsub a ha).trans (hsub b hb).symm))
  have hodd : ¬ Even S.card := by simpa [Nat.even_add_one] using hEven
  refine ⟨S, hS, le_antisymm hle (Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hodd ?_), hsub⟩
  rw [h0]
  exact ⟨0, rfl⟩

end HilbertReciprocityTest
