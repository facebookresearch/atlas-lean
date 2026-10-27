/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The sum of the primitive roots of unity

The primitive `n`-th roots of unity in a domain that contains one sum to the Möbius function
`μ n`. Equivalently, the coefficient of `X ^ (φ n - 1)` in the `n`-th cyclotomic polynomial is
`-μ n`, over any ring.

## Main statements

* `IsPrimitiveRoot.sum_nthRootsFinset_one`: the `n`-th roots of unity sum to `0` for `n > 1`
* `IsPrimitiveRoot.sum_primitiveRoots`: `∑ ζ ∈ primitiveRoots n R, ζ = μ n`
* `Polynomial.cyclotomic_coeff_totient_sub_one`: `(cyclotomic n R).coeff (φ n - 1) = -μ n`
-/

@[expose] public section

open Finset Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace IsPrimitiveRoot

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The `n`-th roots of unity in a domain sum to zero when `n > 1` and a primitive `n`-th root of
unity exists. -/
theorem sum_nthRootsFinset_one {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) :
    ∑ x ∈ nthRootsFinset n (1 : R), x = 0 := by
  classical
  have himage : (range n).image (ζ ^ ·) = nthRootsFinset n (1 : R) := by
    refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := mem_image.mp hx
      rw [Polynomial.mem_nthRootsFinset (by omega), ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one,
        one_pow]
    · rw [hζ.card_nthRootsFinset, card_image_of_injOn (fun i hi j hj h => hζ.pow_inj
        (mem_range.mp hi) (mem_range.mp hj) h), card_range]
  rw [← himage, sum_image (fun i hi j hj h => hζ.pow_inj (mem_range.mp hi) (mem_range.mp hj) h),
    hζ.geom_sum_eq_zero hn]

/-- Summing the sums of primitive `d`-th roots of unity over `d ∣ n` gives the sum of all
`n`-th roots of unity, which is `1` for `n = 1` and `0` otherwise. -/
theorem sum_divisors_sum_primitiveRoots {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) :
    ∑ d ∈ n.divisors, ∑ x ∈ primitiveRoots d R, x = if n = 1 then 1 else 0 := by
  classical
  split_ifs with h1
  · subst h1
    simp
  rw [← sum_biUnion (fun i _ j _ hij => IsPrimitiveRoot.disjoint hij),
    ← nthRoots_one_eq_biUnion_primitiveRoots]
  exact hζ.sum_nthRootsFinset_one (by omega)

/-- The primitive `n`-th roots of unity in a domain containing one sum to the Möbius function
`μ n`. -/
theorem sum_primitiveRoots {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) :
    ∑ x ∈ primitiveRoots n R, x = μ n := by
  have key := (sum_eq_iff_sum_mul_moebius_eq_on (R := R)
    (f := fun d => ∑ x ∈ primitiveRoots d R, x) (g := fun k => if k = 1 then 1 else 0)
    {k | k ∣ n} (fun a b hab hb => dvd_trans hab hb)).mp (by
      intro k hk hkn
      obtain ⟨m, hm⟩ := hkn
      have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
      have := hζ.pow_of_dvd hm0 (Dvd.intro_left k hm.symm)
      rw [hm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)] at this
      exact this.sum_divisors_sum_primitiveRoots hk) n hn (dvd_refl n)
  rw [← key, sum_eq_single (n, 1)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    have hb : b ≠ 1 := by rintro rfl; rw [mul_one] at hab; exact hne (Prod.ext hab rfl)
    simp [hb]
  · intro h; exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, hn.ne'⟩) h

end IsPrimitiveRoot

namespace Polynomial

/-- The coefficient of `X ^ (φ n - 1)` in the `n`-th cyclotomic polynomial is `-μ n`. -/
theorem cyclotomic_coeff_totient_sub_one (R : Type*) [Ring R] {n : ℕ} (hn : 0 < n) :
    (cyclotomic n R).coeff (n.totient - 1) = -μ n := by
  suffices hZ : (cyclotomic n ℤ).coeff (n.totient - 1) = -μ n by
    rw [← map_cyclotomic_int, coeff_map, hZ]
    simp
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  apply (Int.cast_injective (α := ℂ))
  rw [show (((cyclotomic n ℤ).coeff (n.totient - 1) : ℤ) : ℂ) =
      ((cyclotomic n ℤ).map (Int.castRingHom ℂ)).coeff (n.totient - 1) by
      rw [coeff_map]; rfl,
    map_cyclotomic_int]
  have hdeg : (cyclotomic n ℂ).natDegree = n.totient := natDegree_cyclotomic n ℂ
  have hpos : 0 < (cyclotomic n ℂ).natDegree := hdeg ▸ Nat.totient_pos.mpr hn
  rw [← hdeg, ← nextCoeff_of_natDegree_pos hpos, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
    prod_X_sub_C_nextCoeff (fun x => x), hζ.sum_primitiveRoots hn]
  push_cast
  rfl

end Polynomial
