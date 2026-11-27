/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.WittVector.Isocrystal
public import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-!
# The `p`-adic valuation on the fraction field of Witt vectors

Let `p` be a prime and let `k` be a perfect field of characteristic `p`. The ring `𝕎 k` of
`p`-typical Witt vectors over `k` is a discrete valuation ring in which `p` is irreducible
(`WittVector.isDiscreteValuationRing`, `WittVector.irreducible`). This file extends its additive
valuation `IsDiscreteValuationRing.addVal` to the field of fractions `K(p, k)` of `𝕎 k`. The
result is the `p`-adic additive valuation `WittVector.FractionRing.addValuation p k` of `K(p, k)`:
it takes values in `WithTop ℤ`, it is normalized by `v p = 1` as in Fontaine–Ouyang, §8.2.2,
and it is invariant under the Frobenius automorphism `φ(p, k)` of `K(p, k)`.

## Main declarations

* `WittVector.FractionRing.addValuation`: the `p`-adic additive valuation of `K(p, k)`.
* `WittVector.FractionRing.addValuation_p`: its value at `p` is `1`.
* `WittVector.FractionRing.addValuation_p_zpow_mul_unit`: its value at `p ^ m * u` is `m`, for an
  integer `m` and a unit `u` of `𝕎 k`.
* `WittVector.FractionRing.addValuation_frobenius`: it is invariant under `φ(p, k)`.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.2.
-/

@[expose] public section

open scoped Isocrystal

namespace WittVector

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

local notation "𝕎" => WittVector p

/-- The `p`-adic additive valuation of the field of fractions `K(p, k)` of the Witt vectors
`𝕎 k`, for a prime `p` and a perfect field `k` of characteristic `p`. It is the extension to
`K(p, k)` of the additive valuation `IsDiscreteValuationRing.addVal (𝕎 k)` of the discrete
valuation ring `𝕎 k`, read in `WithTop ℤ` through the order embedding `ℕ∞ → WithTop ℤ`
(`WittVector.FractionRing.addValuation_algebraMap`), and it is normalized by `v p = 1`
(`WittVector.FractionRing.addValuation_p`). -/
noncomputable def FractionRing.addValuation : AddValuation K(p, k) (WithTop ℤ) :=
  AddValuation.ofValuation <|
    (AddValuation.toValuation <| (IsDiscreteValuationRing.addVal (𝕎 k)).map
        ⟨⟨⟨ENat.map ((↑) : ℕ → ℤ), by simp⟩, fun a b ↦ by
            simpa using ENat.map_add (Nat.castAddMonoidHom ℤ) a b⟩,
          ENat.monotone_map_iff.2 Nat.mono_cast⟩
        (ENat.map_top ((↑) : ℕ → ℤ))).extendToLocalization
      (S := nonZeroDivisors (𝕎 k))
      (fun x hx ↦ Ideal.mem_primeCompl_iff.2 fun hx' ↦ nonZeroDivisors.ne_zero hx <|
        IsDiscreteValuationRing.addVal_eq_top_iff.1 <|
          (ENat.map_eq_top_iff (f := ((↑) : ℕ → ℤ))).1 hx')
      K(p, k)

/-! ### Values on Witt vectors and on powers of `p` -/

/-- For a prime `p`, a perfect field `k` of characteristic `p` and a Witt vector `x : 𝕎 k`, the
`p`-adic additive valuation of the image of `x` in `K(p, k)` is the additive valuation
`IsDiscreteValuationRing.addVal (𝕎 k) x : ℕ∞` of `x` in the discrete valuation ring `𝕎 k`,
mapped to `WithTop ℤ` by `ENat.map` of the cast `ℕ → ℤ`. -/
theorem FractionRing.addValuation_algebraMap (x : 𝕎 k) :
    FractionRing.addValuation p k (algebraMap (𝕎 k) K(p, k) x) =
      (IsDiscreteValuationRing.addVal (𝕎 k) x).map ((↑) : ℕ → ℤ) := by
  rw [FractionRing.addValuation, AddValuation.ofValuation_apply,
    Valuation.extendToLocalization_apply_map_apply, AddValuation.toValuation_apply,
    AddValuation.map_apply]
  rfl

/-- For a prime `p`, a perfect field `k` of characteristic `p` and a Witt vector `x : 𝕎 k`, the
`p`-adic additive valuation of the image of `x` in `K(p, k)` is nonnegative. -/
theorem FractionRing.addValuation_algebraMap_nonneg (x : 𝕎 k) :
    0 ≤ FractionRing.addValuation p k (algebraMap (𝕎 k) K(p, k) x) := by
  rw [FractionRing.addValuation_algebraMap]
  induction IsDiscreteValuationRing.addVal (𝕎 k) x using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- For a prime `p`, a perfect field `k` of characteristic `p` and a unit `u` of `𝕎 k`, the
`p`-adic additive valuation of the image of `u` in `K(p, k)` is `0`. -/
@[simp]
theorem FractionRing.addValuation_algebraMap_unit (u : (𝕎 k)ˣ) :
    FractionRing.addValuation p k (algebraMap (𝕎 k) K(p, k) u) = 0 := by
  rw [FractionRing.addValuation_algebraMap, IsDiscreteValuationRing.addVal_eq_zero_of_unit]
  simp

/-- For a prime `p`, a perfect field `k` of characteristic `p` and `x : K(p, k)`, the `p`-adic
additive valuation of `x` is `⊤` if and only if `x = 0`. -/
theorem FractionRing.addValuation_eq_top_iff {x : K(p, k)} :
    FractionRing.addValuation p k x = ⊤ ↔ x = 0 :=
  AddValuation.top_iff _

/-- For a prime `p` and a perfect field `k` of characteristic `p`, the `p`-adic additive
valuation of `K(p, k)` takes the value `1` at `p`. -/
@[simp]
theorem FractionRing.addValuation_p : FractionRing.addValuation p k (p : K(p, k)) = 1 := by
  rw [← map_natCast (algebraMap (𝕎 k) K(p, k)), FractionRing.addValuation_algebraMap,
    IsDiscreteValuationRing.addVal_uniformizer (irreducible p)]
  simp

/-- For a prime `p`, a perfect field `k` of characteristic `p` and a natural number `n`, the
`p`-adic additive valuation of `K(p, k)` takes the value `n` at `p ^ n`. -/
theorem FractionRing.addValuation_p_pow (n : ℕ) :
    FractionRing.addValuation p k ((p : K(p, k)) ^ n) = n := by
  rw [AddValuation.map_pow, FractionRing.addValuation_p, nsmul_one]

/-- For a prime `p`, a perfect field `k` of characteristic `p` and an integer `m`, the `p`-adic
additive valuation of `K(p, k)` takes the value `m` at `p ^ m`. -/
@[simp]
theorem FractionRing.addValuation_p_zpow (m : ℤ) :
    FractionRing.addValuation p k ((p : K(p, k)) ^ m) = m := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast, FractionRing.addValuation_p_pow]
    simp
  · rw [zpow_neg, zpow_natCast, AddValuation.map_inv, FractionRing.addValuation_p_pow]
    simp

/-- For a prime `p`, a perfect field `k` of characteristic `p`, an integer `m` and a unit `u` of
`𝕎 k`, the `p`-adic additive valuation of `K(p, k)` takes the value `m` at `p ^ m * u`, where `u`
is viewed in `K(p, k)` through `algebraMap`. -/
theorem FractionRing.addValuation_p_zpow_mul_unit (m : ℤ) (u : (𝕎 k)ˣ) :
    FractionRing.addValuation p k ((p : K(p, k)) ^ m * algebraMap (𝕎 k) K(p, k) u) = m := by
  rw [AddValuation.map_mul, FractionRing.addValuation_p_zpow,
    FractionRing.addValuation_algebraMap_unit, add_zero]

/-! ### Frobenius invariance -/

private theorem addVal_frobenius (x : 𝕎 k) :
    IsDiscreteValuationRing.addVal (𝕎 k) (frobenius x) =
      IsDiscreteValuationRing.addVal (𝕎 k) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero]
  obtain ⟨m, u, rfl⟩ := exists_eq_pow_p_mul' x hx
  have hu : frobenius ((p : 𝕎 k) ^ m * (u : 𝕎 k)) =
      (Units.map (frobenius : 𝕎 k →+* 𝕎 k).toMonoidHom u : 𝕎 k) * (p : 𝕎 k) ^ m := by
    rw [map_mul, map_pow, map_natCast, mul_comm]
    rfl
  rw [hu, IsDiscreteValuationRing.addVal_def _ _ (irreducible p) m rfl,
    IsDiscreteValuationRing.addVal_def _ u (irreducible p) m (mul_comm _ _)]

private theorem frobenius_algebraMap (x : 𝕎 k) :
    φ(p, k) (algebraMap (𝕎 k) K(p, k) x) = algebraMap (𝕎 k) K(p, k) (frobenius x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (frobeniusEquiv p k) x

/-- For a prime `p`, a perfect field `k` of characteristic `p` and `x : K(p, k)`, the `p`-adic
additive valuation of `K(p, k)` takes the same value at `φ(p, k) x` as at `x`: it is invariant
under the Frobenius automorphism `φ(p, k)` of `K(p, k)`. -/
@[simp]
theorem FractionRing.addValuation_frobenius (x : K(p, k)) :
    FractionRing.addValuation p k (φ(p, k) x) = FractionRing.addValuation p k x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝕎 k) x
  simp only [map_div₀, AddValuation.map_div, frobenius_algebraMap,
    FractionRing.addValuation_algebraMap, addVal_frobenius]

/-- For a prime `p`, a perfect field `k` of characteristic `p` and `x : K(p, k)`, the `p`-adic
additive valuation of `K(p, k)` takes the same value at `(FractionRing.frobenius p k).symm x` as
at `x`: it is invariant under the inverse of the Frobenius automorphism of `K(p, k)`. -/
@[simp]
theorem FractionRing.addValuation_frobenius_symm (x : K(p, k)) :
    FractionRing.addValuation p k ((FractionRing.frobenius p k).symm x) =
      FractionRing.addValuation p k x := by
  conv_rhs => rw [← (FractionRing.frobenius p k).apply_symm_apply x]
  exact (FractionRing.addValuation_frobenius p k _).symm

/-- For a prime `p` and a perfect field `k` of characteristic `p`, the pullback of the `p`-adic
additive valuation of `K(p, k)` along the Frobenius automorphism `φ(p, k)` is the `p`-adic
additive valuation itself. -/
theorem FractionRing.addValuation_comap_frobenius :
    (FractionRing.addValuation p k).comap φ(p, k) = FractionRing.addValuation p k :=
  AddValuation.ext (FractionRing.addValuation_frobenius p k)

end WittVector
