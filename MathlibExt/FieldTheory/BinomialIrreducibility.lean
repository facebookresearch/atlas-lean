/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The norm-factor argument is adapted from the following Apache-2.0 sources:

anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2:
P2M/Sol/S_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply.lean
P2M/Sol/S_Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime.lean
Copyright 2026 Anthropic, PBC. The source names no individual proof authors.

Mathlib/FieldTheory/KummerPolynomial.lean:
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Authors: Andrew Yang.
Released under Apache 2.0, https://www.apache.org/licenses/LICENSE-2.0.
-/
module

public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Defs

/-!
# Binomial irreducibility from an integer-valued character

A character on the unit group detects the degree of an irreducible factor
through its root's norm. Coprimality forces that degree to be the full
exponent. No ultrametric inequality or characteristic restriction is used.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

private lemma norm_root_pow_eq {n : ℕ} {a : K} {g : K[X]}
    (hg : g ≠ 0) (hdiv : g ∣ X ^ n - C a) :
    (Algebra.norm K (AdjoinRoot.root g)) ^ n = a ^ g.natDegree := by
  have h := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hdiv
    (AdjoinRoot.eval₂_root g)
  rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at h
  rw [← map_pow, h, ← AdjoinRoot.algebraMap_eq, Algebra.norm_algebraMap,
    (AdjoinRoot.powerBasis hg).finrank, AdjoinRoot.powerBasis_dim hg]

/-- A binomial is irreducible when an integer-valued character of its
coefficient is coprime to its positive exponent. The character is defined
on units; no ultrametric inequality or characteristic assumption is needed.
This is the bundled interface of the two FLT entry295 source statements. -/
theorem irreducible_X_pow_sub_C_of_unitHom {n : ℕ} (hn : 0 < n)
    {a : K} (ha : a ≠ 0) (φ : Kˣ →* Multiplicative ℤ)
    (hφ : (Multiplicative.toAdd (φ (Units.mk0 a ha))).natAbs.Coprime n) :
    Irreducible (X ^ n - C a) := by
  have hunit : ¬ IsUnit (X ^ n - C a) := by
    rw [isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hn,
      Nat.cast_eq_zero]
    exact hn.ne'
  obtain ⟨g, hg, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor hunit
    (X_pow_sub_C_ne_zero hn a)
  have key := norm_root_pow_eq hg.ne_zero hdiv
  have hc : Algebra.norm K (AdjoinRoot.root g) ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at key
    exact pow_ne_zero _ ha key.symm
  have hu : (Units.mk0 (Algebra.norm K (AdjoinRoot.root g)) hc) ^ n =
      (Units.mk0 a ha) ^ g.natDegree := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using key
  have hv := congrArg (fun u => Multiplicative.toAdd (φ u)) hu
  simp only [map_pow, toAdd_pow] at hv
  have hd : (n : ℤ) ∣ (g.natDegree : ℤ) *
      Multiplicative.toAdd (φ (Units.mk0 a ha)) := ⟨_, hv.symm⟩
  have hd' : n ∣ g.natDegree *
      (Multiplicative.toAdd (φ (Units.mk0 a ha))).natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      Int.natAbs_dvd_natAbs.mpr hd
  have hle : g.natDegree ≤ n :=
    (natDegree_le_of_dvd hdiv (X_pow_sub_C_ne_zero hn a)).trans_eq
      natDegree_X_pow_sub_C
  have heq : g.natDegree = n := le_antisymm hle
    (Nat.le_of_dvd (natDegree_pos_iff_degree_pos.mpr
      (degree_pos_of_irreducible hg))
      (hφ.symm.dvd_of_dvd_mul_right hd'))
  exact (associated_of_dvd_of_natDegree_le hdiv
    (X_pow_sub_C_ne_zero hn a)
    (heq.trans natDegree_X_pow_sub_C.symm).ge).irreducible hg

/-- Function form of the integer-character criterion. Multiplication is
required only for nonzero factors, so the value at zero is arbitrary.
The coprimality condition is in `ℤ`, exactly as in the source interface. -/
theorem irreducible_X_pow_sub_C_of_integerCharacter
    (v : K → ℤ)
    (hv : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {n : ℕ} (hn : 0 < n) {a : K} (ha : a ≠ 0)
    (hcop : IsCoprime (v a) (n : ℤ)) :
    Irreducible (X ^ n - C a) := by
  have hv1 : v 1 = 0 := by
    have h := hv 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    omega
  let φ : Kˣ →* Multiplicative ℤ :=
    { toFun := fun u => Multiplicative.ofAdd (v u)
      map_one' := by
        change Multiplicative.ofAdd (v 1) = 1
        rw [hv1]
        rfl
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (v (↑x * ↑y)) =
          Multiplicative.ofAdd (v ↑x + v ↑y)
        rw [hv _ _ x.ne_zero y.ne_zero] }
  apply irreducible_X_pow_sub_C_of_unitHom hn ha φ
  change (v a).natAbs.Coprime n
  simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def,
    Int.natAbs_natCast] using hcop

end Polynomial
