/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WeierstrassCurve_exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_
supersingular.lean`,
`P2M/Sol/S_WeierstrassCurve_exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_
supersingular.lean`,
`Theorems/Thm_WeierstrassCurve_valuation_torsion_of_coeff_prePsi_dvd.lean`,
`P2M/Sol/S_WeierstrassCurve_valuation_torsion_of_coeff_prePsi_dvd.lean`,
`P2M/Sol/S_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff.lean`,
`P2M/Sol/S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi.lean`,
`P2M/Sol/S_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor.lean`, and
`P2M/Sol/S_ValuationSubring_residueField_charP_of_liesOverPrime.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
public import MathlibExt.AlgebraicGeometry.EllipticCurve.Supersingular
public import MathlibExt.RingTheory.Valuation.TameCharacter
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.TensorProduct.Free
import MathlibExt.AlgebraicGeometry.EllipticCurve.DivisionPolynomialMulFormula
import MathlibExt.AlgebraicGeometry.EllipticCurve.TorsionCardinality
import MathlibExt.RingTheory.Valuation.ResidueChar
import MathlibExt.RingTheory.Valuation.ResidueField

/-!
# Tame inertia on the residual representation at a supersingular prime

Let `W` be an integral Weierstrass curve with good reduction at an odd prime `p`, supersingular
in the sense that the inner coefficients of its `p`-division polynomial are divisible by `p`;
this is supersingularity of the reduction of `W` over `AlgebraicClosure (ZMod p)`. At a valuation
subring `P` of `AlgebraicClosure ℚ` over `p`, every nonzero `p`-torsion point has `x`-coordinate
of valuation `v(p) ^ (-2 / (p ^ 2 - 1))`, and the reduction of `x / (y π)` with
`π ^ (p ^ 2 - 1) = p` is an additive functional on the `p`-torsion on which inertia acts through
the tame character. For every finite coefficient field `k` over `𝔽ₚ`, every valuation subring `P`
of `ℚ̄` above `p`, and every `π` with `π^(p²−1) = p`, there is an embedding `k → κ(P)` such that
the representation extended along it has a nonzero inertia eigenvector in `κ(P)²` with
eigencharacter `P.tameCharacter π`.

## Main results

* `WeierstrassCurve.isSupersingular_map_iff_coeff_prePsi_dvd`: the divisibility condition is
  supersingular reduction.
* `WeierstrassCurve.valuation_torsion_of_coeff_prePsi_dvd`: valuations of `p`-torsion
  coordinates.
* `WeierstrassCurve.exists_inertia_mulVec_eq_tameCharacter_smul_of_supersingular`: the inertia
  eigenvector, with eigencharacter the tame character.
* `WeierstrassCurve.exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular`:
  the same eigenvector, with eigencharacter the tame character or its `p`-th power.

## References

* J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*,
  Invent. Math. 15 (1972), 259–331: at a prime of good supersingular reduction, tame inertia acts
  on the `p`-torsion through the fundamental characters of level 2.
-/

-- The point API needs decidable equality on `AlgebraicClosure ℚ`. Take it from classical
-- logic for this file only, matching the residual representation's own file.
attribute [local instance] Classical.decEq

@[expose] public section

open Polynomial

namespace Valuation

variable {K : Type*} {Γ₀ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

private theorem _root_.Valuation.newton_one_slope (c : ℕ → K) (N : ℕ) (x : K)
    (h0 : v (c 0) = 1) (hN0 : v (c N) ≠ 0) (hN1 : v (c N) < 1)
    (hmid : ∀ i, 0 < i → i < N → v (c i) ≤ v (c N))
    (hroot : ∑ i ∈ Finset.range (N + 1), c i * x ^ i = 0) :
    v x ^ N * v (c N) = 1 := by
  classical
  have hterm : ∀ i, v (c i * x ^ i) = v (c i) * v x ^ i := fun i => by
    rw [map_mul, map_pow]
  have hci : ∀ i, 0 < i → i ≤ N → v (c i) ≤ v (c N) := by
    intro i hi hiN
    rcases lt_or_eq_of_le hiN with h | rfl
    · exact hmid i hi h
    · exact le_rfl
  rcases lt_trichotomy (v x ^ N * v (c N)) 1 with hlt | heq | hgt
  · exfalso
    have hM : ∀ i, 0 < i → i ≤ N → v (c i * x ^ i) < 1 := by
      intro i hi hiN
      rw [hterm]
      rcases le_or_gt (v x) 1 with hx | hx
      · calc v (c i) * v x ^ i ≤ v (c N) * 1 := mul_le_mul' (hci i hi hiN) (pow_le_one₀ zero_le hx)
          _ = v (c N) := mul_one _
          _ < 1 := hN1
      · calc v (c i) * v x ^ i ≤ v (c N) * v x ^ N :=
            mul_le_mul' (hci i hi hiN) (pow_le_pow_right₀ hx.le hiN)
          _ = v x ^ N * v (c N) := mul_comm _ _
          _ < 1 := hlt
    have hsum : v (∑ i ∈ Finset.range (N + 1), c i * x ^ i) = v (c 0 * x ^ 0) := by
      apply map_sum_eq_of_lt v (Finset.mem_range.mpr (Nat.succ_pos N))
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
      rw [pow_zero, mul_one, h0]
      exact hM i (Nat.pos_of_ne_zero hi.2) (Nat.lt_succ_iff.mp hi.1)
    rw [hroot, map_zero, pow_zero, mul_one, h0] at hsum
    exact zero_ne_one hsum
  · exact heq
  · exfalso
    have hx : 1 < v x := by
      by_contra hx
      push Not at hx
      have : v x ^ N * v (c N) ≤ 1 * 1 := mul_le_mul' (pow_le_one₀ zero_le hx) hN1.le
      rw [mul_one] at this
      exact not_lt.mpr this hgt
    have hq0 : 0 < v (c N) := zero_lt_iff.mpr hN0
    have hM : ∀ i, i < N → v (c i * x ^ i) < v (c N * x ^ N) := by
      intro i hiN
      rw [hterm, hterm]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [pow_zero, mul_one, h0, mul_comm]
        exact hgt
      · calc v (c i) * v x ^ i ≤ v (c N) * v x ^ i := mul_le_mul_left (hmid i hi hiN) _
          _ < v (c N) * v x ^ N := mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hx hiN) hq0
    have hsum : v (∑ i ∈ Finset.range (N + 1), c i * x ^ i) = v (c N * x ^ N) := by
      apply map_sum_eq_of_lt v (Finset.self_mem_range_succ N)
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
      exact hM i (lt_of_le_of_ne (Nat.lt_succ_iff.mp hi.1) hi.2)
    rw [hroot, map_zero, hterm] at hsum
    exact mul_ne_zero hN0 (pow_ne_zero N (ne_of_gt (lt_trans zero_lt_one hx))) hsum.symm

private theorem _root_.Valuation.sq_eq_cube_of_weierstrass {a₁ a₂ a₃ a₄ a₆ x y : K}
    (ha₁ : v a₁ ≤ 1) (ha₂ : v a₂ ≤ 1) (ha₃ : v a₃ ≤ 1) (ha₄ : v a₄ ≤ 1) (ha₆ : v a₆ ≤ 1)
    (hx : 1 < v x)
    (heq : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) :
    v y ^ 2 = v x ^ 3 := by
  have hX0 : 0 < v x := lt_trans zero_lt_one hx
  have hX12 : v x < v x ^ 2 := by
    simpa only [pow_one] using pow_lt_pow_right₀ hx (show 1 < 2 by norm_num)
  have hX23 : v x ^ 2 < v x ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
  have hX13 : v x < v x ^ 3 := lt_trans hX12 hX23
  have hX03 : (1 : Γ₀) < v x ^ 3 := lt_trans hx hX13
  have hx3 : v (x ^ 3) = v x ^ 3 := by rw [map_pow]
  have hrhs : v (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) = v x ^ 3 := by
    have h1 : v (a₂ * x ^ 2) < v x ^ 3 := by
      rw [map_mul, map_pow]
      calc v a₂ * v x ^ 2 ≤ 1 * v x ^ 2 := mul_le_mul_left ha₂ _
        _ = v x ^ 2 := one_mul _
        _ < v x ^ 3 := hX23
    have h2 : v (a₄ * x) < v x ^ 3 := by
      rw [map_mul]
      calc v a₄ * v x ≤ 1 * v x := mul_le_mul_left ha₄ _
        _ = v x := one_mul _
        _ < v x ^ 3 := hX13
    have h3 : v a₆ < v x ^ 3 := lt_of_le_of_lt ha₆ hX03
    have key : v (a₂ * x ^ 2 + (a₄ * x + a₆)) < v (x ^ 3) := by
      rw [hx3]
      exact map_add_lt v h1 (map_add_lt v h2 h3)
    rw [add_assoc, add_assoc, map_add_eq_of_lt_left v key, hx3]
  have hlhs : v (y ^ 2 + a₁ * x * y + a₃ * y) = v x ^ 3 := by rw [heq, hrhs]
  have hxy : v (a₁ * x * y) ≤ v x * v y := by
    rw [map_mul, map_mul]
    calc v a₁ * v x * v y ≤ 1 * v x * v y := mul_le_mul_left (mul_le_mul_left ha₁ _) _
      _ = v x * v y := by rw [one_mul]
  have hy : v (a₃ * y) ≤ v y := by
    rw [map_mul]
    calc v a₃ * v y ≤ 1 * v y := mul_le_mul_left ha₃ _
      _ = v y := one_mul _
  rcases lt_trichotomy (v y ^ 2) (v x ^ 3) with hlt | he | hgt
  · exfalso
    have hY2 : v y < v x ^ 2 := by
      by_contra h
      push Not at h
      have h4 : v x ^ 4 ≤ v y ^ 2 := by
        calc v x ^ 4 = (v x ^ 2) ^ 2 := by rw [← pow_mul]
          _ ≤ v y ^ 2 := pow_le_pow_left₀ zero_le h 2
      have h34 : v x ^ 3 < v x ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
      exact absurd (lt_trans hlt h34) (not_lt.mpr h4)
    have hY3 : v y < v x ^ 3 := by
      by_contra h
      push Not at h
      have h6 : v x ^ 6 ≤ v y ^ 2 := by
        calc v x ^ 6 = (v x ^ 3) ^ 2 := by rw [← pow_mul]
          _ ≤ v y ^ 2 := pow_le_pow_left₀ zero_le h 2
      have h36 : v x ^ 3 < v x ^ 6 := pow_lt_pow_right₀ hx (by norm_num)
      exact absurd (lt_trans hlt h36) (not_lt.mpr h6)
    have t1 : v (y ^ 2) < v x ^ 3 := by rwa [map_pow]
    have t2 : v (a₁ * x * y) < v x ^ 3 :=
      calc v (a₁ * x * y) ≤ v x * v y := hxy
        _ < v x * v x ^ 2 := mul_lt_mul_of_pos_left hY2 hX0
        _ = v x ^ 3 := by rw [← pow_succ']
    have t3 : v (a₃ * y) < v x ^ 3 := lt_of_le_of_lt hy hY3
    have := map_add_lt v (map_add_lt v t1 t2) t3
    rw [hlhs] at this
    exact lt_irrefl _ this
  · exact he
  · exfalso
    have hXY : v x < v y := by
      by_contra h
      push Not at h
      have : v y ^ 2 ≤ v x ^ 2 := pow_le_pow_left₀ zero_le h 2
      exact absurd (lt_of_le_of_lt this hX23) (not_lt.mpr hgt.le)
    have hY0 : 0 < v y := lt_trans hX0 hXY
    have hY1 : 1 < v y := lt_trans hx hXY
    have t2 : v (a₁ * x * y) < v y ^ 2 :=
      calc v (a₁ * x * y) ≤ v x * v y := hxy
        _ < v y * v y := mul_lt_mul_of_pos_right hXY hY0
        _ = v y ^ 2 := (sq _).symm
    have t3 : v (a₃ * y) < v y ^ 2 :=
      calc v (a₃ * y) ≤ v y := hy
        _ < v y * v y := lt_mul_of_one_lt_left hY0 hY1
        _ = v y ^ 2 := (sq _).symm
    have hy2 : v (y ^ 2) = v y ^ 2 := by rw [map_pow]
    have key : v (a₁ * x * y + a₃ * y) < v (y ^ 2) := by
      rw [hy2]
      exact map_add_lt v t2 t3
    have : v (y ^ 2 + a₁ * x * y + a₃ * y) = v y ^ 2 := by
      rw [add_assoc, map_add_eq_of_lt_left v key, hy2]
    rw [hlhs] at this
    exact hgt.ne this

end Valuation

namespace ValuationSubring

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem _root_.ValuationSubring.valuation_intCast_le_one (c : ℤ) :
    A.valuation (c : L) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A c)

private theorem _root_.ValuationSubring.valuation_intCast_lt_one_of_dvd {p : ℕ}
    (hA : A.LiesOverPrime p) {c : ℤ} (h : (p : ℤ) ∣ c) : A.valuation (c : L) < 1 := by
  obtain ⟨k, rfl⟩ := h
  have hp : A.valuation (p : L) < 1 := A.mem_nonunits_iff.mp hA
  rw [Int.cast_mul, Int.cast_natCast, map_mul]
  calc A.valuation (p : L) * A.valuation (k : L) ≤ A.valuation (p : L) * 1 :=
      mul_le_mul_right (A.valuation_intCast_le_one k) _
    _ < 1 := by rwa [mul_one]

private theorem _root_.ValuationSubring.valuation_intCast_lt_one_iff {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (c : ℤ) :
    A.valuation (c : L) < 1 ↔ (p : ℤ) ∣ c := by
  refine ⟨fun hc => ?_, A.valuation_intCast_lt_one_of_dvd hA⟩
  by_contra hndvd
  have hcop : IsCoprime (p : ℤ) c :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hndvd
  obtain ⟨a, b, hab⟩ := hcop
  have hp1 : A.valuation (p : L) < 1 := A.mem_nonunits_iff.mp hA
  have h1 : A.valuation ((a * p + b * c : ℤ) : L) < 1 := by
    push_cast
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      calc A.valuation (a : L) * A.valuation (p : L) ≤ 1 * A.valuation (p : L) :=
          mul_le_mul_left (A.valuation_intCast_le_one a) _
        _ < 1 := by rwa [one_mul]
    · rw [map_mul]
      calc A.valuation (b : L) * A.valuation (c : L) ≤ 1 * A.valuation (c : L) :=
          mul_le_mul_left (A.valuation_intCast_le_one b) _
        _ < 1 := by rwa [one_mul]
  rw [hab, Int.cast_one, map_one] at h1
  exact lt_irrefl _ h1

private theorem _root_.ValuationSubring.valuation_intCast_eq_one_iff {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (c : ℤ) :
    A.valuation (c : L) = 1 ↔ ¬ (p : ℤ) ∣ c := by
  rw [← A.valuation_intCast_lt_one_iff hp hA c, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (A.valuation_intCast_le_one c) h⟩

private theorem _root_.ValuationSubring.intCast_residueField_eq_zero_iff {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (c : ℤ) :
    ((c : ℤ) : IsLocalRing.ResidueField A) = 0 ↔ (p : ℤ) ∣ c := by
  rw [← map_intCast (IsLocalRing.residue A) c, IsLocalRing.residue_eq_zero_iff,
    ← coe_mem_nonunits_iff, mem_nonunits_iff]
  exact A.valuation_intCast_lt_one_iff hp hA c

end ValuationSubring

namespace WeierstrassCurve
open WeierstrassCurve.Affine

section N1

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

private theorem _root_.WeierstrassCurve.natDegree_prePsi_le_of_odd {n : ℕ} (hn : Odd n) :
    (W.preΨ' n).natDegree ≤ (n ^ 2 - 1) / 2 := by
  simpa only [ite_eq_right (Nat.not_even_iff_odd.mpr hn)] using W.natDegree_preΨ'_le n

private theorem _root_.WeierstrassCurve.coeff_prePsi_of_odd {n : ℕ} (hn : Odd n) :
    (W.preΨ' n).coeff ((n ^ 2 - 1) / 2) = n := by
  simpa only [ite_eq_right (Nat.not_even_iff_odd.mpr hn)] using W.coeff_preΨ' n

end N1

private theorem Affine.exists_nonsingular_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F]
    (W : Affine F) (hΔ : W.Δ ≠ 0) (x : F) : ∃ y, W.Nonsingular x y := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    (C 1 * X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)))
    (by rw [degree_quadratic (one_ne_zero' F)]; decide)
  refine ⟨y, (W.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp ?_⟩
  rw [Affine.equation_iff]
  have := hy.eq_zero
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, one_mul] at this
  linear_combination this

section Setting

variable (W : WeierstrassCurve ℤ) {p : ℕ} [Fact p.Prime]
  (A : ValuationSubring (AlgebraicClosure ℚ))

private lemma not_dvd_two (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have hp : p.Prime := Fact.out
  have h' : p ∣ 2 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

private theorem intBaseChange_prePsi (n : ℕ) :
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).preΨ' n =
      (W.preΨ' n).map (Int.castRingHom (AlgebraicClosure ℚ)) := by
  rw [show ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)) =
      (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ)) from rfl,
    map_preΨ', map_preΨ', Polynomial.map_map]
  congr 1

private lemma _root_.WeierstrassCurve.baseChange_a :
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₁ = (W.a₁ : AlgebraicClosure ℚ) ∧
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₂ = (W.a₂ : AlgebraicClosure ℚ) ∧
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₃ = (W.a₃ : AlgebraicClosure ℚ) ∧
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₄ = (W.a₄ : AlgebraicClosure ℚ) ∧
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₆ = (W.a₆ : AlgebraicClosure ℚ) := by
  simp [WeierstrassCurve.baseChange]

private theorem _root_.WeierstrassCurve.intBaseChange_discr_ne_zero (hΔ : W.Δ ≠ 0) :
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Δ ≠ 0 := by
  simpa [WeierstrassCurve.baseChange, map_Δ] using hΔ

private lemma one_lt_of_pow_mul_eq_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {a b : Γ₀} {N : ℕ} (h : a ^ N * b = 1) (hb : b < 1) : 1 < a := by
  by_contra ha
  push Not at ha
  have : a ^ N * b < 1 :=
    calc a ^ N * b ≤ 1 * b := mul_le_mul_left (pow_le_one₀ zero_le ha) _
      _ = b := one_mul _
      _ < 1 := hb
  exact this.ne h

private theorem _root_.WeierstrassCurve.exists_coeff_prePsi_not_dvd {F : Type} [Field F]
    [IsAlgClosed F] [CharP F p] (hp2 : p ≠ 2) (hΔ : (W.map (Int.castRingHom F)).Δ ≠ 0)
    (hPsi : ∀ {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
      {n : ℕ}, Odd n → ∀ {x y : F} (h : W.toAffine.Nonsingular x y),
      n • Point.some x y h = 0 ↔ (W.preΨ' n).eval x = 0)
    (hTwo : ∀ {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F}
      (h : W.toAffine.Nonsingular x y), 2 • Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0) :
    ∃ i, i ≤ (p ^ 2 - 1) / 2 ∧ ¬ (p : ℤ) ∣ (W.preΨ' p).coeff i := by
  classical
  by_contra hall
  push Not at hall
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set Wt := W.map (Int.castRingHom F) with hWt
  have : Wt.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hzero : Wt.preΨ' p = 0 := by
    rw [hWt, map_preΨ']
    ext i
    rw [coeff_map, coeff_zero, eq_intCast]
    by_cases hi : i ≤ (p ^ 2 - 1) / 2
    · exact (CharP.intCast_eq_zero_iff F p _).mpr (hall i hi)
    · rw [coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (W.natDegree_prePsi_le_of_odd hodd) (not_le.mp hi)), Int.cast_zero]
  have h2 : (2 : F) ≠ 0 := by
    have := (not_congr (CharP.intCast_eq_zero_iff F p 2)).mpr (not_dvd_two hp2)
    exact_mod_cast this
  have h4 : (4 : F) ≠ 0 := by
    have := mul_ne_zero h2 h2
    norm_num at this
    exact this
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root Wt.Ψ₂Sq (by
    rw [degree_eq_natDegree (Wt.Ψ₂Sq_ne_zero h4), Wt.natDegree_Ψ₂Sq h4]; decide)
  obtain ⟨y₀, hP⟩ := Affine.exists_nonsingular_of_isAlgClosed Wt.toAffine hΔ x₀
  have h2P : 2 • Point.some x₀ y₀ hP = 0 := (hTwo Wt hP).mpr hx₀.eq_zero
  have hpP : p • Point.some x₀ y₀ hP = 0 := (hPsi Wt hodd hP).mpr (by rw [hzero, eval_zero])
  obtain ⟨k, hk⟩ := hodd
  rw [hk, add_smul, one_smul, mul_comm, mul_smul, h2P, smul_zero, zero_add] at hpP
  exact Point.some_ne_zero hP hpP

private theorem _root_.WeierstrassCurve.valuation_of_nsmul_eq_zero_of_coeff_prePsi_dvd
    (hp2 : p ≠ 2) (hA : A.LiesOverPrime p)
    (hres : IsAlgClosed (IsLocalRing.ResidueField A))
    (hΔres : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).Δ ≠ 0)
    (hPsi : ∀ {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
      {n : ℕ}, Odd n → ∀ {x y : F} (h : W.toAffine.Nonsingular x y),
      n • Point.some x y h = 0 ↔ (W.preΨ' n).eval x = 0)
    (hTwo : ∀ {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F}
      (h : W.toAffine.Nonsingular x y), 2 • Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hP : p • Point.some x y h = 0) :
    A.valuation x ^ ((p ^ 2 - 1) / 2) * A.valuation (p : AlgebraicClosure ℚ) = 1 ∧
      A.valuation y ^ 2 = A.valuation x ^ 3 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hΔ0 : W.Δ ≠ 0 := by
    intro h0
    apply hΔres
    rw [map_Δ, h0, _root_.map_zero]
  have hEΔ := W.intBaseChange_discr_ne_zero hΔ0
  have : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hEΔ⟩
  have := ValuationSubring.charP_residueField_of_liesOverPrime A p hA
  obtain ⟨i, hiN, hi⟩ := W.exists_coeff_prePsi_not_dvd hp2 hΔres hPsi hTwo
  have hi0 : i = 0 := by
    by_contra hne
    rcases lt_or_eq_of_le hiN with hlt | rfl
    · exact hi (hss i (Nat.one_le_iff_ne_zero.mpr hne) hlt)
    · exact hi (by rw [W.coeff_prePsi_of_odd hodd])
  subst hi0
  set N := (p ^ 2 - 1) / 2 with hN
  set c : ℕ → AlgebraicClosure ℚ := fun j => ((W.preΨ' p).coeff j : AlgebraicClosure ℚ) with hc
  have hroot : ∑ j ∈ Finset.range (N + 1), c j * x ^ j = 0 := by
    have hev := (hPsi _ hodd h).mp hP
    rw [intBaseChange_prePsi, eval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le
      (Nat.lt_succ_of_le (W.natDegree_prePsi_le_of_odd hodd)))] at hev
    simpa only [coeff_map, eq_intCast] using hev
  have hc0 : A.valuation (c 0) = 1 := (A.valuation_intCast_eq_one_iff hp hA _).mpr hi
  have hcN : A.valuation (c N) = A.valuation (p : AlgebraicClosure ℚ) := by
    simp only [hc, hN, W.coeff_prePsi_of_odd hodd, Int.cast_natCast]
  have hvp : A.valuation (p : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  have hcN0 : A.valuation (c N) ≠ 0 := by
    rw [hcN]
    exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hmid : ∀ j, 0 < j → j < N → A.valuation (c j) ≤ A.valuation (c N) := by
    intro j hj hjN
    obtain ⟨k, hk⟩ := hss j hj hjN
    rw [hcN]
    simp only [hc, hk, Int.cast_mul, Int.cast_natCast, map_mul]
    exact mul_le_of_le_one_right' (A.valuation_intCast_le_one k)
  have key := A.valuation.newton_one_slope c N x hc0 hcN0 (hcN ▸ hvp) hmid hroot
  rw [hcN] at key
  refine ⟨key, ?_⟩
  have hx : 1 < A.valuation x := one_lt_of_pow_mul_eq_one key hvp
  have heq := (Affine.equation_iff x y).mp h.left
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := W.baseChange_a
  simp only [h₁, h₂, h₃, h₄, h₆] at heq
  exact A.valuation.sq_eq_cube_of_weierstrass (A.valuation_intCast_le_one _)
    (A.valuation_intCast_le_one _) (A.valuation_intCast_le_one _) (A.valuation_intCast_le_one _)
    (A.valuation_intCast_le_one _) hx heq

end Setting

end WeierstrassCurve

namespace SupersingularInertiaAux

open scoped Polynomial.Bivariate in
private theorem nsmul_some_eq_zero_iff_eval_prePsi {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : Odd n) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    n • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ (W.preΨ' n).eval x = 0 := by
  rw [← natCast_zsmul, WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W h (n : ℤ)]
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_mk.mp
    (WeierstrassCurve.Affine.CoordinateRing.mk_ψ W (n : ℤ))
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h.1
  have h1 := congrArg (evalEval x y) hq
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero] at h1
  rw [h1, WeierstrassCurve.Ψ_ofNat, ite_eq_right (Nat.not_even_iff_odd.mpr hn), mul_one,
    evalEval_C]

private theorem map_residueField_discr_ne_zero_of_isGoodPrimeFor (W : WeierstrassCurve ℤ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).Δ ≠ 0 := by
  rw [WeierstrassCurve.map_Δ, eq_intCast, Ne,
    A.intCast_residueField_eq_zero_iff hℓ hA]
  exact hgood

end SupersingularInertiaAux

open WeierstrassCurve.Affine in
/-- For an integral Weierstrass curve with good supersingular reduction at an odd prime `p`
(the inner coefficients of the `p`-division polynomial are divisible by `p`), every nonzero
`p`-torsion point `(x, y)` over `AlgebraicClosure ℚ` satisfies, at any valuation subring over
`p`, `v(x) ^ ((p ^ 2 - 1) / 2) * v(p) = 1` and `v(y) ^ 2 = v(x) ^ 3`. -/
theorem WeierstrassCurve.valuation_torsion_of_coeff_prePsi_dvd (W : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (x y : AlgebraicClosure ℚ)
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hP : p • (Point.some x y h :
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0) :
    A.valuation x ^ ((p ^ 2 - 1) / 2) * A.valuation (p : AlgebraicClosure ℚ) = 1 ∧
      A.valuation y ^ 2 = A.valuation x ^ 3 :=
  W.valuation_of_nsmul_eq_zero_of_coeff_prePsi_dvd A hp2 hA
    (ValuationSubring.isAlgClosed_residueField A)
    (SupersingularInertiaAux.map_residueField_discr_ne_zero_of_isGoodPrimeFor W Fact.out
      hgood A hA)
    (fun W' _ _ hn _ _ h' => SupersingularInertiaAux.nsmul_some_eq_zero_iff_eval_prePsi W' hn h')
    (fun _ _ _ h' => (WeierstrassCurve.Affine.Ψ₂Sq_eval_eq_zero_iff_two_smul h').symm) hss h hP

/-- Good reduction at `p` makes the reduction of an integral Weierstrass curve elliptic over every
field of characteristic `p`. -/
theorem WeierstrassCurve.IsGoodPrimeFor.isElliptic_map {W : WeierstrassCurve ℤ} {p : ℕ}
    (hgood : W.IsGoodPrimeFor p) (F : Type*) [Field F] [CharP F p] :
    (W.map (Int.castRingHom F)).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by
    rw [WeierstrassCurve.map_Δ, eq_intCast, Ne, CharP.intCast_eq_zero_iff F p]
    exact hgood)⟩

open WeierstrassCurve.Affine in
/-- Let `p` be an odd prime and let `W` be an integral Weierstrass curve whose reduction over
`AlgebraicClosure (ZMod p)` is elliptic. The reduction is supersingular exactly when the inner
coefficients of the `p`-division polynomial `preΨ' p`, those of degree strictly between `0` and
`(p ^ 2 - 1) / 2`, are divisible by `p`. -/
theorem WeierstrassCurve.isSupersingular_map_iff_coeff_prePsi_dvd (W : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    [(W.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).IsElliptic] :
    (W.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).toAffine.IsSupersingular ↔
      ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hΔ : (W.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).Δ ≠ 0 :=
    (W.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).isUnit_Δ.ne_zero
  have hmap : (W.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).preΨ' p =
      (W.preΨ' p).map (Int.castRingHom (AlgebraicClosure (ZMod p))) :=
    map_preΨ' ..
  constructor
  · intro hsup i hi hiN
    by_contra hndvd
    have hci : ((W.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).preΨ' p).coeff i ≠ 0 := by
      rw [hmap, coeff_map, eq_intCast, Ne, CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]
      exact hndvd
    have hdeg : ((W.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).preΨ' p).degree ≠ 0 :=
      (lt_of_lt_of_le (by exact_mod_cast hi) (le_degree_of_ne_zero hci)).ne'
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
    obtain ⟨y, h⟩ := Affine.exists_nonsingular_of_isAlgClosed _ hΔ x
    exact Point.some_ne_zero h (hsup _
      ((SupersingularInertiaAux.nsmul_some_eq_zero_iff_eval_prePsi _ hodd h).mpr hx.eq_zero))
  · intro hss P hP
    obtain ⟨i, hiN, hi⟩ := W.exists_coeff_prePsi_not_dvd (F := AlgebraicClosure (ZMod p)) hp2 hΔ
      (fun W' _ _ hn _ _ h' => SupersingularInertiaAux.nsmul_some_eq_zero_iff_eval_prePsi W' hn h')
      (fun _ _ _ h' => (WeierstrassCurve.Affine.Ψ₂Sq_eval_eq_zero_iff_two_smul h').symm)
    have hi0 : i = 0 := by
      by_contra hne
      rcases lt_or_eq_of_le hiN with hlt | rfl
      · exact hi (hss i (Nat.one_le_iff_ne_zero.mpr hne) hlt)
      · exact hi (by rw [W.coeff_prePsi_of_odd hodd])
    subst hi0
    have hconst : (W.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).preΨ' p =
        C (((W.preΨ' p).coeff 0 : ℤ) : AlgebraicClosure (ZMod p)) := by
      rw [hmap]
      ext j
      rw [coeff_map, eq_intCast]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [coeff_C_zero]
      · rw [coeff_C_of_ne_zero hj.ne', CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]
        rcases lt_trichotomy j ((p ^ 2 - 1) / 2) with hlt | rfl | hgt
        · exact hss j hj hlt
        · rw [W.coeff_prePsi_of_odd hodd]
        · rw [coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (W.natDegree_prePsi_le_of_odd hodd) hgt)]
          exact dvd_zero _
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · have h0 := (SupersingularInertiaAux.nsmul_some_eq_zero_iff_eval_prePsi _ hodd h).mp hP
      rw [hconst, eval_C, CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p] at h0
      exact absurd h0 hi

open Matrix

namespace SSInertia

section groupLaw

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

private lemma bnd_mul {a b : K} {c d : Γ} (ha : v a * c ≤ 1) (hb : v b * d ≤ 1) :
    v (a * b) * (c * d) ≤ 1 := by
  rw [map_mul, mul_mul_mul_comm]
  exact mul_le_one' ha hb

private lemma bnd_add {a b : K} {c : Γ} (ha : v a * c ≤ 1) (hb : v b * c ≤ 1) :
    v (a + b) * c ≤ 1 := by
  rcases le_total (v a) (v b) with h | h
  · exact le_trans (mul_le_mul' (v.map_add_le h le_rfl) le_rfl) hb
  · exact le_trans (mul_le_mul' (v.map_add_le le_rfl h) le_rfl) ha

private lemma bnd_sub {a b : K} {c : Γ} (ha : v a * c ≤ 1) (hb : v b * c ≤ 1) :
    v (a - b) * c ≤ 1 := by
  rw [sub_eq_add_neg]
  exact bnd_add v ha (by rwa [Valuation.map_neg])

private lemma bnd_weaken {a : K} {c d : Γ} (ha : v a * c ≤ 1) (hd : d ≤ 1) :
    v a * (c * d) ≤ 1 := by
  rw [← mul_assoc]; exact mul_le_one' ha hd

private lemma bnd_const {a : K} (ha : v a ≤ 1) {d : Γ} (hd : d ≤ 1) : v a * d ≤ 1 :=
  mul_le_one' ha hd

variable [DecidableEq K] (W : WeierstrassCurve.Affine K)

omit [DecidableEq K] in
private theorem valuation_div_add_div_le (ha₁ : v W.a₁ ≤ 1) (ha₃ : v W.a₃ ≤ 1)
    {γ : Γ} (hγ1 : γ < 1) {x y y' : K}
    (hx : v x * γ ^ 2 = 1) (hy : v y * γ ^ 3 = 1) (hy' : v y' * γ ^ 3 = 1)
    (hsum : y + y' = -(W.a₁ * x + W.a₃)) :
    v (x / y + x / y') ≤ γ ^ 2 := by
  have hγpow : ∀ n : ℕ, γ ^ n ≤ 1 := fun n => pow_le_one₀ zero_le hγ1.le
  have hx0 : x ≠ 0 := by intro h; rw [h, map_zero, zero_mul] at hx; exact zero_ne_one hx
  have hy0 : ∀ {y : K}, v y * γ ^ 3 = 1 → y ≠ 0 := by
    intro y hy h; rw [h, map_zero, zero_mul] at hy; exact zero_ne_one hy
  have hlin : v (W.a₁ * x + W.a₃) * γ ^ 2 ≤ 1 := by
    refine bnd_add v ?_ (bnd_const v ha₃ (hγpow 2))
    have := bnd_mul v (bnd_const v ha₁ (le_refl (1 : Γ))) hx.le
    rwa [one_mul] at this
  have hid : x / y + x / y' = -((x / y) * (x / y') * (W.a₁ * x + W.a₃) * x⁻¹) := by
    rw [show W.a₁ * x + W.a₃ = -(y + y') by rw [hsum]; ring]
    have := hy0 hy
    have := hy0 hy'
    field_simp
    ring
  have ht : ∀ {y : K}, v y * γ ^ 3 = 1 → v (x / y) = γ := by
    intro y hy
    have e : v (x / y) * v y = v x := by rw [← map_mul, div_mul_cancel₀ _ (hy0 hy)]
    calc v (x / y) = v (x / y) * (v y * γ ^ 3) := by rw [hy, mul_one]
      _ = v x * γ ^ 2 * γ := by rw [← mul_assoc, e, pow_succ, mul_assoc]
      _ = γ := by rw [hx, one_mul]
  have hu : v x⁻¹ = γ ^ 2 := by
    have e : v x⁻¹ * v x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    calc v x⁻¹ = v x⁻¹ * (v x * γ ^ 2) := by rw [hx, mul_one]
      _ = γ ^ 2 := by rw [← mul_assoc, e, one_mul]
  rw [hid, Valuation.map_neg, map_mul, map_mul, map_mul, ht hy, ht hy', hu]
  calc γ * γ * v (W.a₁ * x + W.a₃) * γ ^ 2 = (v (W.a₁ * x + W.a₃) * γ ^ 2) * γ ^ 2 := by
        simp only [pow_two]; ac_rfl
    _ ≤ 1 * γ ^ 2 := mul_le_mul' hlin le_rfl
    _ = γ ^ 2 := one_mul _

private theorem valuation_addX_div_addY_sub_le
    (ha₁ : v W.a₁ ≤ 1) (ha₂ : v W.a₂ ≤ 1) (ha₃ : v W.a₃ ≤ 1) (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1)
    {γ : Γ} (hγ1 : γ < 1)
    {x₁ x₂ y₁ y₂ : K} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂))
    (hx₁ : v x₁ * γ ^ 2 = 1) (hx₂ : v x₂ * γ ^ 2 = 1) (hy₁ : v y₁ * γ ^ 3 = 1)
    (hy₂ : v y₂ * γ ^ 3 = 1)
    (hx₃ : v (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) * γ ^ 2 = 1)
    (hy₃ : v (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)) * γ ^ 3 = 1) :
    v (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) / W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)
      - x₁ / y₁ - x₂ / y₂) ≤ γ ^ 2 := by
  set L := W.slope x₁ x₂ y₁ y₂ with hL
  set x₃ := W.addX x₁ x₂ L with hx₃def
  set y₃ := W.addY x₁ x₂ y₁ L with hy₃def
  have hγle : γ ≤ 1 := hγ1.le
  have hγpow : ∀ n : ℕ, γ ^ n ≤ 1 := fun n => pow_le_one₀ zero_le hγle
  have hV := W.addPolynomial_slope h₁ h₂ hxy
  rw [WeierstrassCurve.Affine.addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq] at hV
  have e1 := Cubic.b_of_eq hV
  have e2 := Cubic.c_of_eq hV
  have e3 := Cubic.d_of_eq hV
  simp only [] at e1 e2 e3
  rw [← hL] at e1 e2 e3
  change _ = -(x₁ + x₂ + x₃) at e1
  change _ = x₁ * x₂ + x₁ * x₃ + x₂ * x₃ at e2
  change _ = -(x₁ * x₂ * x₃) at e3
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = y₁ - L * x₁ := ⟨_, rfl⟩
  have hy1 : y₁ = L * x₁ + μ := by rw [hμ]; ring
  have hy2 : y₂ = L * x₂ + μ := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      rw [← WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hy, ← hx, hy1]
    · have : L * (x₁ - x₂) = y₁ - y₂ := by
        rw [hL, WeierstrassCurve.Affine.slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.2 hx)]
      linear_combination this + hy1
  set yR := W.negAddY x₁ x₂ y₁ L with hyRdef
  have hyR : yR = L * x₃ + μ := by
    rw [hyRdef, WeierstrassCurve.Affine.negAddY, hμ]; ring
  have hy3R : y₃ = -yR - W.a₁ * x₃ - W.a₃ := by
    rw [hy₃def, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY]
  have hx0 : ∀ {x : K}, v x * γ ^ 2 = 1 → x ≠ 0 := by
    intro x hx h; rw [h, map_zero, zero_mul] at hx; exact zero_ne_one hx
  have hy0 : ∀ {y : K}, v y * γ ^ 3 = 1 → y ≠ 0 := by
    intro y hy h; rw [h, map_zero, zero_mul] at hy; exact zero_ne_one hy
  have hLb : v L * γ ^ 1 ≤ 1 := by
    rw [pow_one]
    by_contra hcon
    push Not at hcon
    have hbig : v W.a₁ < v L := by
      calc v W.a₁ ≤ 1 := ha₁
        _ < v L * γ := hcon
        _ ≤ v L * 1 := mul_le_mul' le_rfl hγle
        _ = v L := mul_one _
    have hsum : v (L * (L + W.a₁)) * γ ^ 2 ≤ 1 := by
      have : L * (L + W.a₁) = x₁ + x₂ + x₃ + W.a₂ := by linear_combination -e1
      rw [this]
      refine bnd_add v (bnd_add v (bnd_add v hx₁.le hx₂.le) hx₃.le) (bnd_const v ha₂ (hγpow 2))
    have : 1 < v (L * (L + W.a₁)) * γ ^ 2 := by
      rw [map_mul, v.map_add_eq_of_lt_left hbig, pow_two, mul_mul_mul_comm]
      exact one_lt_mul'' hcon hcon
    exact absurd hsum (not_le.2 this)
  have hμb : v μ * γ ^ 3 ≤ 1 := by
    rw [hμ]
    refine bnd_sub v hy₁.le ?_
    have := bnd_mul v hLb hx₁.le
    rwa [← pow_add] at this
  have hlin : v (W.a₁ * x₃ + W.a₃) * γ ^ 2 ≤ 1 := by
    refine bnd_add v ?_ (bnd_const v ha₃ (hγpow 2))
    have := bnd_mul v (bnd_const v ha₁ (le_refl (1 : Γ))) hx₃.le
    rwa [one_mul] at this
  have hyRv : v yR * γ ^ 3 = 1 := by
    have : yR = -(y₃ + (W.a₁ * x₃ + W.a₃)) := by rw [hy3R]; ring
    rw [this, Valuation.map_neg, v.map_add_eq_of_lt_left, hy₃]
    apply lt_of_mul_lt_mul_right' (a := γ ^ 3)
    rw [hy₃]
    calc v (W.a₁ * x₃ + W.a₃) * γ ^ 3 = v (W.a₁ * x₃ + W.a₃) * γ ^ 2 * γ := by
          rw [pow_succ, mul_assoc]
      _ ≤ 1 * γ := mul_le_mul' hlin le_rfl
      _ < 1 := by rw [one_mul]; exact hγ1
  set S : K := 3 * L ^ 2 * (x₁ * x₂ * x₃) + 2 * L * μ * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃)
    + μ ^ 2 * (x₁ + x₂ + x₃) with hSdef
  have hSeq : S = W.a₃ * L ^ 2 * μ - 3 * W.a₆ * L ^ 2 + 2 * W.a₄ * L * μ - W.a₁ * L * μ ^ 2
      - W.a₂ * μ ^ 2 := by
    rw [hy1] at e2 e3
    rw [hSdef]
    linear_combination (3 * L ^ 2) * e3 - (2 * L * μ) * e2 + μ ^ 2 * e1
  have hSb : v S * γ ^ 7 ≤ 1 := by
    rw [hSeq]
    have hL2 : v (L ^ 2) * γ ^ 2 ≤ 1 := by
      have := bnd_mul v hLb hLb; rwa [← pow_two, ← pow_add] at this
    have hμ2 : v (μ ^ 2) * γ ^ 6 ≤ 1 := by
      have := bnd_mul v hμb hμb; rwa [← pow_two, ← pow_add] at this
    refine bnd_sub v (bnd_sub v (bnd_add v (bnd_sub v ?_ ?_) ?_) ?_) ?_
    · have h := bnd_mul v (bnd_mul v (bnd_const v ha₃ (le_refl (1 : Γ))) hL2) hμb
      rw [one_mul, ← pow_add] at h
      have := bnd_weaken v h (hγpow 2)
      rwa [← pow_add] at this
    · have h2 : v (2 : K) ≤ 1 := by
        simpa [one_add_one_eq_two] using v.map_add_le v.map_one.le v.map_one.le
      have h3 : v (3 : K) ≤ 1 := by
        simpa [show (2 : K) + 1 = 3 by norm_num] using v.map_add_le h2 v.map_one.le
      have h := bnd_mul v (bnd_mul v (bnd_const v h3 (le_refl (1 : Γ)))
        (bnd_const v ha₆ (le_refl (1 : Γ)))) hL2
      rw [one_mul, one_mul] at h
      have := bnd_weaken v h (hγpow 5)
      rwa [← pow_add] at this
    · have h2 : v (2 : K) ≤ 1 := by
        simpa [one_add_one_eq_two] using v.map_add_le v.map_one.le v.map_one.le
      have h := bnd_mul v (bnd_mul v (bnd_mul v (bnd_const v h2 (le_refl (1 : Γ)))
        (bnd_const v ha₄ (le_refl (1 : Γ)))) hLb) hμb
      rw [one_mul, one_mul, ← pow_add] at h
      have := bnd_weaken v h (hγpow 3)
      rwa [← pow_add] at this
    · have h := bnd_mul v (bnd_mul v (bnd_const v ha₁ (le_refl (1 : Γ))) hLb) hμ2
      rwa [one_mul, ← pow_add] at h
    · have h := bnd_mul v (bnd_const v ha₂ (le_refl (1 : Γ))) hμ2
      rw [one_mul] at h
      have := bnd_weaken v h (hγpow 1)
      rwa [← pow_add] at this
  have hy10 : y₁ ≠ 0 := hy0 hy₁
  have hy20 : y₂ ≠ 0 := hy0 hy₂
  have hyR0 : yR ≠ 0 := hy0 hyRv
  have hy30 : y₃ ≠ 0 := hy0 hy₃
  have hx30 : x₃ ≠ 0 := hx0 hx₃
  have hT : (x₁ / y₁ + x₂ / y₂ + x₃ / yR) * (y₁ * y₂ * yR) = S := by
    rw [div_add_div _ _ hy10 hy20, div_add_div _ _ (mul_ne_zero hy10 hy20) hyR0,
      div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero hy10 hy20) hyR0), hSdef, hy1, hy2, hyR]
    rw [hy1] at hy10; rw [hy2] at hy20; rw [hyR] at hyR0
    ring
  have hTv : v (x₁ / y₁ + x₂ / y₂ + x₃ / yR) ≤ γ ^ 2 := by
    have hY : v (y₁ * y₂ * yR) * γ ^ 9 = 1 := by
      rw [map_mul, map_mul, show (9 : ℕ) = 3 + 3 + 3 from rfl, pow_add, pow_add]
      calc v y₁ * v y₂ * v yR * (γ ^ 3 * γ ^ 3 * γ ^ 3)
          = (v y₁ * γ ^ 3) * (v y₂ * γ ^ 3) * (v yR * γ ^ 3) := by ac_rfl
        _ = 1 := by rw [hy₁, hy₂, hyRv, one_mul, one_mul]
    calc v (x₁ / y₁ + x₂ / y₂ + x₃ / yR)
        = v (x₁ / y₁ + x₂ / y₂ + x₃ / yR) * (v (y₁ * y₂ * yR) * γ ^ 9) := by rw [hY, mul_one]
      _ = v S * γ ^ 7 * γ ^ 2 := by
          rw [← mul_assoc, ← map_mul, hT, show (9 : ℕ) = 7 + 2 from rfl, pow_add, mul_assoc]
      _ ≤ 1 * γ ^ 2 := mul_le_mul' hSb le_rfl
      _ = γ ^ 2 := one_mul _
  have hU : v (x₃ / y₃ + x₃ / yR) ≤ γ ^ 2 :=
    valuation_div_add_div_le v W ha₁ ha₃ hγ1 hx₃ hy₃ hyRv (by rw [hy3R]; ring)
  have : x₃ / y₃ - x₁ / y₁ - x₂ / y₂ = (x₃ / y₃ + x₃ / yR) - (x₁ / y₁ + x₂ / y₂ + x₃ / yR) := by
    ring
  rw [this]
  exact v.map_sub_le hU hTv

end groupLaw

section eigen

private theorem exists_cast_eq_of_pow_eq_self {p : ℕ} [Fact p.Prime] {E : Type*} [Field E]
    [CharP E p] (r : E) (hr : r ^ p = r) : ∃ c : ZMod p, ZMod.castHom (dvd_refl p) E c = r := by
  have hr' : r ∈ (ZMod.castHom (m := p) dvd_rfl E).fieldRange := by
    rw [ZMod.fieldRange_castHom_eq_bot p]
    exact (Subfield.mem_bot_iff_pow_eq_self E p).mpr hr
  exact RingHom.mem_fieldRange.mp hr'

private theorem mulVec_eq_smul_of_additive_eigenfunctional {p : ℕ} [Fact p.Prime] {E : Type*}
    [Field E] [CharP E p] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (x : Module.Basis (Fin 2) (ZMod p) V) (g : V →ₗ[ZMod p] V) (φ : V →+ E)
    (hφs : ∀ (c : ZMod p) (w : V), φ (c • w) = ZMod.castHom (dvd_refl p) E c * φ w)
    (hφi : ∀ w, φ w = 0 → w = 0) (θ : E) (hθ : ∀ w, φ (g w) = θ * φ w) :
    (![φ (x 1) ^ p, -φ (x 0) ^ p] : Fin 2 → E) ≠ 0 ∧
      ((LinearMap.toMatrix x x g).map (ZMod.castHom (dvd_refl p) E)) *ᵥ
          ![φ (x 1) ^ p, -φ (x 0) ^ p] = θ • ![φ (x 1) ^ p, -φ (x 0) ^ p] := by
  classical
  set c := ZMod.castHom (dvd_refl p) E with hc
  set a := LinearMap.toMatrix x x g with ha
  have hcp : ∀ z : ZMod p, c z ^ p = c z := fun z => by rw [← map_pow, ZMod.pow_card]
  have hφ0 : φ (x 0) ≠ 0 := fun h => x.ne_zero 0 (hφi _ h)
  have hφ1 : φ (x 1) ≠ 0 := fun h => x.ne_zero 1 (hφi _ h)
  have hcol : ∀ j, g (x j) = ∑ i, a i j • x i := fun j => by
    conv_lhs => rw [← Matrix.toLin_toMatrix x x g]
    rw [Matrix.toLin_self]
  have R : ∀ j, θ * φ (x j) = ∑ i, c (a i j) * φ (x i) := by
    intro j
    rw [← hθ, hcol, map_sum]
    simp only [hφs]
  have R0 := R 0
  have R1 := R 1
  simp only [Fin.sum_univ_two] at R0 R1
  have R0' : θ ^ p * φ (x 0) ^ p = c (a 0 0) * φ (x 0) ^ p + c (a 1 0) * φ (x 1) ^ p := by
    have := congrArg (· ^ p) R0
    simpa only [mul_pow, add_pow_char, hcp] using this
  have R1' : θ ^ p * φ (x 1) ^ p = c (a 0 1) * φ (x 0) ^ p + c (a 1 1) * φ (x 1) ^ p := by
    have := congrArg (· ^ p) R1
    simpa only [mul_pow, add_pow_char, hcp] using this
  have hδ : φ (x 0) * φ (x 1) ^ p - φ (x 1) * φ (x 0) ^ p ≠ 0 := by
    intro hδ
    have hq : (φ (x 1) / φ (x 0)) ^ p = φ (x 1) / φ (x 0) := by
      rw [div_pow, div_eq_div_iff (pow_ne_zero _ hφ0) hφ0]
      linear_combination hδ
    obtain ⟨d, hd⟩ := exists_cast_eq_of_pow_eq_self _ hq
    have h1 : φ (x 1 - d • x 0) = 0 := by
      rw [map_sub, hφs, hd, div_mul_cancel₀ _ hφ0, sub_self]
    have h2 := congrArg (fun w => x.repr w 1) (hφi _ h1)
    simp at h2
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    exact hφ1 (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 this)
  · ext i
    fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta, mulVec_fin_two, map_apply, cons_val_zero,
        cons_val_one, cons_val_fin_one, mul_neg, Pi.smul_apply, smul_eq_mul]
      have key : (c (a 0 0) * φ (x 1) ^ p - c (a 0 1) * φ (x 0) ^ p - θ * φ (x 1) ^ p) *
          (φ (x 0) * φ (x 1) ^ p - φ (x 1) * φ (x 0) ^ p) = 0 := by
        linear_combination (-(φ (x 1) ^ p * φ (x 1) ^ p)) * R0 + (φ (x 0) ^ p * φ (x 1) ^ p) * R1
          + (φ (x 1) * φ (x 1) ^ p) * R0' - (φ (x 1) * φ (x 0) ^ p) * R1'
      have := (mul_eq_zero.1 key).resolve_right hδ
      linear_combination this
    · simp only [Fin.isValue, Fin.mk_one, mulVec_fin_two, map_apply, cons_val_zero,
        cons_val_one, cons_val_fin_one, mul_neg, Pi.smul_apply, smul_eq_mul]
      have key : (c (a 1 0) * φ (x 1) ^ p - c (a 1 1) * φ (x 0) ^ p + θ * φ (x 0) ^ p) *
          (φ (x 0) * φ (x 1) ^ p - φ (x 1) * φ (x 0) ^ p) = 0 := by
        linear_combination (φ (x 1) ^ p * φ (x 0) ^ p) * R0 - (φ (x 0) ^ p * φ (x 0) ^ p) * R1
          - (φ (x 0) * φ (x 1) ^ p) * R0' + (φ (x 0) * φ (x 0) ^ p) * R1'
      have := (mul_eq_zero.1 key).resolve_right hδ
      linear_combination this

end eigen

section transport

private theorem transport_eigenvector {p : ℕ} [Fact p.Prime] {k : Type*} [Field k]
    (ι : ZMod p →+* k) (R : ResidualGaloisRep (ZMod p))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k)
    (b : Module.Basis (Fin 2) k (R.baseChangeAlong ι).V)
    (hρ : ∀ σ, (ρ σ).val = LinearMap.toMatrix b b ((R.baseChangeAlong ι).ρ σ))
    {E : Type*} [Field E] (ψ : k →+* E)
    (x : Module.Basis (Fin 2) (ZMod p) R.V) (v : Fin 2 → E) (hv : v ≠ 0) :
    ∃ C : Matrix (Fin 2) (Fin 2) E, C *ᵥ v ≠ 0 ∧
      ∀ σ, (Matrix.GeneralLinearGroup.map ψ (ρ σ)).val *ᵥ (C *ᵥ v) =
        C *ᵥ (((LinearMap.toMatrix x x (R.ρ σ)).map (ψ.comp ι)) *ᵥ v) := by
  classical
  let : Algebra (ZMod p) k := ι.toAlgebra
  let xk : Module.Basis (Fin 2) k (R.baseChangeAlong ι).V := Algebra.TensorProduct.basis k x
  have hxk : ∀ σ, LinearMap.toMatrix xk xk ((R.baseChangeAlong ι).ρ σ) =
      (LinearMap.toMatrix x x (R.ρ σ)).map ι := fun σ =>
    LinearMap.toMatrix_baseChange k (R.ρ σ) x x
  refine ⟨(b.toMatrix xk).map ψ, ?_, fun σ => ?_⟩
  · intro h
    apply hv
    have h1 : (xk.toMatrix b).map ψ * (b.toMatrix xk).map ψ = 1 := by
      rw [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
        Matrix.map_one _ (map_zero ψ) (map_one ψ)]
    have := congrArg ((xk.toMatrix b).map ψ *ᵥ ·) h
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_zero] using this
  · have hval : (Matrix.GeneralLinearGroup.map ψ (ρ σ)).val = (ρ σ).val.map ψ := rfl
    rw [hval, hρ σ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b xk b xk, hxk,
      Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ (map_zero ψ) (map_one ψ), Matrix.mul_one]
    rfl

end transport

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point IsLocalRing
open scoped WeierstrassCurve.Affine

section red
variable {K : Type*} [Field K] (A : ValuationSubring K)

private noncomputable def red (z : K) : ResidueField A := by
  classical
  exact if h : z ∈ A then residue A ⟨z, h⟩ else 0

private lemma red_of_mem {z : K} (h : z ∈ A) : red A z = residue A ⟨z, h⟩ := by
  classical
  exact dite_eq_left h

private lemma red_zero : red A 0 = 0 := by
  rw [red_of_mem A A.zero_mem]; exact map_zero _

private lemma red_add {a b : K} (ha : a ∈ A) (hb : b ∈ A) : red A (a + b) = red A a + red A b := by
  rw [red_of_mem A ha, red_of_mem A hb, red_of_mem A (A.add_mem _ _ ha hb), ← map_add]; rfl

private lemma red_eq_zero_of_lt {a : K} (h : A.valuation a < 1) : red A a = 0 := by
  have ha : a ∈ A := (A.valuation_le_one_iff a).1 h.le
  rw [red_of_mem A ha, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact h

private lemma red_eq_of_sub {a b : K} (ha : a ∈ A) (hb : b ∈ A) (h : A.valuation (a - b) < 1) :
    red A a = red A b := by
  have : a = (a - b) + b := by ring
  rw [this, red_add A (sub_mem ha hb) hb, red_eq_zero_of_lt A h, zero_add]

private lemma red_ne_zero_of_eq_one {a : K} (h : A.valuation a = 1) : red A a ≠ 0 := by
  have ha : a ∈ A := (A.valuation_le_one_iff a).1 h.le
  rw [red_of_mem A ha, Ne, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact fun h' => (lt_irrefl _) (h ▸ h' : A.valuation a < A.valuation a)

end red

private noncomputable def tPar {F : Type*} [Field F] {W : Affine F} : W.Point → F
  | .zero => 0
  | .some x y _ => x / y

private lemma tPar_zero {F : Type*} [Field F] {W : Affine F} : tPar (0 : W.Point) = 0 := rfl
private lemma tPar_some {F : Type*} [Field F] {W : Affine F} {x y : F} (h : W.Nonsingular x y) :
    tPar (Point.some x y h) = x / y := rfl

section curve

variable (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]

local notation "K" => AlgebraicClosure ℚ
local notation "E" => WeierstrassCurve.map W (Int.castRingHom ℚ)

private lemma baseChange_a (A : ValuationSubring K) :
    A.valuation (E⁄K).a₁ ≤ 1 ∧ A.valuation (E⁄K).a₂ ≤ 1 ∧ A.valuation (E⁄K).a₃ ≤ 1 ∧
      A.valuation (E⁄K).a₄ ≤ 1 ∧ A.valuation (E⁄K).a₆ ≤ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [ValuationSubring.valuation_le_one_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eq_intCast,
      map_intCast]
    exact intCast_mem A _

variable (hp2 : p ≠ 2) (hgood : W.IsGoodPrimeFor p)
  (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
  (A : ValuationSubring K) (hA : A.LiesOverPrime p) (π : K) (hπ : π ^ (p ^ 2 - 1) = p)

include hp2 hπ hA in
private lemma gamma_facts : A.valuation π ≠ 0 ∧ A.valuation π < 1 ∧
    A.valuation (p : K) = (A.valuation π ^ 2) ^ ((p ^ 2 - 1) / 2) ∧ (p ^ 2 - 1) / 2 ≠ 0 := by
  have hp : p.Prime := Fact.out
  have heven : 2 * ((p ^ 2 - 1) / 2) = p ^ 2 - 1 :=
    Nat.two_mul_div_two_of_even (Nat.Odd.sub_odd (Odd.pow (hp.odd_of_ne_two hp2)) odd_one)
  have hm : (p ^ 2 - 1) / 2 ≠ 0 := by
    intro h
    have h3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · exact absurd h2 hp2
      · have := hp.two_le; omega
    have : 9 ≤ p ^ 2 := by nlinarith
    omega
  have hvp : A.valuation (p : K) = (A.valuation π ^ 2) ^ ((p ^ 2 - 1) / 2) := by
    rw [← pow_mul, heven, ← map_pow, hπ]
  have hlt : A.valuation (p : K) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  refine ⟨?_, ?_, hvp, hm⟩
  · intro h0
    rw [Valuation.zero_iff] at h0
    rw [h0, zero_pow (by omega)] at hπ
    exact hp.ne_zero (by exact_mod_cast hπ.symm)
  · by_contra hge
    push Not at hge
    have : 1 ≤ A.valuation (p : K) := by
      rw [hvp]; exact one_le_pow₀ (one_le_pow₀ hge)
    exact absurd hlt (not_lt.2 this)

include hp2 hgood hss hA hπ in
private lemma coord_val {x y : K} (h : (E⁄K).Nonsingular x y)
    (hP : (Point.some x y h : (E⁄K).Point) ∈ Submodule.torsionBy ℤ (E⁄K).Point p) :
    A.valuation x * A.valuation π ^ 2 = 1 ∧ A.valuation y * A.valuation π ^ 3 = 1 := by
  obtain ⟨hγ0, hγ1, hvp, hm⟩ := gamma_facts p hp2 A hA π hπ
  have hP' : p • (Point.some x y h : (E⁄K).Point) = 0 := by
    have := (Submodule.mem_torsionBy_iff _ _).1 hP
    rwa [Nat.cast_smul_eq_nsmul] at this
  obtain ⟨h1, h2⟩ := W.valuation_torsion_of_coeff_prePsi_dvd p hp2 hgood hss A hA x y h hP'
  have hx : A.valuation x * A.valuation π ^ 2 = 1 := by
    have : (A.valuation x * A.valuation π ^ 2) ^ ((p ^ 2 - 1) / 2) = 1 := by
      rw [mul_pow, ← hvp, h1]
    exact (pow_eq_one_iff.1 this).resolve_right hm
  refine ⟨hx, ?_⟩
  have : (A.valuation y * A.valuation π ^ 3) ^ 2 = 1 := by
    calc (A.valuation y * A.valuation π ^ 3) ^ 2 = A.valuation y ^ 2 * (A.valuation π ^ 2) ^ 3 := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
      _ = (A.valuation x * A.valuation π ^ 2) ^ 3 := by rw [h2, mul_pow]
      _ = 1 := by rw [hx, one_pow]
  exact (pow_eq_one_iff.1 this).resolve_right two_ne_zero

include hp2 hgood hss hA hπ in
private lemma tPar_val {x y : K} (h : (E⁄K).Nonsingular x y)
    (hP : (Point.some x y h : (E⁄K).Point) ∈ Submodule.torsionBy ℤ (E⁄K).Point p) :
    A.valuation (x / y / π) = 1 := by
  obtain ⟨hγ0, -, -, -⟩ := gamma_facts p hp2 A hA π hπ
  obtain ⟨hx, hy⟩ := coord_val W p hp2 hgood hss A hA π hπ h hP
  have hy0 : A.valuation y ≠ 0 := by intro h0; rw [h0, zero_mul] at hy; exact zero_ne_one hy
  rw [map_div₀, map_div₀, div_div, div_eq_one_iff_eq (mul_ne_zero hy0 hγ0)]
  calc A.valuation x = A.valuation x * (A.valuation y * A.valuation π ^ 3) := by rw [hy, mul_one]
    _ = A.valuation x * A.valuation π ^ 2 * (A.valuation y * A.valuation π) := by
        rw [pow_succ]; ac_rfl
    _ = A.valuation y * A.valuation π := by rw [hx, one_mul]

private noncomputable def phi (Q : Submodule.torsionBy ℤ (E⁄K).Point p) : ResidueField A :=
  red A (tPar (Q : (E⁄K).Point) / π)

include hp2 hgood hss hA hπ in
private lemma phi_ne_zero {Q : Submodule.torsionBy ℤ (E⁄K).Point p} (hQ : Q ≠ 0) :
    phi W p A π Q ≠ 0 := by
  obtain ⟨Q, hQmem⟩ := Q
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl hQ
  · exact red_ne_zero_of_eq_one A (tPar_val W p hp2 hgood hss A hA π hπ h hQmem)

omit [Fact p.Prime] in
private lemma phi_zero : phi W p A π 0 = 0 := by
  simp only [phi, Submodule.coe_zero, tPar_zero, zero_div, red_zero]

include hp2 hπ hA in
private lemma val_div_pi_lt_one {z : K} (hz : A.valuation z ≤ A.valuation π ^ 2) :
    A.valuation (z / π) < 1 := by
  obtain ⟨hγ0, hγ1, -, -⟩ := gamma_facts p hp2 A hA π hπ
  have hπ0 : π ≠ 0 := fun h => hγ0 (by rw [h, Valuation.map_zero])
  have e : A.valuation (z / π) * A.valuation π = A.valuation z := by
    rw [← map_mul, div_mul_cancel₀ _ hπ0]
  apply lt_of_mul_lt_mul_right' (a := A.valuation π)
  rw [e, one_mul]
  calc A.valuation z ≤ A.valuation π ^ 2 := hz
    _ = A.valuation π * A.valuation π := pow_two _
    _ < 1 * A.valuation π := mul_lt_mul_of_pos_right hγ1 (zero_lt_iff.2 hγ0)
    _ = A.valuation π := one_mul _

include hp2 hgood hss hA hπ in
private lemma phi_add (Q₁ Q₂ : Submodule.torsionBy ℤ (E⁄K).Point p) :
    phi W p A π (Q₁ + Q₂) = phi W p A π Q₁ + phi W p A π Q₂ := by
  obtain ⟨hγ0, hγ1, -, -⟩ := gamma_facts p hp2 A hA π hπ
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := baseChange_a W A
  obtain ⟨P₁, hP₁⟩ := Q₁
  obtain ⟨P₂, hP₂⟩ := Q₂
  simp only [phi, Submodule.coe_add]
  rcases P₁ with _ | ⟨x₁, y₁, h₁⟩
  · change red A (tPar ((0 : (E⁄K).Point) + P₂) / π) =
      red A (tPar (0 : (E⁄K).Point) / π) + red A (tPar P₂ / π)
    rw [zero_add, tPar_zero, zero_div, red_zero, zero_add]
  rcases P₂ with _ | ⟨x₂, y₂, h₂⟩
  · change red A (tPar (Point.some x₁ y₁ h₁ + (0 : (E⁄K).Point)) / π) =
      red A (tPar (Point.some x₁ y₁ h₁) / π) + red A (tPar (0 : (E⁄K).Point) / π)
    rw [add_zero, tPar_zero, zero_div, red_zero, add_zero]
  obtain ⟨hx₁, hy₁⟩ := coord_val W p hp2 hgood hss A hA π hπ h₁ hP₁
  obtain ⟨hx₂, hy₂⟩ := coord_val W p hp2 hgood hss A hA π hπ h₂ hP₂
  have mem₁ : x₁ / y₁ / π ∈ A :=
    (A.valuation_le_one_iff _).1 (tPar_val W p hp2 hgood hss A hA π hπ h₁ hP₁).le
  have mem₂ : x₂ / y₂ / π ∈ A :=
    (A.valuation_le_one_iff _).1 (tPar_val W p hp2 hgood hss A hA π hπ h₂ hP₂).le
  by_cases hxy : x₁ = x₂ ∧ y₁ = (E⁄K).negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2, tPar_zero, zero_div, red_zero, tPar_some, tPar_some,
      ← red_add A mem₁ mem₂, eq_comm]
    apply red_eq_zero_of_lt
    have : x₁ / y₁ / π + x₂ / y₂ / π = (x₁ / y₁ + x₁ / y₂) / π := by rw [hxy.1]; ring
    rw [this]
    refine val_div_pi_lt_one p hp2 A hA π hπ ?_
    refine valuation_div_add_div_le A.valuation (E⁄K) ha₁ ha₃ hγ1 hx₁ hy₁ hy₂ ?_
    rw [hxy.2, hxy.1, WeierstrassCurve.Affine.negY]; ring
  · rw [add_some hxy, tPar_some, tPar_some, tPar_some, ← red_add A mem₁ mem₂]
    have hP₃ : (Point.some _ _ (nonsingular_add h₁ h₂ hxy) : (E⁄K).Point) ∈
        Submodule.torsionBy ℤ (E⁄K).Point p := by
      rw [← add_some (h₁ := h₁) (h₂ := h₂) hxy]; exact add_mem hP₁ hP₂
    obtain ⟨hx₃, hy₃⟩ := coord_val W p hp2 hgood hss A hA π hπ _ hP₃
    refine red_eq_of_sub A ((A.valuation_le_one_iff _).1
      (tPar_val W p hp2 hgood hss A hA π hπ _ hP₃).le) (add_mem mem₁ mem₂) ?_
    have : (E⁄K).addX x₁ x₂ ((E⁄K).slope x₁ x₂ y₁ y₂) /
          (E⁄K).addY x₁ x₂ y₁ ((E⁄K).slope x₁ x₂ y₁ y₂) / π - (x₁ / y₁ / π + x₂ / y₂ / π) =
        ((E⁄K).addX x₁ x₂ ((E⁄K).slope x₁ x₂ y₁ y₂) /
          (E⁄K).addY x₁ x₂ y₁ ((E⁄K).slope x₁ x₂ y₁ y₂) - x₁ / y₁ - x₂ / y₂) / π := by ring
    rw [this]
    exact val_div_pi_lt_one p hp2 A hA π hπ (valuation_addX_div_addY_sub_le A.valuation (E⁄K)
      ha₁ ha₂ ha₃ ha₄ ha₆ hγ1 h₁.1 h₂.1 hxy hx₁ hx₂ hy₁ hy₂ hx₃ hy₃)

include hp2 hgood hss hA hπ in
private lemma phi_smul {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (Q : Submodule.torsionBy ℤ (E⁄K).Point p) :
    phi W p A π (σ • Q) = A.tameCharacter π σ * phi W p A π Q := by
  obtain ⟨hγ0, hγ1, -, -⟩ := gamma_facts p hp2 A hA π hπ
  have hπ0 : π ≠ 0 := fun h => hγ0 (by rw [h, Valuation.map_zero])
  obtain ⟨hK1, hK2⟩ :=
    ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn A hσ
  obtain ⟨P, hP⟩ := Q
  change red A (tPar (σ • P) / π) = _ * red A (tPar P / π)
  rcases P with _ | ⟨x, y, h⟩
  · change red A (tPar (0 : (E⁄K).Point) / π) = _ * red A (tPar (0 : (E⁄K).Point) / π)
    rw [tPar_zero, zero_div, red_zero, mul_zero]
  · rw [algEquiv_smul_def, map_some, tPar_some, tPar_some]
    change red A (σ x / σ y / π) = _
    have hu : A.valuation (x / y / π) = 1 := tPar_val W p hp2 hgood hss A hA π hπ h hP
    set u : K := x / y / π with hudef
    have hu_mem : u ∈ A := (A.valuation_le_one_iff _).1 hu.le
    have hunit : IsUnit (⟨u, hu_mem⟩ : A) := (A.valuation_eq_one_iff _).2 hu
    obtain ⟨u', hu'⟩ := hunit
    have hu0 : u ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at hu; exact zero_ne_one hu
    obtain ⟨aπ, haπ, hraπ⟩ := hK1 π hπ0
    obtain ⟨au, hau, hrau⟩ := hK1 u hu0
    have hone : A.tameCharacter u σ = 1 := by
      have := hK2 u'
      rwa [hu'] at this
    have key : σ x / σ y / π = ((au : A) : K) * ((aπ : A) : K) * u := by
      have hxy : x / y = u * π := by rw [hudef, div_mul_cancel₀ _ hπ0]
      rw [← map_div₀, hxy, map_mul, ← hau, ← haπ]
      field_simp
    have hmem : ((au : A) : K) * ((aπ : A) : K) * u ∈ A :=
      mul_mem (mul_mem (au : A).2 (aπ : A).2) hu_mem
    rw [key, red_of_mem A hmem, red_of_mem A hu_mem]
    have : (⟨((au : A) : K) * ((aπ : A) : K) * u, hmem⟩ : A) = (au : A) * (aπ : A) * ⟨u, hu_mem⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, hrau, hraπ, hone, one_mul]

private noncomputable def phiHom : Submodule.torsionBy ℤ (E⁄K).Point p →+ ResidueField A where
  toFun := phi W p A π
  map_zero' := phi_zero W p A π
  map_add' := phi_add W p hp2 hgood hss A hA π hπ

end curve

end SSInertia

namespace WeierstrassCurve

open SSInertia
open scoped WeierstrassCurve.Affine

/-- Let `W` be an integral Weierstrass curve with good supersingular reduction at an odd prime `p`
(the inner coefficients of the `p`-division polynomial are divisible by `p`). Assume that the
`p`-torsion of `W` over `AlgebraicClosure ℚ` has `p ^ 2` points and that the Galois action on it
is trivial on the automorphisms fixing some finite extension of `ℚ`; these two hypotheses define
the residual representation of `W` at `p`. Then for every valuation subring `P` over `p` and every
root `π` of `π ^ (p ^ 2 - 1) = p`, any matrix form `ρ` of this representation after extension of
scalars to a finite field `k` has, after a suitable embedding of `k` into the residue field of `P`,
a nonzero vector on which inertia at `P` acts through the tame character attached to `π`. -/
theorem exists_inertia_mulVec_eq_tameCharacter_smul_of_supersingular
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {k : Type*} [Field k] [Finite k]
    (ι : ZMod p →+* k) (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k)
    (b : Module.Basis (Fin 2) k
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).V)
    (hρ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ σ).val =
      LinearMap.toMatrix b b
        ((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).ρ σ))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = p) :
    ∃ ψk : k →+* IsLocalRing.ResidueField P,
      ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (Matrix.GeneralLinearGroup.map ψk (ρ σ)).val.mulVec v = P.tameCharacter π σ • v := by
  have : CharP (IsLocalRing.ResidueField P) p :=
    ValuationSubring.charP_residueField_of_liesOverPrime P p hP
  have : IsAlgClosed (IsLocalRing.ResidueField P) := ValuationSubring.isAlgClosed_residueField P
  let algk : Algebra (ZMod p) k := ι.toAlgebra
  let algE : Algebra (ZMod p) (IsLocalRing.ResidueField P) := ZMod.algebra _ p
  have : Algebra.IsAlgebraic (ZMod p) k := Algebra.IsAlgebraic.of_finite (ZMod p) k
  let ψk : k →+* IsLocalRing.ResidueField P :=
    (IsAlgClosed.lift : k →ₐ[ZMod p] IsLocalRing.ResidueField P).toRingHom
  have hψι : ψk.comp ι = ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField P) :=
    RingHom.ext_zmod _ _
  let R := (W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker
  let xB : Module.Basis (Fin 2) (ZMod p) R.V := Module.finBasisOfFinrankEq _ _ R.finrank_eq
  let φ : R.V →+ IsLocalRing.ResidueField P := phiHom W p hp2 hgood hss P hP π hπ
  have hφs : ∀ (c : ZMod p) (w : R.V),
      φ (c • w) = ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField P) c * φ w := by
    intro c w
    conv_lhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    rw [← ZMod.natCast_zmod_val c, map_natCast, ZMod.natCast_zmod_val]
  have hφi : ∀ w : R.V, φ w = 0 → w = 0 := fun w hw => by
    by_contra hne
    exact phi_ne_zero W p hp2 hgood hss P hP π hπ hne hw
  have hθ : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : R.V,
      φ (R.ρ σ w) = P.tameCharacter π σ * φ w := fun σ hσ w =>
    phi_smul W p hp2 hgood hss P hP π hπ hσ w
  set vec : Fin 2 → IsLocalRing.ResidueField P := ![φ (xB 1) ^ p, -φ (xB 0) ^ p] with hvec
  have heig : ∀ σ ∈ P.inertiaSubgroupIn ℚ, vec ≠ 0 ∧
      ((LinearMap.toMatrix xB xB (R.ρ σ)).map
        (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField P))) *ᵥ vec =
        P.tameCharacter π σ • vec := fun σ hσ =>
    mulVec_eq_smul_of_additive_eigenfunctional xB (R.ρ σ) φ hφs hφi _ (hθ σ hσ)
  have hvec0 : vec ≠ 0 := (heig 1 (Subgroup.one_mem _)).1
  obtain ⟨C, hC0, hC⟩ := transport_eigenvector ι R ρ b hρ ψk xB vec hvec0
  refine ⟨ψk, C *ᵥ vec, hC0, fun σ hσ => ?_⟩
  rw [hC σ, hψι, (heig σ hσ).2, Matrix.mulVec_smul]

/-- Let `W` be an integral Weierstrass curve with good supersingular reduction at an odd prime `p`
(the inner coefficients of the `p`-division polynomial are divisible by `p`). Assume that the
`p`-torsion of `W` over `AlgebraicClosure ℚ` has `p ^ 2` points and that the Galois action on it
is trivial on the automorphisms fixing some finite extension of `ℚ`; these two hypotheses define
the residual representation of `W` at `p`. Then for every valuation subring `P` over `p` and every
root `π` of `π ^ (p ^ 2 - 1) = p`, any matrix form `ρ` of this representation after extension of
scalars to a finite field `k` has, after a suitable embedding of `k` into the residue field of `P`,
a nonzero vector on which inertia at `P` acts through the tame character attached to `π`, or
through its `p`-th power. -/
theorem exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {k : Type*} [Field k] [Finite k]
    (ι : ZMod p →+* k) (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k)
    (b : Module.Basis (Fin 2) k
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).V)
    (hρ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ σ).val =
      LinearMap.toMatrix b b
        ((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).ρ σ))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = p) :
    ∃ ψk : k →+* IsLocalRing.ResidueField P,
      ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
        ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (Matrix.GeneralLinearGroup.map ψk (ρ σ)).val.mulVec v = P.tameCharacter π σ • v) ∨
          (∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (Matrix.GeneralLinearGroup.map ψk (ρ σ)).val.mulVec v =
              P.tameCharacter π σ ^ p • v)) := by
  obtain ⟨ψk, v, hv, h⟩ := exists_inertia_mulVec_eq_tameCharacter_smul_of_supersingular W p hp2 ι
    hgood hss hcard hker ρ b hρ P hP π hπ
  exact ⟨ψk, v, hv, Or.inl h⟩

end WeierstrassCurve
