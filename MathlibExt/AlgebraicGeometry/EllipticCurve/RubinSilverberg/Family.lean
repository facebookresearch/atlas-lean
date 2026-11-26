/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_RubinSilverberg_Psi3_eval_ne_zero_of_rsFamily.lean`,
`Theorems/Thm_RubinSilverberg_rsMember_Psi3_eval_ne_zero.lean`,
`P2M/Sol/S_RubinSilverberg_Psi3_eval_ne_zero_of_rsFamily.lean`
and
`P2M/Sol/S_RubinSilverberg_rsMember_Psi3_eval_ne_zero.lean`
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

public import MathlibExt.AlgebraicGeometry.EllipticCurve.RubinSilverberg.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import MathlibExt.AlgebraicGeometry.EllipticCurve.RubinSilverberg.KleinCurve
import MathlibExt.FieldTheory.RatFunc.Moebius
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The `3`-division polynomial of a Rubin–Silverberg family member

Let `K` be a field of characteristic zero containing a primitive fifth root of unity. For a
Klein datum `u₀ ∈ K` of `y² = x³ + a x + b` with `a b ≠ 0` and a parameter `l ∈ K`, the generic
member `rsMember a b u₀ l t` of the Rubin–Silverberg family (with `t` transcendental) is a
quadratic twist of `kleinCurve` evaluated at a Möbius transform of `t`. Since the `3`-division
polynomial of `kleinCurve u` has no root in `K(u)`, neither does that of the family member.

## Main statements

* `RubinSilverberg.rsMember_Psi3_eval_ne_zero`: for `K` of characteristic zero containing a
  primitive fifth root of unity, `Ψ₃` of the generic member over `K(t)` has no root.
* `RubinSilverberg.Psi3_eval_ne_zero_of_rsFamily`: the same over `K[t]`, for `K` a subfield of
  an algebraically closed field `F` of characteristic zero, a base point `u₀ ∈ F` and `l ∈ K`,
  when the family's coefficients `A(t)`, `B(t)` are polynomials over `K`.
-/

@[expose] public section

open Polynomial

namespace RubinSilverberg

private theorem psi3_short_eval {K : Type*} [Field K] (A B x : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).Ψ₃).eval x =
      3 * x ^ 4 + 6 * A * x ^ 2 + 12 * B * x - A ^ 2 := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
  ring

section generic

variable {K : Type*} [Field K] [CharZero K]

private theorem kleinCurve_map (φ : RatFunc K ≃ₐ[K] RatFunc K) (u : RatFunc K) :
    (kleinCurve u).map φ.toRingEquiv.toRingHom = kleinCurve (φ u) := by
  simp only [kleinCurve, WeierstrassCurve.map]
  ext <;> simp [map_div₀, map_neg, map_kleinH, map_kleinT, map_ofNat]

private theorem psi3_kleinCurve_transport (φ : RatFunc K ≃ₐ[K] RatFunc K) (y : RatFunc K) :
    ((kleinCurve (φ RatFunc.X)).Ψ₃).eval y =
      φ (((kleinCurve (RatFunc.X : RatFunc K)).Ψ₃).eval (φ.symm y)) := by
  rw [← kleinCurve_map, WeierstrassCurve.map_Ψ₃, eval_map]
  conv_lhs => rw [show y = φ.toRingEquiv.toRingHom (φ.symm y) by simp]
  rw [eval₂_at_apply]
  rfl

/-- Let `K` be a field of characteristic zero containing a primitive fifth root of unity. Over
`K(t)`, the `3`-division polynomial of the generic member of the Rubin–Silverberg family attached
to a Klein datum `u₀` of `y² = x³ + a x + b` with `a b ≠ 0` and a parameter `l ∈ K` has no
root. -/
theorem rsMember_Psi3_eval_ne_zero (ζ : K) (hζ : IsPrimitiveRoot ζ 5) {a b u₀ : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hu₀ : IsKleinDatum a b u₀) (l : K) (x : RatFunc K) :
    ((rsMember (RatFunc.C a) (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l)
      (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 := by
  have hH0 : kleinH u₀ ≠ 0 := hu₀.kleinH_ne_zero ha
  have hT0 : kleinT u₀ ≠ 0 := hu₀.kleinT_ne_zero hb
  have hV : kleinV u₀ ≠ 0 := hu₀.2
  have hu0 : u₀ ≠ 0 := fun h ↦ hV (by rw [kleinV, h, zero_mul])
  have hf : u₀ ^ 10 + 11 * u₀ ^ 5 - 1 ≠ 0 := fun h ↦ hV (by rw [kleinV, h, mul_zero])
  have hrel : 27 * b ^ 2 * kleinH u₀ ^ 3 + 4 * a ^ 3 * kleinT u₀ ^ 2 = 0 := by
    linear_combination hu₀.1 + 4 * a ^ 3 * kleinT_sq_sub_kleinH_cube u₀
  have hdet : (rsBeta u₀ + l * u₀) * 1 - u₀ * (rsGamma u₀ + l) ≠ 0 := by
    rw [show (rsBeta u₀ + l * u₀) * 1 - u₀ * (rsGamma u₀ + l) = rsBeta u₀ - u₀ * rsGamma u₀ by
      ring, rsBeta_sub_mul_rsGamma u₀]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hT0 hH0))
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hu0)) (pow_ne_zero 4 hf))
  obtain ⟨φ, hφ⟩ :=
    RatFunc.exists_algEquiv_apply_X_eq_moebius (rsBeta u₀ + l * u₀) u₀ (rsGamma u₀ + l) 1 hdet
  set D : RatFunc K := RatFunc.C (rsGamma u₀ + l) * RatFunc.X + RatFunc.C 1 with hD_def
  set N : RatFunc K := RatFunc.C (rsBeta u₀ + l * u₀) * RatFunc.X + RatFunc.C u₀ with hN_def
  have hD : D ≠ 0 := by
    intro h0
    have : (RatFunc.C (rsGamma u₀ + l) * RatFunc.X + RatFunc.C 1 : RatFunc K) =
        algebraMap K[X] (RatFunc K) (Polynomial.C (rsGamma u₀ + l) * Polynomial.X + 1) := by
      simp
    rw [hD_def, this, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))] at h0
    have := congrArg (fun p : K[X] ↦ p.coeff 0) h0
    simp at this
  have hm : φ RatFunc.X = N / D := hφ
  have hN : rsNum (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : RatFunc K) = N := by
    simp only [rsNum, hN_def, ← map_rsBeta, map_add, map_mul]
  have hDD : rsDen (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : RatFunc K) = D := by
    simp only [rsDen, hD_def, ← map_rsGamma, map_add, map_one]
  have hHH : kleinHHom N D = D ^ 20 * kleinH (φ RatFunc.X) := by
    rw [hm, ← kleinHHom_one, ← kleinHHom_mul_mul, mul_div_cancel₀ _ hD, mul_one]
  have hTT : kleinTHom N D = D ^ 30 * kleinT (φ RatFunc.X) := by
    rw [hm, ← kleinTHom_one, ← kleinTHom_mul_mul, mul_div_cancel₀ _ hD, mul_one]
  set κ : K := -18 * b / a * kleinH u₀ / kleinT u₀ with hκ
  set ν : RatFunc K := RatFunc.C κ * D ^ 10 with hν_def
  have hκ0 : κ ≠ 0 :=
    div_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) hb) ha) hH0) hT0
  have hν0 : ν ≠ 0 := mul_ne_zero ((_root_.map_ne_zero RatFunc.C).mpr hκ0) (pow_ne_zero 10 hD)
  have hκ2 : κ ^ 2 = -48 * a / kleinH u₀ := by
    rw [hκ]
    field_simp
    linear_combination 12 * hrel
  have hκ3 : κ ^ 3 = 864 * b / kleinT u₀ := by
    rw [pow_succ, hκ2, hκ]
    field_simp
    norm_num
  have hν2 : ν ^ 2 = RatFunc.C (-48 * a / kleinH u₀) * D ^ 20 := by
    rw [hν_def, mul_pow, ← pow_mul, ← map_pow, hκ2]
  have hν3 : ν ^ 3 = RatFunc.C (864 * b / kleinT u₀) * D ^ 30 := by
    rw [hν_def, mul_pow, ← pow_mul, ← map_pow, hκ3]
  have hCH : (RatFunc.C (kleinH u₀) : RatFunc K) ≠ 0 := (_root_.map_ne_zero _).mpr hH0
  have hCT : (RatFunc.C (kleinT u₀) : RatFunc K) ≠ 0 := (_root_.map_ne_zero _).mpr hT0
  have hA : rsFamilyA (RatFunc.C a) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : RatFunc K) =
      ν ^ 2 * (-kleinH (φ RatFunc.X) / 48) := by
    rw [rsFamilyA, hN, hDD, hHH, hν2, ← map_kleinH RatFunc.C u₀, map_div₀, map_mul, map_neg,
      map_ofNat]
    field_simp
  have hB : rsFamilyB (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : RatFunc K) =
      ν ^ 3 * (kleinT (φ RatFunc.X) / 864) := by
    rw [rsFamilyB, hN, hDD, hTT, hν3, ← map_kleinT RatFunc.C u₀, map_div₀, map_mul, map_ofNat]
    field_simp
  have hscale : ((rsMember (RatFunc.C a) (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l)
      (RatFunc.X : RatFunc K)).Ψ₃).eval x
        = ν ^ 4 * ((kleinCurve (φ RatFunc.X)).Ψ₃).eval (x / ν) := by
    rw [rsMember, hA, hB, kleinCurve, psi3_short_eval, psi3_short_eval]
    field_simp
  rw [hscale, psi3_kleinCurve_transport]
  exact mul_ne_zero (pow_ne_zero 4 hν0)
    ((_root_.map_ne_zero φ).mpr (kleinCurve_Psi3_eval_ne_zero ζ hζ (φ.symm (x / ν))))

end generic

section descent

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem rsFamilyA_eq_aeval (a u₀ l : K) (x : F) :
    rsFamilyA (algebraMap K F a) (algebraMap K F u₀) (algebraMap K F l) x =
      aeval x (C (a / kleinH u₀) *
        kleinHHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1)) := by
  rw [map_mul, map_kleinHHom, aeval_C]
  simp only [map_add, map_mul, aeval_C, aeval_X, map_one, rsFamilyA, rsNum, rsDen, ← map_rsBeta,
    ← map_rsGamma, ← map_kleinH, map_div₀]
  ring

private theorem rsFamilyB_eq_aeval (b u₀ l : K) (x : F) :
    rsFamilyB (algebraMap K F b) (algebraMap K F u₀) (algebraMap K F l) x =
      aeval x (C (b / kleinT u₀) *
        kleinTHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1)) := by
  rw [map_mul, map_kleinTHom, aeval_C]
  simp only [map_add, map_mul, aeval_C, aeval_X, map_one, rsFamilyB, rsNum, rsDen, ← map_rsBeta,
    ← map_rsGamma, ← map_kleinT, map_div₀]
  ring

variable [Infinite F]

private theorem map_eq_rsFamilyA_poly {a l : K} {u₀ : F} {pa : K[X]}
    (h : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t =
      (pa.map (algebraMap K F)).eval t) :
    pa.map (algebraMap K F) = C (algebraMap K F a / kleinH u₀) *
      kleinHHom (C (rsBeta u₀ + algebraMap K F l * u₀) * X + C u₀)
        (C (rsGamma u₀ + algebraMap K F l) * X + 1) := by
  apply Polynomial.funext
  intro t
  rw [← h t, ← coe_aeval_eq_eval, ← rsFamilyA_eq_aeval (K := F) (F := F)]
  simp

private theorem map_eq_rsFamilyB_poly {b l : K} {u₀ : F} {pb : K[X]}
    (h : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t =
      (pb.map (algebraMap K F)).eval t) :
    pb.map (algebraMap K F) = C (algebraMap K F b / kleinT u₀) *
      kleinTHom (C (rsBeta u₀ + algebraMap K F l * u₀) * X + C u₀)
        (C (rsGamma u₀ + algebraMap K F l) * X + 1) := by
  apply Polynomial.funext
  intro t
  rw [← h t, ← coe_aeval_eq_eval, ← rsFamilyB_eq_aeval (K := F) (F := F)]
  simp

end descent

/-- Let `K ⊆ F` with `F` algebraically closed of characteristic zero, and let `u₀ ∈ F` be a
Klein datum for `y² = x³ + a x + b` with `a, b ∈ K` nonzero. If, for some `l ∈ K`, the
Rubin–Silverberg coefficients `A(t)`, `B(t)` of the family through `u₀` with parameter `l` are
given by polynomials `pa`, `pb` over `K`, then the `3`-division polynomial of
`y² = x³ + pa x + pb` over `K[t]` has no root in `K[t]`. -/
theorem Psi3_eval_ne_zero_of_rsFamily {K F : Type*} [Field K] [Field F] [CharZero F]
    [IsAlgClosed F] [Algebra K F] {a b l : K} {u₀ : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hu₀ : IsKleinDatum (algebraMap K F a) (algebraMap K F b) u₀) {pa pb : K[X]}
    (hpa : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t =
      (pa.map (algebraMap K F)).eval t)
    (hpb : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t =
      (pb.map (algebraMap K F)).eval t)
    (g : K[X]) : ((⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve K[X]).Ψ₃).eval g ≠ 0 := by
  have : Infinite F := Infinite.of_injective _ Nat.cast_injective
  obtain ⟨ζ, hζ⟩ : ∃ ζ : F, IsPrimitiveRoot ζ 5 := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic 5 F) (by
      rw [degree_cyclotomic, Nat.totient_prime (by decide : Nat.Prime 5)]; norm_num)
    exact ⟨z, isRoot_cyclotomic_iff.mp hz⟩
  set A := algebraMap K F a
  set B := algebraMap K F b
  set L := algebraMap K F l
  have hA : A ≠ 0 := (_root_.map_ne_zero _).mpr ha
  have hB : B ≠ 0 := (_root_.map_ne_zero _).mpr hb
  set j : K[X] →+* RatFunc F :=
    (algebraMap F[X] (RatFunc F)).comp (mapRingHom (algebraMap K F)) with hj
  have hjpa : j pa = rsFamilyA (RatFunc.C A) (RatFunc.C u₀) (RatFunc.C L) RatFunc.X := by
    rw [hj, RingHom.comp_apply, coe_mapRingHom, map_eq_rsFamilyA_poly hpa,
      ← RatFunc.aeval_X_left_eq_algebraMap, ← RatFunc.algebraMap_eq_C, ← rsFamilyA_eq_aeval]
  have hjpb : j pb = rsFamilyB (RatFunc.C B) (RatFunc.C u₀) (RatFunc.C L) RatFunc.X := by
    rw [hj, RingHom.comp_apply, coe_mapRingHom, map_eq_rsFamilyB_poly hpb,
      ← RatFunc.aeval_X_left_eq_algebraMap, ← RatFunc.algebraMap_eq_C, ← rsFamilyB_eq_aeval]
  have hmap : (⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve K[X]).map j =
      rsMember (RatFunc.C A) (RatFunc.C B) (RatFunc.C u₀) (RatFunc.C L) RatFunc.X := by
    simp only [WeierstrassCurve.map, map_zero, hjpa, hjpb, rsMember]
  intro h0
  have h1 : (((⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve K[X]).map j).Ψ₃).eval (j g) = 0 := by
    rw [WeierstrassCurve.map_Ψ₃, eval_map, eval₂_at_apply, h0, map_zero]
  rw [hmap] at h1
  exact rsMember_Psi3_eval_ne_zero ζ hζ hA hB hu₀ L (j g) h1

end RubinSilverberg
