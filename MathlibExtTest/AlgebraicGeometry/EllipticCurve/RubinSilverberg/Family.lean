/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.RubinSilverberg.Family

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

open Polynomial RubinSilverberg

-- Consumers with the original binders.
private theorem exactSource {K F : Type*} [Field K] [Field F] [CharZero F] [IsAlgClosed F]
    [Algebra K F] {a b l : K} {u₀ : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hu₀ : IsKleinDatum (algebraMap K F a) (algebraMap K F b) u₀) {pa pb : Polynomial K}
    (hpa : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t =
      (pa.map (algebraMap K F)).eval t)
    (hpb : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t =
      (pb.map (algebraMap K F)).eval t)
    (g : Polynomial K) : ((⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve (Polynomial K)).Ψ₃).eval g ≠ 0 :=
  Psi3_eval_ne_zero_of_rsFamily ha hb hu₀ hpa hpb g

private theorem exactSource_rsMember {K : Type*} [Field K] [CharZero K] (ζ : K)
    (hζ : IsPrimitiveRoot ζ 5) {a b u₀ : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hu₀ : IsKleinDatum a b u₀) (l : K) (x : RatFunc K) :
    ((rsMember (RatFunc.C a) (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l)
      (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 :=
  rsMember_Psi3_eval_ne_zero ζ hζ ha hb hu₀ l x

-- Boundary: the hypothesis `a ≠ 0` matters. For `a = 0` the family has `A(t) = 0`, and the
-- `3`-division polynomial `3 x⁴ + 12 B x` of `y² = x³ + B` vanishes at `x = 0`.
example {K : Type*} [Field K] (u₀ l t : K) : rsFamilyA 0 u₀ l t = 0 := by
  simp [rsFamilyA]

example {K : Type*} [Field K] (B : K[X]) :
    ((⟨0, 0, 0, 0, B⟩ : WeierstrassCurve K[X]).Ψ₃).eval 0 = 0 := by
  simp [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

-- Concrete instances: both theorems apply to the family through the Klein datum `u₀ = 1` of
-- `kleinCurve 1 : y² = x³ - 31/3 x - 2501/108`, with `l = 0`.
private theorem isKleinDatum_one {K : Type*} [Field K] [CharZero K] :
    IsKleinDatum (-31 / 3 : K) (-2501 / 108) 1 := by
  norm_num [IsKleinDatum, kleinH, kleinV]

example (x : RatFunc (AlgebraicClosure ℚ)) :
    ((rsMember (RatFunc.C (-31 / 3)) (RatFunc.C (-2501 / 108)) (RatFunc.C 1) (RatFunc.C 0)
      (RatFunc.X : RatFunc (AlgebraicClosure ℚ))).Ψ₃).eval x ≠ 0 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ) 5
  exact rsMember_Psi3_eval_ne_zero ζ hζ (by norm_num) (by norm_num) isKleinDatum_one 0 x

-- The coefficient `A(t)` of the family through `u₀ = 1` with `l = 0`, as a polynomial.
private noncomputable def paOne : ℚ[X] :=
  C (-31 / 3 / kleinH 1) * kleinHHom (C (rsBeta 1) * X + 1) (C (rsGamma 1) * X + 1)

-- The coefficient `B(t)` of the family through `u₀ = 1` with `l = 0`, as a polynomial.
private noncomputable def pbOne : ℚ[X] :=
  C (-2501 / 108 / kleinT 1) * kleinTHom (C (rsBeta 1) * X + 1) (C (rsGamma 1) * X + 1)

example (g : ℚ[X]) : ((⟨0, 0, 0, paOne, pbOne⟩ : WeierstrassCurve ℚ[X]).Ψ₃).eval g ≠ 0 := by
  have hβ : ((rsBeta (1 : ℚ) : ℚ) : AlgebraicClosure ℚ) = rsBeta 1 := by
    simpa using map_rsBeta (Rat.castHom (AlgebraicClosure ℚ)) 1
  have hγ : ((rsGamma (1 : ℚ) : ℚ) : AlgebraicClosure ℚ) = rsGamma 1 := by
    simpa using map_rsGamma (Rat.castHom (AlgebraicClosure ℚ)) 1
  refine Psi3_eval_ne_zero_of_rsFamily (F := AlgebraicClosure ℚ) (a := -31 / 3) (b := -2501 / 108)
    (l := 0) (u₀ := 1) (by norm_num) (by norm_num) ?_ ?_ ?_ g
  · simpa only [map_div₀, map_neg, map_ofNat] using isKleinDatum_one
  · intro t
    simp only [paOne, rsFamilyA, rsNum, rsDen, Polynomial.map_mul, map_C, eval_mul, eval_C,
      ← coe_mapRingHom, map_kleinHHom, ← coe_evalRingHom]
    simp [map_div₀, map_kleinH, hβ, hγ]
    ring
  · intro t
    simp only [pbOne, rsFamilyB, rsNum, rsDen, Polynomial.map_mul, map_C, eval_mul, eval_C,
      ← coe_mapRingHom, map_kleinTHom, ← coe_evalRingHom]
    simp [map_div₀, map_kleinT, hβ, hγ]
    ring
