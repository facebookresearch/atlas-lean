/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.RubinSilverberg.Family

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

-- Boundary: the hypothesis `a ≠ 0` matters. For `A = 0` the `3`-division polynomial of
-- `y² = x³ + B` is `3 x⁴ + 12 B x`, which vanishes at `x = 0`.
example {K : Type*} [Field K] (B : K[X]) :
    ((⟨0, 0, 0, 0, B⟩ : WeierstrassCurve K[X]).Ψ₃).eval 0 = 0 := by
  simp [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
