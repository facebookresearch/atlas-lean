/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.FrobeniusTrace

@[expose] public section

open scoped WeierstrassCurve.Affine

universe r s v

/-- Consumer with the original binders: the trace of a Galois
element in the representation on `n`-torsion. -/
theorem exactSource {R : Type r} {S : Type s} {K : Type v} [CommRing R]
    [CommRing S] [Field K] [DecidableEq K] (W' : WeierstrassCurve.Affine R)
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (n : ℕ) (σ : K ≃ₐ[S] K) :
    WeierstrassCurve.Affine.Point.galoisTrace S W' n σ =
      LinearMap.trace (ZMod n)
        (Submodule.torsionBy ℤ (W'⁄K).Point n)
        (WeierstrassCurve.Affine.Point.galoisRepModuleEnd S W' n σ) :=
  WeierstrassCurve.Affine.Point.galoisTrace_def W' n σ

/-- A Frobenius element lies in the decomposition subgroup, with
the original binders. -/
example {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ)
    (h : A.IsFrobeniusAt σ q) : σ ∈ A.decompositionSubgroup K :=
  h.mem_decompositionSubgroup

/-- Galois-stable submodules: the full torsion submodule is
Galois-stable, with the original binders. -/
example {R : Type r} {S : Type s} {K : Type v} [CommRing R]
    [CommRing S] [Field K] [DecidableEq K]
    (W' : WeierstrassCurve.Affine R)
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (n : ℕ) :
    WeierstrassCurve.Affine.Point.IsGaloisStable (K := K) (W' := W') S
      (⊤ : Submodule (ZMod n)
        (Submodule.torsionBy ℤ (W'⁄K).Point n)) :=
  fun σ x _ => Submodule.mem_top
