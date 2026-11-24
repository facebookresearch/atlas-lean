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

/-- Consumer with the source binders plus the rank-two basis: the
trace of a Galois element in the representation on `n`-torsion is the
basis-free trace. -/
theorem exactSource {R : Type r} {S : Type s} {K : Type v} [CommRing R]
    [CommRing S] [Field K] [DecidableEq K] (W' : WeierstrassCurve.Affine R)
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (n : ℕ)
    (b : Module.Basis (Fin 2) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n))
    (σ : K ≃ₐ[S] K) :
    WeierstrassCurve.Affine.Point.galoisTrace S W' n b σ =
      LinearMap.trace (ZMod n)
        (Submodule.torsionBy ℤ (W'⁄K).Point n)
        (WeierstrassCurve.Affine.Point.galoisRepModuleEnd S W' n σ) :=
  WeierstrassCurve.Affine.Point.galoisTrace_eq_trace W' n b σ

/-- The basis the trace requires makes the `n`-torsion finite and free
over `ZMod n`, so the trace is not the zero fallback of
`LinearMap.trace`. -/
example {R : Type r} {K : Type v} [CommRing R] [Field K] [DecidableEq K]
    {W' : WeierstrassCurve.Affine R} [Algebra R K] (n : ℕ)
    (b : Module.Basis (Fin 2) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n)) :
    Module.Free (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) ∧
      Module.Finite (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- The identity element has trace `2`, computed in the basis. -/
example {R : Type r} {S : Type s} {K : Type v} [CommRing R]
    [CommRing S] [Field K] [DecidableEq K] {W' : WeierstrassCurve.Affine R}
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (n : ℕ)
    (b : Module.Basis (Fin 2) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n)) :
    WeierstrassCurve.Affine.Point.galoisTrace S W' n b 1 = 2 := by
  rw [WeierstrassCurve.Affine.Point.galoisTrace_def, map_one,
    LinearMap.toMatrix_one, Matrix.trace_one]
  simp

/-- The trace is independent of the basis. -/
example {R : Type r} {S : Type s} {K : Type v} [CommRing R]
    [CommRing S] [Field K] [DecidableEq K] {W' : WeierstrassCurve.Affine R}
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (n : ℕ)
    (b b' : Module.Basis (Fin 2) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n))
    (σ : K ≃ₐ[S] K) :
    WeierstrassCurve.Affine.Point.galoisTrace S W' n b σ =
      WeierstrassCurve.Affine.Point.galoisTrace S W' n b' σ :=
  WeierstrassCurve.Affine.Point.galoisTrace_congr_basis W' n b b' σ

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
