/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers
of the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a
proof-extraction framework; the statements and proofs are reused
here with that machinery removed and the names restated in
Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import MathlibExt.AlgebraicGeometry.EllipticCurve.PointGaloisAction

@[expose] public section

open scoped WeierstrassCurve.Affine

universe r s v

namespace WeierstrassCurve.Affine.Point

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R]
  [CommRing S] [Field K] [DecidableEq K] {W' : Affine R}
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

variable (S) in
/-- The trace of a Galois element in the representation on
`n`-torsion, computed in a basis `b` exhibiting the `n`-torsion as a
free `ZMod n`-module of rank two.

The basis is the hypothesis that makes this a trace of a
two-dimensional representation, as for the `n`-torsion over a
separably closed field in which `n` is invertible. Unlike the source,
which applies `LinearMap.trace` to an arbitrary torsion module, this
definition is not available when the `n`-torsion has no such basis:
there `LinearMap.trace` would return its fallback value `0`. The
value does not depend on the basis (`galoisTrace_eq_trace`). -/
noncomputable def galoisTrace (W' : Affine R) (n : ℕ)
    (b : Module.Basis (Fin 2) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n))
    (σ : K ≃ₐ[S] K) : ZMod n :=
  Matrix.trace (LinearMap.toMatrix b b (galoisRepModuleEnd S W' n σ))

theorem galoisTrace_def (W' : Affine R) (n : ℕ)
    (b : Module.Basis (Fin 2) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n))
    (σ : K ≃ₐ[S] K) :
    galoisTrace S W' n b σ =
      Matrix.trace (LinearMap.toMatrix b b (galoisRepModuleEnd S W' n σ)) :=
  rfl

/-- The trace computed in a basis is the basis-free trace of the
endomorphism. -/
theorem galoisTrace_eq_trace (W' : Affine R) (n : ℕ)
    (b : Module.Basis (Fin 2) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n))
    (σ : K ≃ₐ[S] K) :
    galoisTrace S W' n b σ =
      LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)
        (galoisRepModuleEnd S W' n σ) :=
  (LinearMap.trace_eq_matrix_trace (ZMod n) b _).symm

/-- The trace does not depend on the chosen basis. -/
theorem galoisTrace_congr_basis (W' : Affine R) (n : ℕ)
    (b b' : Module.Basis (Fin 2) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n))
    (σ : K ≃ₐ[S] K) :
    galoisTrace S W' n b σ = galoisTrace S W' n b' σ := by
  rw [galoisTrace_eq_trace, galoisTrace_eq_trace]

end WeierstrassCurve.Affine.Point

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An automorphism is Frobenius at `q` for a valuation subring if
it lies in the decomposition subgroup and acts on the residue field
by raising to the `q`-th power. -/
public def IsFrobeniusAt (A : ValuationSubring L)
    (σ : L ≃ₐ[K] L) (q : ℕ) : Prop :=
  ∃ hσ : σ ∈ A.decompositionSubgroup K,
    ∀ x : IsLocalRing.ResidueField A,
      (⟨σ, hσ⟩ : A.decompositionSubgroup K) • x = x ^ q

/-- A Frobenius element lies in the decomposition subgroup. -/
theorem IsFrobeniusAt.mem_decompositionSubgroup
    {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) : σ ∈ A.decompositionSubgroup K :=
  h.choose

/-- A Frobenius element raises residue-field elements to the
`q`-th power. -/
theorem IsFrobeniusAt.smul_residue_eq {A : ValuationSubring L}
    {σ : L ≃ₐ[K] L} {q : ℕ} (h : A.IsFrobeniusAt σ q)
    (x : IsLocalRing.ResidueField A) :
    (⟨σ, h.mem_decompositionSubgroup⟩ : A.decompositionSubgroup K) •
        x = x ^ q :=
  h.choose_spec x

end ValuationSubring
