/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GaloisRep_Adic.lean`
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
proof-extraction framework; the statements are reused here with that
machinery removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
public import MathlibExt.RingTheory.Valuation.LiesOverPrime

@[expose] public section

universe u v

/-- A Galois action on an `A`-module is adically continuous if, for
every `n`, the automorphisms fixing some finite-dimensional
intermediate field act trivially modulo the `n`-th power of the
maximal ideal. -/
public def GaloisActionIsAdicContinuous (A : Type u) [CommRing A]
    [IsLocalRing A] {V : Type v} [AddCommGroup V] [Module A V]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End A V) : Prop :=
  ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
    FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ x ∈ L, σ x = x) →
      ∀ w : V, ρ σ w - w ∈
        (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A V)

/-- A two-dimensional adic Galois representation over a local ring
`A`: a free finite `A`-module of rank two with a continuous action of
the absolute Galois group of `ℚ`. -/
public structure GaloisRepAdic (A : Type u) [CommRing A]
    [IsLocalRing A] : Type (max u v + 1) where
  /-- The underlying module. -/
  V : Type v
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module A V]
  [instFree : Module.Free A V]
  [instFinite : Module.Finite A V]
  /-- The representation space is two-dimensional. -/
  finrank_eq : Module.finrank A V = 2
  /-- The Galois action. -/
  ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V
  /-- The action is adically continuous. -/
  isAdicContinuous : GaloisActionIsAdicContinuous A ρ

attribute [instance] GaloisRepAdic.instAddCommGroup
  GaloisRepAdic.instModule GaloisRepAdic.instFree
  GaloisRepAdic.instFinite

namespace GaloisRepAdic

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- An adic representation is unramified at `q` if inertia at every
valuation subring lying over `q` acts trivially. -/
public def IsUnramifiedAt (ρ : GaloisRepAdic A) (q : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1

/-- The determinant character of an adic representation. -/
noncomputable def det (ρ : GaloisRepAdic A) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ :=
  (LinearMap.det.comp ρ.ρ).toHomUnits

/-- The determinant is the unit attached to the linear determinant. -/
theorem det_apply (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.det σ : A) = LinearMap.det (ρ.ρ σ) :=
  rfl

/-- The trace of a Galois element in an adic representation. -/
noncomputable def trace (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : A :=
  LinearMap.trace A ρ.V (ρ.ρ σ)

/-- The trace is the linear trace of the representing endomorphism. -/
theorem trace_def (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ.trace σ = LinearMap.trace A ρ.V (ρ.ρ σ) :=
  rfl

end GaloisRepAdic
