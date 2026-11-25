/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Actual bounded finite-projective lattices in a localized free module

The ambient module is R[1/r]^n. The standard lattice is the actual image
of R^n, and boundedness is the explicit inclusion between r^N R^n and
r^(-N) R^n. Lattices are actual finite-projective submodules, with local
rank n and the canonical localized inclusion bijective.

This generic completed task language specializes to Witt lattices and
theta-adic period lattices; it is not an opaque geometric lattice oracle.
Reference: Bhatt--Scholze, arXiv:1507.06490v3, Theorem1.1 and Section6.
-/

@[expose] public noncomputable section

namespace MathlibExt.LinearAlgebra.LocalizedLattices

open scoped TensorProduct

variable (R : Type) [CommRing R] (r : R) (n : ℕ)

abbrev FractionRing := Localization.Away r
abbrev Ambient := Fin n → FractionRing R r

/-- The actual map from the standard free integral module. -/
def standardMap : (Fin n → R) →ₗ[R] Ambient R r n where
  toFun v i := algebraMap R (FractionRing R r) (v i)
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' a x := by ext i; exact (Algebra.linearMap R _).map_smul a (x i)

/-- The standard integral lattice as the actual submodule image. -/
def standard : Submodule R (Ambient R r n) := LinearMap.range (standardMap R r n)

/-- Actual multiplication by an element of the localized coefficient ring. -/
def scale (a : FractionRing R r) : Ambient R r n →ₗ[R] Ambient R r n where
  toFun v i := a * v i
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' b x := by
    ext i
    change a * (b • x i) = b • (a * x i)
    rw [Algebra.smul_def, Algebra.smul_def]
    ring

/-- The displayed upper bound r^(-N) R^n. -/
def upper (N : ℕ) : Submodule R (Ambient R r n) :=
  (standard R r n).map (scale R r n (IsLocalization.Away.invSelf r ^ N))

/-- The displayed lower bound r^N R^n. -/
def lower (N : ℕ) : Submodule R (Ambient R r n) :=
  (standard R r n).map (scale R r n (algebraMap R _ r ^ N))

/-- The actual localized inclusion into the free ambient module. -/
def localizationMap (L : Submodule R (Ambient R r n)) :
    FractionRing R r ⊗[R] L →ₗ[FractionRing R r] Ambient R r n :=
  L.subtype.liftBaseChange (FractionRing R r)

/-- Actual constant local rank, also for nonfree projective modules. -/
def HasLocalRank (L : Submodule R (Ambient R r n)) : Prop :=
  ∀ x : PrimeSpectrum R,
    let A := Localization.AtPrime x.asIdeal
    Module.Free A (A ⊗[R] L) ∧ Module.finrank A (A ⊗[R] L) = n

/-- A genuine finite-projective full-rank lattice in the actual localization. -/
structure Lattice where
  module : Submodule R (Ambient R r n)
  [finite : Module.Finite R module]
  [projective : Module.Projective R module]
  rank : HasLocalRank R r n module
  full : Function.Bijective (localizationMap R r n module)
  bounded : ∃ N : ℕ, lower R r n N ≤ module ∧ module ≤ upper R r n N

attribute [instance] Lattice.finite Lattice.projective

/-- A lattice model is fixed by its actual submodule. -/
@[ext] theorem Lattice.ext (L M : Lattice R r n) (h : L.module = M.module) :
    L = M := by
  cases L
  cases M
  cases h
  rfl

private theorem scale_one : scale R r n 1 = LinearMap.id := by
  ext v i
  exact one_mul _

@[simp] theorem upper_zero : upper R r n 0 = standard R r n := by
  simp [upper, scale_one]

@[simp] theorem lower_zero : lower R r n 0 = standard R r n := by
  simp [lower, scale_one]

/-- The exact bounded subfunctor, without a freely named Schubert predicate. -/
def IsBoundedBy (L : Lattice R r n) (N : ℕ) : Prop :=
  lower R r n N ≤ L.module ∧ L.module ≤ upper R r n N

/-- The degree-zero bounded component is exactly the standard lattice. -/
theorem boundedZero_eq (L : Lattice R r n) (h : IsBoundedBy R r n L 0) :
    L.module = standard R r n := by
  simp only [IsBoundedBy, lower_zero, upper_zero] at h
  exact le_antisymm h.2 h.1

/-- An elementary modification is actual inclusion with the stated bounds. -/
structure Modification (L M : Lattice R r n) where
  inclusion : L.module ≤ M.module
  quotient : Module.Finite R (M.module ⧸ L.module.comap M.module.subtype)

end MathlibExt.LinearAlgebra.LocalizedLattices
