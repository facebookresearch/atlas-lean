/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FinitePointNormLines

/-!
# Finite nonreduced fibre algebras and their actual determinant norms

The algebra is the native Gamma of the actual finite fibre scheme. It may
be nonreduced, and is not replaced by its reduced algebra or a product of
separable residue fields. The section module is the native Gamma of the
same pulled-back line. Scalar restriction uses the original Gamma scalar
map. Its norm line is the actual Hom of the two exterior-annihilator
determinants. A rank-one algebra frame gives the native determinant
generator and the determinant norm of multiplication by its coordinate.

This is the finite-fibre base case of Deligne symbol/norm recursion.
Sources: Yuan--Zhang, arXiv:2105.13587v9, pp109--110 and Section 4.2.1;
the existing FinitePointNormLines formulas and their imported, attributed
Apache-2.0 exterior determinant primitives. No separability is assumed.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteFlatDeligneNormModels

open CategoryTheory Opposite Module
open _root_.AlgebraicGeometry GenericSectionMaps ProjectiveDeterminantModules

variable {K : Type} [Field K] (Z : Over (Spec (.of K))) (L : Z.left.Modules)

abbrev FibreAlgebra := Γ(Z.left,⊤)
abbrev SectionModule := Γ(L,⊤)

@[instance_reducible] def coefficientAlgebra : Algebra K (FibreAlgebra Z) :=
  (GenericSectionMaps.scalarMap Z).toAlgebra

attribute [local instance] coefficientAlgebra

local instance sectionOverBase : Module K (SectionModule Z L) :=
  Module.compHom (SectionModule Z L) (GenericSectionMaps.scalarMap Z)

local instance sectionTower : IsScalarTower K (FibreAlgebra Z) (SectionModule Z L) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- Actual finite-fibre and rank-one inputs remain in every norm source. -/
structure Sources where
  [finiteScheme : IsFinite Z.hom]
  [finiteAlgebra : FiniteDimensional K (FibreAlgebra Z)]
  [finiteSections : FiniteDimensional K (SectionModule Z L)]
  frame : Basis Unit (FibreAlgebra Z) (SectionModule Z L)

variable (S : Sources Z L)

/-- The frame is the actual Gamma algebra-module equivalence. -/
def frameEquiv : FibreAlgebra Z ≃ₗ[FibreAlgebra Z] SectionModule Z L :=
  ((S.frame.repr.trans (Finsupp.linearEquivFunOnFinite (FibreAlgebra Z) (FibreAlgebra Z) Unit)).trans
    (LinearEquiv.funUnique Unit (FibreAlgebra Z) (FibreAlgebra Z))).symm

/-- The norm module retains all nonreduced scalar directions. -/
def normModule : ModuleCat K :=
  ModuleCat.of K (determinantModule K (FibreAlgebra Z) →ₗ[K]
    determinantModule K (SectionModule Z L))

def normLine : (Spec (.of K)).Modules := (tilde.functor (.of K)).obj (normModule Z L)

def normFrame : normModule Z L :=
  (determinantEquiv ((frameEquiv Z L S).restrictScalars K)).toLinearMap

/-- The coordinate contributes the determinant norm on the whole actual algebra. -/
def normElement (v : SectionModule Z L) : normModule Z L := by
  letI := S.finiteAlgebra
  exact Algebra.norm K (S.frame.repr v ()) • normFrame Z L S

/-- The actual norm generator as a section of its native tilde line. -/
def normSection (v : SectionModule Z L) : Γ(normLine (K := K) Z L,⊤) := by
  change Γ((tilde.functor (.of K)).obj (normModule (K := K) Z L),⊤)
  exact (tilde.isoTop (R := CommRingCat.of K)
    (normModule (K := K) Z L)).hom (normElement Z L S v)

/-- Every actual algebra scalar acts by its full determinant norm. -/
theorem normElement_smul (a : FibreAlgebra Z) (v : SectionModule Z L) :
    normElement Z L S (a • v) = Algebra.norm K a • normElement Z L S v := by
  letI := S.finiteAlgebra
  simp [normElement, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul]

@[simp] theorem normElement_frame : normElement Z L S (S.frame ()) = normFrame Z L S := by
  letI := S.finiteAlgebra
  simp [normElement]

end MathlibExt.AlgebraicGeometry.FiniteFlatDeligneNormModels
