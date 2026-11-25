/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from AxiomMath/Stacks (https://github.com/AxiomMath/Stacks),
revision c496df0d9beea9deaeabcea8492605f9a0a2313b, licensed under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0). The source files carry no
individual copyright or author notice.

* `StacksFrontier/Homology/TwoTermComplex/DeterminantFunctor.lean`

Modifications: the native finite-projective presentation category, the literal
exterior-annihilator determinant and the source-normalized transport system are used; the
functor and all presentation and derived-map comparisons are constructed from that data.
-/
module

public import MathlibExt.AlgebraicGeometry.TwoTermDeterminantModels
public import Mathlib.CategoryTheory.Core

/-!
# Actual two-term determinant functor with all presentation comparisons

The carrier is the core of the native two-term-perfect derived category.
The chosen value is the actual determinant of its finite-projective
presenting modules. Its maps are the source-normalized derived transports.
The comparison is normalized for every presentation and every derived
isomorphism; it is not limited to one preferred affine frame.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TwoTermDeterminantFunctors

open CategoryTheory CategoryTheory.Limits
open TwoTermDeterminantModels

universe u

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- The native inclusion into the actual derived category. -/
def inclusion : PerfectTwoTerm R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (show ObjectProperty (DerivedCategory (ModuleCat.{u} R)) from IsTwoTermPerfect).ι

/-- An actual finite-projective two-term presentation of the specified object. -/
def selectedPresentation (K : PerfectTwoTerm R) : Presentation K.obj :=
  Classical.choice K.property

variable {R} (S : TransportSystem R)

/-- The source-normalized map, with its actual bundled module endpoints. -/
def presentationMap {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : Presentation K) (Q : Presentation L) (a : K ≅ L) :
    ModuleCat.of R (presentationDeterminant P) ⟶ ModuleCat.of R (presentationDeterminant Q) :=
  ModuleCat.ofHom (S.transport P Q a).toLinearMap

/-- The actual determinant functor, assembled from the fixed native
presentation objects and source-normalized derived-isomorphism maps. -/
def determinantFunctor : Core (PerfectTwoTerm R) ⥤ ModuleCat.{u} R where
  obj K := ModuleCat.of R (presentationDeterminant (selectedPresentation R K.of))
  map {K L} a := presentationMap S (selectedPresentation R K.of) (selectedPresentation R L.of)
    ((inclusion R).mapIso a.iso)
  map_id K := by
    change presentationMap S (selectedPresentation R K.of) (selectedPresentation R K.of)
      (Iso.refl K.of.obj) = 𝟙 _
    dsimp only [presentationMap]
    rw [S.identity]
    rfl
  map_comp {K L M} a b := by
    change presentationMap S (selectedPresentation R K.of) (selectedPresentation R M.of)
      ((inclusion R).mapIso a.iso ≪≫ (inclusion R).mapIso b.iso) =
        presentationMap S (selectedPresentation R K.of) (selectedPresentation R L.of)
          ((inclusion R).mapIso a.iso) ≫
        presentationMap S (selectedPresentation R L.of) (selectedPresentation R M.of)
          ((inclusion R).mapIso b.iso)
    dsimp only [presentationMap]
    rw [S.composition]
    rfl

/-- The values of the determinant functor are invertible: for a commutative ring $R$, a transport
system $S$ (`TransportSystem`) and an object $K$ of the core of the category of two-term perfect
complexes in the derived category of $R$-modules, `(determinantFunctor S).obj K`, the module
$\operatorname{Hom}_R(\det P^{-1}, \det P^0)$ for the chosen finite projective presentation $P$ of
$K$ in degrees $-1$ and $0$, is an invertible $R$-module. -/
theorem determinantFunctor_invertible (K : Core (PerfectTwoTerm R)) :
    Module.Invertible R ((determinantFunctor S).obj K) :=
  S.presentationInvertible K.of.obj (selectedPresentation R K.of)

/-- Comparison with every actual finite-projective presentation. -/
def presentationIso (K : Core (PerfectTwoTerm R)) (P : Presentation K.of.obj) :
    (determinantFunctor S).obj K ≅ ModuleCat.of R (presentationDeterminant P) :=
  (S.transport (selectedPresentation R K.of) P (Iso.refl K.of.obj)).toModuleIso

/-- Every derived-isomorphism map is normalized on every source and target presentation. -/
theorem presentationIso_map {K L : Core (PerfectTwoTerm R)} (a : K ⟶ L)
    (P : Presentation K.of.obj) (Q : Presentation L.of.obj) :
    (determinantFunctor S).map a ≫ (presentationIso S L Q).hom =
      (presentationIso S K P).hom ≫ presentationMap S P Q ((inclusion R).mapIso a.iso) := by
  have h₁ := S.composition (selectedPresentation R K.of) (selectedPresentation R L.of) Q
    ((inclusion R).mapIso a.iso) (Iso.refl L.of.obj)
  have h₂ := S.composition (selectedPresentation R K.of) P Q (Iso.refl K.of.obj)
    ((inclusion R).mapIso a.iso)
  simp only [Iso.trans_refl, Iso.refl_trans] at h₁ h₂
  apply ModuleCat.hom_ext
  exact congrArg LinearEquiv.toLinearMap (h₁.symm.trans h₂)

end MathlibExt.AlgebraicGeometry.TwoTermDeterminantFunctors
