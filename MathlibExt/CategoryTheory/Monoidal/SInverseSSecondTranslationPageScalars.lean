/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.SpectralObject.MonoidActionPageScalars
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationModulePages
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageMap

import all MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationModulePages

/-!
# Integral scalars on every actual second-translation BK page

Specialize the canonical commutative-monoid page-scalar API to the constructed
BK class action, preserving the original page forget comparison and original
second-translation bicomplex maps at every page and position.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex₂
open scoped BigOperators
universe u

namespace CategoryTheory.SInverseS

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{u})

local notation "A" => MonoidAlgebra ℤ (Multiplicative (Skeleton C))
local notation "data" => SpectralObject.coreE₁FirstQuadrantHomological


private theorem actualPageForget_eq (r : ℤ) (hr : 1 ≤ r) :
    secondTranslationBKModulePageForgetIso (C := C) R r hr =
      ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).monoidModulePageForgetIso (secondTranslationBKSpectralAction (C := C) R)
        data r hr := rfl

unseal SpectralObject.spectralSequence in
/-- Every integral object generator acts through the exact existing forget
comparison as the original second-translation BK page map, at every page and
position. -/
theorem secondTranslationBKModulePageForgetIso_single_apply (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (W : C) (z : ℤ)
    (x : ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).X (p, q)) :
    (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q)
        (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) z • x) =
      z • (horizontalPageMapOfBicomplex (secondTranslationBKBicomplexMap R W) r hr).f (p, q)
        ((secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q) x) := by
  have h := SpectralObject.monoidModulePageForgetIso_single_apply ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))))
      (secondTranslationBKSpectralAction (C := C) R)
    data r hr (p, q) (Multiplicative.ofAdd (toSkeleton W)) z x
  rw [secondTranslationBKSpectralAction_toSkeleton_map] at h
  simp only [actualPageForget_eq, SpectralObject.Hom.spectralSequencePageMap,
    SpectralObject.Hom.pageMap, horizontalPageMapOfBicomplex_f,
    horizontalFirstQuadrantSpectralSequence, SpectralObject.spectralSequence,
    SpectralObject.SpectralSequence.page, SpectralObject.SpectralSequence.pageX] at h ⊢
  convert h using 1

unseal SpectralObject.spectralSequence in
/-- The same generator formula for an arbitrary actual skeleton class, with
the original translation by its chosen object representative. -/
theorem secondTranslationBKModulePageForgetIso_monomial_apply (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (m : Multiplicative (Skeleton C)) (z : ℤ)
    (x : ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).X (p, q)) :
    (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q)
        (MonoidAlgebra.single m z • x) =
      z • (horizontalPageMapOfBicomplex
        (secondTranslationBKBicomplexMap R m.toAdd.out) r hr).f (p, q)
        ((secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q) x) := by
  have h := SpectralObject.monoidModulePageForgetIso_single_apply ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))))
      (secondTranslationBKSpectralAction (C := C) R)
    data r hr (p, q) m z x
  have hm : (secondTranslationBKSpectralAction (C := C) R m).asHom =
      horizontalCompleteFiltrationSpectralObjectMap
        (secondTranslationBKBicomplexMap R m.toAdd.out) := rfl
  rw [hm] at h
  simp only [actualPageForget_eq, SpectralObject.Hom.spectralSequencePageMap,
    SpectralObject.Hom.pageMap, horizontalPageMapOfBicomplex_f,
    horizontalFirstQuadrantSpectralSequence, SpectralObject.spectralSequence,
    SpectralObject.SpectralSequence.page, SpectralObject.SpectralSequence.pageX] at h ⊢
  convert h using 1

unseal SpectralObject.spectralSequence in
/-- Every integral class-monoid scalar acts through the canonical comparison
as the full finite sum of the original second-translation page maps. -/
theorem secondTranslationBKModulePageForgetIso_smul_apply (r : ℤ) (hr : 1 ≤ r) (p q : ℕ) (a : A)
    (x : ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).X (p, q)) :
    (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q) (a • x) =
      ∑ m ∈ a.coeff.support, (a.coeff m) • (horizontalPageMapOfBicomplex
        (secondTranslationBKBicomplexMap R m.toAdd.out) r hr).f (p, q)
        ((secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q) x) := by
  have h := SpectralObject.monoidModulePageForgetIso_smul_apply ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))))
    (secondTranslationBKSpectralAction (C := C) R) data r hr (p, q) a x
  have hm (m : Multiplicative (Skeleton C)) :
      (secondTranslationBKSpectralAction (C := C) R m).asHom =
        horizontalCompleteFiltrationSpectralObjectMap
            (secondTranslationBKBicomplexMap R m.toAdd.out) := rfl
  simp only [hm] at h
  simp only [actualPageForget_eq, SpectralObject.Hom.spectralSequencePageMap,
    SpectralObject.Hom.pageMap, horizontalPageMapOfBicomplex_f,
    horizontalFirstQuadrantSpectralSequence, SpectralObject.spectralSequence,
    SpectralObject.SpectralSequence.page, SpectralObject.SpectralSequence.pageX] at h ⊢
  convert h using 1

end CategoryTheory.SInverseS

end
