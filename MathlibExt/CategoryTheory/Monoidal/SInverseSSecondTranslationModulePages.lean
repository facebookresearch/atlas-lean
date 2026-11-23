/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.SpectralObject.MonoidActionPages
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationModuleAbutment

/-!
# The actual first-quadrant BK module spectral sequence

The sequence uses the original increasing homological interval recipe,
starting on page one. Its underlying-group comparison is an isomorphism of
whole spectral sequences and preserves the actual successor homology maps,
including boundary positions without an incoming or outgoing neighbor.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian Limits HomologicalComplex₂

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

universe u

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{u})

local notation "A" => MonoidAlgebra ℤ (Multiplicative (Skeleton C))

/-- The actual module sequence's boundary support is derived from the
original complete filtration by faithful forgetting. -/
instance secondTranslationBKModuleSpectralObject_hasSpectralSequence :
    (secondTranslationBKModuleSpectralObject (C := C) R).HasSpectralSequence
      SpectralObject.coreE₁FirstQuadrantHomological :=
  ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).monoidModule_hasSpectralSequence (secondTranslationBKSpectralAction (C := C) R)
    SpectralObject.coreE₁FirstQuadrantHomological

/-- The actual first-quadrant module spectral sequence, starting at page
one with differential bidegree `(-r, r - 1)`. -/
def secondTranslationBKModuleSpectralSequence :
    SpectralSequence (ModuleCat.{u} A)
      (fun r => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1 :=
  (secondTranslationBKModuleSpectralObject (C := C) R).spectralSequence
    SpectralObject.coreE₁FirstQuadrantHomological

/-- The exact native BK successor with an explicit public next-page bound,
so ordinary consumers can use its ModuleCat linear-map interface. -/
@[no_expose]
def secondTranslationBKModuleSuccessorIso
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (x : ℕ × ℕ) :
    ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).homology x ≅
      ((secondTranslationBKModuleSpectralSequence (C := C) R).page r'
        (SpectralObject.spectralSequenceNextPageBound r r' hrr' hr)).X x :=
  ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).monoidModuleSpectralSequenceSuccessorIso (secondTranslationBKSpectralAction (C := C) R)
    SpectralObject.coreE₁FirstQuadrantHomological r r' hrr' hr x

/-- The public BK successor accessor is exactly the unchanged actual
spectral-object successor. -/
theorem secondTranslationBKModuleSuccessorIso_eq
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (x : ℕ × ℕ) :
    secondTranslationBKModuleSuccessorIso (C := C) R r r' hrr' hr x =
      (secondTranslationBKModuleSpectralSequence (C := C) R).iso r r' x hrr' hr := by
  exact ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).monoidModuleSpectralSequenceSuccessorIso_eq
    (secondTranslationBKSpectralAction (C := C) R)
    SpectralObject.coreE₁FirstQuadrantHomological r r' hrr' hr x

/-- The actual native successor is linear for every integral class-monoid
scalar at every page position. -/
theorem secondTranslationBKModuleSuccessorIso_map_smul
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (x : ℕ × ℕ)
    (s : A)
    (z : ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).homology x) :
    (secondTranslationBKModuleSuccessorIso (C := C) R r r' hrr' hr x).hom (s • z) =
      s • (secondTranslationBKModuleSuccessorIso (C := C) R r r' hrr' hr x).hom z := by
  exact ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).monoidModuleSpectralSequenceSuccessorIso_map_smul
    (secondTranslationBKSpectralAction (C := C) R)
    SpectralObject.coreE₁FirstQuadrantHomological r r' hrr' hr x s z

/-- Forgetting scalars, with canonical homology preservation, gives the
whole original first-quadrant BK spectral sequence. -/
def secondTranslationBKModuleSpectralSequenceForgetIso :
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapSpectralSequence
        (secondTranslationBKModuleSpectralSequence (C := C) R) ≅
      horizontalFirstQuadrantSpectralSequence
        (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
          (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) :=
  ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).monoidModuleSpectralSequenceForgetIso (secondTranslationBKSpectralAction (C := C) R)
    SpectralObject.coreE₁FirstQuadrantHomological

/-- The canonical underlying-group complex comparison on every actual
module page, retaining all objects and all differentials. -/
@[no_expose]
def secondTranslationBKModulePageForgetIso (r : ℤ) (hr : 1 ≤ r) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩)).obj
        ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr) ≅
      (horizontalFirstQuadrantSpectralSequence (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).page r hr :=
  (SpectralSequence.pageFunctor AddCommGrpCat.{u}
    (fun r => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1 r hr).mapIso
    (secondTranslationBKModuleSpectralSequenceForgetIso (C := C) R)

private theorem supported_forget_presentation
    {M : Type u} [Monoid M]
    (moduleObject : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) EInt)
    [moduleObject.HasSpectralSequence SpectralObject.coreE₁FirstQuadrantHomological]
    (r : ℤ) (hr : 1 ≤ r) (x : ℕ × ℕ) :
    let underlyingFunctor := forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}
    let recipe := SpectralObject.coreE₁FirstQuadrantHomological
    let i₀ := recipe.i₀ r x hr
    let i₁ := recipe.i₁ x
    let i₂ := recipe.i₂ x
    let i₃ := recipe.i₃ r x hr
    let f₁ := homOfLE (recipe.le₀₁ r x hr)
    let f₂ := homOfLE (recipe.le₁₂ x)
    let f₃ := homOfLE (recipe.le₂₃ r x hr)
    let n := recipe.deg x
    let hn₁ : (n - 1) + 1 = n := by omega
    let hn₂ : n + 1 = n + 1 := rfl
    let modulePageIso := moduleObject.spectralSequencePageXIso recipe r hr x
      i₀ i₁ i₂ i₃ rfl rfl rfl rfl (n - 1) n (n + 1) rfl hn₁ hn₂
    let forgottenObject := SpectralObject.forgetMonoidModule moduleObject
    let forgottenPageIso := forgottenObject.spectralSequencePageXIso recipe r hr x
        i₀ i₁ i₂ i₃ rfl rfl rfl rfl (n - 1) n (n + 1) rfl hn₁ hn₂
    (moduleObject.forgetMonoidModuleSpectralSequencePageIso recipe r hr).hom.f x ≫
        forgottenPageIso.hom =
      underlyingFunctor.map modulePageIso.hom ≫
        (moduleObject.forgetMonoidModuleEIso f₁ f₂ f₃
          (n - 1) n (n + 1) hn₁ hn₂).hom := by
  dsimp only
  let underlying := forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}
  let : PreservesFiniteColimits underlying :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  have h := underlying.mapSpectralObjectSpectralSequencePageIso_presented
    moduleObject SpectralObject.coreE₁FirstQuadrantHomological r hr x
    (SpectralObject.coreE₁FirstQuadrantHomological.i₀ r x hr)
    (SpectralObject.coreE₁FirstQuadrantHomological.i₁ x)
    (SpectralObject.coreE₁FirstQuadrantHomological.i₂ x)
    (SpectralObject.coreE₁FirstQuadrantHomological.i₃ r x hr)
    rfl rfl rfl rfl
    (SpectralObject.coreE₁FirstQuadrantHomological.deg x - 1)
    (SpectralObject.coreE₁FirstQuadrantHomological.deg x)
    (SpectralObject.coreE₁FirstQuadrantHomological.deg x + 1) rfl (by omega) rfl
  simpa only [underlying, SpectralObject.forgetMonoidModuleSpectralSequencePageIso,
    SpectralObject.forgetMonoidModuleEIso, SpectralObject.forgetMonoidModule] using h

private theorem supported_recovery_presentation
    {M : Type u} [Monoid M]
    (moduleSpectral : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) EInt)
    [moduleSpectral.HasSpectralSequence SpectralObject.coreE₁FirstQuadrantHomological]
    (originalSpectral : SpectralObject AddCommGrpCat.{u} EInt)
    [originalSpectral.HasSpectralSequence SpectralObject.coreE₁FirstQuadrantHomological]
    (recovery : SpectralObject.forgetMonoidModule moduleSpectral = originalSpectral)
    (r : ℤ) (hr : 1 ≤ r) (x : ℕ × ℕ) :
    let scalarRing := MonoidAlgebra ℤ M
    let underlyingFunctor := forget₂ (ModuleCat.{u} scalarRing) AddCommGrpCat.{u}
    let recipe := SpectralObject.coreE₁FirstQuadrantHomological
    let i₀ := recipe.i₀ r x hr
    let i₁ := recipe.i₁ x
    let i₂ := recipe.i₂ x
    let i₃ := recipe.i₃ r x hr
    let f₁ := homOfLE (recipe.le₀₁ r x hr)
    let f₂ := homOfLE (recipe.le₁₂ x)
    let f₃ := homOfLE (recipe.le₂₃ r x hr)
    let n := recipe.deg x
    let hn₁ : (n - 1) + 1 = n := by omega
    let hn₂ : n + 1 = n + 1 := rfl
    let modulePageIso := moduleSpectral.spectralSequencePageXIso recipe r hr x
      i₀ i₁ i₂ i₃ rfl rfl rfl rfl (n - 1) n (n + 1) rfl hn₁ hn₂
    let originalPageIso := originalSpectral.spectralSequencePageXIso recipe r hr x
      i₀ i₁ i₂ i₃ rfl rfl rfl rfl (n - 1) n (n + 1) rfl hn₁ hn₂
    let recoveryEq := congrArg
      (fun Z : SpectralObject AddCommGrpCat.{u} EInt =>
        Z.E f₁ f₂ f₃ (n - 1) n (n + 1) hn₁ hn₂)
      recovery
    let hSequence :
        (SpectralObject.forgetMonoidModule moduleSpectral).spectralSequence recipe =
          originalSpectral.spectralSequence recipe := by
      subst originalSpectral
      rfl
    let pageFunctor := SpectralSequence.pageFunctor AddCommGrpCat.{u}
      (fun r => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1 r hr
    let sequenceIso := moduleSpectral.forgetMonoidModuleSpectralSequenceIso recipe ≪≫
      eqToIso hSequence
    (pageFunctor.mapIso sequenceIso).hom.f x ≫ originalPageIso.hom =
      underlyingFunctor.map modulePageIso.hom ≫
        (moduleSpectral.forgetMonoidModuleEIso f₁ f₂ f₃
          (n - 1) n (n + 1) hn₁ hn₂).hom ≫ eqToHom recoveryEq := by
  subst originalSpectral
  dsimp only
  simpa only [eqToIso_refl, Iso.trans_refl, Functor.mapIso_hom,
    SpectralSequence.pageFunctor_map,
    SpectralObject.forgetMonoidModuleSpectralSequenceIso_hom_hom,
    eqToHom_refl, Category.comp_id] using
    supported_forget_presentation moduleSpectral r hr x

/-- The actual page-forget component preserves the original supported-page
presentation and its canonical E-window scalar-forgetting comparison. -/
@[reassoc]
theorem secondTranslationBKModulePageForgetIso_presented
    (r : ℤ) (hr : 1 ≤ r) (x : ℕ × ℕ) :
    let scalarRing := MonoidAlgebra ℤ (Multiplicative (Skeleton C))
    let underlyingFunctor := forget₂ (ModuleCat.{u} scalarRing) AddCommGrpCat.{u}
    let bkComplex := SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
      (SSet.rightCommaNerveDiagram (translationProjection (C := C)))
    let originalSpectral := horizontalCompleteFiltrationSpectralObject bkComplex
    let moduleSpectral := secondTranslationBKModuleSpectralObject (C := C) R
    let recipe := SpectralObject.coreE₁FirstQuadrantHomological
    let i₀ := recipe.i₀ r x hr
    let i₁ := recipe.i₁ x
    let i₂ := recipe.i₂ x
    let i₃ := recipe.i₃ r x hr
    let f₁ := homOfLE (recipe.le₀₁ r x hr)
    let f₂ := homOfLE (recipe.le₁₂ x)
    let f₃ := homOfLE (recipe.le₂₃ r x hr)
    let n := recipe.deg x
    let hn₁ : (n - 1) + 1 = n := by omega
    let hn₂ : n + 1 = n + 1 := rfl
    let modulePageIso := moduleSpectral.spectralSequencePageXIso recipe r hr x
      i₀ i₁ i₂ i₃ rfl rfl rfl rfl (n - 1) n (n + 1) rfl hn₁ hn₂
    let originalPageIso := originalSpectral.spectralSequencePageXIso recipe r hr x
      i₀ i₁ i₂ i₃ rfl rfl rfl rfl (n - 1) n (n + 1) rfl hn₁ hn₂
    let recoveryEq := congrArg
      (fun Z : SpectralObject AddCommGrpCat.{u} EInt =>
        Z.E f₁ f₂ f₃ (n - 1) n (n + 1) hn₁ hn₂)
      (secondTranslationBKModuleSpectralObject_forget (C := C) R)
    (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f x ≫ originalPageIso.hom =
      underlyingFunctor.map modulePageIso.hom ≫
        (moduleSpectral.forgetMonoidModuleEIso f₁ f₂ f₃
          (n - 1) n (n + 1) hn₁ hn₂).hom ≫ eqToHom recoveryEq := by
  dsimp only
  have h := supported_recovery_presentation
    (secondTranslationBKModuleSpectralObject (C := C) R)
    (horizontalCompleteFiltrationSpectralObject
      (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
        (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
    (secondTranslationBKModuleSpectralObject_forget (C := C) R) r hr x
  simpa only [secondTranslationBKModulePageForgetIso,
    secondTranslationBKModuleSpectralSequenceForgetIso,
    SpectralObject.monoidModuleSpectralSequenceForgetIso,
    secondTranslationBKModuleSpectralSequence, secondTranslationBKModuleSpectralObject,
    SpectralSequence.pageFunctor_obj, Functor.mapSpectralSequence_page] using h

/-- Every differential agrees with the original differential under the
canonical page comparison, including zero maps outside the bidegree relation. -/
@[reassoc]
theorem secondTranslationBKModulePageForgetIso_d
    (r : ℤ) (hr : 1 ≤ r) (x y : ℕ × ℕ) :
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
        (((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).d x y) ≫
        (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f y =
      (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f x ≫
        ((horizontalFirstQuadrantSpectralSequence (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).page r hr).d x y :=
  ((secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.comm x y).symm

/-- The actual successor homology isomorphisms agree at every page
position through the canonical forgetful homology comparison. -/
@[reassoc]
theorem secondTranslationBKModuleSpectralSequenceForgetIso_comm
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (x : ℕ × ℕ) :
    HomologicalComplex.homologyMap
        (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom x ≫
      ((horizontalFirstQuadrantSpectralSequence (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).iso r r' x hrr' hr).hom =
    ((HomologicalComplex.mapHomologyFunctorIso x
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).app
        ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr)).hom ≫
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
        (secondTranslationBKModuleSuccessorIso (C := C) R r r' hrr' hr x).hom ≫
      (secondTranslationBKModulePageForgetIso (C := C) R r' (by omega)).hom.f x := by
  rw [secondTranslationBKModuleSuccessorIso_eq]
  change HomologicalComplex.homologyMap
      ((secondTranslationBKModuleSpectralSequenceForgetIso (C := C) R).hom.hom r hr) x ≫
      ((horizontalFirstQuadrantSpectralSequence (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).iso r r' x hrr' hr).hom = _
  simpa only [Functor.mapSpectralSequence_iso, Iso.trans_hom,
    secondTranslationBKModulePageForgetIso, Functor.mapIso_hom,
    SpectralSequence.pageFunctor_map, Category.assoc] using
      (secondTranslationBKModuleSpectralSequenceForgetIso (C := C) R).hom.comm
        r r' x hrr' hr

end CategoryTheory.SInverseS

end
