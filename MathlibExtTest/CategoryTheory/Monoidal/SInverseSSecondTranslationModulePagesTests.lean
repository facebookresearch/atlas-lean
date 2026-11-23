/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationModulePages

/-!
# Ordinary-import consumers of the actual BK module pages

The original terminal-weight right-comma model supplies the support. The
tests exercise the zero differential at the left boundary, the linear
actual successor, and the whole forget comparison at the doubly missing
neighbor position `(0, 0)` on page two.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian Limits HomologicalComplex₂

noncomputable section

namespace CategoryTheory.SInverseS

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{0})

local notation "K" => SSet.bkAlternatingBicomplex AddCommGrpCat R
  (SSet.rightCommaNerveDiagram (translationProjection (C := C)))
local notation "A" => MonoidAlgebra ℤ (Multiplicative (Skeleton C))

/-- Ordinary public use of the canonical presentation at every page and position. -/
theorem ModulePageComponentTests.presented (r : ℤ) (hr : 1 ≤ r) (x : ℕ × ℕ) :
    let scalarRing := MonoidAlgebra ℤ (Multiplicative (Skeleton C))
    let underlyingFunctor := forget₂ (ModuleCat.{0} scalarRing) AddCommGrpCat.{0}
    let bkComplex := SSet.bkAlternatingBicomplex AddCommGrpCat.{0} R
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
      (fun Z : SpectralObject AddCommGrpCat.{0} EInt =>
        Z.E f₁ f₂ f₃ (n - 1) n (n + 1) hn₁ hn₂)
      (secondTranslationBKModuleSpectralObject_forget (C := C) R)
    (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f x ≫ originalPageIso.hom =
      underlyingFunctor.map modulePageIso.hom ≫
        (moduleSpectral.forgetMonoidModuleEIso f₁ f₂ f₃
          (n - 1) n (n + 1) hn₁ hn₂).hom ≫ eqToHom recoveryEq :=
  secondTranslationBKModulePageForgetIso_presented (C := C) R r hr x

example (q : ℕ) :
    let scalarRing := MonoidAlgebra ℤ (Multiplicative (Skeleton C))
    let underlyingFunctor := forget₂ (ModuleCat.{0} scalarRing) AddCommGrpCat.{0}
    let bkComplex := SSet.bkAlternatingBicomplex AddCommGrpCat.{0} R
      (SSet.rightCommaNerveDiagram (translationProjection (C := C)))
    let originalSpectral := horizontalCompleteFiltrationSpectralObject bkComplex
    let moduleSpectral := secondTranslationBKModuleSpectralObject (C := C) R
    let recipe := SpectralObject.coreE₁FirstQuadrantHomological
    let i₀ := recipe.i₀ 2 (0, q) (by decide)
    let i₁ := recipe.i₁ (0, q)
    let i₂ := recipe.i₂ (0, q)
    let i₃ := recipe.i₃ 2 (0, q) (by decide)
    let f₁ := homOfLE (recipe.le₀₁ 2 (0, q) (by decide))
    let f₂ := homOfLE (recipe.le₁₂ (0, q))
    let f₃ := homOfLE (recipe.le₂₃ 2 (0, q) (by decide))
    let n := recipe.deg (0, q)
    let hn₁ : (n - 1) + 1 = n := by omega
    let hn₂ : n + 1 = n + 1 := rfl
    let modulePageIso := moduleSpectral.spectralSequencePageXIso recipe 2 (by decide) (0, q)
      i₀ i₁ i₂ i₃ rfl rfl rfl rfl (n - 1) n (n + 1) rfl hn₁ hn₂
    let originalPageIso := originalSpectral.spectralSequencePageXIso recipe 2 (by decide) (0, q)
      i₀ i₁ i₂ i₃ rfl rfl rfl rfl (n - 1) n (n + 1) rfl hn₁ hn₂
    let recoveryEq := congrArg
      (fun Z : SpectralObject AddCommGrpCat.{0} EInt =>
        Z.E f₁ f₂ f₃ (n - 1) n (n + 1) hn₁ hn₂)
      (secondTranslationBKModuleSpectralObject_forget (C := C) R)
    (secondTranslationBKModulePageForgetIso (C := C) R 2 (by decide)).hom.f (0, q) ≫
        originalPageIso.hom =
      underlyingFunctor.map modulePageIso.hom ≫
        (moduleSpectral.forgetMonoidModuleEIso f₁ f₂ f₃
          (n - 1) n (n + 1) hn₁ hn₂).hom ≫ eqToHom recoveryEq :=
  secondTranslationBKModulePageForgetIso_presented (C := C) R 2 (by decide) (0, q)

example : (secondTranslationBKModuleSpectralObject (C := C) R).HasSpectralSequence
    SpectralObject.coreE₁FirstQuadrantHomological := inferInstance

example (r : ℤ) (hr : 1 ≤ r) (q : ℕ) (y : ℕ × ℕ) :
    ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).d (0, q) y = 0 := by
  apply ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).shape
  intro h
  have hy := h.1
  change (0 : ℤ) + (-r) = (y.1 : ℤ) at hy
  omega

example (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (x : ℕ × ℕ)
    (s : A)
    (z : ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).homology x) :
    (secondTranslationBKModuleSuccessorIso (C := C) R r r' hrr' hr x).hom
        (s • z) =
      s • (secondTranslationBKModuleSuccessorIso (C := C) R r r' hrr' hr x).hom z :=
  (secondTranslationBKModuleSuccessorIso (C := C) R r r' hrr' hr x).hom.hom.map_smul s z

example (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (x : ℕ × ℕ) :
    secondTranslationBKModuleSuccessorIso (C := C) R r r' hrr' hr x =
      (secondTranslationBKModuleSpectralSequence (C := C) R).iso r r' x hrr' hr :=
  secondTranslationBKModuleSuccessorIso_eq (C := C) R r r' hrr' hr x

example :
    (secondTranslationBKModuleSpectralSequenceForgetIso (C := C) R).hom ≫
        (secondTranslationBKModuleSpectralSequenceForgetIso (C := C) R).inv =
      𝟙 ((forget₂ (ModuleCat.{0} A) AddCommGrpCat.{0}).mapSpectralSequence
        (secondTranslationBKModuleSpectralSequence (C := C) R)) :=
  (secondTranslationBKModuleSpectralSequenceForgetIso (C := C) R).hom_inv_id

example
    (z : (((forget₂ (ModuleCat.{0} A) AddCommGrpCat.{0}).mapSpectralSequence
      (secondTranslationBKModuleSpectralSequence (C := C) R)).page 2 (by decide)).homology
        (0, 0)) :
    ((horizontalFirstQuadrantSpectralSequence K).iso 2 3 (0, 0) rfl (by decide)).hom
        (HomologicalComplex.homologyMap
          (secondTranslationBKModulePageForgetIso (C := C) R 2 (by decide)).hom (0, 0) z) =
      (secondTranslationBKModulePageForgetIso (C := C) R 3 (by decide)).hom.f (0, 0)
        (((forget₂ (ModuleCat.{0} A) AddCommGrpCat.{0}).map
          (secondTranslationBKModuleSuccessorIso (C := C) R
            2 3 rfl (by decide) (0, 0)).hom)
          (((HomologicalComplex.mapHomologyFunctorIso (0, 0)
            (forget₂ (ModuleCat.{0} A) AddCommGrpCat.{0})).app
            ((secondTranslationBKModuleSpectralSequence (C := C) R).page 2 (by decide))).hom
            z)) := by
  exact ConcreteCategory.congr_hom
    (secondTranslationBKModuleSpectralSequenceForgetIso_comm (C := C) R
      2 3 rfl (by decide) (0, 0)) z

end CategoryTheory.SInverseS

end
