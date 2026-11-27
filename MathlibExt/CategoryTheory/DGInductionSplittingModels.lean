/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGInductionCoherenceModels
public import MathlibExt.CategoryTheory.DGModuleBiproductModels
public import MathlibExt.CategoryTheory.DGMoritaCospanModels

/-!
# Bar-normalized diagonal and left-dual coproduct splitting

The pushed diagonal inclusion is the actual induction-adjunction mate
of the bar inclusion followed by the outer induction unit. Its finite
biproduct comparison is fixed on both such inclusions. Left-dual maps
are Hom precomposition on every swapped representable, and finite dual
splitting is fixed by those same inclusion maps.

References: Brav--Dyckerhoff, arXiv:1606.00619v1, §2.1,
Lemma4.2 and diagrams6.6--6.7.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGInductionSplittingModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGBarDiagonalModels
open MathlibExt.CategoryTheory.DGCalabiYauMapModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGBimodulePushforwardModels
open MathlibExt.CategoryTheory.DGInductionCoherenceModels
open MathlibExt.CategoryTheory.DGModuleBiproductModels
open MathlibExt.CategoryTheory.DGMoritaCospanModels

universe u
variable {k : Type u} [Field k]

/-- The bar inclusion and outer induction unit give the actual composite restriction unit. -/
def barInclusionUnit {A D X : DGCat k} {a : A ⟶ D} {f : D ⟶ X}
    {Ta : EnvelopingMap a} {Tf : EnvelopingMap f} {Taf : EnvelopingMap (a ≫ f)}
    {Ra : RestrictionModel Ta.functor} {Rf : RestrictionModel Tf.functor}
    {Raf : RestrictionModel Taf.functor} (Lf : ExtensionModel Tf.functor Rf)
    (R : RestrictionCompositionModel a f Ta Tf Taf Ra Rf Raf)
    {DA : EnvelopingModuleModel (diagonal A)} {DD : EnvelopingModuleModel (diagonal D)}
    {FA : FreeDiagonalSystem A} {FD : FreeDiagonalSystem D}
    {PA : BarDiagonalModel DA FA} {PD : BarDiagonalModel DD FD}
    (b : BarRestrictionMapModel a Ta Ra PA PD) :
    DGHom k 0 PA.module
      (Raf.functor.obj (pushedDiagonal Lf PD).obj) :=
  dgComp k (moduleCycle b.map)
    (dgComp k (Ra.functor.dgMap 0 (Lf.unit (⟨PD.module, PD.cofibrant⟩)))
      (moduleCycle (R.iso (pushedDiagonal Lf PD).obj).inv) rfl) rfl

/-- The diagonal coproduct split is fixed by both actual bar-inclusion adjunction mates. -/
structure PushedDiagonalSplitModel {A B X : DGCat k} (P : DGCoproductModel A B)
    (f : P.category ⟶ X)
    (Ta : EnvelopingMap P.inl) (Tb : EnvelopingMap P.inr) (Tf : EnvelopingMap f)
    (Tea : EnvelopingMap (P.inl ≫ f)) (Teb : EnvelopingMap (P.inr ≫ f))
    (Ra : RestrictionModel Ta.functor) (Rb : RestrictionModel Tb.functor)
    (Rf : RestrictionModel Tf.functor) (Rea : RestrictionModel Tea.functor) (Reb : RestrictionModel Teb.functor)
    (Lf : ExtensionModel Tf.functor Rf) (Lea : ExtensionModel Tea.functor Rea) (Leb : ExtensionModel Teb.functor Reb)
    (CA : RestrictionCompositionModel P.inl f Ta Tf Tea Ra Rf Rea)
    (CB : RestrictionCompositionModel P.inr f Tb Tf Teb Rb Rf Reb)
    {DA : EnvelopingModuleModel (diagonal A)} {DB : EnvelopingModuleModel (diagonal B)}
    {DD : EnvelopingModuleModel (diagonal P.category)}
    {FA : FreeDiagonalSystem A} {FB : FreeDiagonalSystem B} {FD : FreeDiagonalSystem P.category}
    (PA : BarDiagonalModel DA FA) (PB : BarDiagonalModel DB FB) (PD : BarDiagonalModel DD FD)
    (ba : BarRestrictionMapModel P.inl Ta Ra PA PD) (bb : BarRestrictionMapModel P.inr Tb Rb PB PD) where
  sum : CofibrantBiproductModel (pushedDiagonal Lea PA) (pushedDiagonal Leb PB)
  inl : (pushedDiagonal Lea PA).obj ⟶ (pushedDiagonal Lf PD).obj
  inr : (pushedDiagonal Leb PB).obj ⟶ (pushedDiagonal Lf PD).obj
  inl_mate : ((Lea.homIso (⟨PA.module, PA.cofibrant⟩) (pushedDiagonal Lf PD).obj).hom.f 0)
      (moduleCycle inl) = barInclusionUnit Lf CA ba
  inr_mate : ((Leb.homIso (⟨PB.module, PB.cofibrant⟩) (pushedDiagonal Lf PD).obj).hom.f 0)
      (moduleCycle inr) = barInclusionUnit Lf CB bb
  comparison : sum.module ⟶ (pushedDiagonal Lf PD).obj
  comparison_inl : sum.inl ≫ comparison = inl
  comparison_inr : sum.inr ≫ comparison = inr
  equivalence : ModuleHomotopyEquivalence comparison

/-- A left-dual map is the actual contravariant Hom precomposition at every representable. -/
structure ModuleDualMapModel {C : DGCat k} (M N : DGDerivedModules k (enveloping C C))
    (f : M.obj ⟶ N.obj) (DM : ModuleLeftDualModel C M) (DN : ModuleLeftDualModel C N) where
  map : DN.replacement.module ⟶ DM.replacement.module
  normalized : ∀ (x : C) (y : Cᵒᵖ) (r : ℤ),
    (moduleComponent map (moduleIndex C C x y)).f r ≫
      (moduleComponent DM.replacement.augmentation (moduleIndex C C x y)).f r ≫
      (DM.valueIso x y).hom.f r =
      (moduleComponent DN.replacement.augmentation (moduleIndex C C x y)).f r ≫
        (DN.valueIso x y).hom.f r ≫
        (homPrecompose f ((dgYoneda k (C := enveloping C C)).obj (op y.unop, x))).f r

/-- Finite left-dual splitting is fixed by the actual two source-module inclusions. -/
structure ModuleDualBiproductModel {C : DGCat k} (M N : DGDerivedModules k (enveloping C C))
    (P : CofibrantBiproductModel M N)
    (DM : ModuleLeftDualModel C M) (DN : ModuleLeftDualModel C N)
    (DP : ModuleLeftDualModel C (⟨P.module, P.cofibrant⟩)) where
  sum : CofibrantBiproductModel
    (⟨DM.replacement.module, DM.replacement.cofibrant⟩)
    (⟨DN.replacement.module, DN.replacement.cofibrant⟩)
  inlDual : ModuleDualMapModel M (⟨P.module, P.cofibrant⟩) P.inl DM DP
  inrDual : ModuleDualMapModel N (⟨P.module, P.cofibrant⟩) P.inr DN DP
  comparison : DP.replacement.module ⟶ sum.module
  fst_eq : comparison ≫ sum.fst = inlDual.map
  snd_eq : comparison ≫ sum.snd = inrDual.map
  equivalence : ModuleHomotopyEquivalence comparison

end MathlibExt.CategoryTheory.DGInductionSplittingModels
