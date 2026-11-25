/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGBimodulePushforwardModels

/-!
# Unit-normalized identity and composition for actual bimodule induction

Restriction comparisons are identity maps after the actual object-image
identifications. The induction comparison is the native enriched
adjunction transpose of the composite units. Its inverse and homotopies
are actual module maps. Naturality is fixed in every Hom degree.

References: Keller, Deriving DG categories, §6; Brav--Dyckerhoff,
arXiv:1606.00619v1, §2.1 and diagram6.4.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGInductionCoherenceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGBimodulePushforwardModels

universe u
variable {k : Type u} [Field k]

/-- The identity restriction has the exact native module-value identity. -/
structure RestrictionIdentityModel (A : DGCat k) (T : EnvelopingMap (𝟙 A))
    (R : RestrictionModel T.functor) where
  iso : ∀ N : RightModule k (enveloping A A), R.functor.obj N ≅ N
  value_eq : ∀ (N : RightModule k (enveloping A A)) (x : A) (y : Aᵒᵖ),
    moduleComponent (iso N).hom (moduleIndex A A x y) = (restrictionValueIso T R N x y).hom

/-- The actual induction identity is the adjunction transpose of that same restriction identity. -/
structure InductionIdentityModel {A : DGCat k} {T : EnvelopingMap (𝟙 A)}
    {R : RestrictionModel T.functor} (L : ExtensionModel T.functor R)
    (I : RestrictionIdentityModel A T R) where
  map : ∀ M : DGDerivedModules k (enveloping A A), (L.functor.obj M).obj ⟶ M.obj
  mate_eq : ∀ M : DGDerivedModules k (enveloping A A),
    ((L.homIso M M.obj).hom.f 0) (moduleCycle (map M)) = moduleCycle (I.iso M.obj).inv
  equivalence : ∀ M : DGDerivedModules k (enveloping A A), ModuleHomotopyEquivalence (map M)
  naturality : ∀ (M N : DGDerivedModules k (enveloping A A)) (p : ℤ) (a : DGHom k p M N),
    dgComp k (L.functor.dgMap p a) (moduleCycle (map N)) (show p + 0 = p by omega) =
      dgComp k (moduleCycle (map M)) a (show 0 + p = p by omega)

/-- Restriction composition is the identity on the same actual transported module values. -/
structure RestrictionCompositionModel {A B C : DGCat k} (f : A ⟶ B) (g : B ⟶ C)
    (Tf : EnvelopingMap f) (Tg : EnvelopingMap g) (Tfg : EnvelopingMap (f ≫ g))
    (Rf : RestrictionModel Tf.functor) (Rg : RestrictionModel Tg.functor)
    (Rfg : RestrictionModel Tfg.functor) where
  iso : ∀ N : RightModule k (enveloping C C), Rfg.functor.obj N ≅ Rf.functor.obj (Rg.functor.obj N)
  value_eq : ∀ (N : RightModule k (enveloping C C)) (x : A) (y : Aᵒᵖ),
    moduleComponent (iso N).hom (moduleIndex A A x y) ≫
      (restrictionValueIso Tf Rf (Rg.functor.obj N) x y).hom ≫
      (restrictionValueIso Tg Rg N (f.obj x) (op (f.obj y.unop))).hom =
      (restrictionValueIso Tfg Rfg N x y).hom

/-- The native composite adjunction unit, transported by the fixed restriction composition. -/
def compositionUnit {A B C : DGCat k} {f : A ⟶ B} {g : B ⟶ C}
    {Tf : EnvelopingMap f} {Tg : EnvelopingMap g} {Tfg : EnvelopingMap (f ≫ g)}
    {Rf : RestrictionModel Tf.functor} {Rg : RestrictionModel Tg.functor}
    {Rfg : RestrictionModel Tfg.functor}
    (Lf : ExtensionModel Tf.functor Rf) (Lg : ExtensionModel Tg.functor Rg)
    (R : RestrictionCompositionModel f g Tf Tg Tfg Rf Rg Rfg)
    (M : DGDerivedModules k (enveloping A A)) :
    DGHom k 0 M.obj (Rfg.functor.obj (Lg.functor.obj (Lf.functor.obj M)).obj) :=
  dgComp k (Lf.unit M)
    (dgComp k (Rf.functor.dgMap 0 (Lg.unit (Lf.functor.obj M)))
      (moduleCycle (R.iso (Lg.functor.obj (Lf.functor.obj M)).obj).inv) rfl) rfl

/-- Induction composition is its actual unit-normalized mate, with all-degree naturality. -/
structure InductionCompositionModel {A B C : DGCat k} {f : A ⟶ B} {g : B ⟶ C}
    {Tf : EnvelopingMap f} {Tg : EnvelopingMap g} {Tfg : EnvelopingMap (f ≫ g)}
    {Rf : RestrictionModel Tf.functor} {Rg : RestrictionModel Tg.functor}
    {Rfg : RestrictionModel Tfg.functor}
    (Lf : ExtensionModel Tf.functor Rf) (Lg : ExtensionModel Tg.functor Rg)
    (Lfg : ExtensionModel Tfg.functor Rfg)
    (R : RestrictionCompositionModel f g Tf Tg Tfg Rf Rg Rfg) where
  map : ∀ M : DGDerivedModules k (enveloping A A),
    (Lfg.functor.obj M).obj ⟶ (Lg.functor.obj (Lf.functor.obj M)).obj
  mate_eq : ∀ M : DGDerivedModules k (enveloping A A),
    ((Lfg.homIso M (Lg.functor.obj (Lf.functor.obj M)).obj).hom.f 0) (moduleCycle (map M)) =
      compositionUnit Lf Lg R M
  equivalence : ∀ M : DGDerivedModules k (enveloping A A), ModuleHomotopyEquivalence (map M)
  naturality : ∀ (M N : DGDerivedModules k (enveloping A A)) (p : ℤ) (a : DGHom k p M N),
    dgComp k (Lfg.functor.dgMap p a) (moduleCycle (map N)) (show p + 0 = p by omega) =
      dgComp k (moduleCycle (map M)) (Lg.functor.dgMap p (Lf.functor.dgMap p a)) (show 0 + p = p by omega)

/-- Shifting the actual induction unit fixes the source comparison on every module value. -/
structure ShiftedInductionUnitModel {A B : DGCat k} {f : A ⟶ B}
    {T : EnvelopingMap f} {R : RestrictionModel T.functor} (L : ExtensionModel T.functor R)
    (M : DGDerivedModules k (enveloping A A)) (n : ℤ)
    (SM : CofibrantShiftModel M n) (SN : CofibrantShiftModel (L.functor.obj M) n) where
  map : SM.module ⟶ R.functor.obj SN.module
  normalized : ∀ (x : A) (y : Aᵒᵖ) (r : ℤ),
    (moduleComponent map (moduleIndex A A x y)).f r ≫
      (restrictionValueIso T R SN.module x y).hom.f r ≫
      (SN.valueIso (moduleIndex B B (f.obj x) (op (f.obj y.unop)))).hom.f r ≫
      (((L.functor.obj M).obj.toEnrichedFunctor.obj
        (moduleIndex B B (f.obj x) (op (f.obj y.unop)))).shiftFunctorObjXIso n r (r + n) rfl).hom =
      (SM.valueIso (moduleIndex A A x y)).hom.f r ≫
        ((M.obj.toEnrichedFunctor.obj (moduleIndex A A x y)).shiftFunctorObjXIso n r (r + n) rfl).hom ≫
        (DGFunctor.dgApp k 0 (moduleIndex A A x y) (L.unit M) : CochainComplex.HomComplex.Cochain _ _ 0).v
          (r + n) (r + n) (by omega) ≫
        (restrictionValueIso T R (L.functor.obj M).obj x y).hom.f (r + n)

/-- Induction commutes with the actual module shift by that same normalized unit mate. -/
structure InductionShiftModel {A B : DGCat k} {f : A ⟶ B}
    {T : EnvelopingMap f} {R : RestrictionModel T.functor} (L : ExtensionModel T.functor R)
    (M : DGDerivedModules k (enveloping A A)) (n : ℤ)
    (SM : CofibrantShiftModel M n) (SN : CofibrantShiftModel (L.functor.obj M) n)
    (U : ShiftedInductionUnitModel L M n SM SN) where
  map : (L.functor.obj (⟨SM.module, SM.cofibrant⟩)).obj ⟶ SN.module
  mate_eq : ((L.homIso (⟨SM.module, SM.cofibrant⟩) SN.module).hom.f 0)
    (moduleCycle map) = moduleCycle U.map
  equivalence : ModuleHomotopyEquivalence map

end MathlibExt.CategoryTheory.DGInductionCoherenceModels
