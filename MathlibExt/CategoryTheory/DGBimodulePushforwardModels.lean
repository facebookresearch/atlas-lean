/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModuleConeShiftModels
public import MathlibExt.CategoryTheory.DGCalabiYauMapModels
public import MathlibExt.CategoryTheory.DGScalarExtensionModels

/-!
# Actual bimodule pushforward, bar counits and left-duality mates

The enveloping map is the native opposite/tensor map of the DG functor.
Restriction and induction retain their all-degree enriched adjunctions.
The bar counit is the actual adjunction transpose of the functor-induced
map on every path word. Left dual values are enriched Hom to the actual
swapped representables, and their base-change map is normalized through
those representables and the same induction adjunction.

References: Brav--Dyckerhoff, arXiv:1606.00619v1, §2.1,
Lemma4.2 and Proposition4.3. These inputs contain no CY class or
nondegeneracy conclusion.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGBimodulePushforwardModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGBarDiagonalModels
open MathlibExt.CategoryTheory.DGCalabiYauMapModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [Field k]

/-- The actual left-dual value of a projective enveloping module. -/
def moduleDualValue (C : DGCat k) (M : DGDerivedModules k (enveloping C C))
    (x : C) (y : Cᵒᵖ) : Cochains k :=
  dgHomComplex k M.obj ((dgYoneda k (C := enveloping C C)).obj (op y.unop, x))

/-- The actual left-dual action is Yoneda/postcomposition after the native factor swap. -/
def moduleDualAction (C : DGCat k) (M : DGDerivedModules k (enveloping C C))
    (x x' : C) (y y' : Cᵒᵖ) (p : ℤ)
    (a : DGHom k p (moduleIndex C C x y) (moduleIndex C C x' y')) :
    Cochain (moduleDualValue C M x y) (moduleDualValue C M x' y') p :=
  (cochainCorepresentable M.obj).dgMap p
    ((dgYoneda k (C := enveloping C C)).dgMap p ((inverseDualIndexHom C x x' y y').f p a))

/-- A left-dual module retains every actual value and all enveloping arrows. -/
structure ModuleLeftDualModel (C : DGCat k) (M : DGDerivedModules k (enveloping C C)) where
  module : RightModule k (enveloping C C)
  valueIso : ∀ (x : C) (y : Cᵒᵖ),
    module.toEnrichedFunctor.obj (moduleIndex C C x y) ≅ moduleDualValue C M x y
  action_eq : ∀ (x x' : C) (y y' : Cᵒᵖ) (p r s : ℤ) (h : r + p = s)
    (a : DGHom k p (moduleIndex C C x y) (moduleIndex C C x' y'))
    (v : (module.toEnrichedFunctor.obj (moduleIndex C C x y)).X r),
    ((valueIso x' y').hom.f s)
      (((module.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r s h) v) =
      (moduleDualAction C M x x' y y' p a).v r s h (((valueIso x y).hom.f r) v)
  replacement : ModuleReplacement module

/-- The normalized inverse diagonal dual is the corresponding actual module left dual. -/
def InverseDualModel.toModuleLeftDual {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    {F : FreeDiagonalSystem C} {P : BarDiagonalModel D F} (I : InverseDualModel P) :
    ModuleLeftDualModel C (⟨P.module, P.cofibrant⟩ : DGDerivedModules k (enveloping C C)) where
  module := I.module
  valueIso := I.valueIso
  action_eq := I.action_eq
  replacement := I.replacement

/-- The actual enveloping functor is the source opposite/tensor map. -/
abbrev EnvelopingMap {A B : DGCat k} (f : A ⟶ B) :=
  TensorMapModel
    (show oppositeCategory A ⟶ oppositeCategory B from EnrichedFunctor.op (V := Cochains k) f) f

/-- Restriction values are fixed at the actual images of both DG objects. -/
def restrictionValueIso {A B : DGCat k} {f : A ⟶ B} (T : EnvelopingMap f)
    (R : RestrictionModel T.functor) (N : RightModule k (enveloping B B)) (x : A) (y : Aᵒᵖ) :
    (R.functor.obj N).toEnrichedFunctor.obj (moduleIndex A A x y) ≅
      N.toEnrichedFunctor.obj (moduleIndex B B (f.obj x) (op (f.obj y.unop))) :=
  eqToIso (by
    rw [R.object_eq]
    change N.toEnrichedFunctor.obj (op (T.functor.obj (op x, y.unop))) = _
    rw [T.object_eq]
    rfl)

/-- A DG functor maps each actual intermediate-object bar path. -/
def mappedPath {A B : DGCat k} (f : A ⟶ B) {n : ℕ} (v : PathVertices A n) : PathVertices B n :=
  ⟨v.val.map f.obj, by simp [v.property]⟩

/-- The native functor-induced bar map is fixed on all path generators before taking its mate. -/
structure BarRestrictionMapModel {A B : DGCat k} (f : A ⟶ B)
    (T : EnvelopingMap f) (R : RestrictionModel T.functor)
    {DA : EnvelopingModuleModel (diagonal A)} {DB : EnvelopingModuleModel (diagonal B)}
    {FA : FreeDiagonalSystem A} {FB : FreeDiagonalSystem B}
    (PA : BarDiagonalModel DA FA) (PB : BarDiagonalModel DB FB) where
  map : PA.module ⟶ R.functor.obj PB.module
  normalized : ∀ (x : A) (y : Aᵒᵖ) (r : ℤ) (n : ℕ) (v : PathVertices A n)
    (z : (pathTensor A y.unop v.val x).X (r + (n : ℤ))),
    ((PB.termIso (f.obj x) (op (f.obj y.unop)) r).hom)
      (((restrictionValueIso T R PB.module x y).hom.f r)
        (((moduleComponent map (moduleIndex A A x y)).f r)
          ((PA.termIso x y r).inv
            (includeDiagonal A x y r n
              (((Sigma.ι (fun w : PathVertices A n => pathTensor A y.unop w.val x) v).f
                (r + (n : ℤ))) z))))) =
      includeDiagonal B (f.obj x) (op (f.obj y.unop)) r n
        (((Sigma.ι (fun w : PathVertices B n => pathTensor B (f.obj y.unop) w.val (f.obj x))
          (mappedPath f v)).f (r + (n : ℤ)))
          (((mapPathTensor f y.unop v.val x).f (r + (n : ℤ))) z))

/-- The genuine pushforward counit is the unit-normalized enriched adjunction transpose. -/
structure BarCounitModel {A B : DGCat k} {f : A ⟶ B}
    {T : EnvelopingMap f} {R : RestrictionModel T.functor} (L : ExtensionModel T.functor R)
    {DA : EnvelopingModuleModel (diagonal A)} {DB : EnvelopingModuleModel (diagonal B)}
    {FA : FreeDiagonalSystem A} {FB : FreeDiagonalSystem B}
    {PA : BarDiagonalModel DA FA} {PB : BarDiagonalModel DB FB}
    (F : BarRestrictionMapModel f T R PA PB) where
  map : (L.functor.obj (⟨PA.module, PA.cofibrant⟩ : DGDerivedModules k (enveloping A A))).obj ⟶ PB.module
  normalized :
    ((L.homIso (⟨PA.module, PA.cofibrant⟩ : DGDerivedModules k (enveloping A A)) PB.module).hom.f 0)
      (moduleCycle map) = moduleCycle F.map

/-- The actual representable restriction map is the DG functor's two Hom-factor maps. -/
structure RepresentableRestrictionMapModel {A B : DGCat k} (f : A ⟶ B)
    (T : EnvelopingMap f) (R : RestrictionModel T.functor) (x : A) (y : Aᵒᵖ) where
  map : ((dgYoneda k (C := enveloping A A)).obj (op y.unop, x)) ⟶
    R.functor.obj ((dgYoneda k (C := enveloping B B)).obj (op (f.obj y.unop), f.obj x))
  normalized : ∀ (z : A) (w : Aᵒᵖ) (r : ℤ),
    (moduleComponent map (moduleIndex A A z w)).f r ≫
      (restrictionValueIso T R
        ((dgYoneda k (C := enveloping B B)).obj (op (f.obj y.unop), f.obj x)) z w).hom.f r =
      (f.map y.unop z ⊗ₘ f.map w.unop x).f r

/-- The left-duality base-change map is fixed by representable restriction and the same adjunction. -/
structure DualBaseChangeModel {A B : DGCat k} {f : A ⟶ B}
    {T : EnvelopingMap f} {R : RestrictionModel T.functor} (L : ExtensionModel T.functor R)
    {DA : EnvelopingModuleModel (diagonal A)} {FA : FreeDiagonalSystem A}
    (PA : BarDiagonalModel DA FA) (IA : InverseDualModel PA)
    (J : ModuleLeftDualModel B
      (L.functor.obj (⟨PA.module, PA.cofibrant⟩ : DGDerivedModules k (enveloping A A)))) where
  representable : ∀ (x : A) (y : Aᵒᵖ), RepresentableRestrictionMapModel f T R x y
  transpose : IA.replacement.module ⟶ R.functor.obj J.module
  transpose_eq : ∀ (x : A) (y : Aᵒᵖ) (r : ℤ),
    (moduleComponent transpose (moduleIndex A A x y)).f r ≫
      (restrictionValueIso T R J.module x y).hom.f r =
      (moduleComponent IA.replacement.augmentation (moduleIndex A A x y)).f r ≫
        (IA.valueIso x y).hom.f r ≫
        (homPostcompose PA.module (representable x y).map).f r ≫
        ((L.homIso (⟨PA.module, PA.cofibrant⟩ : DGDerivedModules k (enveloping A A))
          ((dgYoneda k (C := enveloping B B)).obj (op (f.obj y.unop), f.obj x))).inv.f r) ≫
        (J.valueIso (f.obj x) (op (f.obj y.unop))).inv.f r
  map : (L.functor.obj
      (⟨IA.replacement.module, IA.replacement.cofibrant⟩ : DGDerivedModules k (enveloping A A))).obj ⟶
    J.replacement.module
  mate_eq :
    ((L.homIso
        (⟨IA.replacement.module, IA.replacement.cofibrant⟩ : DGDerivedModules k (enveloping A A))
        J.module).hom.f 0) (moduleCycle (map ≫ J.replacement.augmentation)) = moduleCycle transpose
  equivalence : ModuleHomotopyEquivalence map

/-- The source pushforward diagonal is the actual output of the same induction functor. -/
def pushedDiagonal {A B : DGCat k} {f : A ⟶ B}
    {T : EnvelopingMap f} {R : RestrictionModel T.functor} (L : ExtensionModel T.functor R)
    {DA : EnvelopingModuleModel (diagonal A)} {FA : FreeDiagonalSystem A}
    (PA : BarDiagonalModel DA FA) : DGDerivedModules k (enveloping B B) :=
  L.functor.obj (⟨PA.module, PA.cofibrant⟩ : DGDerivedModules k (enveloping A A))

/-- The dual counit is fixed by precomposition with the actual bar counit on every representable. -/
structure DualCounitModel {A B : DGCat k} {f : A ⟶ B}
    {T : EnvelopingMap f} {R : RestrictionModel T.functor} (L : ExtensionModel T.functor R)
    {DA : EnvelopingModuleModel (diagonal A)} {DB : EnvelopingModuleModel (diagonal B)}
    {FA : FreeDiagonalSystem A} {FB : FreeDiagonalSystem B}
    {PA : BarDiagonalModel DA FA} {PB : BarDiagonalModel DB FB}
    {F : BarRestrictionMapModel f T R PA PB} (c : BarCounitModel L F)
    (IB : InverseDualModel PB) (J : ModuleLeftDualModel B (pushedDiagonal L PA)) where
  map : IB.replacement.module ⟶ J.replacement.module
  normalized : ∀ (x : B) (y : Bᵒᵖ) (r : ℤ),
    (moduleComponent map (moduleIndex B B x y)).f r ≫
      (moduleComponent J.replacement.augmentation (moduleIndex B B x y)).f r ≫
      (J.valueIso x y).hom.f r =
      (moduleComponent IB.replacement.augmentation (moduleIndex B B x y)).f r ≫
        (IB.valueIso x y).hom.f r ≫
        (homPrecompose c.map ((dgYoneda k (C := enveloping B B)).obj (op y.unop, x))).f r

/-- Extension followed by the actual left-duality mate acts on every Hom degree. -/
def phiMiddle {A B : DGCat k} {f : A ⟶ B}
    {T : EnvelopingMap f} {R : RestrictionModel T.functor} (L : ExtensionModel T.functor R)
    {DA : EnvelopingModuleModel (diagonal A)} {FA : FreeDiagonalSystem A}
    {PA : BarDiagonalModel DA FA} {IA : InverseDualModel PA}
    {J : ModuleLeftDualModel B (pushedDiagonal L PA)} (d : DualBaseChangeModel L PA IA J) :
    dgHomComplex k IA.replacement.module PA.module ⟶
      dgHomComplex k J.replacement.module (pushedDiagonal L PA).obj :=
  L.functor.map
      (⟨IA.replacement.module, IA.replacement.cofibrant⟩ : DGDerivedModules k (enveloping A A))
      (⟨PA.module, PA.cofibrant⟩ : DGDerivedModules k (enveloping A A)) ≫
    homPrecompose d.equivalence.inverse (pushedDiagonal L PA).obj

/-- Proposition4.3's map is the actual extension, dual counit, and counit composition. -/
def phiTransfer {A B : DGCat k} {f : A ⟶ B}
    {T : EnvelopingMap f} {R : RestrictionModel T.functor} (L : ExtensionModel T.functor R)
    {DA : EnvelopingModuleModel (diagonal A)} {DB : EnvelopingModuleModel (diagonal B)}
    {FA : FreeDiagonalSystem A} {FB : FreeDiagonalSystem B}
    {PA : BarDiagonalModel DA FA} {PB : BarDiagonalModel DB FB}
    {IA : InverseDualModel PA} {IB : InverseDualModel PB}
    {F : BarRestrictionMapModel f T R PA PB} (c : BarCounitModel L F)
    {J : ModuleLeftDualModel B (pushedDiagonal L PA)} (d : DualBaseChangeModel L PA IA J)
    (cdual : DualCounitModel L c IB J) :
    dgHomComplex k IA.replacement.module PA.module ⟶ dgHomComplex k IB.replacement.module PB.module :=
  phiMiddle L d ≫ homPrecompose cdual.map (pushedDiagonal L PA).obj ≫
    homPostcompose IB.replacement.module c.map

end MathlibExt.CategoryTheory.DGBimodulePushforwardModels
