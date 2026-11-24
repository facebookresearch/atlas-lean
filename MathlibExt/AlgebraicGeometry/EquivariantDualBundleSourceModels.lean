/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EquivariantCharacterLineModels
public import MathlibExt.AlgebraicGeometry.GlobalPOTVirtualClass

/-!
# The quotient of the actual negative-dual bundle

The action is fixed by its original universal linear form and the
original bundle linearization. On the quotient, every affine-point
module is identified with those actual invariant forms on the original
torsor, including addition, scalar multiplication and all reindex maps.
The native stack bundle has the literal quotient of the original total
scheme as its total space. BGm is allowed; no DM condition is imposed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EquivariantDualBundleSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels LinearizedLineBundles GlobalPOTVirtualClass
open AlgebraicEquivariantChowModels EquivariantCharacterLineModels
open StackCycleGeometry StackAffineModules StackVectorBundles StackFibreModels

/-- Reindex the original form by the actual module pullback and unit comparison. -/
def pullForm {X Y V : Over base} (E : X.left.Modules) (p : Y ⟶ X)
    (s : (Scheme.Modules.pullback p.left).obj E ⟶ SheafOfModules.unit Y.left.ringCatSheaf)
    (g : V ⟶ Y) :
    (Scheme.Modules.pullback (g ≫ p).left).obj E ⟶ SheafOfModules.unit V.left.ringCatSheaf :=
  (Scheme.Modules.pullbackComp g.left p.left).inv.app E ≫
    (Scheme.Modules.pullback g.left).map s ≫ (AlgebraicBundleGeometry.pullbackUnit _ _ g.left).hom

/-- Equivariance of a linear form uses the original inverse fibre transport. -/
def InvariantForm {X Y : Over base} [ModObj Gm X] [ModObj Gm Y]
    {E : X.left.Modules} (L : Linearization Gm X E) (p : Y ⟶ X)
    (hp : γ[Gm,Y] ≫ p = (Gm ◁ p) ≫ γ[Gm,X])
    (s : (Scheme.Modules.pullback p.left).obj E ⟶ SheafOfModules.unit Y.left.ringCatSheaf) : Prop :=
  pullForm E p s γ[Gm,Y] =
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hp)).hom.app E ≫
      reindexHom (Gm ◁ p).left L.comparison.hom ≫
        (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (whiskerLeft_snd Gm p))).hom.app E ≫
          pullForm E p s (snd Gm Y)

variable {X : Over base} [ModObj Gm X] {E : X.left.Modules}
  (L : Linearization Gm X E) {r : ℕ} (B : DualBundleModel X E r)
  [ModObj Gm B.total]
  (hp : γ[Gm,B.total] ≫ B.projection = (Gm ◁ B.projection) ≫ γ[Gm,X])

/-- This condition determines the action on the same universal dual bundle. -/
def DualActionNormalized : Prop := InvariantForm L B.projection hp B.universalForm

variable (Q : EquivariantSource X)

def torsorForms (a : AffinePoint Q.quotient.stack) : Type :=
  let P := (Q.quotient.fibre a.obj.base).functor.obj a.obj.fiber
  letI := P.torsor.action
  {s : (Scheme.Modules.pullback P.map.left).obj E ⟶
      SheafOfModules.unit P.torsor.total.left.ringCatSheaf //
    InvariantForm L P.map P.equivariant s}

/-- The source is the actual invariant-form module on every original torsor. -/
structure TorsorFormModule (M : FPModule Q.quotient.stack) where
  forms : ∀ a : AffinePoint Q.quotient.stack, M.presheaf.obj (op a) ≃ torsorForms L Q a
  add : ∀ (a : AffinePoint Q.quotient.stack) (s t : M.presheaf.obj (op a)),
    (forms a (s+t)).1 = (forms a s).1 + (forms a t).1
  scalar : ∀ (a : AffinePoint Q.quotient.stack) (c : Γ(a.obj.base.left, ⊤))
    (s : M.presheaf.obj (op a)),
    (forms a (c • s)).1 = (forms a s).1 ≫
      scalarEnd ((Q.quotient.fibre a.obj.base).functor.obj a.obj.fiber).torsor.total.left
        (SheafOfModules.unit
          ((Q.quotient.fibre a.obj.base).functor.obj a.obj.fiber).torsor.total.left.ringCatSheaf)
        (((Q.quotient.fibre a.obj.base).functor.obj a.obj.fiber).torsor.projection.left.appTop c)
  arrows : ∀ {a b : (AffinePoint Q.quotient.stack)ᵒᵖ} (f : a ⟶ b)
    (s : M.presheaf.obj a),
    HEq (forms b.unop (M.presheaf.restrictₛₗ f s)).1
      (pullForm E ((Q.quotient.fibre a.unop.obj.base).functor.obj a.unop.obj.fiber).map
        (forms a.unop s).1 (torsorMap Q f.unop))

variable (R : EquivariantSource B.total) (M : EquivariantMap R Q B.projection hp)

/-- A represented module section evaluates by the same original universal form. -/
structure SectionLiftData {a : AffinePoint Q.quotient.stack}
    (b : AffinePoint R.quotient.stack) (s : torsorForms L Q a) where
  baseIso : a.obj.base ≅ b.obj.base
  torsorIso : ((Q.quotient.fibre a.obj.base).functor.obj a.obj.fiber).torsor.total ≅
    ((R.quotient.fibre b.obj.base).functor.obj b.obj.fiber).torsor.total
  projection : torsorIso.hom ≫
      ((R.quotient.fibre b.obj.base).functor.obj b.obj.fiber).torsor.projection =
    ((Q.quotient.fibre a.obj.base).functor.obj a.obj.fiber).torsor.projection ≫ baseIso.hom
  equivariant : (Gm ◁ torsorIso.hom) ≫
      ((R.quotient.fibre b.obj.base).functor.obj b.obj.fiber).torsor.action.smul =
    ((Q.quotient.fibre a.obj.base).functor.obj a.obj.fiber).torsor.action.smul ≫ torsorIso.hom
  over : (torsorIso.hom ≫ ((R.quotient.fibre b.obj.base).functor.obj b.obj.fiber).map) ≫
      B.projection = ((Q.quotient.fibre a.obj.base).functor.obj a.obj.fiber).map
  normalized : s.1 = pulledForm E B.projection B.universalForm
    ((Q.quotient.fibre a.obj.base).functor.obj a.obj.fiber).map
    (torsorIso.hom ≫ ((R.quotient.fibre b.obj.base).functor.obj b.obj.fiber).map) over

/-- The total stack and projection are exactly the quotient of the original bundle. -/
structure QuotientDualBundle where
  actionNormalized : DualActionNormalized L B hp
  module : VectorModule Q.quotient.stack r
  forms : TorsorFormModule L Q module.val
  comparison : AffinePoint R.quotient.stack ≌ (sectionPresheaf module.val).Elementsᵒᵖ
  overBase : comparison.functor ⋙ sectionForget module.val ≅ affineMap M.map
  fibres : ∀ (T : Over base) (x : Q.quotient.stack.Fibre T), SchemeFibreModel M.map T x
  sectionNormalization : ∀ (a : AffinePoint Q.quotient.stack) (s : module.val.presheaf.obj (op a)),
    SectionLiftData L B Q R
      (comparison.inverse.obj (op ((sectionPresheaf module.val).elementsMk (op a) s)))
      (forms.forms a s)
  /-- The section lift uses the specified arrow `a ⟶ M.map b` (the comparison counit followed by
  `overBase`) for its base, and the torsor map of that arrow followed by the fibre comparison of
  `M` for its torsor isomorphism, rather than independently chosen isomorphisms (which could hide
  a nonlinear gauge on the fibre). -/
  sectionArrow : ∀ (a : AffinePoint Q.quotient.stack) (s : module.val.presheaf.obj (op a)),
    let e := op ((sectionPresheaf module.val).elementsMk (op a) s)
    let b := comparison.inverse.obj e
    let φ : a ⟶ (affineMap M.map).obj b :=
      ((sectionForget module.val).mapIso (comparison.counitIso.app e)).inv ≫ (overBase.app b).hom
    (sectionNormalization a s).baseIso.hom = φ.hom.base ∧
      (sectionNormalization a s).torsorIso.hom =
        torsorMap Q φ ≫ ((M.fibre b.obj.base).hom.app b.obj.fiber).iso.hom

/-- The native stack bundle reuses the literal original quotient total space. -/
@[implicit_reducible] def QuotientDualBundle.native
    (P : QuotientDualBundle L B hp Q R M) : VectorBundle Q.quotient.stack :=
  { rank := r
    module := P.module
    total := R.quotient.stack
    projection := M.map
    comparison := P.comparison
    overBase := P.overBase
    fibres := P.fibres }

end MathlibExt.AlgebraicGeometry.EquivariantDualBundleSourceModels
