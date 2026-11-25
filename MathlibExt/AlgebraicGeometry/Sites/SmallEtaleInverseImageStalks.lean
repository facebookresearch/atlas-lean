/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageCoherence
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricStalkExactness
public import MathlibExt.CategoryTheory.Sites.Point.Mates
public import Mathlib.CategoryTheory.Sites.Point.Comap

/-! # Actual inverse image preserves the original geometric stalks

The common stalk is the same original-neighborhood filtered colimit from the
geometric exactness criterion. The canonical comparison is constructed from
the actual original base-change maps and the same concrete adjunctions.
Both identity and composition diagrams use the previously proved canonical
sheaf-functor comparisons. No comparison or coherence premise is supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

instance smallEtaleBaseChangeIsContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  smallEtaleBaseChange_isContinuous f

instance smallEtaleBaseChangeRepresentablyFlat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RepresentablyFlat (smallEtaleBaseChange f) := by
  let : PreservesFiniteLimits (smallEtaleBaseChange f) :=
    smallEtaleBaseChange_preservesFiniteLimits f
  exact flat_of_preservesFiniteLimits (smallEtaleBaseChange f)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The literal geometric fiber after actual base change identifies with the
literal fiber at the same geometric point composed with the original `f`. -/
def smallEtaleBaseChangePointFiberIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    smallEtaleBaseChange f ⋙ (Scheme.pointSmallEtale x).fiber ≅
      (Scheme.pointSmallEtale (x ≫ f)).fiber :=
  let a := CategoryTheory.Over.mk x
  let H := coyoneda.obj (op a)
  (Functor.associator (smallEtaleBaseChange f) (Scheme.Etale.forget X) H).symm ≪≫
    Functor.associator (Scheme.Etale.forget Y) (CategoryTheory.Over.pullback f) H ≪≫
    (Functor.isoWhiskerLeft (Scheme.Etale.forget Y)
      ((CategoryTheory.Over.mapPullbackAdj f).compCoyonedaIso.app (op a))).symm

/-- The category of actual geometric neighborhoods after base change is
initially small, derived from the original image geometric point. -/
instance smallEtaleBaseChangePointInitiallySmall {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    InitiallySmall.{u} (smallEtaleBaseChange f ⋙ (Scheme.pointSmallEtale x).fiber).Elements := by
  let F := smallEtaleBaseChange f ⋙ (Scheme.pointSmallEtale x).fiber
  let G := (Scheme.pointSmallEtale (x ≫ f)).fiber
  let e : F.Elements ≌ G.Elements :=
    (Functor.Elements.structuredArrowEquivalence F).trans
      ((StructuredArrow.mapNatIso (smallEtaleBaseChangePointFiberIso f x)).trans
        (Functor.Elements.structuredArrowEquivalence G).symm)
  exact initiallySmall_of_initial_of_initiallySmall.{u} e.inverse

/-- The point obtained by the actual original small-site base change. -/
def smallEtaleGeometricPointComap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) : Y.smallEtaleTopology.Point.{u} :=
  (Scheme.pointSmallEtale x).comap (smallEtaleBaseChange f)
    (smallEtaleBaseChange_coverPreserving f)

/-- This actual comap point is the original geometric point `x ≫ f`. -/
def smallEtaleGeometricPointComapIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    smallEtaleGeometricPointComap f x ≅ Scheme.pointSmallEtale (x ≫ f) where
  hom := ⟨(smallEtaleBaseChangePointFiberIso f x).inv⟩
  inv := ⟨(smallEtaleBaseChangePointFiberIso f x).hom⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleBaseChangePointFiberIso f x).hom_inv_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleBaseChangePointFiberIso f x).inv_hom_id

/-- The same point comparison induces the comparison of actual common-universe
abelian-sheaf fiber functors. -/
def smallEtaleGeometricPointComapSheafFiberIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    (smallEtaleGeometricPointComap f x).sheafFiber (A := AddCommGrpCat.{max u w}) ≅
      (Scheme.pointSmallEtale (x ≫ f)).sheafFiber (A := AddCommGrpCat.{max u w}) where
  hom := (smallEtaleGeometricPointComapIso f x).inv.sheafFiber
  inv := (smallEtaleGeometricPointComapIso f x).hom.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (smallEtaleGeometricPointComapIso f x).hom_inv_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (smallEtaleGeometricPointComapIso f x).inv_hom_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _

instance smallEtaleBaseChangePushforwardIsRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max u w}
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint :=
  (smallEtaleInverseImageAdjunction.{u, w} f).isRightAdjoint

/-- The actual affine construction is the same left adjoint as the chosen
full original-site pullback; no full-site presheaf Kan premise is needed. -/
def smallEtaleInverseImageFullSitePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleInverseImage.{u, w} f ≅
      (smallEtaleBaseChange f).sheafPullback AddCommGrpCat.{max u w}
        Y.smallEtaleTopology X.smallEtaleTopology :=
  Adjunction.leftAdjointUniq (smallEtaleInverseImageAdjunction.{u, w} f)
    ((smallEtaleBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{max u w}
      Y.smallEtaleTopology X.smallEtaleTopology)

/-- Actual inverse-image stalks are the original stalks at the image geometric
point, naturally on every common-universe sheaf and sheaf morphism. -/
def smallEtaleInverseImageGeometricStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    smallEtaleInverseImage.{u, w} f ⋙
        (Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{max u w}) ≅
      (Scheme.pointSmallEtale (x ≫ f)).sheafFiber (A := AddCommGrpCat.{max u w}) :=
  Functor.isoWhiskerRight (smallEtaleInverseImageFullSitePullbackIso.{u, w} f)
      ((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{max u w})) ≪≫
    ((Scheme.pointSmallEtale x).sheafFiberComapIso (smallEtaleBaseChange f)
      (smallEtaleBaseChange_coverPreserving f) AddCommGrpCat.{max u w}).symm ≪≫
    smallEtaleGeometricPointComapSheafFiberIso.{u, w} f x

/-- The actual geometric stalk functor preserves finite limits in the common
coefficient universe. -/
theorem smallEtaleGeometricSheafFiber_preservesFiniteLimits {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteLimits ((Scheme.pointSmallEtale x).sheafFiber
      (A := AddCommGrpCat.{max u w})) := by
  infer_instance

/-- After every actual geometric point, inverse image preserves finite limits.
This statement does not assume conservativity in a larger coefficient universe. -/
theorem smallEtaleInverseImageAtGeometricPoint_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteLimits (smallEtaleInverseImage.{u, w} f ⋙
      (Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{max u w})) := by
  let : PreservesFiniteLimits ((Scheme.pointSmallEtale (x ≫ f)).sheafFiber
      (A := AddCommGrpCat.{max u w})) :=
    smallEtaleGeometricSheafFiber_preservesFiniteLimits.{u, w} (x ≫ f)
  exact preservesFiniteLimits_of_natIso
    (smallEtaleInverseImageGeometricStalkIso.{u, w} f x).symm

/-- The original geometric point's common-universe fiber after base change
is the same original image point's lifted fiber. -/
def smallEtaleBaseChangeCommonPointFiberIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    smallEtaleBaseChange f ⋙ (smallEtaleGeometricPointCommon.{u, w} x).fiber ≅
      (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).fiber :=
  (Functor.associator (smallEtaleBaseChange f) (Scheme.pointSmallEtale x).fiber
    uliftFunctor.{w, u}).symm ≪≫
      Functor.isoWhiskerRight (smallEtaleBaseChangePointFiberIso f x) uliftFunctor.{w, u}

instance smallEtaleBaseChangeCommonPointInitiallySmall {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    InitiallySmall.{max u w}
      (smallEtaleBaseChange f ⋙ (smallEtaleGeometricPointCommon.{u, w} x).fiber).Elements := by
  let F := smallEtaleBaseChange f ⋙ (smallEtaleGeometricPointCommon.{u, w} x).fiber
  let G := (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).fiber
  let e : F.Elements ≌ G.Elements :=
    (Functor.Elements.structuredArrowEquivalence F).trans
      ((StructuredArrow.mapNatIso (smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x)).trans
        (Functor.Elements.structuredArrowEquivalence G).symm)
  exact initiallySmall_of_initial_of_initiallySmall e.inverse

/-- The actual common-universe comap point along the original base change. -/
def smallEtaleCommonGeometricPointComap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) : Y.smallEtaleTopology.Point.{max u w} :=
  (smallEtaleGeometricPointCommon.{u, w} x).comap (smallEtaleBaseChange f)
    (smallEtaleBaseChange_coverPreserving f)

/-- The common-universe comap is the same prescribed original image geometric point. -/
def smallEtaleCommonGeometricPointComapIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    smallEtaleCommonGeometricPointComap.{u, w} f x ≅
      smallEtaleGeometricPointCommon.{u, w} (x ≫ f) where
  hom := ⟨(smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).inv⟩
  inv := ⟨(smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).hom⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).hom_inv_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).inv_hom_id

/-- The same point comparison induces the comparison of actual abelian-sheaf stalks. -/
def smallEtaleCommonGeometricPointComapSheafFiberIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    (smallEtaleCommonGeometricPointComap.{u, w} f x).sheafFiber
        (A := AddCommGrpCat.{max u w}) ≅
      (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).sheafFiber
        (A := AddCommGrpCat.{max u w}) where
  hom := (smallEtaleCommonGeometricPointComapIso.{u, w} f x).inv.sheafFiber
  inv := (smallEtaleCommonGeometricPointComapIso.{u, w} f x).hom.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (smallEtaleCommonGeometricPointComapIso.{u, w} f x).hom_inv_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (smallEtaleCommonGeometricPointComapIso.{u, w} f x).inv_hom_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _

/-- Actual inverse image has the original image-point stalk in the same common universe. -/
def smallEtaleInverseImageCommonGeometricStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    smallEtaleInverseImage.{u, w} f ⋙
        (smallEtaleGeometricPointCommon.{u, w} x).sheafFiber (A := AddCommGrpCat.{max u w}) ≅
      (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).sheafFiber
        (A := AddCommGrpCat.{max u w}) :=
  Functor.isoWhiskerRight (smallEtaleInverseImageFullSitePullbackIso.{u, w} f)
      ((smallEtaleGeometricPointCommon.{u, w} x).sheafFiber (A := AddCommGrpCat.{max u w})) ≪≫
    ((smallEtaleGeometricPointCommon.{u, w} x).sheafFiberComapIso (smallEtaleBaseChange f)
      (smallEtaleBaseChange_coverPreserving f) AddCommGrpCat.{max u w}).symm ≪≫
    smallEtaleCommonGeometricPointComapSheafFiberIso.{u, w} f x

theorem smallEtaleCommonGeometricSheafFiber_preservesFiniteLimits {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteLimits ((smallEtaleGeometricPointCommon.{u, w} x).sheafFiber
      (A := AddCommGrpCat.{max u w})) := by
  infer_instance

theorem smallEtaleInverseImageAtCommonGeometricPoint_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteLimits (smallEtaleInverseImage.{u, w} f ⋙
      (smallEtaleGeometricPointCommon.{u, w} x).sheafFiber (A := AddCommGrpCat.{max u w})) := by
  let : PreservesFiniteLimits ((smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).sheafFiber
      (A := AddCommGrpCat.{max u w})) :=
    smallEtaleCommonGeometricSheafFiber_preservesFiniteLimits.{u, w} (x ≫ f)
  exact preservesFiniteLimits_of_natIso
    (smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x).symm

end AlgebraicGeometry.Scheme.DerivedSections



namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The right-adjoint comparison belonging to the same actual common-point stalk isomorphism. -/
def smallEtaleInverseImageCommonGeometricStalkRightIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) ≅
      (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) ⋙ smallEtaleDirectImage.{u, max u w} f :=
  conjugateIsoEquiv
    (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).skyscraperSheafAdjunction
    ((smallEtaleInverseImageAdjunction.{u, w} f).comp
      (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafAdjunction)
    (smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same stalk comparison has the mate supplied by its actual comap-point morphism. -/
theorem smallEtaleInverseImageCommonGeometricStalkRightIso_hom_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) :
    (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x).hom =
      conjugateEquiv
        (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).skyscraperSheafAdjunction
        (smallEtaleCommonGeometricPointComap.{u, w} f x).skyscraperSheafAdjunction
        ((smallEtaleCommonGeometricPointComapIso.{u, w} f x).inv.sheafFiber
          (A := AddCommGrpCat.{max u w})) := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} x
  let Ψ := smallEtaleGeometricPointCommon.{u, w} (x ≫ f)
  let Φf := smallEtaleCommonGeometricPointComap.{u, w} f x
  let a := smallEtaleInverseImageAdjunction.{u, w} f
  let a' := (smallEtaleBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{max u w}
    Y.smallEtaleTopology X.smallEtaleTopology
  let ε := smallEtaleInverseImageFullSitePullbackIso.{u, w} f
  let β := Φ.sheafFiberComapIso (smallEtaleBaseChange f)
    (smallEtaleBaseChange_coverPreserving f) AddCommGrpCat.{max u w}
  let τ := (smallEtaleCommonGeometricPointComapIso.{u, w} f x).inv.sheafFiber
    (A := AddCommGrpCat.{max u w})
  have hu : conjugateEquiv (a'.comp Φ.skyscraperSheafAdjunction)
      (a.comp Φ.skyscraperSheafAdjunction)
      (Functor.whiskerRight ε.hom (Φ.sheafFiber (A := AddCommGrpCat.{max u w}))) = 𝟙 _ := by
    rw [conjugateEquiv_whiskerRight]
    have he : conjugateEquiv a' a ε.hom = 𝟙 _ :=
      (conjugateEquiv a' a).apply_symm_apply (𝟙 _)
    rw [he]
    rfl
  have hc : conjugateEquiv Φf.skyscraperSheafAdjunction
      (a'.comp Φ.skyscraperSheafAdjunction) β.inv = 𝟙 _ := by
    simp [Φf, smallEtaleCommonGeometricPointComap, Φ, a', β,
      GrothendieckTopology.Point.sheafFiberComapIso,
      GrothendieckTopology.Point.skyscraperSheafFunctorCompSheafPushforwardContinuous]
    rfl
  change conjugateEquiv Ψ.skyscraperSheafAdjunction
    (a.comp Φ.skyscraperSheafAdjunction)
      (Functor.whiskerRight ε.hom (Φ.sheafFiber (A := AddCommGrpCat.{max u w})) ≫ β.inv ≫ τ) =
    conjugateEquiv Ψ.skyscraperSheafAdjunction Φf.skyscraperSheafAdjunction τ
  rw [← Category.assoc,
    ← conjugateEquiv_comp Ψ.skyscraperSheafAdjunction Φf.skyscraperSheafAdjunction
      (a.comp Φ.skyscraperSheafAdjunction),
    ← conjugateEquiv_comp Φf.skyscraperSheafAdjunction
      (a'.comp Φ.skyscraperSheafAdjunction) (a.comp Φ.skyscraperSheafAdjunction), hc, hu]
  simp

/-- The same actual stalk comparison's mate sends each product coordinate
through the original geometric base-change fiber map. -/
theorem smallEtaleInverseImageCommonGeometricStalkRightIso_hom_app_π
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (M : AddCommGrpCat.{max u w}) (U : Y.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj ((smallEtaleBaseChange f).obj U)) :
    ((smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x).hom.app M).hom.app (op U) ≫
        Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
          ((smallEtaleBaseChange f).obj U)) => M) z =
      Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).fiber.obj U) => M)
        ((smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).hom.app U z) := by
  rw [smallEtaleInverseImageCommonGeometricStalkRightIso_hom_eq]
  exact GrothendieckTopology.Point.conjugateEquiv_sheafFiber_app_π
    (smallEtaleCommonGeometricPointComapIso.{u, w} f x).inv M U z

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original base-change fiber comparison is the pullback projection on neighborhoods. -/
theorem smallEtaleBaseChangePointFiberIso_hom_app_left {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (U : Y.Etale)
    (z : (Scheme.pointSmallEtale x).fiber.obj ((smallEtaleBaseChange f).obj U)) :
    ((smallEtaleBaseChangePointFiberIso f x).hom.app U z).left =
      z.left ≫ pullback.fst U.hom f := by
  change (((CategoryTheory.Over.mapPullbackAdj f).homEquiv (CategoryTheory.Over.mk x)
    ((Scheme.Etale.forget Y).obj U)).symm z).left = z.left ≫ pullback.fst U.hom f
  simp [CategoryTheory.Over.mapPullbackAdj]

/-- The common-universe comparison preserves the same original neighborhood projection. -/
theorem smallEtaleBaseChangeCommonPointFiberIso_hom_app_down_left {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (U : Y.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj ((smallEtaleBaseChange f).obj U)) :
    ((smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).hom.app U z).down.left =
      z.down.left ≫ pullback.fst U.hom f := by
  exact smallEtaleBaseChangePointFiberIso_hom_app_left f x U z.down

/-- Actual common geometric fibers send an original neighborhood arrow to composition. -/
theorem smallEtaleGeometricPointCommon_map_down_left {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) {U V : X.Etale} (g : U ⟶ V)
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj U) :
    ((smallEtaleGeometricPointCommon.{u, w} x).fiber.map g z).down.left = z.down.left ≫ g.left :=
  rfl

/-- The canonical original image-point comparison for the identity morphism. -/
def smallEtaleGeometricImageIdFiberIso {X : Scheme.{u}} (x : Spec (.of Ω) ⟶ X) :
    (Scheme.pointSmallEtale (x ≫ 𝟙 X)).fiber ≅ (Scheme.pointSmallEtale x).fiber :=
  Functor.isoWhiskerLeft (Scheme.Etale.forget X)
    (coyoneda.mapIso (((CategoryTheory.Over.mapId X).app (CategoryTheory.Over.mk x)).op))

/-- The same identity image comparison in the common fiber-element universe. -/
def smallEtaleCommonGeometricImageIdFiberIso {X : Scheme.{u}} (x : Spec (.of Ω) ⟶ X) :
    (smallEtaleGeometricPointCommon.{u, w} (x ≫ 𝟙 X)).fiber ≅
      (smallEtaleGeometricPointCommon.{u, w} x).fiber :=
  Functor.isoWhiskerRight (smallEtaleGeometricImageIdFiberIso x) uliftFunctor.{w, u}

/-- The canonical original comparison of iterated and single image geometric points. -/
def smallEtaleGeometricImageCompFiberIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) :
    (Scheme.pointSmallEtale ((x ≫ f) ≫ g)).fiber ≅
      (Scheme.pointSmallEtale (x ≫ f ≫ g)).fiber :=
  Functor.isoWhiskerLeft (Scheme.Etale.forget Z)
    (coyoneda.mapIso (((CategoryTheory.Over.mapComp f g).app
      (CategoryTheory.Over.mk x)).symm.op))

/-- The same actual composition image comparison in the common fiber-element universe. -/
def smallEtaleCommonGeometricImageCompFiberIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) :
    (smallEtaleGeometricPointCommon.{u, w} ((x ≫ f) ≫ g)).fiber ≅
      (smallEtaleGeometricPointCommon.{u, w} (x ≫ f ≫ g)).fiber :=
  Functor.isoWhiskerRight (smallEtaleGeometricImageCompFiberIso f g x) uliftFunctor.{w, u}

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Identity image transport retains the original geometric neighborhood map. -/
theorem smallEtaleCommonGeometricImageIdFiberIso_hom_app_down_left {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) (U : X.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} (x ≫ 𝟙 X)).fiber.obj U) :
    ((smallEtaleCommonGeometricImageIdFiberIso.{u, w} x).hom.app U z).down.left = z.down.left := by
  simp [smallEtaleCommonGeometricImageIdFiberIso, smallEtaleGeometricImageIdFiberIso,
    Functor.isoWhiskerRight, Functor.isoWhiskerLeft, CategoryTheory.Over.mapId,
    NatIso.ofComponents, coyoneda]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Composition image transport retains the original geometric neighborhood map. -/
theorem smallEtaleCommonGeometricImageCompFiberIso_hom_app_down_left {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) (U : Z.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} ((x ≫ f) ≫ g)).fiber.obj U) :
    ((smallEtaleCommonGeometricImageCompFiberIso.{u, w} f g x).hom.app U z).down.left =
      z.down.left := by
  simp [smallEtaleCommonGeometricImageCompFiberIso, smallEtaleGeometricImageCompFiberIso,
    Functor.isoWhiskerRight, Functor.isoWhiskerLeft, CategoryTheory.Over.mapComp,
    NatIso.ofComponents, coyoneda]

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The single fiber-product projection is the iterated projection under the
same canonical base-change comparison. -/
theorem smallEtaleBaseChangeComp_inv_app_left_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Etale) :
    ((smallEtaleBaseChangeComp f g).inv.app U).left ≫ pullback.fst U.hom (f ≫ g) =
      pullback.fst (pullback.snd U.hom g) f ≫ pullback.fst U.hom g := by
  simp [smallEtaleBaseChangeComp, MorphismProperty.Over.pullbackComp,
    NatIso.ofComponents, MorphismProperty.Over.isoMk]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual identity base-change fiber comparison agrees with the canonical
original image-point identity and the preceding BaseId comparison. -/
theorem smallEtaleBaseChangeCommonPointFiberIso_id {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    smallEtaleBaseChangeCommonPointFiberIso.{u, w} (𝟙 X) x ≪≫
        smallEtaleCommonGeometricImageIdFiberIso.{u, w} x =
      Functor.isoWhiskerRight (smallEtaleBaseChangeId X)
        (smallEtaleGeometricPointCommon.{u, w} x).fiber ≪≫
        Functor.leftUnitor (smallEtaleGeometricPointCommon.{u, w} x).fiber := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  ext : 1
  apply DFunLike.ext
  intro z
  apply ULift.ext
  apply (CategoryTheory.Over.forget X).map_injective
  simp only [Over.forget_obj, Over.mk_left, Etale.forget_obj_left, pointSmallEtale_fiber,
    Functor.comp_obj, Functor.flip_obj_obj, yoneda_obj_obj, Iso.trans_hom, NatTrans.comp_app,
    comp_apply, Over.forget_map, Functor.isoWhiskerRight_hom, Functor.id_obj,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Category.comp_id,
    smallEtaleCommonGeometricImageIdFiberIso_hom_app_down_left,
    smallEtaleGeometricPointCommon_map_down_left, smallEtaleBaseChangeId_hom_app_left]
  exact smallEtaleBaseChangeCommonPointFiberIso_hom_app_down_left (𝟙 X) x U z

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The two actual base-change fiber comparisons agree with the same original
image-point composition and the preceding BaseComp comparison. -/
theorem smallEtaleBaseChangeCommonPointFiberIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) :
    Functor.isoWhiskerLeft (smallEtaleBaseChange g)
        (smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x) ≪≫
        smallEtaleBaseChangeCommonPointFiberIso.{u, w} g (x ≫ f) ≪≫
        smallEtaleCommonGeometricImageCompFiberIso.{u, w} f g x =
      (Functor.associator (smallEtaleBaseChange g) (smallEtaleBaseChange f)
        (smallEtaleGeometricPointCommon.{u, w} x).fiber).symm ≪≫
        Functor.isoWhiskerRight (smallEtaleBaseChangeComp f g).symm
          (smallEtaleGeometricPointCommon.{u, w} x).fiber ≪≫
        smallEtaleBaseChangeCommonPointFiberIso.{u, w} (f ≫ g) x := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  ext : 1
  apply DFunLike.ext
  intro z
  apply ULift.ext
  apply (CategoryTheory.Over.forget Z).map_injective
  simp only [Over.forget_obj, Over.mk_left, Etale.forget_obj_left, pointSmallEtale_fiber,
    Functor.comp_obj, Functor.flip_obj_obj, yoneda_obj_obj, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app, comp_apply,
    Over.forget_map, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp]
  calc
    _ = ((smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).hom.app
          ((smallEtaleBaseChange g).obj U) z).down.left ≫ pullback.fst U.hom g :=
      smallEtaleBaseChangeCommonPointFiberIso_hom_app_down_left g (x ≫ f) U _
    _ = (z.down.left ≫ pullback.fst (pullback.snd U.hom g) f) ≫ pullback.fst U.hom g :=
      congrArg (fun k => k ≫ pullback.fst U.hom g)
        (smallEtaleBaseChangeCommonPointFiberIso_hom_app_down_left f x
          ((smallEtaleBaseChange g).obj U) z)
    _ = z.down.left ≫ (pullback.fst (pullback.snd U.hom g) f ≫ pullback.fst U.hom g) :=
      Category.assoc _ _ _
    _ = z.down.left ≫
          (((smallEtaleBaseChangeComp f g).inv.app U).left ≫ pullback.fst U.hom (f ≫ g)) :=
      congrArg (fun k => z.down.left ≫ k) (smallEtaleBaseChangeComp_inv_app_left_fst f g U).symm
    _ = (z.down.left ≫ ((smallEtaleBaseChangeComp f g).inv.app U).left) ≫
          pullback.fst U.hom (f ≫ g) := (Category.assoc _ _ _).symm
    _ = ((smallEtaleGeometricPointCommon.{u, w} x).fiber.map
          ((smallEtaleBaseChangeComp f g).inv.app U) z).down.left ≫
          pullback.fst U.hom (f ≫ g) :=
      congrArg (fun k => k ≫ pullback.fst U.hom (f ≫ g))
        (smallEtaleGeometricPointCommon_map_down_left x
          ((smallEtaleBaseChangeComp f g).inv.app U) z).symm
    _ = _ := (smallEtaleBaseChangeCommonPointFiberIso_hom_app_down_left (f ≫ g) x U _).symm

/-- Canonical identity comparison of the original common geometric points. -/
def smallEtaleCommonGeometricImageIdIso {X : Scheme.{u}} (x : Spec (.of Ω) ⟶ X) :
    smallEtaleGeometricPointCommon.{u, w} (x ≫ 𝟙 X) ≅ smallEtaleGeometricPointCommon.{u, w} x where
  hom := ⟨(smallEtaleCommonGeometricImageIdFiberIso.{u, w} x).inv⟩
  inv := ⟨(smallEtaleCommonGeometricImageIdFiberIso.{u, w} x).hom⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleCommonGeometricImageIdFiberIso.{u, w} x).hom_inv_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleCommonGeometricImageIdFiberIso.{u, w} x).inv_hom_id

/-- Canonical comparison of the iterated and single original image geometric points. -/
def smallEtaleCommonGeometricImageCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) :
    smallEtaleGeometricPointCommon.{u, w} ((x ≫ f) ≫ g) ≅
      smallEtaleGeometricPointCommon.{u, w} (x ≫ f ≫ g) where
  hom := ⟨(smallEtaleCommonGeometricImageCompFiberIso.{u, w} f g x).inv⟩
  inv := ⟨(smallEtaleCommonGeometricImageCompFiberIso.{u, w} f g x).hom⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleCommonGeometricImageCompFiberIso.{u, w} f g x).hom_inv_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (smallEtaleCommonGeometricImageCompFiberIso.{u, w} f g x).inv_hom_id

/-- The same image-point identity comparison on actual common geometric stalks. -/
def smallEtaleCommonGeometricStalkImageIdIso {X : Scheme.{u}} (x : Spec (.of Ω) ⟶ X) :
    smallEtaleCommonGeometricStalk.{u, w} (x ≫ 𝟙 X) ≅ smallEtaleCommonGeometricStalk.{u, w} x where
  hom := (smallEtaleCommonGeometricImageIdIso.{u, w} x).inv.sheafFiber
  inv := (smallEtaleCommonGeometricImageIdIso.{u, w} x).hom.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (smallEtaleCommonGeometricImageIdIso.{u, w} x).hom_inv_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (smallEtaleCommonGeometricImageIdIso.{u, w} x).inv_hom_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _

/-- The same image-point composition comparison on actual common geometric stalks. -/
def smallEtaleCommonGeometricStalkImageCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) :
    smallEtaleCommonGeometricStalk.{u, w} ((x ≫ f) ≫ g) ≅
      smallEtaleCommonGeometricStalk.{u, w} (x ≫ f ≫ g) where
  hom := (smallEtaleCommonGeometricImageCompIso.{u, w} f g x).inv.sheafFiber
  inv := (smallEtaleCommonGeometricImageCompIso.{u, w} f g x).hom.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (smallEtaleCommonGeometricImageCompIso.{u, w} f g x).hom_inv_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (smallEtaleCommonGeometricImageCompIso.{u, w} f g x).inv_hom_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse of the same DI identity comparison is the original restriction along BaseId. -/
theorem smallEtaleDirectImageIdIso_inv_app_hom_app (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (U : X.Etaleᵒᵖ) :
    ((smallEtaleDirectImageIdIso.{u, w} X).inv.app Q).hom.app U =
      Q.obj.map ((smallEtaleBaseChangeId X).hom.app U.unop).op := by
  dsimp [smallEtaleDirectImageIdIso, Functor.sheafPushforwardContinuousId',
    Functor.sheafPushforwardContinuousId, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The right mate of the same κ identity comparison has the original BaseId coordinates. -/
theorem smallEtaleCommonStalkRightId_app_π {X : Scheme.{u}} (x : Spec (.of Ω) ⟶ X)
    (M : AddCommGrpCat.{max u w}) (U : X.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj ((smallEtaleBaseChange (𝟙 X)).obj U)) :
    ((conjugateEquiv
        (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafAdjunction
        (smallEtaleGeometricPointCommon.{u, w} (x ≫ 𝟙 X)).skyscraperSheafAdjunction
        (smallEtaleCommonGeometricStalkImageIdIso.{u, w} x).hom).app M).hom.app (op U) ≫
      (((smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} (𝟙 X) x).hom.app M).hom.app
        (op U) ≫ Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
          ((smallEtaleBaseChange (𝟙 X)).obj U)) => M) z) =
    ((smallEtaleDirectImageIdIso.{u, w} X).inv.app
        ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.obj M)).hom.app (op U) ≫
      Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
        ((smallEtaleBaseChange (𝟙 X)).obj U)) => M) z := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} x
  let Ψ := smallEtaleGeometricPointCommon.{u, w} (x ≫ 𝟙 X)
  let c := (smallEtaleBaseChangeCommonPointFiberIso.{u, w} (𝟙 X) x).hom.app U z
  have hB : (smallEtaleCommonGeometricImageIdFiberIso.{u, w} x).hom.app U c =
      Φ.fiber.map ((smallEtaleBaseChangeId X).hom.app U) z := by
    simpa [c, Φ] using congrArg (fun e => e.hom.app U z)
      (smallEtaleBaseChangeCommonPointFiberIso_id.{u, w} x)
  calc
    _ = ((conjugateEquiv Φ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
          (smallEtaleCommonGeometricStalkImageIdIso.{u, w} x).hom).app M).hom.app (op U) ≫
          Pi.π (fun (_ : Ψ.fiber.obj U) => M) c :=
      congrArg (fun k => ((conjugateEquiv Φ.skyscraperSheafAdjunction
          Ψ.skyscraperSheafAdjunction
          (smallEtaleCommonGeometricStalkImageIdIso.{u, w} x).hom).app M).hom.app (op U) ≫ k)
        (smallEtaleInverseImageCommonGeometricStalkRightIso_hom_app_π.{u, w} (𝟙 X) x M U z)
    _ = Pi.π (fun (_ : Φ.fiber.obj U) => M)
          ((smallEtaleCommonGeometricImageIdFiberIso.{u, w} x).hom.app U c) :=
      GrothendieckTopology.Point.conjugateEquiv_sheafFiber_app_π
        (smallEtaleCommonGeometricImageIdIso.{u, w} x).inv M U c
    _ = Pi.π (fun (_ : Φ.fiber.obj U) => M)
          (Φ.fiber.map ((smallEtaleBaseChangeId X).hom.app U) z) :=
      congrArg (fun v => Pi.π (fun (_ : Φ.fiber.obj U) => M) v) hB
    _ = _ := by
      rw [smallEtaleDirectImageIdIso_inv_app_hom_app]
      exact (GrothendieckTopology.Point.skyscraperSheaf_restrict_π Φ M
        ((smallEtaleBaseChangeId X).hom.app U) z).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual right-adjoint identity diagram for the same κ. -/
theorem smallEtaleCommonStalkRightId {X : Scheme.{u}} (x : Spec (.of Ω) ⟶ X) :
    conjugateEquiv
        (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafAdjunction
        (smallEtaleGeometricPointCommon.{u, w} (x ≫ 𝟙 X)).skyscraperSheafAdjunction
        (smallEtaleCommonGeometricStalkImageIdIso.{u, w} x).hom ≫
      (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} (𝟙 X) x).hom =
    (Functor.rightUnitor (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor).inv ≫
      Functor.whiskerLeft (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
        (smallEtaleDirectImageIdIso.{u, w} X).inv := by
  apply NatTrans.ext
  funext M
  apply (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).map_injective
  apply NatTrans.ext
  funext U
  apply Pi.hom_ext _ _
  intro z
  have h := smallEtaleCommonStalkRightId_app_π.{u, w} x M U.unop z
  simp only [op_unop] at h
  simp only [Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Category.id_comp, Category.assoc,
    ObjectProperty.ι, inducedFunctor]
  exact h

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same κ agrees with the accepted actual inverse-image identity
comparison and canonical original image-point identity transport. -/
theorem smallEtaleInverseImageCommonGeometricStalkIso_id {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    smallEtaleInverseImageCommonGeometricStalkIso.{u, w} (𝟙 X) x ≪≫
        smallEtaleCommonGeometricStalkImageIdIso.{u, w} x =
      Functor.isoWhiskerRight (smallEtaleInverseImageIdIso.{u, w} X)
        (smallEtaleCommonGeometricStalk.{u, w} x) ≪≫
        Functor.leftUnitor (smallEtaleCommonGeometricStalk.{u, w} x) := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} x
  let Ψ := smallEtaleGeometricPointCommon.{u, w} (x ≫ 𝟙 X)
  let a := smallEtaleInverseImageAdjunction.{u, w} (𝟙 X)
  let p := Φ.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let p' := Ψ.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let e := smallEtaleInverseImageCommonGeometricStalkIso.{u, w} (𝟙 X) x
  let η := smallEtaleCommonGeometricStalkImageIdIso.{u, w} x
  let τ := Functor.whiskerRight (smallEtaleInverseImageIdIso.{u, w} X).hom
    (smallEtaleCommonGeometricStalk.{u, w} x)
  let ν := (Functor.leftUnitor (smallEtaleCommonGeometricStalk.{u, w} x)).hom
  apply Iso.ext
  apply (conjugateEquiv p (a.comp p)).injective
  change conjugateEquiv p (a.comp p) (e.hom ≫ η.hom) =
    conjugateEquiv p (a.comp p) (τ ≫ ν)
  have hν : conjugateEquiv p ((Adjunction.id (C :=
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})).comp p) ν =
      (Functor.rightUnitor Φ.skyscraperSheafFunctor).inv :=
    conjugateEquiv_leftUnitor_hom p
  have hτ : conjugateEquiv ((Adjunction.id (C :=
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})).comp p) (a.comp p) τ =
      Functor.whiskerLeft Φ.skyscraperSheafFunctor (smallEtaleDirectImageIdIso.{u, w} X).inv := by
    rw [conjugateEquiv_whiskerRight]
    exact congrArg (Functor.whiskerLeft Φ.skyscraperSheafFunctor)
      (smallEtaleInverseImageIdIso_mate.{u, w} X)
  calc
    _ = conjugateEquiv p p' η.hom ≫
          (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} (𝟙 X) x).hom :=
      (conjugateEquiv_comp p p' (a.comp p) η.hom e.hom).symm
    _ = (Functor.rightUnitor Φ.skyscraperSheafFunctor).inv ≫
          Functor.whiskerLeft Φ.skyscraperSheafFunctor (smallEtaleDirectImageIdIso.{u, w} X).inv :=
      smallEtaleCommonStalkRightId.{u, w} x
    _ = conjugateEquiv p ((Adjunction.id (C :=
          Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})).comp p) ν ≫
          conjugateEquiv ((Adjunction.id (C :=
          Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})).comp p) (a.comp p) τ :=
      congrArg₂ (fun α β => α ≫ β) hν.symm hτ.symm
    _ = _ := conjugateEquiv_comp p ((Adjunction.id (C :=
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})).comp p) (a.comp p) ν τ

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse of the accepted DI composition comparison is restriction along BaseComp.inv. -/
theorem smallEtaleDirectImageCompIso_inv_app_hom_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (U : Z.Etaleᵒᵖ) :
    ((smallEtaleDirectImageCompIso.{u, w} f g).inv.app Q).hom.app U =
      Q.obj.map ((smallEtaleBaseChangeComp f g).inv.app U.unop).op := by
  dsimp [smallEtaleDirectImageCompIso, smallEtaleDirectImage,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Both actual κ composition routes have the same original product coordinates. -/
theorem smallEtaleCommonStalkRightComp_app_π {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X)
    (M : AddCommGrpCat.{max u w}) (U : Z.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
      ((smallEtaleBaseChange f).obj ((smallEtaleBaseChange g).obj U))) :
    ((conjugateEquiv
      (smallEtaleGeometricPointCommon.{u, w} (x ≫ f ≫ g)).skyscraperSheafAdjunction
      (smallEtaleGeometricPointCommon.{u, w} ((x ≫ f) ≫ g)).skyscraperSheafAdjunction
      (smallEtaleCommonGeometricStalkImageCompIso.{u, w} f g x).hom).app M).hom.app (op U) ≫
      (((smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} g (x ≫ f)).hom.app M).hom.app
        (op U) ≫
        (((smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x).hom.app M).hom.app
          (op ((smallEtaleBaseChange g).obj U)) ≫
          Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
            ((smallEtaleBaseChange f).obj ((smallEtaleBaseChange g).obj U))) => M) z)) =
    ((smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} (f ≫ g) x).hom.app M).hom.app
      (op U) ≫
      (((smallEtaleDirectImageCompIso.{u, w} f g).inv.app
        ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.obj M)).hom.app (op U) ≫
        Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
          ((smallEtaleBaseChange f).obj ((smallEtaleBaseChange g).obj U))) => M) z) := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} x
  let Ψ := smallEtaleGeometricPointCommon.{u, w} (x ≫ f)
  let Θ := smallEtaleGeometricPointCommon.{u, w} ((x ≫ f) ≫ g)
  let Δ := smallEtaleGeometricPointCommon.{u, w} (x ≫ f ≫ g)
  let c := (smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).hom.app
    ((smallEtaleBaseChange g).obj U) z
  let d := (smallEtaleBaseChangeCommonPointFiberIso.{u, w} g (x ≫ f)).hom.app U c
  let r := Φ.fiber.map ((smallEtaleBaseChangeComp f g).inv.app U) z
  let η := conjugateEquiv Δ.skyscraperSheafAdjunction Θ.skyscraperSheafAdjunction
    (smallEtaleCommonGeometricStalkImageCompIso.{u, w} f g x).hom
  let κg := (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} g (x ≫ f)).hom
  let κf := (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x).hom
  let κfg := (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} (f ≫ g) x).hom
  have hB : (smallEtaleCommonGeometricImageCompFiberIso.{u, w} f g x).hom.app U d =
      (smallEtaleBaseChangeCommonPointFiberIso.{u, w} (f ≫ g) x).hom.app U r := by
    simpa [c, d, r, Φ] using congrArg (fun e => e.hom.app U z)
      (smallEtaleBaseChangeCommonPointFiberIso_comp.{u, w} f g x)
  calc
    _ = (η.app M).hom.app (op U) ≫
          ((κg.app M).hom.app (op U) ≫ Pi.π (fun (_ : Ψ.fiber.obj
            ((smallEtaleBaseChange g).obj U)) => M) c) :=
      congrArg (fun k => (η.app M).hom.app (op U) ≫ (κg.app M).hom.app (op U) ≫ k)
        (smallEtaleInverseImageCommonGeometricStalkRightIso_hom_app_π.{u, w} f x M
          ((smallEtaleBaseChange g).obj U) z)
    _ = (η.app M).hom.app (op U) ≫ Pi.π (fun (_ : Θ.fiber.obj U) => M) d :=
      congrArg (fun k => (η.app M).hom.app (op U) ≫ k)
        (smallEtaleInverseImageCommonGeometricStalkRightIso_hom_app_π.{u, w} g (x ≫ f) M U c)
    _ = Pi.π (fun (_ : Δ.fiber.obj U) => M)
          ((smallEtaleCommonGeometricImageCompFiberIso.{u, w} f g x).hom.app U d) :=
      GrothendieckTopology.Point.conjugateEquiv_sheafFiber_app_π
        (smallEtaleCommonGeometricImageCompIso.{u, w} f g x).inv M U d
    _ = Pi.π (fun (_ : Δ.fiber.obj U) => M)
          ((smallEtaleBaseChangeCommonPointFiberIso.{u, w} (f ≫ g) x).hom.app U r) :=
      congrArg (fun v => Pi.π (fun (_ : Δ.fiber.obj U) => M) v) hB
    _ = (κfg.app M).hom.app (op U) ≫ Pi.π (fun (_ : Φ.fiber.obj
          ((smallEtaleBaseChange (f ≫ g)).obj U)) => M) r :=
      (smallEtaleInverseImageCommonGeometricStalkRightIso_hom_app_π.{u, w} (f ≫ g) x M U r).symm
    _ = _ := by
      rw [smallEtaleDirectImageCompIso_inv_app_hom_app]
      exact congrArg (fun k => (κfg.app M).hom.app (op U) ≫ k)
        (GrothendieckTopology.Point.skyscraperSheaf_restrict_π Φ M
          ((smallEtaleBaseChangeComp f g).inv.app U) z).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same κ right-adjoint comparison agrees with the accepted DI composition law. -/
theorem smallEtaleCommonStalkRightComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) :
    conjugateEquiv
        (smallEtaleGeometricPointCommon.{u, w} (x ≫ f ≫ g)).skyscraperSheafAdjunction
        (smallEtaleGeometricPointCommon.{u, w} ((x ≫ f) ≫ g)).skyscraperSheafAdjunction
        (smallEtaleCommonGeometricStalkImageCompIso.{u, w} f g x).hom ≫
      (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} g (x ≫ f)).hom ≫
      Functor.whiskerRight (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x).hom
        (smallEtaleDirectImage.{u, max u w} g) ≫
      (Functor.associator (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
        (smallEtaleDirectImage.{u, max u w} f) (smallEtaleDirectImage.{u, max u w} g)).hom =
    (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} (f ≫ g) x).hom ≫
      Functor.whiskerLeft (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
        (smallEtaleDirectImageCompIso.{u, w} f g).inv := by
  apply NatTrans.ext
  funext M
  apply (sheafToPresheaf Z.smallEtaleTopology AddCommGrpCat.{max u w}).map_injective
  apply NatTrans.ext
  funext U
  apply Pi.hom_ext _ _
  intro z
  have h := smallEtaleCommonStalkRightComp_app_π.{u, w} f g x M U.unop z
  simp only [op_unop] at h
  simp only [Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id, Category.assoc,
    smallEtaleDirectImage, Functor.sheafPushforwardContinuous, ObjectProperty.lift,
    ObjectProperty.ι, inducedFunctor, Functor.comp_map]
  exact h

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The accepted LF composition's forward map has the same actual DI inverse as mate. -/
theorem smallEtaleInverseImageCompIso_hom_mate {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g))
      ((smallEtaleInverseImageAdjunction.{u, w} g).comp
        (smallEtaleInverseImageAdjunction.{u, w} f))
      (smallEtaleInverseImageCompIso.{u, w} f g).hom =
      (smallEtaleDirectImageCompIso.{u, w} f g).inv :=
  (conjugateEquiv (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g))
    ((smallEtaleInverseImageAdjunction.{u, w} g).comp
      (smallEtaleInverseImageAdjunction.{u, w} f))).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same κ agrees with the accepted actual inverse-image composition
and the canonical original image-point composition transport. -/
theorem smallEtaleInverseImageCommonGeometricStalkIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) :
    Functor.associator (smallEtaleInverseImage.{u, w} g) (smallEtaleInverseImage.{u, w} f)
        (smallEtaleCommonGeometricStalk.{u, w} x) ≪≫
        Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} g)
          (smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x) ≪≫
        smallEtaleInverseImageCommonGeometricStalkIso.{u, w} g (x ≫ f) ≪≫
        smallEtaleCommonGeometricStalkImageCompIso.{u, w} f g x =
      Functor.isoWhiskerRight (smallEtaleInverseImageCompIso.{u, w} f g)
          (smallEtaleCommonGeometricStalk.{u, w} x) ≪≫
        smallEtaleInverseImageCommonGeometricStalkIso.{u, w} (f ≫ g) x := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} x
  let Ψ := smallEtaleGeometricPointCommon.{u, w} (x ≫ f)
  let Θ := smallEtaleGeometricPointCommon.{u, w} ((x ≫ f) ≫ g)
  let Δ := smallEtaleGeometricPointCommon.{u, w} (x ≫ f ≫ g)
  let af := smallEtaleInverseImageAdjunction.{u, w} f
  let ag := smallEtaleInverseImageAdjunction.{u, w} g
  let afg := smallEtaleInverseImageAdjunction.{u, w} (f ≫ g)
  let p := Φ.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let p' := Ψ.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let p'' := Θ.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let p''' := Δ.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let e := smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x
  let e' := smallEtaleInverseImageCommonGeometricStalkIso.{u, w} g (x ≫ f)
  let e'' := smallEtaleInverseImageCommonGeometricStalkIso.{u, w} (f ≫ g) x
  let η := smallEtaleCommonGeometricStalkImageCompIso.{u, w} f g x
  let σ := (Functor.associator (smallEtaleInverseImage.{u, w} g)
    (smallEtaleInverseImage.{u, w} f) (smallEtaleCommonGeometricStalk.{u, w} x)).hom
  let τ := Functor.whiskerLeft (smallEtaleInverseImage.{u, w} g) e.hom
  let ν := Functor.whiskerRight (smallEtaleInverseImageCompIso.{u, w} f g).hom
    (smallEtaleCommonGeometricStalk.{u, w} x)
  have hσ : conjugateEquiv (ag.comp (af.comp p)) ((ag.comp af).comp p) σ =
      (Functor.associator Φ.skyscraperSheafFunctor (smallEtaleDirectImage.{u, max u w} f)
        (smallEtaleDirectImage.{u, max u w} g)).hom :=
    conjugateEquiv_associator_hom ag af p
  have hτ : conjugateEquiv (ag.comp p') (ag.comp (af.comp p)) τ =
      Functor.whiskerRight (smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x).hom
        (smallEtaleDirectImage.{u, max u w} g) := by
    rw [conjugateEquiv_whiskerLeft]
    rfl
  have hν : conjugateEquiv (afg.comp p) ((ag.comp af).comp p) ν =
      Functor.whiskerLeft Φ.skyscraperSheafFunctor
        (smallEtaleDirectImageCompIso.{u, w} f g).inv := by
    rw [conjugateEquiv_whiskerRight]
    exact congrArg (Functor.whiskerLeft Φ.skyscraperSheafFunctor)
      (smallEtaleInverseImageCompIso_hom_mate.{u, w} f g)
  apply Iso.ext
  apply (conjugateEquiv p''' ((ag.comp af).comp p)).injective
  change conjugateEquiv p''' ((ag.comp af).comp p) (σ ≫ τ ≫ e'.hom ≫ η.hom) =
    conjugateEquiv p''' ((ag.comp af).comp p) (ν ≫ e''.hom)
  rw [← Category.assoc, ← Category.assoc,
    ← conjugateEquiv_comp p''' p'' ((ag.comp af).comp p),
    ← conjugateEquiv_comp p'' (ag.comp p') ((ag.comp af).comp p),
    ← conjugateEquiv_comp (ag.comp p') (ag.comp (af.comp p)) ((ag.comp af).comp p),
    hσ, hτ,
    ← conjugateEquiv_comp p''' (afg.comp p) ((ag.comp af).comp p), hν]
  exact smallEtaleCommonStalkRightComp.{u, w} f g x

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The complete original geometric-stalk comparison family, with its actual
additive values, naturality, original-neighborhood coordinate law, and both
identity/composition compatibility diagrams for the same canonical κ. -/
theorem original_small_etale_inverse_image_stalks :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ X),
      (∀ Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w},
        Nonempty (((smallEtaleCommonGeometricStalk.{u, w} x).obj
            ((smallEtaleInverseImage.{u, w} f).obj Q)) ≃+
          ((smallEtaleCommonGeometricStalk.{u, w} (x ≫ f)).obj Q))) ∧
      (∀ (Q Q' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q'),
        (smallEtaleInverseImage.{u, w} f ⋙ smallEtaleCommonGeometricStalk.{u, w} x).map τ ≫
            (smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x).hom.app Q' =
          (smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x).hom.app Q ≫
            (smallEtaleCommonGeometricStalk.{u, w} (x ≫ f)).map τ) ∧
      ∀ (M : AddCommGrpCat.{max u w}) (U : Y.Etale)
        (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj ((smallEtaleBaseChange f).obj U)),
        ((smallEtaleInverseImageCommonGeometricStalkRightIso.{u, w} f x).hom.app M).hom.app (op U) ≫
            Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
              ((smallEtaleBaseChange f).obj U)) => M) z =
          Pi.π (fun (_ : (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).fiber.obj U) => M)
            ((smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).hom.app U z)) ∧
    (∀ {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
      smallEtaleInverseImageCommonGeometricStalkIso.{u, w} (𝟙 X) x ≪≫
          smallEtaleCommonGeometricStalkImageIdIso.{u, w} x =
        Functor.isoWhiskerRight (smallEtaleInverseImageIdIso.{u, w} X)
            (smallEtaleCommonGeometricStalk.{u, w} x) ≪≫
          Functor.leftUnitor (smallEtaleCommonGeometricStalk.{u, w} x)) ∧
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Functor.associator (smallEtaleInverseImage.{u, w} g) (smallEtaleInverseImage.{u, w} f)
          (smallEtaleCommonGeometricStalk.{u, w} x) ≪≫
          Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} g)
            (smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x) ≪≫
          smallEtaleInverseImageCommonGeometricStalkIso.{u, w} g (x ≫ f) ≪≫
          smallEtaleCommonGeometricStalkImageCompIso.{u, w} f g x =
        Functor.isoWhiskerRight (smallEtaleInverseImageCompIso.{u, w} f g)
            (smallEtaleCommonGeometricStalk.{u, w} x) ≪≫
          smallEtaleInverseImageCommonGeometricStalkIso.{u, w} (f ≫ g) x := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y f Ω _ _ x
    refine ⟨?_, ?_, ?_⟩
    · intro Q
      let e := (smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x).app Q
      exact ⟨e.addCommGroupIsoToAddEquiv⟩
    · intro Q Q' τ
      exact (smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f x).hom.naturality τ
    · intro M U z
      exact smallEtaleInverseImageCommonGeometricStalkRightIso_hom_app_π.{u, w} f x M U z
  · intro X Ω _ _ x
    exact smallEtaleInverseImageCommonGeometricStalkIso_id.{u, w} x
  · intro X Y Z f g Ω _ _ x
    exact smallEtaleInverseImageCommonGeometricStalkIso_comp.{u, w} f g x

end AlgebraicGeometry.Scheme.DerivedSections
