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

/-!
# Geometric stalks of small étale inverse images

Let `f : X → Y` be a scheme morphism and `x : Spec Ω → X` a geometric point, with `Ω`
separably closed in the scheme universe `u`. Base change identifies the fiber over `x` with
the fiber over `x ≫ f`. The corresponding point-comap and sheaf-pullback comparisons give
`stalk_x(f^*Q) ≅ stalk_(x≫f)(Q)` for abelian coefficients in universe `max u w`.

The comparison is defined both with the point fiber in universe `u` and with its common-
universe lift. Its right-adjoint mate identifies the skyscraper at `x ≫ f` with the skyscraper
at `x` followed by direct image. On sections, this mate reindexes coefficient-product
coordinates by the base-change fiber isomorphism.

The geometric representative maps are the pullback projections. The point, stalk, and right-
adjoint comparisons respect identity and composition through the canonical sheaf-image and
image-point isomorphisms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Small étale base change is continuous.

For every scheme morphism `f : X → Y`, the small étale base-change functor is continuous from
the topology of `Y` to that of `X`. -/
instance smallEtaleBaseChangeIsContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  smallEtaleBaseChange_isContinuous f

/-- Small étale base change is representably flat.

The site base-change functor is representably flat, using its preservation of finite limits. -/
instance smallEtaleBaseChangeRepresentablyFlat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RepresentablyFlat (smallEtaleBaseChange f) := by
  let : PreservesFiniteLimits (smallEtaleBaseChange f) :=
    smallEtaleBaseChange_preservesFiniteLimits f
  exact flat_of_preservesFiniteLimits (smallEtaleBaseChange f)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Geometric fiber comparison after base change.

For `x : Spec Ω → X` over a separably closed field in universe `u`, base change along `f`
followed by the fiber of `x` is naturally isomorphic to the fiber of `x ≫ f`. -/
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

/-- Base changed geometric neighborhoods are initially small.

The elements category of the base-changed geometric fiber is initially small in universe `u`. -/
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

/-- Comap of a geometric point along base change.

The point of `X` defined by `x` has a comap point on `Y` along the covering-preserving base-
change functor. -/
def smallEtaleGeometricPointComap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) : Y.smallEtaleTopology.Point.{u} :=
  (Scheme.pointSmallEtale x).comap (smallEtaleBaseChange f)
    (smallEtaleBaseChange_coverPreserving f)

/-- Geometric point comap is the image point.

The comap point on `Y` is isomorphic to the geometric point defined by the composite `x ≫ f`. -/
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

/-- Geometric comap identification on sheaf fibers.

The comap-point identification induces an isomorphism of sheaf-fiber functors with the fiber
at `x ≫ f`, for additive coefficients in `max u w`. -/
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

/-- Full site sheaf pushforward is a right adjoint.

Continuous sheaf pushforward along small étale base change is right adjoint to the inverse-
image construction. -/
instance smallEtaleBaseChangePushforwardIsRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max u w}
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint :=
  (smallEtaleInverseImageAdjunction.{u, w} f).isRightAdjoint

/-- Affine inverse image agrees with full site sheaf pullback.

The affine-basis inverse-image functor is naturally isomorphic to sheaf pullback along the
full small étale base-change functor. -/
def smallEtaleInverseImageFullSitePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleInverseImage.{u, w} f ≅
      (smallEtaleBaseChange f).sheafPullback AddCommGrpCat.{max u w}
        Y.smallEtaleTopology X.smallEtaleTopology :=
  Adjunction.leftAdjointUniq (smallEtaleInverseImageAdjunction.{u, w} f)
    ((smallEtaleBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{max u w}
      Y.smallEtaleTopology X.smallEtaleTopology)

/-- Inverse image preserves geometric stalks.

For common-universe abelian coefficients, inverse image followed by the geometric stalk at `x`
is naturally isomorphic to the stalk at `x ≫ f`. -/
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

/-- Geometric sheaf fibers preserve finite limits.

The geometric stalk functor with additive-group coefficients in `max u w` preserves finite
limits. -/
theorem smallEtaleGeometricSheafFiber_preservesFiniteLimits {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteLimits ((Scheme.pointSmallEtale x).sheafFiber
      (A := AddCommGrpCat.{max u w})) := by
  infer_instance

/-- Inverse image followed by a geometric stalk preserves finite limits.

The composite of inverse image along `f` and the geometric stalk at `x` preserves finite
limits. -/
theorem smallEtaleInverseImageAtGeometricPoint_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteLimits (smallEtaleInverseImage.{u, w} f ⋙
      (Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{max u w})) := by
  let : PreservesFiniteLimits ((Scheme.pointSmallEtale (x ≫ f)).sheafFiber
      (A := AddCommGrpCat.{max u w})) :=
    smallEtaleGeometricSheafFiber_preservesFiniteLimits.{u, w} (x ≫ f)
  exact preservesFiniteLimits_of_natIso
    (smallEtaleInverseImageGeometricStalkIso.{u, w} f x).symm

/-- Lifted geometric fiber comparison after base change.

Lift the geometric fiber comparison to obtain a natural isomorphism from base change followed
by the common point's fiber to the common fiber of `x ≫ f`. -/
def smallEtaleBaseChangeCommonPointFiberIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) :
    smallEtaleBaseChange f ⋙ (smallEtaleGeometricPointCommon.{u, w} x).fiber ≅
      (smallEtaleGeometricPointCommon.{u, w} (x ≫ f)).fiber :=
  (Functor.associator (smallEtaleBaseChange f) (Scheme.pointSmallEtale x).fiber
    uliftFunctor.{w, u}).symm ≪≫
      Functor.isoWhiskerRight (smallEtaleBaseChangePointFiberIso f x) uliftFunctor.{w, u}

/-- Lifted base changed neighborhoods are initially small.

The elements category of base change followed by the lifted geometric fiber is initially small
in `max u w`. -/
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

/-- Comap of a lifted geometric point along base change.

The common-universe point of `X` has a comap point on `Y` along the small étale base-change
functor. -/
def smallEtaleCommonGeometricPointComap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) : Y.smallEtaleTopology.Point.{max u w} :=
  (smallEtaleGeometricPointCommon.{u, w} x).comap (smallEtaleBaseChange f)
    (smallEtaleBaseChange_coverPreserving f)

/-- Lifted geometric point comap is the image point.

The common-universe comap point is isomorphic to the lifted geometric point at `x ≫ f`. -/
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

/-- Lifted comap identification on sheaf fibers.

The common comap-point isomorphism identifies its sheaf-fiber functor with the common
geometric stalk at `x ≫ f`. -/
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

/-- Inverse image preserves common universe geometric stalks.

The canonical inverse-image functor followed by the common stalk at `x` is naturally
isomorphic to the common stalk at `x ≫ f`. -/
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

/-- Common universe geometric sheaf fibers preserve finite limits.

The common geometric stalk functor preserves finite limits of abelian sheaves. -/
theorem smallEtaleCommonGeometricSheafFiber_preservesFiniteLimits {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteLimits ((smallEtaleGeometricPointCommon.{u, w} x).sheafFiber
      (A := AddCommGrpCat.{max u w})) := by
  infer_instance

/-- Inverse image followed by a common universe stalk preserves finite limits.

Inverse image followed by the common geometric stalk at `x` preserves finite limits, through
its comparison with the image-point stalk. -/
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

/-- Right adjoint comparison for common universe stalk preservation.

The adjunction mate identifies the skyscraper functor at `x ≫ f` with the skyscraper functor
at `x` followed by direct image along `f`. -/
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
/-- Forward stalk right adjoint comparison is the comap mate.

The forward right-adjoint comparison equals the adjunction conjugate of the comap-point sheaf-
fiber identification. -/
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

/-- Stalk right adjoint comparison reindexes skyscraper coordinates.

At coefficient group `M` and étale object `U`, projection after the right-adjoint comparison
at a base-changed fiber element `z` equals projection at its image under the forward common
fiber comparison. -/
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
/-- Geometric fiber comparison uses the pullback projection.

The underlying scheme map of a fiber element after the comparison is its given map followed by
the first projection `U ×_Y X → U`. -/
theorem smallEtaleBaseChangePointFiberIso_hom_app_left {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (U : Y.Etale)
    (z : (Scheme.pointSmallEtale x).fiber.obj ((smallEtaleBaseChange f).obj U)) :
    ((smallEtaleBaseChangePointFiberIso f x).hom.app U z).left =
      z.left ≫ pullback.fst U.hom f := by
  change (((CategoryTheory.Over.mapPullbackAdj f).homEquiv (CategoryTheory.Over.mk x)
    ((Scheme.Etale.forget Y).obj U)).symm z).left = z.left ≫ pullback.fst U.hom f
  simp [CategoryTheory.Over.mapPullbackAdj]

/-- Lifted geometric fiber comparison uses the pullback projection.

After lowering the lifted fiber element, the forward comparison's scheme map is its underlying
map followed by the first pullback projection. -/
theorem smallEtaleBaseChangeCommonPointFiberIso_hom_app_down_left {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (U : Y.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj ((smallEtaleBaseChange f).obj U)) :
    ((smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).hom.app U z).down.left =
      z.down.left ≫ pullback.fst U.hom f := by
  exact smallEtaleBaseChangePointFiberIso_hom_app_left f x U z.down

/-- Lifted geometric fiber maps use the étale arrow.

For an étale arrow `g`, the lowered scheme map of the image fiber element is the given lowered
scheme map composed with `g.left`. -/
theorem smallEtaleGeometricPointCommon_map_down_left {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) {U V : X.Etale} (g : U ⟶ V)
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj U) :
    ((smallEtaleGeometricPointCommon.{u, w} x).fiber.map g z).down.left = z.down.left ≫ g.left :=
  rfl

/-- Geometric image of the identity has the same fiber.

The geometric fiber at `x ≫ 𝟙 X` is naturally isomorphic to the fiber at `x`. -/
def smallEtaleGeometricImageIdFiberIso {X : Scheme.{u}} (x : Spec (.of Ω) ⟶ X) :
    (Scheme.pointSmallEtale (x ≫ 𝟙 X)).fiber ≅ (Scheme.pointSmallEtale x).fiber :=
  Functor.isoWhiskerLeft (Scheme.Etale.forget X)
    (coyoneda.mapIso (((CategoryTheory.Over.mapId X).app (CategoryTheory.Over.mk x)).op))

/-- Lifted geometric image of the identity has the same fiber.

Lift the identity-image geometric fiber isomorphism to the common point universe. -/
def smallEtaleCommonGeometricImageIdFiberIso {X : Scheme.{u}} (x : Spec (.of Ω) ⟶ X) :
    (smallEtaleGeometricPointCommon.{u, w} (x ≫ 𝟙 X)).fiber ≅
      (smallEtaleGeometricPointCommon.{u, w} x).fiber :=
  Functor.isoWhiskerRight (smallEtaleGeometricImageIdFiberIso x) uliftFunctor.{w, u}

/-- Successive geometric images have the composite fiber.

The geometric fibers at `(x ≫ f) ≫ g` and `x ≫ (f ≫ g)` are naturally isomorphic through
scheme-composition associativity. -/
def smallEtaleGeometricImageCompFiberIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) :
    (Scheme.pointSmallEtale ((x ≫ f) ≫ g)).fiber ≅
      (Scheme.pointSmallEtale (x ≫ f ≫ g)).fiber :=
  Functor.isoWhiskerLeft (Scheme.Etale.forget Z)
    (coyoneda.mapIso (((CategoryTheory.Over.mapComp f g).app
      (CategoryTheory.Over.mk x)).symm.op))

/-- Successive lifted geometric images have the composite fiber.

The common-universe fibers of the two parenthesizations of the image geometric point are
naturally isomorphic. -/
def smallEtaleCommonGeometricImageCompFiberIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Spec (.of Ω) ⟶ X) :
    (smallEtaleGeometricPointCommon.{u, w} ((x ≫ f) ≫ g)).fiber ≅
      (smallEtaleGeometricPointCommon.{u, w} (x ≫ f ≫ g)).fiber :=
  Functor.isoWhiskerRight (smallEtaleGeometricImageCompFiberIso f g x) uliftFunctor.{w, u}

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Lifted geometric identity coordinate preserves the underlying map.

The forward identity-image fiber coordinate preserves the scheme map of the lowered geometric
element. -/
theorem smallEtaleCommonGeometricImageIdFiberIso_hom_app_down_left {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) (U : X.Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} (x ≫ 𝟙 X)).fiber.obj U) :
    ((smallEtaleCommonGeometricImageIdFiberIso.{u, w} x).hom.app U z).down.left = z.down.left := by
  simp [smallEtaleCommonGeometricImageIdFiberIso, smallEtaleGeometricImageIdFiberIso,
    Functor.isoWhiskerRight, Functor.isoWhiskerLeft, CategoryTheory.Over.mapId,
    NatIso.ofComponents, coyoneda]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Lifted geometric composite coordinate preserves the underlying map.

The forward image-composition fiber coordinate preserves the scheme map of the lowered
geometric element. -/
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
/-- Inverse base change composition preserves the iterated first projection.

The inverse base-change composition map followed by the first projection of the composite
pullback equals the composite of the two first projections of the iterated pullback. -/
theorem smallEtaleBaseChangeComp_inv_app_left_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Etale) :
    ((smallEtaleBaseChangeComp f g).inv.app U).left ≫ pullback.fst U.hom (f ≫ g) =
      pullback.fst (pullback.snd U.hom g) f ≫ pullback.fst U.hom g := by
  simp [smallEtaleBaseChangeComp, MorphismProperty.Over.pullbackComp,
    NatIso.ofComponents, MorphismProperty.Over.isoMk]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Lifted base change fiber comparisons respect identity.

The identity base-change fiber comparison followed by the identity-image fiber coordinate
equals the base-change identity isomorphism whiskered with the point fiber and its unitor. -/
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
/-- Lifted base change fiber comparisons respect composition.

The two successive fiber comparisons, followed by the image-associativity coordinate, equal
the composite fiber comparison after base-change composition and the functor associator. -/
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

/-- Lifted identity image is isomorphic to the geometric point.

The fiber identity comparison gives an isomorphism of common geometric points from the
identity image back to `x`. -/
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

/-- Successive lifted images are isomorphic to the composite point.

The fiber associativity comparison gives an isomorphism between the common geometric points of
the two image-composition parentheses. -/
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

/-- Geometric identity image stalk coordinate.

The identity-image point isomorphism induces a natural isomorphism from the common stalk at `x
≫ 𝟙 X` to the common stalk at `x`. -/
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

/-- Geometric composite image stalk coordinate.

The image-associativity point isomorphism induces the natural stalk isomorphism for the two
parenthesizations of the image point. -/
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
/-- Inverse direct image identity comparison on sections.

The inverse direct-image identity component acts on sections by restriction along the forward
base-change identity map. -/
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
/-- Identity right adjoint stalk comparison on skyscraper coordinates.

At every coefficient group, étale object, and fiber index, the point-identity mate followed by
the identity stalk right comparison agrees with the inverse direct-image identity path after
projection. -/
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
/-- Right adjoint stalk comparisons respect identity.

The point-identity mate followed by the identity stalk right comparison equals the inverse
skyscraper unitor followed by the whiskered inverse direct-image identity comparison. -/
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
/-- Inverse image stalk comparisons respect identity.

The identity inverse-image stalk comparison followed by the point-identity stalk coordinate
equals the inverse-image identity comparison whiskered with the stalk functor and its unitor. -/
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
/-- Inverse direct image composition comparison on sections.

The inverse direct-image composition component acts by restriction along the inverse base-
change composition isomorphism. -/
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
/-- Composite right adjoint stalk comparison on skyscraper coordinates.

After the image-associativity mate, the two successive stalk right comparisons agree at every
skyscraper coordinate with the composite stalk right comparison followed by the inverse
direct-image composition comparison. -/
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
/-- Right adjoint stalk comparisons respect composition.

The image-associativity mate and the two successive right-adjoint stalk comparisons, with
their functor associator, equal the composite right comparison followed by the whiskered
inverse direct-image composition coordinate. -/
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
/-- Forward inverse image composition comparison is the inverse direct image mate.

Under adjunction conjugation, the forward inverse-image composition map corresponds to the
inverse direct-image composition map. -/
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
/-- Inverse image stalk comparisons respect composition.

Successive inverse images and their stalk comparisons, with the functor associator and image-
point composition coordinate, equal the inverse-image composition comparison followed by the
stalk comparison for `f ≫ g`. -/
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

/-- Natural coherent preservation of common universe geometric stalks.

For every scheme map and geometric point over a separably closed field in universe `u`, the
common stalk comparison is an additive equivalence natural in sheaf maps. Its right-adjoint
section coordinates are the stated fiber reindexings, and the comparisons satisfy the identity
and composition equations. -/
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
