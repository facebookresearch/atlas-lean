/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
See NOTICE in the repository root for the original attribution.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.CanonicalSphereHoGroup
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SphereNullHom
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.NegativeHom
import Mathlib.Tactic.FastInstance

/-!
# Original native Omega-target Hom groups

The original Q counit, scalar mapping adjunction, fundamental group and
Omega delooping identify each complete ordinary Hom set with its actual
represented group. Every original source map and ordinary null class are
retained. The native orthogonal construction uses the same full original
Omega condition, model parameter B and independent coefficient universes.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests
open scoped CGWH.modelCategory ZeroObject

namespace PointedCGWH.Spectra.Orthogonal.OriginalOmegaHoHomGroup

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal

private def precompositionEquiv {D : Type*} [Category* D] {X Y : D}
    (e : X ≅ Y) (T : D) : (Y ⟶ T) ≃ (X ⟶ T) where
  toFun g := e.hom ≫ g
  invFun g := e.inv ≫ g
  left_inv g := e.inv_hom_id_assoc g
  right_inv g := e.hom_inv_id_assoc g

private def postcompositionEquiv {D : Type*} [Category* D] (X : D) {Y Z : D}
    (e : Y ≅ Z) : (X ⟶ Y) ≃ (X ⟶ Z) where
  toFun g := g ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv g := by
    change (g ≫ e.hom) ≫ e.inv = g
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv g := by
    change (g ≫ e.inv) ≫ e.hom = g
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem transSymm_spec {A B C : Type*} (e : A ≃ B) (f : C ≃ B) (x : A) :
    f (e.trans f.symm x) = e x := f.apply_symm_apply (e x)

@[instance_reducible]
private def groupTransport {A B : Type*} [Group B] (e : A ≃ B) : Group A :=
  fast_instance% e.group

private theorem groupTransport_mul {A B : Type*} [Group B] (e : A ≃ B) (a b : A) :
    letI := groupTransport e
    e (a * b) = e a * e b := by
  let _ := groupTransport e
  change e (e.symm (e a * e b)) = e a * e b
  exact e.apply_symm_apply _

private def transportHom {A AX B BX : Type*} [Group B] [Group BX]
    (e : A ≃ B) (eX : AX ≃ BX) (h : B →* BX) :
    letI := groupTransport e
    letI := groupTransport eX
    A →* AX := by
  let _ := groupTransport e
  let _ := groupTransport eX
  exact eX.mulEquiv.symm.toMonoidHom.comp (h.comp e.mulEquiv.toMonoidHom)

private theorem transportHom_apply {A AX B BX : Type*} [Group B] [Group BX]
    (e : A ≃ B) (eX : AX ≃ BX) (h : B →* BX) (a : A) :
    transportHom e eX h a = eX.symm (h (e a)) := rfl

private theorem exists_transportHom {A AX B BX : Type*} [Group B] [Group BX]
    (e : A ≃ B) (eX : AX ≃ BX) (f : A → AX) (h : B →* BX)
    (hn : ∀ a, eX (f a) = h (e a)) :
    letI := groupTransport e
    letI := groupTransport eX
    ∃ g : A →* AX, ∀ a, g a = f a := by
  let _ := groupTransport e
  let _ := groupTransport eX
  refine ⟨transportHom e eX h, ?_⟩
  intro a
  apply eX.injective
  rw [transportHom_apply, Equiv.apply_symm_apply]
  exact (hn a).symm

private def IsTransportedGroupMap {A AX B BX : Type*} [Group B] [Group BX]
    (e : A ≃ B) (eX : AX ≃ BX) (f : A → AX) : Prop :=
  letI := groupTransport e
  letI := groupTransport eX
  ∀ a b, f (a * b) = f a * f b

private theorem transportedMap_of_commuting {A AX B BX : Type*} [Group B] [Group BX]
    (e : A ≃ B) (eX : AX ≃ BX) (f : A → AX) (h : B →* BX)
    (hn : ∀ a, eX (f a) = h (e a)) : IsTransportedGroupMap e eX f := by
  let _ := groupTransport e
  let _ := groupTransport eX
  obtain ⟨g, hg⟩ := exists_transportHom e eX f h hn
  intro a b
  exact (hg (a * b)).symm.trans
    ((g.map_mul a b).trans (congrArg₂ (fun x y => x * y) (hg a) (hg b)))

private theorem transportedMap_one {A AX B BX : Type*} [Group B] [Group BX]
    (e : A ≃ B) (eX : AX ≃ BX) (f : A → AX) (hf : IsTransportedGroupMap e eX f) :
    letI := groupTransport e
    letI := groupTransport eX
    f 1 = 1 := by
  let _ := groupTransport e
  let _ := groupTransport eX
  exact (MonoidHom.mk' f hf).map_one

private theorem composeNaturality3
    {A AX B BX C CX D DX : Type*}
    (aX : AX ≃ BX) (a : A ≃ B) (bX : BX ≃ CX) (b : B ≃ C) (cX : CX ≃ DX) (c : C ≃ D)
    (u : A → AX) (v : B → BX) (w : C → CX) (z : D → DX)
    (ha : ∀ x, aX (u x) = v (a x)) (hb : ∀ x, bX (v x) = w (b x))
    (hc : ∀ x, cX (w x) = z (c x)) (x : A) :
    (aX.trans (bX.trans cX)) (u x) = z ((a.trans (b.trans c)) x) :=
  (congrArg (fun t => cX (bX t)) (ha x)).trans
    ((congrArg cX (hb (a x))).trans (hc (b (a x))))

/-- The identity of the actual represented fundamental group. -/
def groupIdentity (G : GrpCat.{v}) : G := 1

private theorem identityByZero
    {A0 A : Type*} [Subsingleton A0] (G0 GX : GrpCat.{v})
    (e0 : A0 ≃ G0) (ex : A ≃ GX) (f : A0 → A) (pm : G0 →* GX)
    (n0 : A0) (nx : A) (hz : f n0 = nx) (hn : ex (f n0) = pm (e0 n0)) :
    ex nx = groupIdentity GX := by
  have h0 : e0 n0 = groupIdentity G0 := e0.symm.injective (Subsingleton.elim _ _)
  exact (congrArg ex hz).symm.trans
    (hn.trans ((congrArg pm h0).trans pm.map_one))

namespace Generic

private abbrev V := PointedCGWH.{u, v}
variable {I : Type} [EnrichedCategory V.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev C := EnrichedFunctorCat V.{u, v} I
private abbrev H := toHomotopyCategory (C.{u, v} (I := I))
private abbrev P := toHomotopyCategory V.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)
private abbrev R := cotensor (I := I) PointedCGWH.sphereOne.{u, v}

private instance sphereCofibrant : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
  PointedCGWH.modelCategory.sphereOne_isCofibrant

private def qIso (X : C.{u, v} (I := I)) : H.obj (Q.obj X) ≅ H.obj X := by
  let _ : IsIso (H.map (ε.app X)) := Localization.inverts H (weakEquivalences (C (I := I))) _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
  exact asIso (H.map (ε.app X))

private theorem qIso_hom (X : C.{u, v} (I := I)) :
    (qIso X).hom = H.map (ε.app X) := rfl

/-- The entire original Q source and scalar mapping adjunction identify each native loop-target Hom. -/
def loopScalarEquiv (X D : C.{u, v} (I := I)) :
    (H.obj X ⟶ H.obj (R.obj D)) ≃
      (P.obj PointedCGWH.sphereOne ⟶
        P.obj (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D)) := by
  let _ : IsCofibrant (Q.obj X) := Replacement.isCofibrant_cofibrantReplacement (B := B) X
  exact (precompositionEquiv (qIso X) (H.obj (R.obj D))).trans
    (DerivedLocalMapping.scalarMappingHoEquiv (B := B) PointedCGWH.sphereOne (Q.obj X) D).symm

/-- Source naturality keeps the actual whole Q map and original weighted-end map. -/
theorem loopScalarEquiv_source {X Y : C.{u, v} (I := I)} (f : X ⟶ Y) (D : C.{u, v} (I := I))
    (g : H.obj Y ⟶ H.obj (R.obj D)) :
    loopScalarEquiv X D (H.map f ≫ g) = loopScalarEquiv Y D g ≫
      P.map (WeightedEndVariance.pre (Q.map f) D) := by
  let _ : IsCofibrant (Q.obj X) := Replacement.isCofibrant_cofibrantReplacement (B := B) X
  let _ : IsCofibrant (Q.obj Y) := Replacement.isCofibrant_cofibrantReplacement (B := B) Y
  apply (DerivedLocalMapping.scalarMappingHoEquiv (B := B) PointedCGWH.sphereOne (Q.obj X) D).injective
  change DerivedLocalMapping.scalarMappingHoEquiv (B := B) PointedCGWH.sphereOne (Q.obj X) D
      ((DerivedLocalMapping.scalarMappingHoEquiv (B := B) PointedCGWH.sphereOne (Q.obj X) D).symm
        ((qIso X).hom ≫ (H.map f ≫ g))) =
    DerivedLocalMapping.scalarMappingHoEquiv (B := B) PointedCGWH.sphereOne (Q.obj X) D
      (((DerivedLocalMapping.scalarMappingHoEquiv (B := B) PointedCGWH.sphereOne (Q.obj Y) D).symm
        ((qIso Y).hom ≫ g)) ≫ P.map (WeightedEndVariance.pre (Q.map f) D))
  rw [Equiv.apply_symm_apply, DerivedLocalMapping.scalarMappingHoEquiv_source (B := B),
    Equiv.apply_symm_apply]
  have hε : H.map (Q.map f) ≫ (qIso Y).hom = (qIso X).hom ≫ H.map f := by
    simpa only [Functor.map_comp, Functor.id_map, qIso_hom] using H.congr_map (ε.naturality f)
  exact (Category.assoc (qIso X).hom (H.map f) g).symm.trans
    ((congrArg (fun k => k ≫ g) hε.symm).trans
      (Category.assoc (H.map (Q.map f)) (qIso Y).hom g))

end Generic

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := Actual.OrthogonalCarrier.{u, v}
private abbrev V := PointedCGWH.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev P := toHomotopyCategory V.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := O.{u, v})

private instance nativeZero : HasZeroObject C.{u, v} := Diagrams.nativeHasZeroObject
private instance nativeSphereCofibrant : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
  PointedCGWH.modelCategory.sphereOne_isCofibrant

private def sphereUnitIso : PointedCGWH.SphereHom.canonicalSphere.{u, v} 1 ≅
    PointedCGWH.sphereOne.{u, v} := λ_ PointedCGWH.sphereOne

private def sphereHoUnitIso : P.obj (PointedCGWH.SphereHom.canonicalSphere.{u, v} 1) ≅
    P.obj PointedCGWH.sphereOne := P.mapIso sphereUnitIso

private def coefficientPiEquiv (T : V.{u, v}) :
    (P.obj PointedCGWH.sphereOne ⟶ P.obj T) ≃ PointedCGWH.piN 1 T :=
  (precompositionEquiv sphereHoUnitIso (P.obj T)).trans
    (PointedCGWH.SphereHom.canonicalSpherePiHomEquiv 1 T).symm

omit B in
private theorem coefficientPiEquiv_spec (T : V.{u, v})
    (g : P.obj PointedCGWH.sphereOne ⟶ P.obj T) :
    PointedCGWH.SphereHom.canonicalSpherePiHomEquiv 1 T (coefficientPiEquiv T g) =
      sphereHoUnitIso.hom ≫ g :=
  transSymm_spec (precompositionEquiv sphereHoUnitIso (P.obj T))
    (PointedCGWH.SphereHom.canonicalSpherePiHomEquiv 1 T) g

omit B in
private theorem coefficientPiEquiv_naturality {T U : V.{u, v}} (f : T ⟶ U)
    (g : P.obj PointedCGWH.sphereOne ⟶ P.obj T) :
    coefficientPiEquiv U (g ≫ P.map f) =
      (PointedCGWH.piNPositiveMap 0 f).hom (coefficientPiEquiv T g) := by
  have h : coefficientPiEquiv U (g ≫ P.map f) =
      PointedCGWH.piNMap 1 f (coefficientPiEquiv T g) := by
    apply (PointedCGWH.SphereHom.canonicalSpherePiHomEquiv 1 U).injective
    rw [coefficientPiEquiv_spec, PointedCGWH.SphereHom.canonicalSpherePiHomEquiv_naturality,
      coefficientPiEquiv_spec]
    exact (Category.assoc sphereHoUnitIso.hom g (P.map f)).symm
  exact h.trans (PointedCGWH.piNPositiveMap_apply 0 f (coefficientPiEquiv T g)).symm

omit B in
private def pointPiHom {T U : V.{u, v}} (f : T ⟶ U) :
    PointedCGWH.piN 1 T →* PointedCGWH.piN 1 U := by
  refine MonoidHom.mk' (PointedCGWH.piNMap 1 f) ?_
  intro a b
  have hp (k : PointedCGWH.piN 1 T) :
      (PointedCGWH.piNPositiveMap 0 f).hom k = PointedCGWH.piNMap 1 f k :=
    PointedCGWH.piNPositiveMap_apply 0 f k
  exact (hp (a * b)).symm.trans
    (((PointedCGWH.piNPositiveMap 0 f).hom.map_mul a b).trans
      (congrArg₂ (fun x y => x * y) (hp a) (hp b)))

omit B in
private theorem pointPiHom_apply {T U : V.{u, v}} (f : T ⟶ U) (a : PointedCGWH.piN 1 T) :
    pointPiHom f a = PointedCGWH.piNMap 1 f a := rfl

omit B in
private theorem pointPiHom_eq_positive {T U : V.{u, v}} (f : T ⟶ U) :
    pointPiHom f = (PointedCGWH.piNPositiveMap 0 f).hom := by
  apply MonoidHom.ext
  intro a
  exact (pointPiHom_apply f a).trans (PointedCGWH.piNPositiveMap_apply 0 f a).symm

omit B in
private theorem identityByBasedMap
    {A0 A : Type*} [Subsingleton A0] (R S : V.{u, v})
    (e0 : A0 ≃ ((PointedCGWH.piNPositiveFunctor 0).obj R))
    (ex : A ≃ ((PointedCGWH.piNPositiveFunctor 0).obj S))
    (f : A0 → A) (p : R ⟶ S) (n0 : A0) (nx : A) (hz : f n0 = nx)
    (hn : ex (f n0) = (PointedCGWH.piNPositiveMap 0 p).hom (e0 n0)) :
    ex nx = groupIdentity ((PointedCGWH.piNPositiveFunctor 0).obj S) :=
  identityByZero ((PointedCGWH.piNPositiveFunctor 0).obj R)
    ((PointedCGWH.piNPositiveFunctor 0).obj S) e0 ex f
    (PointedCGWH.piNPositiveMap 0 p).hom n0 nx hz hn

omit B in
private theorem identityByBasedNull
    {A0 A : Type*} [Subsingleton A0] (R S : V.{u, v})
    (e0 : A0 ≃ ((PointedCGWH.piNPositiveFunctor 0).obj R))
    (ex : A ≃ ((PointedCGWH.piNPositiveFunctor 0).obj S))
    (f : A0 → A) (p : R ⟶ S) (n0 : A0) (nx : A) (hz : f n0 = nx)
    (hn : ex (f n0) = PointedCGWH.piNMap 1 p (e0 n0)) :
    ex nx = groupIdentity ((PointedCGWH.piNPositiveFunctor 0).obj S) := by
  have h0 : e0 n0 = PointedCGWH.SphereHom.nullCube 1 R :=
    e0.symm.injective (Subsingleton.elim _ _)
  exact (congrArg ex hz).symm.trans
    (hn.trans ((congrArg (PointedCGWH.piNMap 1 p) h0).trans
      ((PointedCGWH.SphereHom.nullCube_map 1 p).trans
        (PointedCGWH.SphereHom.nullCube_eq_one 0 S))))

private def qCounitIso (X : C.{u, v}) : H.obj (Q.obj X) ≅ H.obj X := by
  let _ : IsIso (H.map (ε.app X)) :=
    Localization.inverts H (weakEquivalences C.{u, v}) _
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
  exact asIso (H.map (ε.app X))

private theorem qCounitIso_hom (X : C.{u, v}) :
    (qCounitIso X).hom = H.map (ε.app X) := rfl

private abbrev delooping (E : C.{u, v}) := (deloopTarget 1).obj E
private abbrev mappingEnd (X E : C.{u, v}) :=
  PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) (delooping E)

/-- The original full Omega delta isomorphism in the original native level Ho. -/
def omegaLoopIso (E : C.{u, v}) (hE : NativeK.IsOmega Actual.orthogonalFamily E) :
    H.obj E ≅ H.obj ((scalarLoopFunctor.{u, v}).obj (delooping E)) :=
  deltaHoIso (B := B) 0 E hE

omit B in
private def loopRecordIso : scalarLoopFunctor.{u, v} ≅
    cotensor (I := O.{u, v}) PointedCGWH.sphereOne.{u, v} :=
  Iso.refl _

namespace Generic

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private instance nativeZero : HasZeroObject (C.{u, v} (I := I)) := Diagrams.nativeHasZeroObject

/-- Original Q, the given actual loop-target isomorphism, and the native scalar adjunction
identify the entire original target Hom set with its original mapping-end fundamental group. -/
def homGroupEquiv (X E D : C.{u, v} (I := I)) (e : H.obj E ≅ H.obj (R.obj D)) :
    (H.obj X ⟶ H.obj E) ≃
      ((PointedCGWH.piNPositiveFunctor 0).obj
        (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D)) :=
  (postcompositionEquiv (H.obj X) e).trans
    ((loopScalarEquiv (B := B) X D).trans
      (coefficientPiEquiv (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D)))

/-- The actual fundamental group of the entire original Q-source mapping end. -/
def representedHomGroup (X D : C.{u, v} (I := I)) : GrpCat.{v} :=
  (PointedCGWH.piNPositiveFunctor 0).obj
    (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D)

/-- The original full source action as a homomorphism of its represented groups. -/
def sourceGroupHom {X Y : C.{u, v} (I := I)} (f : X ⟶ Y) (D : C.{u, v} (I := I)) :
    representedHomGroup Y D →* representedHomGroup X D :=
  pointPiHom (WeightedEndVariance.pre (Q.map f) D)

/-- Every full original source map acts by its original Q and weighted-end fundamental-group map. -/
theorem homGroupEquiv_source {X Y : C.{u, v} (I := I)} (f : X ⟶ Y)
    (E D : C.{u, v} (I := I)) (e : H.obj E ≅ H.obj (R.obj D)) (g : H.obj Y ⟶ H.obj E) :
    homGroupEquiv X E D e (H.map f ≫ g) =
      (PointedCGWH.piNPositiveMap 0 (WeightedEndVariance.pre (Q.map f) D)).hom
        (homGroupEquiv Y E D e g) :=
  composeNaturality3 (postcompositionEquiv (H.obj X) e) (postcompositionEquiv (H.obj Y) e)
    (loopScalarEquiv (B := B) X D) (loopScalarEquiv (B := B) Y D)
    (coefficientPiEquiv (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D))
    (coefficientPiEquiv (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj Y) D))
    (fun k => H.map f ≫ k) (fun k => H.map f ≫ k)
    (fun k => k ≫ P.map (WeightedEndVariance.pre (Q.map f) D))
    (PointedCGWH.piNPositiveMap 0 (WeightedEndVariance.pre (Q.map f) D)).hom
    (fun k => Category.assoc (H.map f) k e.hom)
    (fun k => loopScalarEquiv_source (B := B) f D k)
    (fun k => coefficientPiEquiv_naturality (WeightedEndVariance.pre (Q.map f) D) k) g

/-- This group homomorphism has the source's same whole precomposition function. -/
theorem homGroupEquiv_source_group {X Y : C.{u, v} (I := I)} (f : X ⟶ Y)
    (E D : C.{u, v} (I := I)) (e : H.obj E ≅ H.obj (R.obj D)) (g : H.obj Y ⟶ H.obj E) :
    homGroupEquiv X E D e (H.map f ≫ g) =
      sourceGroupHom f D (homGroupEquiv Y E D e g) :=
  (homGroupEquiv_source f E D e g).trans
    ((PointedCGWH.piNPositiveMap_apply 0 (WeightedEndVariance.pre (Q.map f) D) _).trans
      (pointPiHom_apply (WeightedEndVariance.pre (Q.map f) D) _).symm)

/-- The entire original null Hom class is the identity in the original mapping-end fundamental group. -/
theorem homGroupEquiv_null (X E D : C.{u, v} (I := I)) (e : H.obj E ≅ H.obj (R.obj D)) :
    homGroupEquiv X E D e (OrdinaryHoCofiberKernel.nullHom X E) =
      groupIdentity ((PointedCGWH.piNPositiveFunctor 0).obj
        (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D)) := by
  let _ : IsFibrant E := Native.allObjectsFibrant E
  let _ : Subsingleton (H.obj (0 : C.{u, v} (I := I)) ⟶ H.obj E) :=
    OrdinaryHoCofiberKernel.subsingleton_hom_from_zero E
  have hn : homGroupEquiv X E D e
      (H.map (HasZeroObject.zeroIsTerminal.from X) ≫ OrdinaryHoCofiberKernel.nullHom 0 E) =
      (PointedCGWH.piNPositiveMap 0
        (WeightedEndVariance.pre (Q.map (HasZeroObject.zeroIsTerminal.from X)) D)).hom
        (homGroupEquiv 0 E D e (OrdinaryHoCofiberKernel.nullHom 0 E)) :=
    homGroupEquiv_source (HasZeroObject.zeroIsTerminal.from X) E D e
      (OrdinaryHoCofiberKernel.nullHom 0 E)
  have hn' : homGroupEquiv X E D e
      (H.map (HasZeroObject.zeroIsTerminal.from X) ≫ OrdinaryHoCofiberKernel.nullHom 0 E) =
      PointedCGWH.piNMap 1
        (WeightedEndVariance.pre (Q.map (HasZeroObject.zeroIsTerminal.from X)) D)
        (homGroupEquiv 0 E D e (OrdinaryHoCofiberKernel.nullHom 0 E)) :=
    hn.trans (PointedCGWH.piNPositiveMap_apply 0
      (WeightedEndVariance.pre (Q.map (HasZeroObject.zeroIsTerminal.from X)) D) _)
  have h0 : homGroupEquiv 0 E D e (OrdinaryHoCofiberKernel.nullHom 0 E) =
      PointedCGWH.SphereHom.nullCube 1
        (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj 0) D) :=
    (homGroupEquiv 0 E D e).symm.injective (Subsingleton.elim _ _)
  have hmap : PointedCGWH.piNMap 1
      (WeightedEndVariance.pre (Q.map (HasZeroObject.zeroIsTerminal.from X)) D)
      (homGroupEquiv 0 E D e (OrdinaryHoCofiberKernel.nullHom 0 E)) =
      PointedCGWH.SphereHom.nullCube 1
        (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D) :=
    (congrArg (PointedCGWH.piNMap 1
      (WeightedEndVariance.pre (Q.map (HasZeroObject.zeroIsTerminal.from X)) D)) h0).trans
      (PointedCGWH.SphereHom.nullCube_map 1
        (WeightedEndVariance.pre (Q.map (HasZeroObject.zeroIsTerminal.from X)) D))
  have hz : H.map (HasZeroObject.zeroIsTerminal.from X) ≫ OrdinaryHoCofiberKernel.nullHom 0 E =
      OrdinaryHoCofiberKernel.nullHom X E :=
    OrdinaryHoCofiberKernel.precomp_nullHom (HasZeroObject.zeroIsTerminal.from X)
  have hnx : homGroupEquiv X E D e (OrdinaryHoCofiberKernel.nullHom X E) =
      homGroupEquiv X E D e
        (H.map (HasZeroObject.zeroIsTerminal.from X) ≫ OrdinaryHoCofiberKernel.nullHom 0 E) :=
    congrArg (homGroupEquiv X E D e) hz.symm
  have hnull : homGroupEquiv X E D e (OrdinaryHoCofiberKernel.nullHom X E) =
      PointedCGWH.SphereHom.nullCube 1
      (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D) :=
    hnx.trans (hn'.trans hmap)
  have hone : PointedCGWH.SphereHom.nullCube 1
      (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D) =
      groupIdentity ((PointedCGWH.piNPositiveFunctor 0).obj
        (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D)) :=
    PointedCGWH.SphereHom.nullCube_eq_one 0 _
  exact hnull.trans hone

/-- The whole native source Hom family is typed before its represented group values are supplied. -/
structure SourceHomGroups (E : C.{u, v} (I := I)) where
  /-- The original fundamental group of each whole Q-source mapping end. -/
  obj : C.{u, v} (I := I) → GrpCat.{v}
  /-- Both inverse functions identify the original entire source-target Hom set. -/
  equiv : ∀ X : C.{u, v} (I := I), (H.obj X ⟶ H.obj E) ≃ obj X
  /-- Every original source map gives its original represented group map. -/
  map : ∀ {X Y : C.{u, v} (I := I)}, (X ⟶ Y) → (obj Y ⟶ obj X)
  /-- The complete original source precomposition square. -/
  naturality : ∀ {X Y : C.{u, v} (I := I)} (f : X ⟶ Y) (g : H.obj Y ⟶ H.obj E),
    equiv X (H.map f ≫ g) = (map f).hom (equiv Y g)
  /-- The original ordinary null class is the original group identity. -/
  null : ∀ X : C.{u, v} (I := I), equiv X (OrdinaryHoCofiberKernel.nullHom X E) =
    groupIdentity (obj X)

/-- Original Q, the actual loop-target isomorphism and original based maps construct this whole family. -/
def sourceHomGroups (E D : C.{u, v} (I := I)) (e : H.obj E ≅ H.obj (R.obj D)) :
    SourceHomGroups E where
  obj X := (PointedCGWH.piNPositiveFunctor 0).obj
    (PointedCGWH.EnrichedFunctorMapping.mappingObject (Q.obj X) D)
  equiv X := homGroupEquiv X E D e
  map f := PointedCGWH.piNPositiveMap 0 (WeightedEndVariance.pre (Q.map f) D)
  naturality f g := homGroupEquiv_source f E D e g
  null X := homGroupEquiv_null X E D e


end Generic

private def actualSourceHomGroupsFromLoop (E D : C.{u, v})
    (e : H.obj E ≅ H.obj ((cotensor (I := O.{u, v}) PointedCGWH.sphereOne).obj D)) :
    Generic.SourceHomGroups (B := B) (I := O.{u, v}) E :=
  Generic.sourceHomGroups (B := B) (I := O.{u, v}) E D e

/-- The original native Omega delooping supplies the entire source-group family
before any concrete source or integer target is substituted. -/
def omegaSourceHomGroups (E : C.{u, v}) (hE : NativeK.IsOmega Actual.orthogonalFamily E) :
    Generic.SourceHomGroups (B := B) (I := O.{u, v}) E :=
  actualSourceHomGroupsFromLoop E (delooping E)
    ((omegaLoopIso E hE).trans (H.mapIso (loopRecordIso.app (delooping E))))


end PointedCGWH.Spectra.Orthogonal.OriginalOmegaHoHomGroup
