/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationDeltaGenerated
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.ConnectedSimplexTriviality
public import MathlibExt.AlgebraicTopology.SimplicialSet.PreimagePushout
public import MathlibExt.AlgebraicTopology.SimplicialSet.MinimalFibration.Realization.OneCellPointLocalTriviality
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedSimplexBoundaryCollar
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationDeltaGeneratedFiniteLimits
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonArbitrary
public import MathlibExt.Topology.Category.TopCat.DeltaGeneratedOpen
public import MathlibExt.Topology.Category.TopCat.FixedFiberGauge
public import MathlibExt.Topology.Category.TopCat.CompactPushoutProduct
public import MathlibExt.Topology.Category.TopCat.PreimageSubspacePullback
public import MathlibExt.Topology.Category.TopCat.PushoutOpenRestriction
public import MathlibExt.Topology.Convenient.DeltaGeneratedProduct

/-!
# Fixed-fiber local charts across a simplicial cell

Let p:E→B be a minimal simplicial fibration over a finite connected simplicial set in universe
u, and let B₀→B₁ attach one cell ∂Δ[n]→Δ[n] between finite subobjects of B. Fix an ambient
vertex b₀ and the realized strict fiber F over b₀.

If |E×_B B₀|→|B₀| has point-local product charts with fiber F at every point, then |E×_B
B₁|→|B₁| has such charts both at points from the old stage and at every point of the new stage.
Positive-dimensional attachments use a radial boundary collar, and dimension zero uses the
coproduct attachment.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Simplicial Topology
open scoped Simplicial

namespace SSet.MinimalFibration

private theorem map_pullbackComparison_toDeltaGenerated_isIso
    {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIso (TopCat.toDeltaGenerated.map
      (pullbackComparison SSet.toTop f g)) := by
  let cTop := pullbackComparison SSet.toTop f g
  let cCore := pullbackComparison TopCat.toDeltaGenerated
    (SSet.toTop.map f) (SSet.toTop.map g)
  let cComp := pullbackComparison
    (SSet.toTop ⋙ TopCat.toDeltaGenerated) f g
  have hComp : cComp = TopCat.toDeltaGenerated.map cTop ≫ cCore :=
    pullbackComparison_comp SSet.toTop TopCat.toDeltaGenerated f g
  let _ : IsIso cComp := inferInstance
  let _ : IsIso cCore := inferInstance
  have : IsIso (TopCat.toDeltaGenerated.map cTop ≫ cCore) := by
    rw [← hComp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ cCore

private theorem pullbackComparison_preimage_snd
    {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (T : Set (SSet.toTop.obj Y)) :
    (pullbackComparison SSet.toTop f g) ⁻¹'
        ((pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)) ⁻¹' T) =
      (SSet.toTop.map (pullback.snd f g)) ⁻¹' T := by
  ext x
  change pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)
      (pullbackComparison SSet.toTop f g x) ∈ T ↔
    SSet.toTop.map (pullback.snd f g) x ∈ T
  have hEq := ConcreteCategory.congr_hom
    (pullbackComparison_comp_snd SSet.toTop f g) x
  change pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)
      (pullbackComparison SSet.toTop f g x) =
    SSet.toTop.map (pullback.snd f g) x at hEq
  rw [hEq]

private theorem toTop_preimage_range_eq_pullback_fst_range
    {E B X : SSet.{u}} (p : E ⟶ B) (f : X ⟶ B) :
    SSet.toTop.map p ⁻¹' Set.range (SSet.toTop.map f) =
      Set.range (SSet.toTop.map (pullback.fst p f)) := by
  let sq := (IsPullback.of_hasPullback p f).map
    (SSet.toTop ⋙ forget TopCat)
  ext z
  constructor
  · rintro ⟨x, hx⟩
    have hcomm : SSet.toTop.map p z = SSet.toTop.map f x := hx.symm
    obtain ⟨w, hw₁, _hw₂⟩ := Types.exists_of_isPullback sq z x hcomm
    exact ⟨w, hw₁⟩
  · rintro ⟨w, rfl⟩
    refine ⟨SSet.toTop.map (pullback.snd p f) w, ?_⟩
    have h := ConcreteCategory.congr_hom
      (congrArg SSet.toTop.map (pullback.condition (f := p) (g := f))) w
    rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at h
    exact h.symm

private theorem isPullback_subspaceMaps_of_isPullback
    {E E₁ B B₁ : TopCat.{u}}
    {p : E ⟶ B} {p₁ : E₁ ⟶ B₁}
    {e₁ : E₁ ⟶ E} {b₁ : B₁ ⟶ B}
    (sq : IsPullback e₁ p₁ p b₁) (U : Set B) :
    IsPullback
      (AlgebraicTopology.subspaceMap e₁ (by
        intro x hx
        change p (e₁ x) ∈ U
        have hw := ConcreteCategory.congr_hom sq.w x
        change p (e₁ x) = b₁ (p₁ x) at hw
        rw [hw]
        exact hx))
      (AlgebraicTopology.subspaceMap p₁
        (fun _x hx => hx : Set.MapsTo p₁
          (p₁ ⁻¹' (b₁ ⁻¹' U)) (b₁ ⁻¹' U)))
      (AlgebraicTopology.subspaceMap p
        (fun _x hx => hx : Set.MapsTo p (p ⁻¹' U) U))
      (AlgebraicTopology.subspaceMap b₁
        (fun _x hx => hx : Set.MapsTo b₁ (b₁ ⁻¹' U) U)) := by
  have hBack :=
    AlgebraicTopology.isPullback_preimageSubspace_of_isPullback
      sq U (b₁ ⁻¹' U) rfl
  have hOuter := hBack.paste_vert sq
  let hp₁ : Set.MapsTo p₁
      (p₁ ⁻¹' (b₁ ⁻¹' U)) (b₁ ⁻¹' U) := fun _x hx => hx
  let hp : Set.MapsTo p (p ⁻¹' U) U := fun _x hx => hx
  rw [← AlgebraicTopology.subspaceMap_comp_subspaceIncl p₁ hp₁,
    ← AlgebraicTopology.subspaceMap_comp_subspaceIncl p hp] at hOuter
  have hBottom := AlgebraicTopology.isPullback_preimageSubspace b₁ U
  have hFrontComm :
      AlgebraicTopology.subspaceMap e₁ (by
        intro x hx
        change p (e₁ x) ∈ U
        have hw := ConcreteCategory.congr_hom sq.w x
        change p (e₁ x) = b₁ (p₁ x) at hw
        rw [hw]
        exact hx) ≫
          AlgebraicTopology.subspaceMap p
            (fun _x hx => hx : Set.MapsTo p (p ⁻¹' U) U) =
        AlgebraicTopology.subspaceMap p₁
            (fun _x hx => hx : Set.MapsTo p₁
              (p₁ ⁻¹' (b₁ ⁻¹' U)) (b₁ ⁻¹' U)) ≫
          AlgebraicTopology.subspaceMap b₁
            (fun _x hx => hx : Set.MapsTo b₁ (b₁ ⁻¹' U) U) := by
    apply TopCat.hom_ext
    ext x
    have hw := ConcreteCategory.congr_hom sq.w x.1
    change p (e₁ x.1) = b₁ (p₁ x.1)
    simpa using hw
  exact IsPullback.of_bot hOuter hFrontComm hBottom

private theorem isPullback_subspaceMaps_of_isPullback_eq
    {E E₁ B B₁ : TopCat.{u}}
    {p : E ⟶ B} {p₁ : E₁ ⟶ B₁}
    {e₁ : E₁ ⟶ E} {b₁ : B₁ ⟶ B}
    (sq : IsPullback e₁ p₁ p b₁)
    (U : Set B) (U₁ : Set B₁) (hU : b₁ ⁻¹' U = U₁) :
    IsPullback
      (AlgebraicTopology.subspaceMap e₁ (by
        intro x hx
        change p (e₁ x) ∈ U
        have hw := ConcreteCategory.congr_hom sq.w x
        change p (e₁ x) = b₁ (p₁ x) at hw
        rw [hw]
        have : p₁ x ∈ b₁ ⁻¹' U := hU.symm ▸ hx
        exact this))
      (AlgebraicTopology.subspaceMap p₁
        (fun _x hx => hx : Set.MapsTo p₁ (p₁ ⁻¹' U₁) U₁))
      (AlgebraicTopology.subspaceMap p
        (fun _x hx => hx : Set.MapsTo p (p ⁻¹' U) U))
      (AlgebraicTopology.subspaceMap b₁ (by
        intro x hx
        have : x ∈ b₁ ⁻¹' U := hU.symm ▸ hx
        exact this)) := by
  subst U₁
  exact isPullback_subspaceMaps_of_isPullback sq U

private theorem deltaGeneratedSpace_of_trivialBundle
    {E B F : TopCat.{u}} (q : E ⟶ B)
    (h : TrivialBundleWithFiber F q)
    [LocallyCompactSpace B] [DeltaGeneratedSpace B]
    [DeltaGeneratedSpace F] : DeltaGeneratedSpace E := by
  let eProd := h.isLimit.conePointUniqueUpToIso (prodIsProd B F)
  let e : E ≅ TopCat.of (B × F) := eProd ≪≫ TopCat.prodIsoProd B F
  have : DeltaGeneratedSpace (B × F) :=
    DeltaGeneratedSpace.prod_of_locallyCompact_left
  exact (TopCat.homeoOfIso e).symm.isQuotientMap.isGeneratedBy

private noncomputable def restrictedBoundaryIso
    {X Y Z R : SSet.{u}} [Y.Finite]
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (T : Set (SSet.toTop.obj Y)) (hT : IsOpen T)
    (hTarget : TrivialBundleWithFiber (SSet.toTop.obj R)
      (AlgebraicTopology.subspaceMap
        (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
        (fun _x hx => hx : Set.MapsTo
          (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
          ((pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)) ⁻¹' T) T))) :
    TopCat.of ((SSet.toTop.map (pullback.snd f g)) ⁻¹' T) ≅
      TopCat.of
        ((pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)) ⁻¹' T) := by
  let cTop := pullbackComparison SSet.toTop f g
  let qV := AlgebraicTopology.subspaceMap
    (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
    (fun _x hx => hx : Set.MapsTo
      (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
      ((pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)) ⁻¹' T) T)
  let V :=
    (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)) ⁻¹' T
  let W := cTop ⁻¹' V
  let W' := (SSet.toTop.map (pullback.snd f g)) ⁻¹' T
  have hV : IsOpen V :=
    hT.preimage
      (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)).hom.continuous
  have hW : IsOpen W := hV.preimage cTop.hom.continuous
  let _ : DeltaGeneratedSpace W := hW.deltaGeneratedSpace
  let _ : DeltaGeneratedSpace T := hT.deltaGeneratedSpace
  let _ : LocallyCompactSpace T := hT.locallyCompactSpace
  let _ : DeltaGeneratedSpace V :=
    deltaGeneratedSpace_of_trivialBundle
      (E := TopCat.of V) (B := TopCat.of T)
      (F := SSet.toTop.obj R) qV hTarget
  let _ : IsIso (TopCat.toDeltaGenerated.map cTop) :=
    map_pullbackComparison_toDeltaGenerated_isIso f g
  let hcU : Set.MapsTo cTop W V := fun _x hx => hx
  let cU := AlgebraicTopology.subspaceMap cTop hcU
  let _ : IsIso cU :=
    TopCat.isIso_subspaceMap_of_toDeltaGenerated_map_isIso cTop V
  have hSource : W = W' := pullbackComparison_preimage_snd f g T
  let eSource : TopCat.of W' ≅ TopCat.of W :=
    { hom := AlgebraicTopology.subspaceInclOfSubset (by rw [hSource])
      inv := AlgebraicTopology.subspaceInclOfSubset (by rw [← hSource])
      hom_inv_id := by apply TopCat.hom_ext; ext x; rfl
      inv_hom_id := by apply TopCat.hom_ext; ext x; rfl }
  let eBoundary : TopCat.of W' ≅ TopCat.of V := eSource ≪≫ asIso cU
  exact eBoundary

@[reassoc]
private theorem restrictedBoundaryIso_hom_projection
    {X Y Z R : SSet.{u}} [Y.Finite]
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (T : Set (SSet.toTop.obj Y)) (hT : IsOpen T)
    (hTarget : TrivialBundleWithFiber (SSet.toTop.obj R)
      (AlgebraicTopology.subspaceMap
        (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
        (fun _x hx => hx : Set.MapsTo
          (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
          ((pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)) ⁻¹' T) T))) :
    (restrictedBoundaryIso f g T hT hTarget).hom ≫
        AlgebraicTopology.subspaceMap
          (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
          (fun _x hx => hx : Set.MapsTo
            (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
            ((pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)) ⁻¹' T) T) =
      AlgebraicTopology.subspaceMap
        (SSet.toTop.map (pullback.snd f g))
        (fun _x hx => hx : Set.MapsTo
          (SSet.toTop.map (pullback.snd f g))
          ((SSet.toTop.map (pullback.snd f g)) ⁻¹' T) T) := by
  apply TopCat.hom_ext
  ext x
  change pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)
      (pullbackComparison SSet.toTop f g x.1) =
    SSet.toTop.map (pullback.snd f g) x.1
  exact ConcreteCategory.congr_hom
    (pullbackComparison_comp_snd SSet.toTop f g) x.1

private noncomputable def restrictedBoundaryChart
    {X Y Z R : SSet.{u}} [Y.Finite]
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (T : Set (SSet.toTop.obj Y)) (hT : IsOpen T)
    (hTarget : TrivialBundleWithFiber (SSet.toTop.obj R)
      (AlgebraicTopology.subspaceMap
        (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
        (fun _x hx => hx : Set.MapsTo
          (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
          ((pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)) ⁻¹' T) T))) :
    TrivialBundleWithFiber (SSet.toTop.obj R)
      (AlgebraicTopology.subspaceMap
        (SSet.toTop.map (pullback.snd f g))
        (fun _x hx => hx : Set.MapsTo
          (SSet.toTop.map (pullback.snd f g))
          ((SSet.toTop.map (pullback.snd f g)) ⁻¹' T) T)) :=
  TrivialBundleWithFiber.ofIso (restrictedBoundaryIso f g T hT hTarget)
    (restrictedBoundaryIso_hom_projection f g T hT hTarget) hTarget

@[simp]
private theorem restrictedBoundaryChart_r
    {X Y Z R : SSet.{u}} [Y.Finite]
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (T : Set (SSet.toTop.obj Y)) (hT : IsOpen T)
    (hTarget : TrivialBundleWithFiber (SSet.toTop.obj R)
      (AlgebraicTopology.subspaceMap
        (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
        (fun _x hx => hx : Set.MapsTo
          (pullback.snd (SSet.toTop.map f) (SSet.toTop.map g))
          ((pullback.snd (SSet.toTop.map f) (SSet.toTop.map g)) ⁻¹' T) T))) :
    (restrictedBoundaryChart f g T hT hTarget).r =
      (restrictedBoundaryIso f g T hT hTarget).hom ≫ hTarget.r :=
  rfl

private noncomputable def stagePullbackIso
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {E B B₀ B₁ : C}
    (p : E ⟶ B) (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B)
    (r : B₀ ⟶ B₁) (hr : r ≫ j₁ = j₀) :
    pullback p j₀ ≅ pullback (pullback.snd p j₁) r := by
  let sqNested : IsPullback
      (pullback.fst (pullback.snd p j₁) r ≫ pullback.fst p j₁)
      (pullback.snd (pullback.snd p j₁) r) p j₀ := by
    rw [← hr]
    exact (IsPullback.of_hasPullback (pullback.snd p j₁) r).paste_horiz
      (IsPullback.of_hasPullback p j₁)
  exact (IsPullback.of_hasPullback p j₀).isoIsPullback E B₀ sqNested

@[reassoc]
private theorem stagePullbackIso_hom_snd
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {E B B₀ B₁ : C}
    (p : E ⟶ B) (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B)
    (r : B₀ ⟶ B₁) (hr : r ≫ j₁ = j₀) :
    (stagePullbackIso p j₀ j₁ r hr).hom ≫
        pullback.snd (pullback.snd p j₁) r =
      pullback.snd p j₀ := by
  apply IsPullback.isoIsPullback_hom_snd

@[reassoc]
private theorem stagePullbackIso_hom_fst
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {E B B₀ B₁ : C}
    (p : E ⟶ B) (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B)
    (r : B₀ ⟶ B₁) (hr : r ≫ j₁ = j₀) :
    (stagePullbackIso p j₀ j₁ r hr).hom ≫
        (pullback.fst (pullback.snd p j₁) r ≫ pullback.fst p j₁) =
      pullback.fst p j₀ := by
  apply IsPullback.isoIsPullback_hom_fst

private theorem stagePullbackIso_hom_fst_boundaryToOld
    {A B₀ B₁ E : SSet.{u}} {t : A ⟶ B₀} {r : B₀ ⟶ B₁}
    (p : E ⟶ B₁) :
    (stagePullbackIso p (t ≫ r) r t rfl).hom ≫
        pullback.fst (pullback.snd p r) t =
      SSet.PreimagePushout.boundaryToOld p := by
  apply pullback.hom_ext
  · exact (stagePullbackIso_hom_fst p (t ≫ r) r t rfl).trans
      (SSet.PreimagePushout.boundaryToOld_fst p).symm
  · calc
      ((stagePullbackIso p (t ≫ r) r t rfl).hom ≫
            pullback.fst (pullback.snd p r) t) ≫ pullback.snd p r =
          (stagePullbackIso p (t ≫ r) r t rfl).hom ≫
            (pullback.fst (pullback.snd p r) t ≫ pullback.snd p r) := by
              rw [Category.assoc]
      _ = (stagePullbackIso p (t ≫ r) r t rfl).hom ≫
            (pullback.snd (pullback.snd p r) t ≫ t) := by
              rw [pullback.condition]
      _ = ((stagePullbackIso p (t ≫ r) r t rfl).hom ≫
            pullback.snd (pullback.snd p r) t) ≫ t := by
              rw [Category.assoc]
      _ = pullback.snd p (t ≫ r) ≫ t := by
              rw [stagePullbackIso_hom_snd]
      _ = SSet.PreimagePushout.boundaryToOld p ≫ pullback.snd p r :=
        (SSet.PreimagePushout.boundaryToOld_snd p).symm

private theorem stagePullbackIso_hom_fst_boundaryToCell
    {A B₀ D B₁ E : SSet.{u}}
    {t : A ⟶ B₀} {i : A ⟶ D} {r : B₀ ⟶ B₁} {b : D ⟶ B₁}
    (sq : IsPushout t i r b) (p : E ⟶ B₁) :
    (stagePullbackIso p (t ≫ r) b i sq.w.symm).hom ≫
        pullback.fst (pullback.snd p b) i =
      SSet.PreimagePushout.boundaryToCell sq p := by
  apply pullback.hom_ext
  · exact (stagePullbackIso_hom_fst p (t ≫ r) b i sq.w.symm).trans
      (SSet.PreimagePushout.boundaryToCell_fst sq p).symm
  · calc
      ((stagePullbackIso p (t ≫ r) b i sq.w.symm).hom ≫
            pullback.fst (pullback.snd p b) i) ≫ pullback.snd p b =
          (stagePullbackIso p (t ≫ r) b i sq.w.symm).hom ≫
            (pullback.fst (pullback.snd p b) i ≫ pullback.snd p b) := by
              rw [Category.assoc]
      _ = (stagePullbackIso p (t ≫ r) b i sq.w.symm).hom ≫
            (pullback.snd (pullback.snd p b) i ≫ i) := by
              rw [pullback.condition]
      _ = ((stagePullbackIso p (t ≫ r) b i sq.w.symm).hom ≫
            pullback.snd (pullback.snd p b) i) ≫ i := by
              rw [Category.assoc]
      _ = pullback.snd p (t ≫ r) ≫ i := by
              rw [stagePullbackIso_hom_snd]
      _ = SSet.PreimagePushout.boundaryToCell sq p ≫ pullback.snd p b :=
        (SSet.PreimagePushout.boundaryToCell_snd sq p).symm

private noncomputable def ambientIsoOver
    {F E E' B B' : TopCat.{u}}
    {p : E ⟶ B} {p' : E' ⟶ B} {f : B' ⟶ B}
    (e : E ≅ E') (he : e.hom ≫ p' = p)
    (h : MorphismProperty.TrivialBundleWithFiberOver F p f) :
    MorphismProperty.TrivialBundleWithFiberOver F p' f := by
  let sqIso : IsPullback e.hom p p' (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨by simpa using he⟩
  exact
    { E' := h.E'
      p' := h.p'
      t := h.t ≫ e.hom
      sq := by
        simpa only [Category.comp_id] using h.sq.paste_horiz sqIso
      trivial := h.trivial }

private noncomputable def canonicalPreimageTrivial
    {F E B : TopCat.{u}} {p : E ⟶ B} (U : Set B)
    (h : MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl U)) :
    TrivialBundleWithFiber F
      (AlgebraicTopology.subspaceMap p
        (fun _ hx => hx : Set.MapsTo p (p ⁻¹' U) U)) := by
  let sq := (AlgebraicTopology.isPullback_preimageSubspace p U).flip
  let e := sq.isoIsPullback E (TopCat.of U) h.sq
  exact TrivialBundleWithFiber.ofIso e
    (sq.isoIsPullback_hom_snd E (TopCat.of U) h.sq) h.trivial

private noncomputable def chartIso
    {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    {F E B : C} {p : E ⟶ B}
    (h : TrivialBundleWithFiber F p) : E ≅ B ⨯ F where
  hom := prod.lift p h.r
  inv := BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd
  hom_inv_id := by
    apply BinaryFan.IsLimit.hom_ext h.isLimit
    · simp only [BinaryFan.mk_fst, Category.id_comp]
      have hfst :
          BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫ p =
            prod.fst := by
        simpa only [BinaryFan.mk_fst] using
          BinaryFan.IsLimit.lift_fst h.isLimit prod.fst prod.snd
      calc
        (prod.lift p h.r ≫
              BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd) ≫ p =
            prod.lift p h.r ≫
              (BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫ p) := by
                rw [Category.assoc]
        _ = prod.lift p h.r ≫ prod.fst := by rw [hfst]
        _ = p := prod.lift_fst _ _
    · simp only [BinaryFan.mk_snd, Category.id_comp]
      have hsnd :
          BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫ h.r =
            prod.snd := by
        simpa only [BinaryFan.mk_snd] using
          BinaryFan.IsLimit.lift_snd h.isLimit prod.fst prod.snd
      calc
        (prod.lift p h.r ≫
              BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd) ≫ h.r =
            prod.lift p h.r ≫
              (BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫ h.r) := by
                rw [Category.assoc]
        _ = prod.lift p h.r ≫ prod.snd := by rw [hsnd]
        _ = h.r := prod.lift_snd _ _
  inv_hom_id := by
    apply prod.hom_ext
    · simp only [Category.id_comp]
      calc
        (BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫
              prod.lift p h.r) ≫ prod.fst =
            BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫
              (prod.lift p h.r ≫ prod.fst) := by rw [Category.assoc]
        _ = BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫ p := by
              rw [prod.lift_fst]
        _ = prod.fst := BinaryFan.IsLimit.lift_fst _ _ _
    · simp only [Category.id_comp]
      calc
        (BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫
              prod.lift p h.r) ≫ prod.snd =
            BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫
              (prod.lift p h.r ≫ prod.snd) := by rw [Category.assoc]
        _ = BinaryFan.IsLimit.lift h.isLimit prod.fst prod.snd ≫ h.r := by
              rw [prod.lift_snd]
        _ = prod.snd := BinaryFan.IsLimit.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem chartIso_hom_fst
    {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    {F E B : C} {p : E ⟶ B}
    (h : TrivialBundleWithFiber F p) :
    (chartIso h).hom ≫ prod.fst = p :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
private theorem chartIso_hom_snd
    {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    {F E B : C} {p : E ⟶ B}
    (h : TrivialBundleWithFiber F p) :
    (chartIso h).hom ≫ prod.snd = h.r :=
  prod.lift_snd _ _

private noncomputable def trivialBundleWithFiber_of_pushouts
    {F X₁ X₂ X₃ X₄ E₁ E₂ E₃ E₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    {s₂ : E₁ ⟶ E₂} {s₃ : E₁ ⟶ E₃}
    {u₂ : E₂ ⟶ E₄} {u₃ : E₃ ⟶ E₄}
    {q₁ : E₁ ⟶ X₁} {q₂ : E₂ ⟶ X₂}
    {q₃ : E₃ ⟶ X₃} {q₄ : E₄ ⟶ X₄}
    (sqE : IsPushout s₂ s₃ u₂ u₃)
    (sqProd : IsPushout (prod.map t (𝟙 F)) (prod.map l (𝟙 F))
      (prod.map r (𝟙 F)) (prod.map b (𝟙 F)))
    (h₁ : TrivialBundleWithFiber F q₁)
    (h₂ : TrivialBundleWithFiber F q₂)
    (h₃ : TrivialBundleWithFiber F q₃)
    (hs₂ : s₂ ≫ q₂ = q₁ ≫ t)
    (hs₃ : s₃ ≫ q₃ = q₁ ≫ l)
    (hu₂ : u₂ ≫ q₄ = q₂ ≫ r)
    (hu₃ : u₃ ≫ q₄ = q₃ ≫ b)
    (hf₂ : s₂ ≫ h₂.r = h₁.r)
    (hf₃ : s₃ ≫ h₃.r = h₁.r) :
    TrivialBundleWithFiber F q₄ := by
  let e₁ := chartIso h₁
  let e₂ := chartIso h₂
  let e₃ := chartIso h₃
  have ht : s₂ ≫ e₂.hom = e₁.hom ≫ prod.map t (𝟙 F) := by
    dsimp only [e₁, e₂, chartIso]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst]
      rw [← Category.assoc, prod.lift_fst]
      exact hs₂
    · simpa only [Category.assoc, prod.lift_snd, prod.map_snd,
        Category.comp_id] using hf₂
  have hl : s₃ ≫ e₃.hom = e₁.hom ≫ prod.map l (𝟙 F) := by
    dsimp only [e₁, e₃, chartIso]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst]
      rw [← Category.assoc, prod.lift_fst]
      exact hs₃
    · simpa only [Category.assoc, prod.lift_snd, prod.map_snd,
        Category.comp_id] using hf₃
  have sqE' : IsPushout (prod.map t (𝟙 F)) (prod.map l (𝟙 F))
      (e₂.inv ≫ u₂) (e₃.inv ≫ u₃) :=
    sqE.of_iso e₁ e₂ e₃ (Iso.refl _) ht hl (by simp) (by simp)
  let eApex : E₄ ≅ X₄ ⨯ F := sqE'.isoIsPushout _ _ sqProd
  have he : eApex.hom ≫ prod.fst = q₄ := by
    apply sqE.hom_ext
    · have hleg := sqE'.inl_isoIsPushout_hom _ _ sqProd
      calc
        u₂ ≫ eApex.hom ≫ prod.fst =
            e₂.hom ≫ (e₂.inv ≫ u₂) ≫ eApex.hom ≫ prod.fst := by
              simp
        _ = e₂.hom ≫ prod.map r (𝟙 F) ≫ prod.fst := by
              simpa only [Category.assoc] using
                congrArg (fun k => e₂.hom ≫ k ≫ prod.fst) hleg
        _ = e₂.hom ≫ prod.fst ≫ r := by rw [prod.map_fst]
        _ = q₂ ≫ r := by
              dsimp only [e₂, chartIso]
              rw [← Category.assoc, prod.lift_fst]
        _ = u₂ ≫ q₄ := hu₂.symm
    · have hleg := sqE'.inr_isoIsPushout_hom _ _ sqProd
      calc
        u₃ ≫ eApex.hom ≫ prod.fst =
            e₃.hom ≫ (e₃.inv ≫ u₃) ≫ eApex.hom ≫ prod.fst := by
              simp
        _ = e₃.hom ≫ prod.map b (𝟙 F) ≫ prod.fst := by
              simpa only [Category.assoc] using
                congrArg (fun k => e₃.hom ≫ k ≫ prod.fst) hleg
        _ = e₃.hom ≫ prod.fst ≫ b := by rw [prod.map_fst]
        _ = q₃ ≫ b := by
              dsimp only [e₃, chartIso]
              rw [← Category.assoc, prod.lift_fst]
        _ = u₃ ≫ q₄ := hu₃.symm
  exact TrivialBundleWithFiber.ofIso eApex he
    { r := prod.snd
      isLimit := prodIsProd _ _ }

private noncomputable def toTopTrivialBundleWithFiberOfFiniteBase
    {F E K : SSet.{u}} [K.Finite] {q : E ⟶ K}
    (h : TrivialBundleWithFiber F q) :
    TrivialBundleWithFiber (SSet.toTop.obj F) (SSet.toTop.map q) := by
  let eS : E ≅ K ⨯ F := chartIso h
  let _ : IsIso (prodComparison SSet.toTop K F) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary K F
  let eT : SSet.toTop.obj E ≅
      SSet.toTop.obj K ⨯ SSet.toTop.obj F :=
    SSet.toTop.mapIso eS ≪≫ asIso (prodComparison SSet.toTop K F)
  have he : eT.hom ≫ prod.fst = SSet.toTop.map q := by
    dsimp only [eT, Iso.trans_hom, Functor.mapIso_hom]
    change SSet.toTop.map eS.hom ≫
        prodComparison SSet.toTop K F ≫ prod.fst = SSet.toTop.map q
    rw [prodComparison_fst, ← SSet.toTop.map_comp]
    rw [show eS.hom ≫ prod.fst = q from chartIso_hom_fst h]
  exact TrivialBundleWithFiber.ofIso eT he
    { r := prod.snd
      isLimit := prodIsProd _ _ }

private noncomputable def subspaceIsoOfEq
    {X : Type u} [TopologicalSpace X] {A B : Set X} (h : A = B) :
    TopCat.of A ≅ TopCat.of B :=
  TopCat.isoOfHomeo (Homeomorph.setCongr h)

private noncomputable def preimageIsoOfIso
    {E E' B : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B}
    (e : E ≅ E') (he : e.hom ≫ p' = p) (U : Set B) :
    TopCat.of (p ⁻¹' U) ≅ TopCat.of (p' ⁻¹' U) := by
  let hom : TopCat.of (p ⁻¹' U) ⟶ TopCat.of (p' ⁻¹' U) :=
    AlgebraicTopology.subspaceMap e.hom (by
      intro x hx
      change p' (e.hom x) ∈ U
      have h := ConcreteCategory.congr_hom he x
      change p' (e.hom x) = p x at h
      rwa [h])
  let inv : TopCat.of (p' ⁻¹' U) ⟶ TopCat.of (p ⁻¹' U) :=
    AlgebraicTopology.subspaceMap e.inv (by
      intro x hx
      change p (e.inv x) ∈ U
      have h := ConcreteCategory.congr_hom he (e.inv x)
      change p' (e.hom (e.inv x)) = p (e.inv x) at h
      rw [← h]
      simpa using hx)
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply TopCat.hom_ext
        ext x
        exact ConcreteCategory.congr_hom e.hom_inv_id x.1
      inv_hom_id := by
        apply TopCat.hom_ext
        ext x
        exact ConcreteCategory.congr_hom e.inv_hom_id x.1 }

@[reassoc]
private theorem preimageIsoOfIso_hom_projection
    {E E' B : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B}
    (e : E ≅ E') (he : e.hom ≫ p' = p) (U : Set B) :
    (preimageIsoOfIso e he U).hom ≫
        AlgebraicTopology.subspaceMap p'
          (fun _x hx => hx : Set.MapsTo p' (p' ⁻¹' U) U) =
      AlgebraicTopology.subspaceMap p
        (fun _x hx => hx : Set.MapsTo p (p ⁻¹' U) U) := by
  apply TopCat.hom_ext
  ext x
  exact ConcreteCategory.congr_hom he x.1

private theorem isPushout_restrict_of_eq
    {X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t l r b) (U : Set X₄) (hU : IsOpen U)
    (U₁ : Set X₁) (U₂ : Set X₂) (U₃ : Set X₃)
    (h₁ : (t ≫ r) ⁻¹' U = U₁)
    (h₂ : r ⁻¹' U = U₂) (h₃ : b ⁻¹' U = U₃)
    (ht : Set.MapsTo t U₁ U₂) (hl : Set.MapsTo l U₁ U₃)
    (hr : Set.MapsTo r U₂ U) (hb : Set.MapsTo b U₃ U) :
    IsPushout (AlgebraicTopology.subspaceMap t ht)
      (AlgebraicTopology.subspaceMap l hl)
      (AlgebraicTopology.subspaceMap r hr)
      (AlgebraicTopology.subspaceMap b hb) := by
  let P := TopCat.RestrictedPushout.of sq U
  let e₁ : P.obj₁ ≅ TopCat.of U₁ := subspaceIsoOfEq h₁
  let e₂ : P.obj₂ ≅ TopCat.of U₂ := subspaceIsoOfEq h₂
  let e₃ : P.obj₃ ≅ TopCat.of U₃ := subspaceIsoOfEq h₃
  apply (P.isPushout hU).of_iso e₁ e₂ e₃ (Iso.refl _)
  · apply TopCat.hom_ext
    ext x
    rfl
  · apply TopCat.hom_ext
    ext x
    rfl
  · apply TopCat.hom_ext
    ext x
    rfl
  · apply TopCat.hom_ext
    ext x
    rfl

private theorem isPushout_prodMap_restrict_of_eq
    {X₁ X₂ X₃ X₄ : TopCat.{u}}
    [CompactSpace X₂] [CompactSpace X₃] [T2Space X₄]
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t l r b) (U : Set X₄) (hU : IsOpen U)
    (U₁ : Set X₁) (U₂ : Set X₂) (U₃ : Set X₃)
    (h₁ : (t ≫ r) ⁻¹' U = U₁)
    (h₂ : r ⁻¹' U = U₂) (h₃ : b ⁻¹' U = U₃)
    (ht : Set.MapsTo t U₁ U₂) (hl : Set.MapsTo l U₁ U₃)
    (hr : Set.MapsTo r U₂ U) (hb : Set.MapsTo b U₃ U)
    (F : TopCat.{u}) :
    IsPushout
      (prod.map (AlgebraicTopology.subspaceMap t ht) (𝟙 F))
      (prod.map (AlgebraicTopology.subspaceMap l hl) (𝟙 F))
      (prod.map (AlgebraicTopology.subspaceMap r hr) (𝟙 F))
      (prod.map (AlgebraicTopology.subspaceMap b hb) (𝟙 F)) := by
  let P := TopCat.RestrictedPushout.of sq U
  let _ : CompactSpace P.X₂ := by
    change CompactSpace X₂
    infer_instance
  let _ : CompactSpace P.X₃ := by
    change CompactSpace X₃
    infer_instance
  let _ : T2Space P.X₄ := by
    change T2Space X₄
    infer_instance
  let e₁ : P.obj₁ ≅ TopCat.of U₁ := subspaceIsoOfEq h₁
  let e₂ : P.obj₂ ≅ TopCat.of U₂ := subspaceIsoOfEq h₂
  let e₃ : P.obj₃ ≅ TopCat.of U₃ := subspaceIsoOfEq h₃
  let e₄ : P.obj₄ ≅ TopCat.of U := Iso.refl _
  have ht₀ : P.tU ≫ e₂.hom =
      e₁.hom ≫ AlgebraicTopology.subspaceMap t ht := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hl₀ : P.lU ≫ e₃.hom =
      e₁.hom ≫ AlgebraicTopology.subspaceMap l hl := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hr₀ : P.rU ≫ e₄.hom =
      e₂.hom ≫ AlgebraicTopology.subspaceMap r hr := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hb₀ : P.bU ≫ e₄.hom =
      e₃.hom ≫ AlgebraicTopology.subspaceMap b hb := by
    apply TopCat.hom_ext
    ext x
    rfl
  apply (P.isPushout_prodMap_right_of_compact_to_t2 hU F).of_iso
    (prod.mapIso e₁ (Iso.refl F)) (prod.mapIso e₂ (Iso.refl F))
    (prod.mapIso e₃ (Iso.refl F)) (prod.mapIso e₄ (Iso.refl F))
  · apply prod.hom_ext
    · simp only [prod.mapIso_hom, Iso.refl_hom]
      rw [prod.map_map, prod.map_fst, prod.map_map, prod.map_fst]
      simpa only [Category.comp_id] using
        congrArg (fun k => prod.fst ≫ k) ht₀
    · simp
  · apply prod.hom_ext
    · simp only [prod.mapIso_hom, Iso.refl_hom]
      rw [prod.map_map, prod.map_fst, prod.map_map, prod.map_fst]
      simpa only [Category.comp_id] using
        congrArg (fun k => prod.fst ≫ k) hl₀
    · simp
  · apply prod.hom_ext
    · simp only [prod.mapIso_hom, Iso.refl_hom]
      rw [prod.map_map, prod.map_fst, prod.map_map, prod.map_fst]
      simpa only [Category.comp_id] using
        congrArg (fun k => prod.fst ≫ k) hr₀
    · simp
  · apply prod.hom_ext
    · simp only [prod.mapIso_hom, Iso.refl_hom]
      rw [prod.map_map, prod.map_fst, prod.map_map, prod.map_fst]
      simpa only [Category.comp_id] using
        congrArg (fun k => prod.fst ≫ k) hb₀
    · simp

private noncomputable def realizedCellChart
    {E B B₁ : SSet.{u}} [B.IsConnected]
    (p : E ⟶ B) (hp : IsMinimalFibration p)
    (b₀ : B _⦋0⦌) (j₁ : B₁ ⟶ B)
    {n : ℕ} (b : (Δ[n] : SSet.{u}) ⟶ B₁) :
    TrivialBundleWithFiber
      (SSet.toTop.obj
        (pullback p
          (SSet.const (X := (Δ[0] : SSet.{u})) b₀)))
      (SSet.toTop.map (pullback.snd (pullback.snd p j₁) b)) := by
  let hAmbient :=
    trivialBundleWithFiber_pullback_stdSimplex p hp b₀ (b ≫ j₁)
  let eCell := stagePullbackIso p (b ≫ j₁) j₁ b rfl
  let hCell : TrivialBundleWithFiber
      (pullback p
        (SSet.const (X := (Δ[0] : SSet.{u})) b₀))
      (pullback.snd (pullback.snd p j₁) b) :=
    TrivialBundleWithFiber.ofIso_rev eCell
      (stagePullbackIso_hom_snd p (b ≫ j₁) j₁ b rfl) hAmbient
  exact toTopTrivialBundleWithFiberOfFiniteBase hCell

private theorem boundaryImage_ne_realizedBarycenter
    (n : ℕ)
    (a : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u})) :
    SSet.toTop.map (SSet.boundary.{u} n).ι a ≠
      SSet.realizedBarycenter n := by
  intro h
  obtain ⟨j, hj⟩ :=
    SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange n
      (SSet.toTop.map (SSet.boundary.{u} n).ι a) ⟨a, rfl⟩
  have hweights := congrArg
    (fun q : SSet.toTop.obj (Δ[n] : SSet.{u}) =>
      ((⦋n⦌.toTopHomeo) q).weights j) h
  rw [hj] at hweights
  simp [SSet.realizedBarycenter,
    Convexity.StdSimplex.weights_barycenter_apply] at hweights
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  linarith

private def boundaryTrace
    {X : TopCat.{u}} {n : ℕ}
    (t : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ⟶ X)
    (U : Set X) : Set (SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u})) :=
  t ⁻¹' U

private def collarSet
    {X : TopCat.{u}} {n : ℕ}
    (t : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ⟶ X)
    (U : Set X) : Set (SSet.toTop.obj (Δ[n] : SSet.{u})) :=
  {q | ∃ hq : q ≠ SSet.realizedBarycenter n,
    t (SSet.realizedBoundaryRadialRetraction n ⟨q, hq⟩) ∈ U}

private theorem isOpen_collarSet
    {X : TopCat.{u}} {n : ℕ}
    (t : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ⟶ X)
    (U : Set X) (hU : IsOpen U) :
    IsOpen (collarSet t U) := by
  let K : Set (SSet.toTop.obj (Δ[n] : SSet.{u})) :=
    {SSet.realizedBarycenter n}ᶜ
  let f : C(K, X) :=
    t.hom.comp (SSet.realizedBoundaryRadialRetraction n).hom
  let V : Set K := f ⁻¹' U
  have hK : IsOpen K := isOpen_compl_singleton
  have hV : IsOpen V := hU.preimage f.continuous
  have hEq : collarSet t U = Subtype.val '' V := by
    ext q
    constructor
    · rintro ⟨hq, hmem⟩
      exact ⟨⟨q, hq⟩, hmem, rfl⟩
    · rintro ⟨q', hq', rfl⟩
      exact ⟨q'.property, hq'⟩
  rw [hEq]
  exact hK.isOpenMap_subtype_val V hV

private noncomputable def collarInclusion
    {X : TopCat.{u}} {n : ℕ}
    (t : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ⟶ X)
    (U : Set X) :
    TopCat.of (boundaryTrace t U) ⟶ TopCat.of (collarSet t U) :=
  AlgebraicTopology.subspaceMap
    (SSet.toTop.map (SSet.boundary.{u} n).ι) (by
      intro a ha
      refine ⟨boundaryImage_ne_realizedBarycenter n a, ?_⟩
      simpa only [Set.mem_preimage] using
        (show t
            (SSet.realizedBoundaryRadialRetraction n
              ⟨SSet.toTop.map (SSet.boundary.{u} n).ι a,
                boundaryImage_ne_realizedBarycenter n a⟩) ∈ U by
          rw [SSet.realizedBoundaryRadialRetraction_on_boundary]
          exact ha))

private noncomputable def collarRetraction
    {X : TopCat.{u}} {n : ℕ}
    (t : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ⟶ X)
    (U : Set X) :
    TopCat.of (collarSet t U) ⟶ TopCat.of (boundaryTrace t U) := by
  let toComplement :
      C(collarSet t U,
        {q : SSet.toTop.obj (Δ[n] : SSet.{u}) //
          q ≠ SSet.realizedBarycenter n}) :=
    ⟨fun q => ⟨q.1, q.2.choose⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩
  exact TopCat.ofHom
    ⟨fun q =>
      ⟨SSet.realizedBoundaryRadialRetraction n (toComplement q),
        q.2.choose_spec⟩,
      Continuous.subtype_mk
        ((SSet.realizedBoundaryRadialRetraction n).hom.continuous.comp
          toComplement.continuous) _⟩

@[reassoc]
private theorem collarInclusion_retraction
    {X : TopCat.{u}} {n : ℕ}
    (t : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ⟶ X)
    (U : Set X) :
    collarInclusion t U ≫ collarRetraction t U = 𝟙 _ := by
  apply TopCat.hom_ext
  ext a
  exact SSet.realizedBoundaryRadialRetraction_on_boundary n a.1
    (boundaryImage_ne_realizedBarycenter n a.1)

private theorem boundary_preimage_collarSet
    {X : TopCat.{u}} {n : ℕ}
    (t : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ⟶ X)
    (U : Set X) :
    SSet.toTop.map (SSet.boundary.{u} n).ι ⁻¹' collarSet t U =
      boundaryTrace t U := by
  ext a
  constructor
  · rintro ⟨ha, hmem⟩
    change t a ∈ U
    simpa only [
      SSet.realizedBoundaryRadialRetraction_on_boundary n a ha] using hmem
  · intro ha
    change t a ∈ U at ha
    refine ⟨boundaryImage_ne_realizedBarycenter n a, ?_⟩
    simpa only [
      SSet.realizedBoundaryRadialRetraction_on_boundary n a
        (boundaryImage_ne_realizedBarycenter n a)] using ha

private theorem saturated_old_preimage
    {X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {i : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t i r b) (hi : Function.Injective i)
    (U : Set X₂) (C : Set X₃)
    (hcompat : i ⁻¹' C = t ⁻¹' U) :
    r ⁻¹' (r '' U ∪ b '' C) = U := by
  let hType := sq.flip.map (forget TopCat)
  have hr : Function.Injective r :=
    Types.pushoutCocone_inr_injective_of_isColimit hType.isColimit hi
  ext y
  constructor
  · rintro (⟨y', hy', hEq⟩ | ⟨z, hz, hEq⟩)
    · exact hr hEq ▸ hy'
    · have hcross :
          ∃ a : X₁, i a = z ∧ t a = y := by
        apply (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
          hType.isColimit hi z y).1
        exact hEq
      obtain ⟨a, ha, rfl⟩ := hcross
      have : a ∈ i ⁻¹' C := by
        change i a ∈ C
        rw [ha]
        exact hz
      rw [hcompat] at this
      exact this
  · intro hy
    exact Or.inl ⟨y, hy, rfl⟩

private theorem saturated_cell_preimage
    {X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {i : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t i r b) (hi : Function.Injective i)
    (U : Set X₂) (C : Set X₃)
    (hcompat : i ⁻¹' C = t ⁻¹' U) :
    b ⁻¹' (r '' U ∪ b '' C) = C := by
  let hType := sq.flip.map (forget TopCat)
  ext z
  constructor
  · rintro (⟨y, hy, hEq⟩ | ⟨z', hz', hEq⟩)
    · have hcross :
          ∃ a : X₁, i a = z ∧ t a = y := by
        apply (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
          hType.isColimit hi z y).1
        exact hEq.symm
      obtain ⟨a, rfl, ha⟩ := hcross
      have : a ∈ t ⁻¹' U := by
        change t a ∈ U
        rw [ha]
        exact hy
      rw [← hcompat] at this
      exact this
    · by_cases hzrange : z ∈ Set.range i
      · obtain ⟨a, rfl⟩ := hzrange
        have hcross :
            ∃ a' : X₁, i a' = z' ∧ t a' = t a := by
          apply (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
            hType.isColimit hi z' (t a)).1
          exact hEq.trans
            (ConcreteCategory.congr_hom sq.w a).symm
        obtain ⟨a', ha'i, ha't⟩ := hcross
        have ha' : a' ∈ i ⁻¹' C := by
          change i a' ∈ C
          rw [ha'i]
          exact hz'
        rw [hcompat] at ha'
        have ha : a ∈ t ⁻¹' U := by
          change t a ∈ U
          rw [← ha't]
          exact ha'
        rwa [← hcompat] at ha
      · have hzEq : z = z' :=
          Types.pushoutCocone_inr_eq_inr_of_not_mem_range_of_isColimit
            (sq.map (forget TopCat)).isColimit hzrange hEq.symm
        rwa [hzEq]
  · intro hz
    exact Or.inr ⟨z, hz, rfl⟩

private theorem isOpen_saturated
    {X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {i : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPushout t i r b) (hi : Function.Injective i)
    (U : Set X₂) (C : Set X₃)
    (hcompat : i ⁻¹' C = t ⁻¹' U)
    (hU : IsOpen U) (hC : IsOpen C) :
    IsOpen (r '' U ∪ b '' C) := by
  have hr := saturated_old_preimage sq hi U C hcompat
  have hb := saturated_cell_preimage sq hi U C hcompat
  have hq := TopCat.isQuotientMap_sumElim_of_isPushout sq
  rw [← hq.isOpen_preimage]
  rw [isOpen_sum_iff]
  change IsOpen (r ⁻¹' (r '' U ∪ b '' C)) ∧
    IsOpen (b ⁻¹' (r '' U ∪ b '' C))
  rw [hr, hb]
  exact ⟨hU, hC⟩

@[nolint unusedArguments] -- Passed down from the public `oneCellPointLocal_of_old_ambient` API.
private theorem oneCellPointLocal_of_open_data
    {E B B₀ B₁ : SSet.{u}}
    [B.Finite] [B.IsConnected] [B₀.Finite] [B₁.Finite]
    (p : E ⟶ B) (hp : IsMinimalFibration p)
    (b₀ : B _⦋0⦌)
    (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B) [Mono j₀] [Mono j₁]
    (n : ℕ) (t : (SSet.boundary n : SSet.{u}) ⟶ B₀)
    (r : B₀ ⟶ B₁) (b : (Δ[n] : SSet.{u}) ⟶ B₁)
    (hj : r ≫ j₁ = j₀)
    (sq : IsPushout t (SSet.boundary n).ι r b)
    (x : SSet.toTop.obj B₀)
    (U₂ : Set (SSet.toTop.obj B₀)) (hU₂ : IsOpen U₂) (hx : x ∈ U₂)
    (hOldDirect : MorphismProperty.TrivialBundleWithFiberOver
      (SSet.toTop.obj
        (pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀)))
      (SSet.toTop.map (pullback.snd p j₀))
      (AlgebraicTopology.subspaceIncl U₂))
    (T : Set (SSet.toTop.obj (SSet.boundary n : SSet.{u})))
    (C : Set (SSet.toTop.obj (Δ[n] : SSet.{u})))
    (hT : IsOpen T) (hC : IsOpen C)
    (j : TopCat.of T ⟶ TopCat.of C) (rho : TopCat.of C ⟶ TopCat.of T)
    (hjrho : j ≫ rho = 𝟙 _)
    (hjval : ∀ z : TopCat.of T,
      (j z).1 = SSet.toTop.map (SSet.boundary n).ι z.1)
    (hcompat : SSet.toTop.map (SSet.boundary n).ι ⁻¹' C = T)
    (htrace : SSet.toTop.map t ⁻¹' U₂ = T) :
    TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
      (SSet.toTop.map (pullback.snd p j₁))
      (SSet.toTop.obj
        (pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀)))
      (SSet.toTop.map r x) := by
  let F := pullback p
    (SSet.const (X := (Δ[0] : SSet.{u})) b₀)
  let FTop := SSet.toTop.obj F
  let p₀ := pullback.snd p j₀
  let p₁ := pullback.snd p j₁
  let pold := pullback.snd p₁ r
  let pcell := pullback.snd p₁ b
  let tT := SSet.toTop.map t
  let iT := SSet.toTop.map (SSet.boundary n).ι
  let rT := SSet.toTop.map r
  let bT := SSet.toTop.map b
  let poldT := SSet.toTop.map pold
  let pcellT := SSet.toTop.map pcell
  let eOld : SSet.toTop.obj (pullback p j₀) ≅
      SSet.toTop.obj (pullback p₁ r) :=
    SSet.toTop.mapIso (stagePullbackIso p j₀ j₁ r hj)
  have heOld : eOld.hom ≫ poldT = SSet.toTop.map p₀ := by
    dsimp only [eOld, poldT, pold, p₁, p₀, Functor.mapIso_hom]
    rw [← SSet.toTop.map_comp,
      stagePullbackIso_hom_snd p j₀ j₁ r hj]
  let hOldNested := ambientIsoOver eOld heOld hOldDirect
  let hOldU := canonicalPreimageTrivial U₂ hOldNested
  let hCellTop : TrivialBundleWithFiber FTop pcellT :=
    realizedCellChart p hp b₀ j₁ b
  let sqTop : IsPushout tT iT rT bT := sq.map SSet.toTop
  have hcompatBase : iT ⁻¹' C = tT ⁻¹' U₂ :=
    hcompat.trans htrace.symm
  let htTrace : Set.MapsTo tT T U₂ := by
    intro z hz
    change z ∈ tT ⁻¹' U₂
    rw [htrace]
    exact hz
  have hi : Function.Injective iT :=
    (SSet.boundary.closedT1Embeddings_toTop_map_ι n).isEmbedding.injective
  let U₄ : Set (SSet.toTop.obj B₁) := rT '' U₂ ∪ bT '' C
  have hrU : rT ⁻¹' U₄ = U₂ :=
    saturated_old_preimage sqTop hi U₂ C hcompatBase
  have hbU : bT ⁻¹' U₄ = C :=
    saturated_cell_preimage sqTop hi U₂ C hcompatBase
  have hU₄ : IsOpen U₄ :=
    isOpen_saturated sqTop hi U₂ C hcompatBase hU₂ hC
  have hx₄ : rT x ∈ U₄ := Or.inl ⟨x, hx, rfl⟩
  let oldSq := IsPullback.of_hasPullback poldT tT
  let hOldTarget := hOldU.pullback
    (isPullback_subspaceMaps_of_isPullback_eq oldSq U₂ T htrace)
  let hOldBoundary := restrictedBoundaryChart
    (R := pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀))
    pold t T hT hOldTarget
  let hCellC := hCellTop.pullback
    (AlgebraicTopology.isPullback_preimageSubspace pcellT C).flip
  let cellSq := IsPullback.of_hasPullback pcellT iT
  let hNewTarget : TrivialBundleWithFiber FTop
      (AlgebraicTopology.subspaceMap
        (pullback.snd pcellT iT)
        (fun _z hz => hz : Set.MapsTo (pullback.snd pcellT iT)
          ((pullback.snd pcellT iT) ⁻¹' T) T)) :=
    hCellC.pullback
      (isPullback_subspaceMaps_of_isPullback_eq cellSq C T hcompat)
  let hNewBoundary := restrictedBoundaryChart pcell
    (SSet.boundary n).ι T hT hNewTarget
  let pBd := pullback.snd p₁ (t ≫ r)
  let pBdT := SSet.toTop.map pBd
  let eOldBd : SSet.toTop.obj (pullback p₁ (t ≫ r)) ≅
      SSet.toTop.obj (pullback pold t) :=
    SSet.toTop.mapIso (stagePullbackIso p₁ (t ≫ r) r t rfl)
  have heOldBd : eOldBd.hom ≫ SSet.toTop.map (pullback.snd pold t) =
      pBdT := by
    dsimp only [eOldBd, pold, pBdT, pBd, Functor.mapIso_hom]
    rw [← SSet.toTop.map_comp,
      stagePullbackIso_hom_snd p₁ (t ≫ r) r t rfl]
  let eOldBdU := preimageIsoOfIso eOldBd heOldBd T
  let hOldBoundary₀ : TrivialBundleWithFiber FTop
      (AlgebraicTopology.subspaceMap pBdT
        (fun _z hz => hz : Set.MapsTo pBdT (pBdT ⁻¹' T) T)) :=
    TrivialBundleWithFiber.ofIso eOldBdU
      (preimageIsoOfIso_hom_projection eOldBd heOldBd T) hOldBoundary
  let eNewBd : SSet.toTop.obj (pullback p₁ (t ≫ r)) ≅
      SSet.toTop.obj
        (pullback pcell (SSet.boundary n).ι) :=
    SSet.toTop.mapIso
      (stagePullbackIso p₁ (t ≫ r) b
        (SSet.boundary n).ι sq.w.symm)
  have heNewBd : eNewBd.hom ≫
        SSet.toTop.map
          (pullback.snd pcell (SSet.boundary n).ι) =
      pBdT := by
    dsimp only [eNewBd, pcell, pBdT, pBd, Functor.mapIso_hom]
    rw [← SSet.toTop.map_comp,
      stagePullbackIso_hom_snd p₁ (t ≫ r) b
        (SSet.boundary n).ι sq.w.symm]
  let eNewBdU := preimageIsoOfIso eNewBd heNewBd T
  let hNewBoundary₀ : TrivialBundleWithFiber FTop
      (AlgebraicTopology.subspaceMap pBdT
        (fun _z hz => hz : Set.MapsTo pBdT (pBdT ⁻¹' T) T)) :=
    TrivialBundleWithFiber.ofIso eNewBdU
      (preimageIsoOfIso_hom_projection eNewBd heNewBd T) hNewBoundary
  let cOld := restrictedBoundaryIso pold t T hT hOldTarget
  let oldTargetFst : TopCat.of ((pullback.snd poldT tT) ⁻¹' T) ⟶
      TopCat.of (poldT ⁻¹' U₂) :=
    AlgebraicTopology.subspaceMap (pullback.fst poldT tT) (by
      intro z hz
      change poldT (pullback.fst poldT tT z) ∈ U₂
      have hw := ConcreteCategory.congr_hom oldSq.w z
      change poldT (pullback.fst poldT tT z) =
        tT (pullback.snd poldT tT z) at hw
      rw [hw]
      exact htTrace hz)
  have hOldTarget_r : hOldTarget.r = oldTargetFst ≫ hOldU.r := rfl
  let cNew := restrictedBoundaryIso pcell
    (SSet.boundary n).ι T hT hNewTarget
  let newTargetFst : TopCat.of ((pullback.snd pcellT iT) ⁻¹' T) ⟶
      TopCat.of (pcellT ⁻¹' C) :=
    AlgebraicTopology.subspaceMap (pullback.fst pcellT iT) (by
      intro z hz
      change pcellT (pullback.fst pcellT iT z) ∈ C
      have hw := ConcreteCategory.congr_hom cellSq.w z
      change pcellT (pullback.fst pcellT iT z) =
        iT (pullback.snd pcellT iT z) at hw
      rw [hw]
      change pullback.snd pcellT iT z ∈ iT ⁻¹' C
      rw [hcompat]
      exact hz)
  have hNewTarget_r : hNewTarget.r = newTargetFst ≫ hCellC.r := by
    rfl
  let sOld₀ : SSet.toTop.obj (pullback p₁ (t ≫ r)) ⟶
      SSet.toTop.obj (pullback p₁ r) := SSet.toTop.map
    (SSet.PreimagePushout.boundaryToOld
      (A := (SSet.boundary n : SSet.{u}))
      (B₀ := B₀) (B₁ := B₁) (E := pullback p j₁)
      (t := t) (r := r) p₁)
  let sCell₀ := SSet.toTop.map (SSet.PreimagePushout.boundaryToCell sq p₁)
  let qBd := AlgebraicTopology.subspaceMap
    (S := pBdT ⁻¹' T) (T := T) pBdT
    (fun _z hz => hz : Set.MapsTo pBdT (pBdT ⁻¹' T) T)
  let qOld := AlgebraicTopology.subspaceMap
    (S := poldT ⁻¹' U₂) (T := U₂) poldT
    (fun _z hz => hz : Set.MapsTo poldT (poldT ⁻¹' U₂) U₂)
  let qCell := AlgebraicTopology.subspaceMap
    (S := pcellT ⁻¹' C) (T := C) pcellT
    (fun _z hz => hz : Set.MapsTo pcellT (pcellT ⁻¹' C) C)
  let sOld : TopCat.of (pBdT ⁻¹' T) ⟶
      TopCat.of (poldT ⁻¹' U₂) :=
    AlgebraicTopology.subspaceMap sOld₀ (by
      intro z hz
      change poldT (sOld₀ z) ∈ U₂
      have hmap := congrArg SSet.toTop.map
        (SSet.PreimagePushout.boundaryToOld_snd
          (A := (SSet.boundary n : SSet.{u}))
          (B₀ := B₀) (B₁ := B₁) (E := pullback p j₁)
          (t := t) (r := r) (p := p₁))
      rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at hmap
      have h := ConcreteCategory.congr_hom hmap z
      change poldT (sOld₀ z) = tT (pBdT z) at h
      rw [h]
      exact htTrace hz)
  let sCell : TopCat.of (pBdT ⁻¹' T) ⟶
      TopCat.of (pcellT ⁻¹' C) :=
    AlgebraicTopology.subspaceMap sCell₀ (by
      intro z hz
      change pcellT (sCell₀ z) ∈ C
      have hmap := congrArg SSet.toTop.map
        (SSet.PreimagePushout.boundaryToCell_snd sq p₁)
      rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at hmap
      have h := ConcreteCategory.congr_hom hmap z
      change pcellT (sCell₀ z) = iT (pBdT z) at h
      rw [h]
      change pBdT z ∈ iT ⁻¹' C
      rw [hcompat]
      exact hz)
  have hsOld : sOld ≫ qOld = qBd ≫
      AlgebraicTopology.subspaceMap tT
        htTrace := by
    apply TopCat.hom_ext
    ext z
    have hmap := congrArg SSet.toTop.map
      (SSet.PreimagePushout.boundaryToOld_snd
        (A := (SSet.boundary n : SSet.{u}))
        (B₀ := B₀) (B₁ := B₁) (E := pullback p j₁)
        (t := t) (r := r) (p := p₁))
    rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at hmap
    change poldT (sOld₀ z.1) = tT (pBdT z.1)
    exact ConcreteCategory.congr_hom hmap z.1
  have hsCell : sCell ≫ qCell = qBd ≫ j := by
    apply TopCat.hom_ext
    ext z
    have hmap := congrArg SSet.toTop.map
      (SSet.PreimagePushout.boundaryToCell_snd sq p₁)
    rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at hmap
    change pcellT (sCell₀ z.1) = (j (qBd z)).1
    exact (ConcreteCategory.congr_hom hmap z.1).trans (hjval (qBd z)).symm
  have hOldWhole : eOldBd.hom ≫
        pullbackComparison SSet.toTop pold t ≫
        pullback.fst poldT tT = sOld₀ := by
    dsimp only [eOldBd, sOld₀, poldT, pold, tT,
      Functor.mapIso_hom]
    rw [pullbackComparison_comp_fst,
      ← SSet.toTop.map_comp,
      stagePullbackIso_hom_fst_boundaryToOld]
  have hNewWhole : eNewBd.hom ≫
        pullbackComparison SSet.toTop pcell (SSet.boundary n).ι ≫
        pullback.fst pcellT iT = sCell₀ := by
    dsimp only [eNewBd, sCell₀, pcellT, pcell, iT,
      Functor.mapIso_hom]
    rw [pullbackComparison_comp_fst,
      ← SSet.toTop.map_comp,
      stagePullbackIso_hom_fst_boundaryToCell]
  have hOldMap : eOldBdU.hom ≫ cOld.hom ≫ oldTargetFst = sOld := by
    apply TopCat.hom_ext
    ext z
    exact ConcreteCategory.congr_hom hOldWhole z.1
  have hNewMap : eNewBdU.hom ≫ cNew.hom ≫ newTargetFst = sCell := by
    apply TopCat.hom_ext
    ext z
    exact ConcreteCategory.congr_hom hNewWhole z.1
  have hOldFiber : sOld ≫ hOldU.r = hOldBoundary₀.r := by
    change sOld ≫ hOldU.r =
      (eOldBdU.hom ≫ cOld.hom) ≫ hOldTarget.r
    rw [hOldTarget_r]
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ hOldU.r) hOldMap).symm
  have hNewFiber : sCell ≫ hCellC.r = hNewBoundary₀.r := by
    change sCell ≫ hCellC.r =
      (eNewBdU.hom ≫ cNew.hom) ≫ hNewTarget.r
    rw [hNewTarget_r]
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ hCellC.r) hNewMap).symm
  let a := hOldBoundary₀.transitionGauge hNewBoundary₀
  let hCellGauge := hCellC.gauge (a.baseChange rho)
  set_option backward.isDefEq.respectTransparency false in
  have hCellChart : sCell ≫
        CartesianMonoidalCategory.lift qCell hCellC.r =
      CartesianMonoidalCategory.lift (qBd ≫ j) hNewBoundary₀.r := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc] using
        (congrArg (fun k => sCell ≫ k)
          (CartesianMonoidalCategory.lift_fst qCell hCellC.r)).trans
          (hsCell.trans
            (CartesianMonoidalCategory.lift_fst
              (qBd ≫ j) hNewBoundary₀.r).symm)
    · simpa only [Category.assoc] using
        (congrArg (fun k => sCell ≫ k)
          (CartesianMonoidalCategory.lift_snd qCell hCellC.r)).trans
          (hNewFiber.trans
            (CartesianMonoidalCategory.lift_snd
              (qBd ≫ j) hNewBoundary₀.r).symm)
  have hReindex :
      CartesianMonoidalCategory.lift (qBd ≫ j) hNewBoundary₀.r ≫
          CartesianMonoidalCategory.lift
            (CartesianMonoidalCategory.fst (TopCat.of C) FTop ≫ rho)
            (CartesianMonoidalCategory.snd (TopCat.of C) FTop) =
        CartesianMonoidalCategory.lift qBd hNewBoundary₀.r := by
    apply CartesianMonoidalCategory.hom_ext
    · calc
        (CartesianMonoidalCategory.lift (qBd ≫ j) hNewBoundary₀.r ≫
              CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.fst (TopCat.of C) FTop ≫ rho)
                (CartesianMonoidalCategory.snd (TopCat.of C) FTop)) ≫
            CartesianMonoidalCategory.fst (TopCat.of T) FTop =
          (qBd ≫ j) ≫ rho := by
            calc
              (CartesianMonoidalCategory.lift
                    (qBd ≫ j) hNewBoundary₀.r ≫
                  CartesianMonoidalCategory.lift
                    (CartesianMonoidalCategory.fst (TopCat.of C) FTop ≫ rho)
                    (CartesianMonoidalCategory.snd (TopCat.of C) FTop)) ≫
                  CartesianMonoidalCategory.fst (TopCat.of T) FTop =
                CartesianMonoidalCategory.lift
                    (qBd ≫ j) hNewBoundary₀.r ≫
                  (CartesianMonoidalCategory.lift
                      (CartesianMonoidalCategory.fst (TopCat.of C) FTop ≫ rho)
                      (CartesianMonoidalCategory.snd (TopCat.of C) FTop) ≫
                    CartesianMonoidalCategory.fst (TopCat.of T) FTop) := by
                      rw [Category.assoc]
              _ = CartesianMonoidalCategory.lift
                    (qBd ≫ j) hNewBoundary₀.r ≫
                  (CartesianMonoidalCategory.fst (TopCat.of C) FTop ≫ rho) := by
                    rw [CartesianMonoidalCategory.lift_fst]
              _ = (CartesianMonoidalCategory.lift
                    (qBd ≫ j) hNewBoundary₀.r ≫
                  CartesianMonoidalCategory.fst (TopCat.of C) FTop) ≫ rho := by
                    rw [Category.assoc]
              _ = (qBd ≫ j) ≫ rho := by
                    rw [CartesianMonoidalCategory.lift_fst]
        _ = qBd := by
          rw [Category.assoc]
          exact (congrArg (fun k => qBd ≫ k) hjrho).trans
            (Category.comp_id qBd)
        _ = CartesianMonoidalCategory.lift qBd hNewBoundary₀.r ≫
            CartesianMonoidalCategory.fst (TopCat.of T) FTop := by
          rw [CartesianMonoidalCategory.lift_fst]
    · calc
        (CartesianMonoidalCategory.lift (qBd ≫ j) hNewBoundary₀.r ≫
              CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.fst (TopCat.of C) FTop ≫ rho)
                (CartesianMonoidalCategory.snd (TopCat.of C) FTop)) ≫
            CartesianMonoidalCategory.snd (TopCat.of T) FTop =
          CartesianMonoidalCategory.lift
              (qBd ≫ j) hNewBoundary₀.r ≫
            (CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.fst (TopCat.of C) FTop ≫ rho)
                (CartesianMonoidalCategory.snd (TopCat.of C) FTop) ≫
              CartesianMonoidalCategory.snd (TopCat.of T) FTop) := by
                rw [Category.assoc]
        _ = CartesianMonoidalCategory.lift
              (qBd ≫ j) hNewBoundary₀.r ≫
            CartesianMonoidalCategory.snd (TopCat.of C) FTop := by
              rw [CartesianMonoidalCategory.lift_snd]
        _ = hNewBoundary₀.r := CartesianMonoidalCategory.lift_snd _ _
        _ = CartesianMonoidalCategory.lift qBd hNewBoundary₀.r ≫
            CartesianMonoidalCategory.snd (TopCat.of T) FTop :=
          (CartesianMonoidalCategory.lift_snd _ _).symm
  have hCellGauge_r : hCellGauge.r =
      CartesianMonoidalCategory.lift qCell hCellC.r ≫
        (a.baseChange rho).e.hom ≫
          CartesianMonoidalCategory.snd (TopCat.of C) FTop := by
    exact TrivialBundleWithFiber.gauge_r hCellC (a.baseChange rho)
  have hGaugeFiber : sCell ≫ hCellGauge.r = hOldBoundary₀.r := by
    calc
      sCell ≫ hCellGauge.r = sCell ≫
          (CartesianMonoidalCategory.lift qCell hCellC.r ≫
            (a.baseChange rho).e.hom ≫
              CartesianMonoidalCategory.snd (TopCat.of C) FTop) := by
            exact congrArg (fun k => sCell ≫ k) hCellGauge_r
      _ =
          (sCell ≫ CartesianMonoidalCategory.lift qCell hCellC.r) ≫
            (a.baseChange rho).e.hom ≫
              CartesianMonoidalCategory.snd (TopCat.of C) FTop := by
              simp only [Category.assoc]
      _ = CartesianMonoidalCategory.lift (qBd ≫ j) hNewBoundary₀.r ≫
            (a.baseChange rho).e.hom ≫
              CartesianMonoidalCategory.snd (TopCat.of C) FTop := by
                rw [hCellChart]
      _ = CartesianMonoidalCategory.lift (qBd ≫ j) hNewBoundary₀.r ≫
            (CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.fst (TopCat.of C) FTop ≫ rho)
                (CartesianMonoidalCategory.snd (TopCat.of C) FTop) ≫
              a.e.hom ≫
                CartesianMonoidalCategory.snd (TopCat.of T) FTop) := by
                simpa only [Category.assoc] using congrArg
                  (fun k => CartesianMonoidalCategory.lift
                    (qBd ≫ j) hNewBoundary₀.r ≫ k)
                  (TopCat.FixedFiberGauge.baseChange_hom_snd rho a)
      _ = (CartesianMonoidalCategory.lift
              (qBd ≫ j) hNewBoundary₀.r ≫
            CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.fst (TopCat.of C) FTop ≫ rho)
              (CartesianMonoidalCategory.snd (TopCat.of C) FTop)) ≫
              a.e.hom ≫
                CartesianMonoidalCategory.snd (TopCat.of T) FTop := by
                simp only [Category.assoc]
      _ = CartesianMonoidalCategory.lift qBd hNewBoundary₀.r ≫
            a.e.hom ≫ CartesianMonoidalCategory.snd (TopCat.of T) FTop := by
            rw [hReindex]
      _ = (hNewBoundary₀.gauge a).r := by
            exact (TrivialBundleWithFiber.gauge_r hNewBoundary₀ a).symm
      _ = hOldBoundary₀.r := by
            exact congrArg TrivialBundleWithFiber.r
              (TrivialBundleWithFiber.gauge_transition
                hOldBoundary₀ hNewBoundary₀)
  have hBase₁ : (tT ≫ rT) ⁻¹' U₄ = T := by
    change tT ⁻¹' (rT ⁻¹' U₄) = T
    rw [hrU]
    exact htrace
  let ht : Set.MapsTo tT T U₂ := htTrace
  let hl : Set.MapsTo iT T C := by
    intro z hz
    change z ∈ iT ⁻¹' C
    rw [hcompat]
    exact hz
  let hr : Set.MapsTo rT U₂ U₄ := by
    intro z hz
    change z ∈ rT ⁻¹' U₄
    rw [hrU]
    exact hz
  let hb : Set.MapsTo bT C U₄ := by
    intro z hz
    change z ∈ bT ⁻¹' U₄
    rw [hbU]
    exact hz
  let tU := AlgebraicTopology.subspaceMap (S := T) (T := U₂) tT ht
  let lU := AlgebraicTopology.subspaceMap (S := T) (T := C) iT hl
  let rU := AlgebraicTopology.subspaceMap (S := U₂) (T := U₄) rT hr
  let bU := AlgebraicTopology.subspaceMap (S := C) (T := U₄) bT hb
  have hl_eq : lU = j := by
    apply TopCat.hom_ext
    ext z
    exact (hjval z).symm
  let sqBaseU : IsPushout tU j rU bU := by
    rw [← hl_eq]
    exact isPushout_restrict_of_eq sqTop U₄ hU₄ T U₂ C
      hBase₁ hrU hbU ht hl hr hb
  let sqProd : IsPushout (prod.map tU (𝟙 FTop))
      (prod.map j (𝟙 FTop)) (prod.map rU (𝟙 FTop))
      (prod.map bU (𝟙 FTop)) := by
    rw [← hl_eq]
    exact isPushout_prodMap_restrict_of_eq sqTop U₄ hU₄ T U₂ C
      hBase₁ hrU hbU ht hl hr hb FTop
  let p₁T := SSet.toTop.map p₁
  let oldIn₀ := SSet.toTop.map (pullback.fst p₁ r)
  let cellIn₀ := SSet.toTop.map (pullback.fst p₁ b)
  let ET : Set (SSet.toTop.obj (pullback p₁ (t ≫ r))) := pBdT ⁻¹' T
  let EOld : Set (SSet.toTop.obj (pullback p₁ r)) := poldT ⁻¹' U₂
  let ECell : Set (SSet.toTop.obj (pullback p₁ b)) := pcellT ⁻¹' C
  let ENew : Set (SSet.toTop.obj (pullback p j₁)) := p₁T ⁻¹' U₄
  have hOldIn : oldIn₀ ≫ p₁T = poldT ≫ rT := by
    dsimp only [oldIn₀, p₁T, poldT, pold, rT]
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
      pullback.condition]
  have hCellIn : cellIn₀ ≫ p₁T = pcellT ≫ bT := by
    dsimp only [cellIn₀, p₁T, pcellT, pcell, bT]
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
      pullback.condition]
  have hSOld₀ : sOld₀ ≫ poldT = pBdT ≫ tT := by
    dsimp only [sOld₀, poldT, pold, pBdT, pBd, tT]
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
      SSet.PreimagePushout.boundaryToOld_snd]
  have hSCell₀ : sCell₀ ≫ pcellT = pBdT ≫ iT := by
    dsimp only [sCell₀, pcellT, pcell, pBdT, pBd, iT]
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
      SSet.PreimagePushout.boundaryToCell_snd]
  have hTot₂ : oldIn₀ ⁻¹' ENew = EOld := by
    ext z
    change p₁T (oldIn₀ z) ∈ U₄ ↔ poldT z ∈ U₂
    have h := ConcreteCategory.congr_hom hOldIn z
    change p₁T (oldIn₀ z) = rT (poldT z) at h
    rw [h]
    change poldT z ∈ rT ⁻¹' U₄ ↔ poldT z ∈ U₂
    rw [hrU]
  have hTot₃ : cellIn₀ ⁻¹' ENew = ECell := by
    ext z
    change p₁T (cellIn₀ z) ∈ U₄ ↔ pcellT z ∈ C
    have h := ConcreteCategory.congr_hom hCellIn z
    change p₁T (cellIn₀ z) = bT (pcellT z) at h
    rw [h]
    change pcellT z ∈ bT ⁻¹' U₄ ↔ pcellT z ∈ C
    rw [hbU]
  have hTot₁ : (sOld₀ ≫ oldIn₀) ⁻¹' ENew = ET := by
    ext z
    change p₁T (oldIn₀ (sOld₀ z)) ∈ U₄ ↔ pBdT z ∈ T
    have h₁ := ConcreteCategory.congr_hom hOldIn (sOld₀ z)
    change p₁T (oldIn₀ (sOld₀ z)) = rT (poldT (sOld₀ z)) at h₁
    have h₂ := ConcreteCategory.congr_hom hSOld₀ z
    change poldT (sOld₀ z) = tT (pBdT z) at h₂
    rw [h₁, h₂]
    change tT (pBdT z) ∈ rT ⁻¹' U₄ ↔ pBdT z ∈ T
    rw [hrU]
    change pBdT z ∈ tT ⁻¹' U₂ ↔ pBdT z ∈ T
    rw [htrace]
  have hENew : IsOpen ENew := hU₄.preimage p₁T.hom.continuous
  let hsOldMap : Set.MapsTo sOld₀ ET EOld := by
    intro z hz
    change poldT (sOld₀ z) ∈ U₂
    have h := ConcreteCategory.congr_hom hSOld₀ z
    change poldT (sOld₀ z) = tT (pBdT z) at h
    rw [h]
    exact htTrace hz
  let hsCellMap : Set.MapsTo sCell₀ ET ECell := by
    intro z hz
    change pcellT (sCell₀ z) ∈ C
    have h := ConcreteCategory.congr_hom hSCell₀ z
    change pcellT (sCell₀ z) = iT (pBdT z) at h
    rw [h]
    change pBdT z ∈ iT ⁻¹' C
    rw [hcompat]
    exact hz
  let hOldInMap : Set.MapsTo oldIn₀ EOld ENew := by
    intro z hz
    change p₁T (oldIn₀ z) ∈ U₄
    have h := ConcreteCategory.congr_hom hOldIn z
    change p₁T (oldIn₀ z) = rT (poldT z) at h
    rw [h]
    change poldT z ∈ rT ⁻¹' U₄
    rw [hrU]
    exact hz
  let hCellInMap : Set.MapsTo cellIn₀ ECell ENew := by
    intro z hz
    change p₁T (cellIn₀ z) ∈ U₄
    have h := ConcreteCategory.congr_hom hCellIn z
    change p₁T (cellIn₀ z) = bT (pcellT z) at h
    rw [h]
    change pcellT z ∈ bT ⁻¹' U₄
    rw [hbU]
    exact hz
  let oldIn := AlgebraicTopology.subspaceMap
    (S := EOld) (T := ENew) oldIn₀ hOldInMap
  let cellIn := AlgebraicTopology.subspaceMap
    (S := ECell) (T := ENew) cellIn₀ hCellInMap
  let qNew := AlgebraicTopology.subspaceMap
    (S := ENew) (T := U₄) p₁T (fun _z hz => hz)
  have huOld : oldIn ≫ qNew = qOld ≫ rU := by
    apply TopCat.hom_ext
    ext z
    exact ConcreteCategory.congr_hom hOldIn z.1
  have huCell : cellIn ≫ qNew = qCell ≫ bU := by
    apply TopCat.hom_ext
    ext z
    exact ConcreteCategory.congr_hom hCellIn z.1
  let sqTotalTop :=
    (SSet.PreimagePushout.isPushout sq p₁).map SSet.toTop
  let sqTotalU : IsPushout sOld sCell oldIn cellIn := by
    exact isPushout_restrict_of_eq sqTotalTop ENew hENew ET EOld ECell
      hTot₁ hTot₂ hTot₃ hsOldMap hsCellMap hOldInMap hCellInMap
  let hApex : TrivialBundleWithFiber FTop qNew :=
    trivialBundleWithFiber_of_pushouts sqTotalU sqProd
      hOldBoundary₀ hOldU hCellGauge hsOld hsCell huOld huCell
      hOldFiber hGaugeFiber
  let hOver : MorphismProperty.TrivialBundleWithFiberOver FTop p₁T
      (AlgebraicTopology.subspaceIncl U₄) :=
    { E' := TopCat.of ENew
      p' := qNew
      t := AlgebraicTopology.subspaceIncl ENew
      sq := (AlgebraicTopology.isPullback_preimageSubspace p₁T U₄).flip
      trivial := hApex }
  let _ := hOldBoundary₀
  let _ := hNewBoundary₀
  let _ := hsOld
  let _ := hsCell
  let _ := hOldFiber
  let _ := hNewFiber
  let _ := hGaugeFiber
  let _ := sqBaseU
  let _ := sqProd
  let _ := hOver
  let _ := hjrho
  let _ := hrU
  let _ := hbU
  let _ := hU₄
  let _ := hx₄
  exact ⟨U₄, hU₄, hx₄, ⟨hOver⟩⟩

private theorem oneCellPointLocal_of_old_ambient_succ
    {E B B₀ B₁ : SSet.{u}}
    [B.Finite] [B.IsConnected] [B₀.Finite] [B₁.Finite]
    (p : E ⟶ B) (hp : IsMinimalFibration p)
    (b₀ : B _⦋0⦌)
    (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B) [Mono j₀] [Mono j₁]
    (n : ℕ) (t : (SSet.boundary (n + 1) : SSet.{u}) ⟶ B₀)
    (r : B₀ ⟶ B₁) (b : (Δ[n + 1] : SSet.{u}) ⟶ B₁)
    (hj : r ≫ j₁ = j₀)
    (sq : IsPushout t (SSet.boundary (n + 1)).ι r b)
    (hOld : ∀ x : SSet.toTop.obj B₀,
      TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
        (SSet.toTop.map (pullback.snd p j₀))
        (SSet.toTop.obj
          (pullback p
            (SSet.const (X := (Δ[0] : SSet.{u})) b₀))) x)
    (x : SSet.toTop.obj B₀) :
    TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
      (SSet.toTop.map (pullback.snd p j₁))
      (SSet.toTop.obj
        (pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀)))
      (SSet.toTop.map r x) := by
  obtain ⟨U₂, hU₂, hx, ⟨hOldDirect⟩⟩ := hOld x
  let tT := SSet.toTop.map t
  let iT := SSet.toTop.map (SSet.boundary (n + 1)).ι
  let T := boundaryTrace tT U₂
  let C := collarSet tT U₂
  have hT : IsOpen T := hU₂.preimage tT.hom.continuous
  have hC : IsOpen C := isOpen_collarSet tT U₂ hU₂
  let j : TopCat.of T ⟶ TopCat.of C := collarInclusion tT U₂
  let rho : TopCat.of C ⟶ TopCat.of T := collarRetraction tT U₂
  have hjrho : j ≫ rho = 𝟙 _ := collarInclusion_retraction tT U₂
  have hjval (z : TopCat.of T) : (j z).1 = iT z.1 := rfl
  have hcompat : iT ⁻¹' C = T := boundary_preimage_collarSet tT U₂
  have htrace : tT ⁻¹' U₂ = T := rfl
  exact oneCellPointLocal_of_open_data p hp b₀ j₀ j₁
    (n + 1) t r b hj sq x U₂ hU₂ hx hOldDirect
    T C hT hC j rho hjrho hjval hcompat htrace

private theorem oneCellPointLocal_of_old_ambient_zero
    {E B B₀ B₁ : SSet.{u}}
    [B.Finite] [B.IsConnected] [B₀.Finite] [B₁.Finite]
    (p : E ⟶ B) (hp : IsMinimalFibration p)
    (b₀ : B _⦋0⦌)
    (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B) [Mono j₀] [Mono j₁]
    (t : (SSet.boundary 0 : SSet.{u}) ⟶ B₀)
    (r : B₀ ⟶ B₁) (b : (Δ[0] : SSet.{u}) ⟶ B₁)
    (hj : r ≫ j₁ = j₀)
    (sq : IsPushout t (SSet.boundary 0).ι r b)
    (hOld : ∀ x : SSet.toTop.obj B₀,
      TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
        (SSet.toTop.map (pullback.snd p j₀))
        (SSet.toTop.obj
          (pullback p
            (SSet.const (X := (Δ[0] : SSet.{u})) b₀))) x)
    (x : SSet.toTop.obj B₀) :
    TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
      (SSet.toTop.map (pullback.snd p j₁))
      (SSet.toTop.obj
        (pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀)))
      (SSet.toTop.map r x) := by
  obtain ⟨U₂, hU₂, hx, ⟨hOldDirect⟩⟩ := hOld x
  let tT := SSet.toTop.map t
  let iT := SSet.toTop.map (SSet.boundary 0).ι
  let T := boundaryTrace tT U₂
  let C : Set (SSet.toTop.obj (Δ[0] : SSet.{u})) := ∅
  have hT : IsOpen T := hU₂.preimage tT.hom.continuous
  have hC : IsOpen C := isOpen_empty
  let _ : IsEmpty (SSet.toTop.obj (SSet.boundary 0 : SSet.{u})) :=
    ⟨fun z => by
      have hz : iT z ∈ Set.range iT := ⟨z, rfl⟩
      rw [realizedBoundaryZero_range_empty] at hz
      exact hz⟩
  let _ : IsEmpty (TopCat.of.{u} T : Type u) :=
    ⟨fun z => isEmptyElim z.1⟩
  let _ : IsEmpty (TopCat.of.{u} C : Type u) :=
    ⟨fun z => z.2⟩
  let j : TopCat.of T ⟶ TopCat.of C :=
    AlgebraicTopology.subspaceMap iT (by
      intro z _hz
      exact isEmptyElim z)
  let eEmpty : TopCat.of C ≅ TopCat.of T :=
    TopCat.isoOfHomeo Homeomorph.empty
  let rho : TopCat.of C ⟶ TopCat.of T := eEmpty.hom
  have hjrho : j ≫ rho = 𝟙 _ := by
    apply TopCat.hom_ext
    ext z
    exact isEmptyElim z.1
  have hjval (z : TopCat.of T) : (j z).1 = iT z.1 := rfl
  have hcompat : iT ⁻¹' C = T := by
    ext z
    exact isEmptyElim z
  have htrace : tT ⁻¹' U₂ = T := rfl
  exact oneCellPointLocal_of_open_data p hp b₀ j₀ j₁
    0 t r b hj sq x U₂ hU₂ hx hOldDirect
    T C hT hC j rho hjrho hjval hcompat htrace

/-- Let p:E→B be a minimal simplicial fibration in universe u, with B finite and connected. Let
B₀,B₁ be finite stages with monomorphisms j₀:B₀→B and j₁:B₁→B, and choose a vertex b₀ of the
ambient B. For n∈ℕ, let t:∂Δ[n]→B₀, r:B₀→B₁ and c:Δ[n]→B₁ form the pushout square with
∂Δ[n]→Δ[n], with r≫j₁=j₀. Set p_i=|E×_B B_i→B_i| and F=|E×_B Δ[0]| over b₀. Assume p₀ has, at
every point of |B₀|, an open neighborhood U with a trivialization over U by U×F. Then p₁ has
such a point-local product chart at |r|(x) for every x∈|B₀|. The conclusion is for the realized
simplicial pullback over B₁. -/
theorem oneCellPointLocal_of_old_ambient
    {E B B₀ B₁ : SSet.{u}}
    [B.Finite] [B.IsConnected] [B₀.Finite] [B₁.Finite]
    (p : E ⟶ B) (hp : IsMinimalFibration p)
    (b₀ : B _⦋0⦌)
    (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B) [Mono j₀] [Mono j₁]
    {n : ℕ} (t : (SSet.boundary n : SSet.{u}) ⟶ B₀)
    (r : B₀ ⟶ B₁) (b : (Δ[n] : SSet.{u}) ⟶ B₁)
    (hj : r ≫ j₁ = j₀)
    (sq : IsPushout t (SSet.boundary n).ι r b)
    (hOld : ∀ x : SSet.toTop.obj B₀,
      TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
        (SSet.toTop.map (pullback.snd p j₀))
        (SSet.toTop.obj
          (pullback p
            (SSet.const (X := (Δ[0] : SSet.{u})) b₀))) x)
    (x : SSet.toTop.obj B₀) :
    TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
      (SSet.toTop.map (pullback.snd p j₁))
      (SSet.toTop.obj
        (pullback p
          (SSet.const (X := (Δ[0] : SSet.{u})) b₀)))
      (SSet.toTop.map r x) := by
  cases n with
  | zero =>
      exact oneCellPointLocal_of_old_ambient_zero
        p hp b₀ j₀ j₁ t r b hj sq hOld x
  | succ n =>
      exact oneCellPointLocal_of_old_ambient_succ
        p hp b₀ j₀ j₁ n t r b hj sq hOld x

private theorem oneCellPointLocal_of_complement_ambient
    {E B B₀ B₁ : SSet.{u}}
    [B.IsConnected]
    (p : E ⟶ B) (hp : IsMinimalFibration p)
    (b₀ : B _⦋0⦌) (j₁ : B₁ ⟶ B)
    {n : ℕ} (t : (SSet.boundary n : SSet.{u}) ⟶ B₀)
    (r : B₀ ⟶ B₁) (b : (Δ[n] : SSet.{u}) ⟶ B₁)
    (sq : IsPushout t (SSet.boundary n).ι r b)
    (y : SSet.toTop.obj B₁)
    (hy : y ∈ (Set.range (SSet.toTop.map r))ᶜ) :
    TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
      (SSet.toTop.map (pullback.snd p j₁))
      (SSet.toTop.obj
        (pullback p
          (SSet.const (X := (Δ[0] : SSet.{u})) b₀))) y := by
  let F := pullback p
    (SSet.const (X := (Δ[0] : SSet.{u})) b₀)
  let FTop := SSet.toTop.obj F
  let p₁ := pullback.snd p j₁
  let pcell := pullback.snd p₁ b
  let iT := SSet.toTop.map (SSet.boundary n).ι
  let rT := SSet.toTop.map r
  let bT := SSet.toTop.map b
  let p₁T := SSet.toTop.map p₁
  let pcellT := SSet.toTop.map pcell
  let oldIn₀ := SSet.toTop.map (pullback.fst p₁ r)
  let cellIn₀ := SSet.toTop.map (pullback.fst p₁ b)
  let sCell₀ := SSet.toTop.map (SSet.PreimagePushout.boundaryToCell sq p₁)
  let sqTop : IsPushout (SSet.toTop.map t) iT rT bT := sq.map SSet.toTop
  let sqTotalTop :=
    (SSet.PreimagePushout.isPushout sq p₁).map SSet.toTop
  let _ : Mono r := Adhesive.mono_of_isPushout_of_mono_right sq
  let _ : Mono (pullback.fst p₁ r) := inferInstance
  have hrClosed : IsClosedEmbedding rT.hom :=
    TopCat.closedT1Embeddings_le_isClosedEmbedding rT
      (SSet.closedT1Embeddings_toTop_map_of_mono r)
  have hOldTotalClosed : IsClosedEmbedding oldIn₀.hom :=
    TopCat.closedT1Embeddings_le_isClosedEmbedding oldIn₀
      (SSet.closedT1Embeddings_toTop_map_of_mono (pullback.fst p₁ r))
  let Unew : Set (SSet.toTop.obj B₁) := (Set.range rT)ᶜ
  let Cnew : Set (SSet.toTop.obj (Δ[n] : SSet.{u})) := (Set.range iT)ᶜ
  let UEnew : Set (SSet.toTop.obj (pullback p j₁)) :=
    (Set.range oldIn₀)ᶜ
  let ENew : Set (SSet.toTop.obj (pullback p j₁)) := p₁T ⁻¹' Unew
  let ECell : Set (SSet.toTop.obj (pullback p₁ b)) := pcellT ⁻¹' Cnew
  have hUnew : IsOpen Unew := TopCat.isOpen_oneCellOpenComplement hrClosed
  have hBaseSource : bT ⁻¹' Unew = Cnew :=
    TopCat.preimage_oneCellOpenComplement_eq sqTop
  have hENew : UEnew = ENew := by
    ext z
    change z ∉ Set.range oldIn₀ ↔ p₁T z ∉ Set.range rT
    have hmem := Set.ext_iff.mp
      (toTop_preimage_range_eq_pullback_fst_range p₁ r) z
    exact not_congr hmem.symm
  have hCellIn : cellIn₀ ≫ p₁T = pcellT ≫ bT := by
    dsimp only [cellIn₀, p₁T, pcellT, pcell, bT]
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
      pullback.condition]
  have hTotalSource : cellIn₀ ⁻¹' UEnew = ECell := by
    ext z
    change cellIn₀ z ∈ UEnew ↔ pcellT z ∈ Cnew
    rw [hENew]
    change p₁T (cellIn₀ z) ∈ Unew ↔ pcellT z ∈ Cnew
    have h := ConcreteCategory.congr_hom hCellIn z
    change p₁T (cellIn₀ z) = bT (pcellT z) at h
    rw [h]
    change pcellT z ∈ bT ⁻¹' Unew ↔ pcellT z ∈ Cnew
    rw [hBaseSource]
  let baseSub := AlgebraicTopology.subspaceMap
    (S := bT ⁻¹' Unew) (T := Unew) bT (fun _z hz => hz)
  have hBaseSub : IsHomeomorph baseSub.hom := by
    exact TopCat.isHomeomorph_oneCellOpenComplement_restrictPreimage
      sqTop hrClosed
  let _ : IsIso baseSub := (TopCat.isIso_iff_isHomeomorph baseSub).mpr hBaseSub
  let eBase : TopCat.of Cnew ≅ TopCat.of Unew :=
    subspaceIsoOfEq hBaseSource.symm ≪≫ asIso baseSub
  let totalSub := AlgebraicTopology.subspaceMap
    (S := cellIn₀ ⁻¹' UEnew) (T := UEnew)
    cellIn₀ (fun _z hz => hz)
  have hTotalSub : IsHomeomorph totalSub.hom := by
    exact TopCat.isHomeomorph_oneCellOpenComplement_restrictPreimage
      sqTotalTop hOldTotalClosed
  let _ : IsIso totalSub :=
    (TopCat.isIso_iff_isHomeomorph totalSub).mpr hTotalSub
  let eTotal : TopCat.of ECell ≅ TopCat.of ENew :=
    subspaceIsoOfEq hTotalSource.symm ≪≫ asIso totalSub ≪≫
      subspaceIsoOfEq hENew
  let qCell := AlgebraicTopology.subspaceMap
    (S := ECell) (T := Cnew) pcellT (fun _z hz => hz)
  let qNew := AlgebraicTopology.subspaceMap
    (S := ENew) (T := Unew) p₁T (fun _z hz => hz)
  have heTotal : eTotal.hom ≫ qNew = qCell ≫ eBase.hom := by
    apply TopCat.hom_ext
    ext z
    exact ConcreteCategory.congr_hom hCellIn z.1
  let hCellTop : TrivialBundleWithFiber FTop pcellT :=
    realizedCellChart p hp b₀ j₁ b
  let hCellC : TrivialBundleWithFiber FTop qCell :=
    hCellTop.pullback
      (AlgebraicTopology.isPullback_preimageSubspace pcellT Cnew).flip
  let eChart : TopCat.of ENew ≅ TopCat.of Unew ⨯ FTop :=
    eTotal.symm ≪≫ chartIso hCellC ≪≫
      prod.mapIso eBase (Iso.refl FTop)
  have heInv : eTotal.inv ≫ qCell = qNew ≫ eBase.inv := by
    apply (cancel_epi eTotal.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    calc
      qCell = (qCell ≫ eBase.hom) ≫ eBase.inv := by simp
      _ = (eTotal.hom ≫ qNew) ≫ eBase.inv := by rw [heTotal]
      _ = eTotal.hom ≫ (qNew ≫ eBase.inv) := by rw [Category.assoc]
  have heChart : eChart.hom ≫ prod.fst = qNew := by
    change (eTotal.inv ≫ (chartIso hCellC).hom ≫
        prod.map eBase.hom (𝟙 FTop)) ≫ prod.fst = qNew
    calc
      (eTotal.inv ≫ (chartIso hCellC).hom ≫
            prod.map eBase.hom (𝟙 FTop)) ≫ prod.fst =
          eTotal.inv ≫ (chartIso hCellC).hom ≫
            (prod.map eBase.hom (𝟙 FTop) ≫ prod.fst) := by
              simp only [Category.assoc]
      _ = eTotal.inv ≫ (chartIso hCellC).hom ≫
            (prod.fst ≫ eBase.hom) := by rw [prod.map_fst]
      _ = (eTotal.inv ≫ (chartIso hCellC).hom ≫ prod.fst) ≫
            eBase.hom := by simp only [Category.assoc]
      _ = (eTotal.inv ≫ qCell) ≫ eBase.hom := by
            rw [chartIso_hom_fst]
      _ = (qNew ≫ eBase.inv) ≫ eBase.hom := by rw [heInv]
      _ = qNew := by simp
  let hNew : TrivialBundleWithFiber FTop qNew :=
    TrivialBundleWithFiber.ofIso eChart heChart
      { r := prod.snd
        isLimit := prodIsProd _ _ }
  let hOver : MorphismProperty.TrivialBundleWithFiberOver FTop p₁T
      (AlgebraicTopology.subspaceIncl Unew) :=
    { E' := TopCat.of ENew
      p' := qNew
      t := AlgebraicTopology.subspaceIncl ENew
      sq := (AlgebraicTopology.isPullback_preimageSubspace p₁T Unew).flip
      trivial := hNew }
  exact ⟨Unew, hUnew, hy, ⟨hOver⟩⟩

/-- Let p:E→B be a minimal simplicial fibration in universe u, with B finite and connected. Let
B₀,B₁ be finite stages with monomorphisms j₀:B₀→B and j₁:B₁→B, and choose a vertex b₀ of the
ambient B. For n∈ℕ, let t:∂Δ[n]→B₀, r:B₀→B₁ and c:Δ[n]→B₁ form the pushout square with
∂Δ[n]→Δ[n], with r≫j₁=j₀. Set p_i=|E×_B B_i→B_i| and F=|E×_B Δ[0]| over b₀. Assume p₀ has, at
every point of |B₀|, an open neighborhood U with a trivialization over U by U×F. Then p₁ has
such a point-local product chart at every y∈|B₁|. The cell dimension may be zero; all three
stated base objects retain their finiteness hypotheses. -/
theorem oneCellPointLocal_all_of_old_ambient
    {E B B₀ B₁ : SSet.{u}}
    [B.Finite] [B.IsConnected] [B₀.Finite] [B₁.Finite]
    (p : E ⟶ B) (hp : IsMinimalFibration p)
    (b₀ : B _⦋0⦌)
    (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B) [Mono j₀] [Mono j₁]
    {n : ℕ} (t : (SSet.boundary n : SSet.{u}) ⟶ B₀)
    (r : B₀ ⟶ B₁) (b : (Δ[n] : SSet.{u}) ⟶ B₁)
    (hj : r ≫ j₁ = j₀)
    (sq : IsPushout t (SSet.boundary n).ι r b)
    (hOld : ∀ x : SSet.toTop.obj B₀,
      TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
        (SSet.toTop.map (pullback.snd p j₀))
        (SSet.toTop.obj
          (pullback p
            (SSet.const (X := (Δ[0] : SSet.{u})) b₀))) x)
    (y : SSet.toTop.obj B₁) :
    TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
      (SSet.toTop.map (pullback.snd p j₁))
      (SSet.toTop.obj
        (pullback p
          (SSet.const (X := (Δ[0] : SSet.{u})) b₀))) y := by
  by_cases hy : y ∈ Set.range (SSet.toTop.map r)
  · obtain ⟨x, rfl⟩ := hy
    exact oneCellPointLocal_of_old_ambient
      p hp b₀ j₀ j₁ t r b hj sq hOld x
  · apply oneCellPointLocal_of_complement_ambient
      p hp b₀ j₁ t r b sq y
    exact hy

end SSet.MinimalFibration
