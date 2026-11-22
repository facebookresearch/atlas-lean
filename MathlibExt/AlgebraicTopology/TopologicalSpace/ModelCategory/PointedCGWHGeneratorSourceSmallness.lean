/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHGenerators
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellTransfinite
public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorFilteredFamilyFactorization
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorStageEq
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Realized generator sources and arbitrary closed chains

The source Hom functor preserves the original fixed-cardinal colimit when
all transitions are closed embeddings. The actual base generator and its
costar image are retained. This source engine has no selected model,
cofibration, target small-object argument or coefficient-cofibrancy input.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory Limits Topology

private theorem strictMapPreimage_exists
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (I : MorphismProperty C) (F : C ⥤ D)
    {X Y : D} {f : X ⟶ Y} (hf : (I.strictMap F) f) :
    ∃ q : I.toSet,
      Nonempty (Arrow.mk f ≅ Arrow.mk (F.map q.1.hom)) := by
  cases hf with
  | @map X' Y' g hg =>
      exact ⟨⟨Arrow.mk g, hg⟩, ⟨Iso.refl _⟩⟩

private noncomputable def costarCoyonedaIso
    (A : CGWH.{u, v}) :
    PointedCGWH.pointedToCGWH.{u, v} ⋙
        coyoneda.obj (Opposite.op A) ≅
      coyoneda.obj
        (Opposite.op ((Under.costar CGWH.point).obj A)) :=
  ((Under.costarAdjForget CGWH.point).compCoyonedaIso.app
    (Opposite.op A)).symm

private noncomputable def fullyFaithfulCoyonedaIso
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v} D]
    (T : C ⥤ D) [T.Full] [T.Faithful] (A : C) :
    T ⋙ coyoneda.obj (Opposite.op (T.obj A)) ≅
      coyoneda.obj (Opposite.op A) := by
  let hT := Functor.FullyFaithful.ofFullyFaithful T
  exact NatIso.ofComponents
    (fun X => Equiv.toIso hT.homEquiv.symm)
    (fun f => by
      ext g
      apply T.map_injective
      simp [hT])

private theorem cgwhRealizedGenerator_map_mem
    {A B : CGWH.{u, v}} (g : A ⟶ B)
    (hg : (CGWH.realizedBoundaryInclusions ⊔
      CGWH.realizedHornInclusions) g) :
    (TopCat.realizedBoundaryInclusions ⊔
      TopCat.realizedHornInclusions) (CGWH.cgwhToTop.map g) := by
  rw [MorphismProperty.sup_iff] at hg ⊢
  cases hg with
  | inl hgB =>
      left
      unfold CGWH.realizedBoundaryInclusions at hgB
      rw [MorphismProperty.ofHoms_iff] at hgB
      obtain ⟨n, hArrow⟩ := hgB
      unfold TopCat.realizedBoundaryInclusions
      rw [MorphismProperty.ofHoms_iff]
      refine ⟨n, ?_⟩
      let T := CGWH.cgwhToTop.{u, v}
      let j := CGWH.cgwhToCompactlyGenerated.{u, v}
      let k := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
      have hMapped : Arrow.mk (T.map g) =
          Arrow.mk (T.map (CGWH.realizedBoundaryInclusion.{v, u} n)) := by
        simpa [T] using
          congrArg (fun a : Arrow CGWH.{u, v} => T.mapArrow.obj a) hArrow
      have hLiteral :
          T.map (CGWH.realizedBoundaryInclusion.{v, u} n) =
            SSet.toTop.map (SSet.boundary.{v} n).ι := by
        change k.map (j.map
          (CGWH.realizedBoundaryInclusion.{v, u} n)) = _
        exact (congrArg (fun q => k.map q)
          (CGWH.cgwhToCompactlyGenerated_map_realizedBoundaryInclusion n)).trans
            (CompactlyGenerated.compactlyGeneratedToTop_map_realizedBoundaryInclusion n)
      exact hMapped.trans (congrArg Arrow.mk hLiteral)
  | inr hgH =>
      right
      unfold CGWH.realizedHornInclusions at hgH
      rw [MorphismProperty.iSup_iff] at hgH
      obtain ⟨r, hr⟩ := hgH
      rw [MorphismProperty.ofHoms_iff] at hr
      obtain ⟨i, hArrow⟩ := hr
      unfold TopCat.realizedHornInclusions
      rw [MorphismProperty.iSup_iff]
      refine ⟨r, ?_⟩
      rw [MorphismProperty.ofHoms_iff]
      refine ⟨i, ?_⟩
      let T := CGWH.cgwhToTop.{u, v}
      let j := CGWH.cgwhToCompactlyGenerated.{u, v}
      let k := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
      have hMapped : Arrow.mk (T.map g) =
          Arrow.mk (T.map (CGWH.realizedHornInclusion.{v, u} r i)) := by
        simpa [T] using
          congrArg (fun a : Arrow CGWH.{u, v} => T.mapArrow.obj a) hArrow
      have hLiteral :
          T.map (CGWH.realizedHornInclusion.{v, u} r i) =
            SSet.toTop.map (SSet.horn.{v} (r + 1) i).ι := by
        change k.map (j.map
          (CGWH.realizedHornInclusion.{v, u} r i)) = _
        exact (congrArg (fun q => k.map q)
          (CGWH.cgwhToCompactlyGenerated_map_realizedHornInclusion r i)).trans
            (CompactlyGenerated.compactlyGeneratedToTop_map_realizedHornInclusion r i)
      exact hMapped.trans (congrArg Arrow.mk hLiteral)

private theorem topRealizedGeneratorSource_preservesClosedColimit
    {A B : TopCat.{v}} (g : A ⟶ B)
    (hg : (TopCat.realizedBoundaryInclusions ⊔
      TopCat.realizedHornInclusions) g)
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ TopCat.{v})
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (F.map φ).hom) :
    PreservesColimit F (coyoneda.obj (Opposite.op A)) := by
  have : Fact realizedGeneratorCardinal.{v}.IsRegular :=
    ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  have : EssentiallySmall.{v}
      realizedGeneratorCardinal.{v}.ord.ToType :=
    EssentiallySmall.mk' CategoryTheory.Equivalence.refl
  refine ⟨fun {c} hc => ?_⟩
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
  · intro x
    obtain ⟨a, s, hs⟩ :=
      realizedGenerator_stage_exists c hc hF g hg x
    exact ⟨a, s, by simpa using hs.symm⟩
  · intro a b x y hxy
    have h : x ≫ c.ι.app a = y ≫ c.ι.app b := by
      simpa using hxy
    obtain ⟨d, p, q, hpq⟩ :=
      realizedGenerator_stage_eq c hc hF g hg x y h
    exact ⟨d, p, q, by simpa using hpq⟩

namespace CGWH

/-- Realized native generator sources preserve the actual fixed-cardinal colimit
for arbitrary closed-embedding transitions. -/
theorem realizedGeneratorSource_preservesClosedColimit
    {A B : CGWH.{u, v}} (g : A ⟶ B)
    (hg : (CGWH.realizedBoundaryInclusions ⊔
      CGWH.realizedHornInclusions) g)
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ CGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (CGWH.cgwhToTop.map (F.map φ)).hom) :
    PreservesColimit F (coyoneda.obj (Opposite.op A)) := by
  let κ : Cardinal.{v} := realizedGeneratorCardinal.{v}
  let J := κ.ord.ToType
  have : Fact κ.IsRegular := ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  have : Nonempty J :=
    Ordinal.nonempty_toType_iff.mpr
      (by simpa [κ] using isRegular_realizedGeneratorCardinal.{v}.ne_zero)
  let _ : OrderBot J := WellFoundedLT.toOrderBot J
  have : EssentiallySmall.{v} J :=
    EssentiallySmall.mk' CategoryTheory.Equivalence.refl
  let j := CGWH.cgwhToCompactlyGenerated.{u, v}
  let k := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  let T := CGWH.cgwhToTop.{u, v}
  have hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (j.map (F.map (homOfLE (Order.le_succ a)))).hom := by
    intro a ha
    change Function.Injective
      (T.map (F.map (homOfLE (Order.le_succ a)))).hom
    exact (hF (homOfLE (Order.le_succ a))).injective
  have hJ : PreservesColimit F j :=
    preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit F)
      (CGWH.isColimitMapCoconeOfInjectiveSucc F hSucc
        (colimit.cocone F) (colimit.isColimit F))
  let _ : PreservesColimit F j := hJ
  let _ : PreservesColimit (F ⋙ j) k := inferInstance
  let _ : PreservesColimit F (j ⋙ k) := inferInstance
  let _ : PreservesColimit F T := by
    change PreservesColimit F (j ⋙ k)
    infer_instance
  have hTopMaps : ∀ ⦃a b : J⦄ (φ : a ⟶ b),
      IsClosedEmbedding ((F ⋙ T).map φ).hom := by
    intro a b φ
    exact hF φ
  have hTop : PreservesColimit (F ⋙ T)
      (coyoneda.obj (Opposite.op (T.obj A))) :=
    topRealizedGeneratorSource_preservesClosedColimit
      (T.map g) (cgwhRealizedGenerator_map_mem g hg) (F ⋙ T) hTopMaps
  let _ : PreservesColimit (F ⋙ T)
      (coyoneda.obj (Opposite.op (T.obj A))) := hTop
  let _ : PreservesColimit F
      (T ⋙ coyoneda.obj (Opposite.op (T.obj A))) := inferInstance
  exact preservesColimit_of_natIso F (fullyFaithfulCoyonedaIso T A)

end CGWH

namespace PointedCGWH

/-- Costar images of actual realized generators preserve colimits of closed
chains, without requiring the transitions to be model cofibrations. -/
theorem realizedGeneratorSource_preservesClosedColimit
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔
      CGWH.realizedHornInclusions)
    {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : (K.strictMap (Under.costar CGWH.point)) g)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op Q)) := by
  let κ : Cardinal.{v} := realizedGeneratorCardinal.{v}
  let J := κ.ord.ToType
  have : Fact κ.IsRegular := ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  have : Nonempty J :=
    Ordinal.nonempty_toType_iff.mpr
      (by simpa [κ] using isRegular_realizedGeneratorCardinal.{v}.ne_zero)
  let _ : OrderBot J := WellFoundedLT.toOrderBot J
  let U := PointedCGWH.pointedToCGWH.{u, v}
  let F := E ⋙ U
  let _ : PreservesWellOrderContinuousOfShape J U :=
    { preservesColimitsOfShape := fun b hb => by
        let _ : Nonempty (Set.Iio b) := ⟨⟨⊥, hb.bot_lt⟩⟩
        let _ : IsFiltered (Set.Iio b) := inferInstance
        infer_instance }
  let _ : F.IsWellOrderContinuous := inferInstance
  obtain ⟨q, ⟨eCostar⟩⟩ :=
    strictMapPreimage_exists K (Under.costar CGWH.point) hg
  let ePoint : Q ≅ (Under.costar CGWH.point).obj q.1.left :=
    Arrow.leftFunc.mapIso eCostar
  have hClosed : ∀ ⦃a b : J⦄ (φ : a ⟶ b),
      IsClosedEmbedding (CGWH.cgwhToTop.map (F.map φ)).hom := by
    intro a b φ
    exact hE φ
  have hNative : PreservesColimit F
      (coyoneda.obj (Opposite.op q.1.left)) :=
    CGWH.realizedGeneratorSource_preservesClosedColimit
      q.1.hom (hK _ q.2) F hClosed
  let _ : PreservesColimit E U := inferInstance
  let _ : PreservesColimit F
      (coyoneda.obj (Opposite.op q.1.left)) := hNative
  let _ : PreservesColimit E
      (U ⋙ coyoneda.obj (Opposite.op q.1.left)) := inferInstance
  let hCostar : PreservesColimit E
      (coyoneda.obj
        (Opposite.op ((Under.costar CGWH.point).obj q.1.left))) :=
    preservesColimit_of_natIso E (costarCoyonedaIso q.1.left)
  let _ : PreservesColimit E
      (coyoneda.obj
        (Opposite.op ((Under.costar CGWH.point).obj q.1.left))) := hCostar
  exact preservesColimit_of_natIso E (coyoneda.mapIso ePoint.op)

/-- Pointed boundary-generator sources preserve closed-chain colimits. -/
theorem realizedBoundarySource_preservesClosedColimit
    {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : (CGWH.realizedBoundaryInclusions.{u, v}.strictMap
      (Under.costar CGWH.point)) g)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op Q)) :=
  realizedGeneratorSource_preservesClosedColimit
    CGWH.realizedBoundaryInclusions le_sup_left g hg E hE

/-- Pointed horn-generator sources preserve closed-chain colimits. -/
theorem realizedHornSource_preservesClosedColimit
    {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : (CGWH.realizedHornInclusions.{u, v}.strictMap
      (Under.costar CGWH.point)) g)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op Q)) :=
  realizedGeneratorSource_preservesClosedColimit
    CGWH.realizedHornInclusions le_sup_right g hg E hE

end PointedCGWH
