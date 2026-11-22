/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.Colimits.BoundedTopologicalSource
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeBasedSources
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHGeneratorSourceSmallness

/-!
# Native sources bounded at the original realized cardinal

The actual CGWH closed-chain colimit witnesses and original fully faithful
inclusion carry bounded-source Hom preservation from TopCat. Actual costar
adjunction and the original Under finite pushout presentation supply pointed
source preservation. No native source preservation/model/LP dictionary is
assumed. The cardinal bound is a genuine carrier property to be proved for
the original finite coefficient objects.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC uD vH

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology

private def fullyFaithfulCoyonedaIso
    {C : Type uC} [Category.{vH} C] {D : Type uD} [Category.{vH} D]
    (T : C ⥤ D) [T.Full] [T.Faithful] (A : C) :
    T ⋙ coyoneda.obj (Opposite.op (T.obj A)) ≅ coyoneda.obj (Opposite.op A) := by
  let hT := Functor.FullyFaithful.ofFullyFaithful T
  exact NatIso.ofComponents (fun X => Equiv.toIso hT.homEquiv.symm) (fun f => by
    ext g
    apply T.map_injective
    simp [hT])

namespace CGWH.BoundedSource

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- A genuinely bounded native source preserves the same actual closed continuous κ chain. -/
theorem preservesClosedColimit (A : CGWH.{u, v})
    (hA : HasCardinalLT ↥(CGWH.cgwhToTop.{u, v}.obj A) realizedGeneratorCardinal.{v})
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ CGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (CGWH.cgwhToTop.map (F.map φ)).hom) :
    PreservesColimit F (coyoneda.obj (Opposite.op A)) := by
  let κ : Cardinal.{v} := realizedGeneratorCardinal.{v}
  let J := κ.ord.ToType
  have : Fact κ.IsRegular := ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  have : Nonempty J := Ordinal.nonempty_toType_iff.mpr
    (by simpa [κ] using isRegular_realizedGeneratorCardinal.{v}.ne_zero)
  have : EssentiallySmall.{v} J := EssentiallySmall.mk' CategoryTheory.Equivalence.refl
  let j := CGWH.cgwhToCompactlyGenerated.{u, v}
  let k := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  let T := CGWH.cgwhToTop.{u, v}
  have hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (j.map (F.map (homOfLE (Order.le_succ a)))).hom := by
    intro a ha
    change Function.Injective (T.map (F.map (homOfLE (Order.le_succ a)))).hom
    exact (hF (homOfLE (Order.le_succ a))).injective
  let _ : PreservesColimit F j :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
      (CGWH.isColimitMapCoconeOfInjectiveSucc F hSucc
        (colimit.cocone F) (colimit.isColimit F))
  let _ : PreservesColimit (F ⋙ j) k := inferInstance
  let _ : PreservesColimit F T := by
    change PreservesColimit F (j ⋙ k)
    infer_instance
  have hTopMaps : ∀ ⦃a b : J⦄ (φ : a ⟶ b),
      IsClosedEmbedding ((F ⋙ T).map φ).hom := fun _ _ φ => hF φ
  let _ : PreservesColimit (F ⋙ T)
      (coyoneda.obj (Opposite.op (T.obj A))) :=
    TopCat.BoundedSource.preservesClosedColimit (T.obj A) hA (F ⋙ T) hTopMaps
  let _ : PreservesColimit F (T ⋙ coyoneda.obj (Opposite.op (T.obj A))) := inferInstance
  exact preservesColimit_of_natIso F (fullyFaithfulCoyonedaIso T A)

end CGWH.BoundedSource

namespace PointedCGWH.BoundedSource

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit B in
private def costarCoyonedaIso (A : CGWH.{u, v}) :
    PointedCGWH.pointedToCGWH.{u, v} ⋙ coyoneda.obj (Opposite.op A) ≅
      coyoneda.obj (Opposite.op ((Under.costar CGWH.point.{u, v}).obj A)) :=
  ((Under.costarAdjForget CGWH.point.{u, v}).compCoyonedaIso.app (Opposite.op A)).symm

/-- The actual original freely pointed bounded underlying source preserves the same κ diagram. -/
theorem costar_preservesClosedColimit (A : CGWH.{u, v})
    (hA : HasCardinalLT ↥(CGWH.cgwhToTop.{u, v}.obj A) realizedGeneratorCardinal.{v})
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b), IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right)) :
    PreservesColimit E (coyoneda.obj
      (Opposite.op ((Under.costar CGWH.point.{u, v}).obj A))) := by
  let κ : Cardinal.{v} := realizedGeneratorCardinal.{v}
  let J := κ.ord.ToType
  have : Fact κ.IsRegular := ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  have : Nonempty J := Ordinal.nonempty_toType_iff.mpr
    (by simpa [κ] using isRegular_realizedGeneratorCardinal.{v}.ne_zero)
  let U := PointedCGWH.pointedToCGWH.{u, v}
  let F := E ⋙ U
  let _ : PreservesWellOrderContinuousOfShape J U :=
    { preservesColimitsOfShape := fun b hb => by
        let _ : Nonempty (Set.Iio b) := ⟨⟨⊥, hb.bot_lt⟩⟩
        let _ : IsFiltered (Set.Iio b) := inferInstance
        infer_instance }
  let _ : F.IsWellOrderContinuous := inferInstance
  have hClosed : ∀ ⦃a b : J⦄ (φ : a ⟶ b),
      IsClosedEmbedding (CGWH.cgwhToTop.map (F.map φ)).hom := fun _ _ φ => hE φ
  let _ : PreservesColimit F (coyoneda.obj (Opposite.op A)) :=
    CGWH.BoundedSource.preservesClosedColimit A hA F hClosed
  let _ : PreservesColimit E U := inferInstance
  let _ : PreservesColimit E (U ⋙ coyoneda.obj (Opposite.op A)) := inferInstance
  exact preservesColimit_of_natIso E (costarCoyonedaIso A)

/-- Every actual pointed object with bounded underlying carrier
has original κ source preservation. -/
theorem preservesClosedColimit (A : PointedCGWH.{u, v})
    (hA : HasCardinalLT ↥(CGWH.cgwhToTop.{u, v}.obj A.right) realizedGeneratorCardinal.{v})
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b), IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op A)) := by
  let _ : Fact realizedGeneratorCardinal.{v}.IsRegular :=
    ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  exact Under.source_preservesColimit_of_costarSources realizedGeneratorCardinal.{v} E A
    (PointedCGWH.freePointSource_preservesClosedColimit E hE)
    (costar_preservesClosedColimit A.right hA E hE)

end PointedCGWH.BoundedSource
