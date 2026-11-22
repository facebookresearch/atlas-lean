/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CompactlyGenerated.Products
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Convenient.OpenClosed

/-!
# Closed embeddings and native products of compactly generated spaces

The native product map of two closed embeddings is a closed embedding.  The
proof first shows that compact generation preserves a raw closed embedding,
then transports the ordinary product map through the canonical native
product isomorphisms.

No claim identifies the native product with the ordinary product topology.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace CompactlyGenerated

private theorem toCompactlyGenerated_map_isClosedEmbedding
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f)) :
    IsClosedEmbedding
      (ConcreteCategory.hom
        (TopCat.toCompactlyGenerated.{u, v}.map f)) := by
  let P := compactHausProbes.{u}
  let R := TopCat.toCompactlyGenerated.{u, v}
  have heContinuous : Continuous (ConcreteCategory.hom (R.map f)) :=
    (ConcreteCategory.hom (R.map f)).continuous
  let e : WithGeneratedByTopology P X →
      WithGeneratedByTopology P Y := fun x =>
    WithGeneratedByTopology.equiv.symm
      (f (WithGeneratedByTopology.equiv x))
  let tGeneratedX : TopologicalSpace (WithGeneratedByTopology P X) :=
    inferInstance
  let tGeneratedY : TopologicalSpace (WithGeneratedByTopology P Y) :=
    inferInstance
  change IsClosedEmbedding e
  change Continuous e at heContinuous
  have heInjective : Function.Injective e := by
    intro x y hxy
    exact hf.injective hxy
  have heClosed : IsClosed (Set.range e) := by
    change @IsClosed Y (TopologicalSpace.generatedBy P)
      (Set.range (ConcreteCategory.hom f))
    exact hf.isClosed_range.mono TopologicalSpace.generatedBy_le
  let tInd : TopologicalSpace (WithGeneratedByTopology P X) :=
    TopologicalSpace.induced e tGeneratedY
  let _ : ∀ (K : CompHaus.{u})
      (F : TopologicalSpace.Closeds (P K)), IsGeneratedBy P F :=
    fun K F => by
      let _ : CompactSpace F :=
        isCompact_iff_compactSpace.1 F.2.isCompact
      exact (isGeneratedBy_compactHausProbes_iff (Y := F)).2 inferInstance
  have heInduced : @IsClosedEmbedding
      (WithGeneratedByTopology P X) (WithGeneratedByTopology P Y)
      tInd tGeneratedY e :=
    { toIsEmbedding := heInjective.isEmbedding_induced
      isClosed_range := heClosed }
  have hIndGenerated : @IsGeneratedBy _ P _
      (WithGeneratedByTopology P X) tInd :=
    heInduced.isGeneratedBy
  have hRawInducing : @IsInducing
      (WithGeneratedByTopology P X) (WithGeneratedByTopology P Y)
      X.str Y.str e := by
    change IsInducing (ConcreteCategory.hom f)
    exact hf.isInducing
  have hGenerated_le_raw :
      @TopologicalSpace.generatedBy _ P inferInstance Y Y.str ≤ Y.str :=
    TopologicalSpace.generatedBy_le
  have hRawTopologyEq : X.str = TopologicalSpace.induced e Y.str :=
    @IsInducing.eq_induced _ _ X.str Y.str e hRawInducing
  have hInd_le_raw : tInd ≤ X.str := by
    have hle : tInd ≤ TopologicalSpace.induced e Y.str := by
      change TopologicalSpace.induced e
          (@TopologicalSpace.generatedBy _ P inferInstance Y Y.str) ≤
        TopologicalSpace.induced e Y.str
      exact induced_mono hGenerated_le_raw
    rw [hRawTopologyEq]
    exact hle
  have hInd_le_generated : tInd ≤
      tGeneratedX := by
    calc
      tInd = @TopologicalSpace.generatedBy _ P inferInstance
          (WithGeneratedByTopology P X) tInd :=
        (@IsGeneratedBy.generatedBy_eq _ P inferInstance
          (WithGeneratedByTopology P X) tInd hIndGenerated).symm
      _ ≤ @TopologicalSpace.generatedBy _ P inferInstance
          (WithGeneratedByTopology P X) X.str :=
        TopologicalSpace.generatedBy_mono hInd_le_raw
      _ = tGeneratedX := by
        change @TopologicalSpace.generatedBy _ P inferInstance X X.str =
          @TopologicalSpace.generatedBy _ P inferInstance X X.str
        rfl
  have hContinuous_le : tGeneratedX ≤
      TopologicalSpace.induced e tGeneratedY :=
    @Continuous.le_induced _ _ tGeneratedX tGeneratedY e heContinuous
  have hInduced_le : TopologicalSpace.induced e tGeneratedY ≤
      tGeneratedX := by
    change tInd ≤ tGeneratedX
    exact hInd_le_generated
  change @IsClosedEmbedding (WithGeneratedByTopology P X)
    (WithGeneratedByTopology P Y) tGeneratedX tGeneratedY e
  have hInducing : @IsInducing (WithGeneratedByTopology P X)
      (WithGeneratedByTopology P Y) tGeneratedX tGeneratedY e :=
    @IsInducing.mk _ _ tGeneratedX tGeneratedY e
      (le_antisymm hContinuous_le hInduced_le)
  have hEmbedding : @IsEmbedding (WithGeneratedByTopology P X)
      (WithGeneratedByTopology P Y) tGeneratedX tGeneratedY e :=
    @IsEmbedding.mk _ _ tGeneratedX tGeneratedY e hInducing heInjective
  exact @IsClosedEmbedding.mk _ _ tGeneratedX tGeneratedY e
    hEmbedding heClosed

private noncomputable def closedEmbeddingBinaryKificationIso
    (X Y : CompactlyGenerated.{u, v}) :
    TopCat.toCompactlyGenerated.obj
      (TopCat.of (↑(compactlyGeneratedToTop.obj X) ×
        ↑(compactlyGeneratedToTop.obj Y))) ≅ X ⊗ Y := by
  let I := compactlyGeneratedToTop.{u, v}
  let R := TopCat.toCompactlyGenerated.{u, v}
  let _ : R.IsRightAdjoint := adj.isRightAdjoint
  let unitInvX : R.obj (I.obj X) ≅ X :=
    (asIso (adj.unit.app X)).symm
  let unitInvY : R.obj (I.obj Y) ≅ Y :=
    (asIso (adj.unit.app Y)).symm
  let productIsoTensor : X ⨯ Y ≅ X ⊗ Y :=
    { hom := CartesianMonoidalCategory.lift Limits.prod.fst Limits.prod.snd
      inv := Limits.prod.lift (CartesianMonoidalCategory.fst X Y)
        (CartesianMonoidalCategory.snd X Y)
      hom_inv_id := by
        apply Limits.prod.hom_ext
        · simp only [Category.assoc, Limits.prod.lift_fst,
            CartesianMonoidalCategory.lift_fst, Category.id_comp]
        · simp only [Category.assoc, Limits.prod.lift_snd,
            CartesianMonoidalCategory.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
            Limits.prod.lift_fst, Category.id_comp]
        · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd,
            Limits.prod.lift_snd, Category.id_comp] }
  exact R.mapIso (TopCat.prodIsoProd (I.obj X) (I.obj Y)).symm ≪≫
    PreservesLimitPair.iso R (I.obj X) (I.obj Y) ≪≫
      Limits.prod.mapIso unitInvX unitInvY ≪≫
        productIsoTensor

@[simp]
private theorem closedEmbeddingBinaryKificationIso_hom_fst
    (X Y : CompactlyGenerated.{u, v}) :
    (closedEmbeddingBinaryKificationIso X Y).hom ≫
        CartesianMonoidalCategory.fst X Y =
      TopCat.toCompactlyGenerated.map
          (TopCat.prodFst : TopCat.of
            (↑(compactlyGeneratedToTop.obj X) ×
              ↑(compactlyGeneratedToTop.obj Y)) ⟶
            compactlyGeneratedToTop.obj X) ≫
        (asIso (adj.unit.app X)).inv := by
  let I := compactlyGeneratedToTop.{u, v}
  let R := TopCat.toCompactlyGenerated.{u, v}
  let _ : R.IsRightAdjoint := adj.isRightAdjoint
  have hTop : (TopCat.prodIsoProd (I.obj X) (I.obj Y)).symm.hom ≫
      (Limits.prod.fst : I.obj X ⨯ I.obj Y ⟶ I.obj X) =
      (TopCat.prodFst : TopCat.of (↑(I.obj X) × ↑(I.obj Y)) ⟶
        I.obj X) :=
    TopCat.prodIsoProd_inv_fst (I.obj X) (I.obj Y)
  simp only [closedEmbeddingBinaryKificationIso, Iso.trans_hom,
    Functor.mapIso_hom, Limits.prod.mapIso_hom, Category.assoc,
    CartesianMonoidalCategory.lift_fst, Limits.prod.map_fst,
    PreservesLimitPair.iso_hom,
    Limits.prodComparison_fst_assoc]
  rw [← Category.assoc, ← R.map_comp, hTop]
  rfl

@[simp]
private theorem closedEmbeddingBinaryKificationIso_hom_snd
    (X Y : CompactlyGenerated.{u, v}) :
    (closedEmbeddingBinaryKificationIso X Y).hom ≫
        CartesianMonoidalCategory.snd X Y =
      TopCat.toCompactlyGenerated.map
          (TopCat.prodSnd : TopCat.of
            (↑(compactlyGeneratedToTop.obj X) ×
              ↑(compactlyGeneratedToTop.obj Y)) ⟶
            compactlyGeneratedToTop.obj Y) ≫
        (asIso (adj.unit.app Y)).inv := by
  let I := compactlyGeneratedToTop.{u, v}
  let R := TopCat.toCompactlyGenerated.{u, v}
  let _ : R.IsRightAdjoint := adj.isRightAdjoint
  have hTop : (TopCat.prodIsoProd (I.obj X) (I.obj Y)).symm.hom ≫
      (Limits.prod.snd : I.obj X ⨯ I.obj Y ⟶ I.obj Y) =
      (TopCat.prodSnd : TopCat.of (↑(I.obj X) × ↑(I.obj Y)) ⟶
        I.obj Y) :=
    TopCat.prodIsoProd_inv_snd (I.obj X) (I.obj Y)
  simp only [closedEmbeddingBinaryKificationIso, Iso.trans_hom,
    Functor.mapIso_hom, Limits.prod.mapIso_hom, Category.assoc,
    CartesianMonoidalCategory.lift_snd, Limits.prod.map_snd,
    PreservesLimitPair.iso_hom,
    Limits.prodComparison_snd_assoc]
  rw [← Category.assoc, ← R.map_comp, hTop]
  rfl

/-- Native binary products preserve closed embeddings. -/
theorem isClosedEmbedding_prodMap
    {A B C D : CompactlyGenerated.{u, v}}
    (f : A ⟶ B) (g : C ⟶ D)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f))
    (hg : IsClosedEmbedding (ConcreteCategory.hom g)) :
    IsClosedEmbedding (ConcreteCategory.hom (f ⊗ₘ g)) := by
  let I := compactlyGeneratedToTop.{u, v}
  let R := TopCat.toCompactlyGenerated.{u, v}
  let m : TopCat.of (↑(I.obj A) × ↑(I.obj C)) ⟶
      TopCat.of (↑(I.obj B) × ↑(I.obj D)) :=
    TopCat.ofHom
      ((ConcreteCategory.hom f).prodMap (ConcreteCategory.hom g))
  have hm : IsClosedEmbedding (ConcreteCategory.hom m) := by
    change IsClosedEmbedding
      (Prod.map (ConcreteCategory.hom f) (ConcreteCategory.hom g))
    exact hf.prodMap hg
  have hRm : IsClosedEmbedding (ConcreteCategory.hom (R.map m)) :=
    toCompactlyGenerated_map_isClosedEmbedding m hm
  let eAC := closedEmbeddingBinaryKificationIso A C
  let eBD := closedEmbeddingBinaryKificationIso B D
  have hUnitNaturalityF : f ≫ adj.unit.app B =
      adj.unit.app A ≫ R.map (I.map f) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      adj.unit.naturality f
  have hUnitF : R.map (I.map f) ≫
      (asIso (adj.unit.app B)).inv =
      (asIso (adj.unit.app A)).inv ≫ f := by
    apply (IsIso.comp_inv_eq (adj.unit.app B)).2
    rw [Category.assoc]
    apply (IsIso.eq_inv_comp (adj.unit.app A)).2
    exact hUnitNaturalityF.symm
  have hUnitNaturalityG : g ≫ adj.unit.app D =
      adj.unit.app C ≫ R.map (I.map g) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      adj.unit.naturality g
  have hUnitG : R.map (I.map g) ≫
      (asIso (adj.unit.app D)).inv =
      (asIso (adj.unit.app C)).inv ≫ g := by
    apply (IsIso.comp_inv_eq (adj.unit.app D)).2
    rw [Category.assoc]
    apply (IsIso.eq_inv_comp (adj.unit.app C)).2
    exact hUnitNaturalityG.symm
  let fstAC : TopCat.of (↑(I.obj A) × ↑(I.obj C)) ⟶ I.obj A :=
    TopCat.prodFst
  let fstBD : TopCat.of (↑(I.obj B) × ↑(I.obj D)) ⟶ I.obj B :=
    TopCat.prodFst
  let sndAC : TopCat.of (↑(I.obj A) × ↑(I.obj C)) ⟶ I.obj C :=
    TopCat.prodSnd
  let sndBD : TopCat.of (↑(I.obj B) × ↑(I.obj D)) ⟶ I.obj D :=
    TopCat.prodSnd
  have hmFst : m ≫ fstBD = fstAC ≫ I.map f := by
    apply TopCat.hom_ext
    ext p
    rfl
  have hmSnd : m ≫ sndBD = sndAC ≫ I.map g := by
    apply TopCat.hom_ext
    ext p
    rfl
  have hNatural : eAC.hom ≫ (f ⊗ₘ g) =
      R.map m ≫ eBD.hom := by
    apply CartesianMonoidalCategory.hom_ext
    · calc
        (eAC.hom ≫ (f ⊗ₘ g)) ≫
            CartesianMonoidalCategory.fst B D =
          eAC.hom ≫ ((f ⊗ₘ g) ≫
            CartesianMonoidalCategory.fst B D) := Category.assoc _ _ _
        _ = eAC.hom ≫
            (CartesianMonoidalCategory.fst A C ≫ f) := by
          rw [CartesianMonoidalCategory.tensorHom_fst]
        _ = (R.map fstAC ≫ (asIso (adj.unit.app A)).inv) ≫ f := by
          dsimp only [eAC]
          rw [← Category.assoc,
            closedEmbeddingBinaryKificationIso_hom_fst]
        _ = R.map fstAC ≫
            ((asIso (adj.unit.app A)).inv ≫ f) := Category.assoc _ _ _
        _ = R.map fstAC ≫
            (R.map (I.map f) ≫ (asIso (adj.unit.app B)).inv) := by
          rw [hUnitF]
        _ = R.map (fstAC ≫ I.map f) ≫
            (asIso (adj.unit.app B)).inv := by
          rw [R.map_comp, Category.assoc]
        _ = R.map (m ≫ fstBD) ≫
            (asIso (adj.unit.app B)).inv := by rw [hmFst]
        _ = (R.map m ≫ R.map fstBD) ≫
            (asIso (adj.unit.app B)).inv := by
          rw [R.map_comp]
        _ = R.map m ≫
            (R.map fstBD ≫ (asIso (adj.unit.app B)).inv) :=
          Category.assoc _ _ _
        _ = R.map m ≫
            (eBD.hom ≫ CartesianMonoidalCategory.fst B D) := by
          dsimp only [eBD]
          rw [closedEmbeddingBinaryKificationIso_hom_fst]
        _ = (R.map m ≫ eBD.hom) ≫
            CartesianMonoidalCategory.fst B D := (Category.assoc _ _ _).symm
    · calc
        (eAC.hom ≫ (f ⊗ₘ g)) ≫
            CartesianMonoidalCategory.snd B D =
          eAC.hom ≫ ((f ⊗ₘ g) ≫
            CartesianMonoidalCategory.snd B D) := Category.assoc _ _ _
        _ = eAC.hom ≫
            (CartesianMonoidalCategory.snd A C ≫ g) := by
          rw [CartesianMonoidalCategory.tensorHom_snd]
        _ = (R.map sndAC ≫ (asIso (adj.unit.app C)).inv) ≫ g := by
          dsimp only [eAC]
          rw [← Category.assoc,
            closedEmbeddingBinaryKificationIso_hom_snd]
        _ = R.map sndAC ≫
            ((asIso (adj.unit.app C)).inv ≫ g) := Category.assoc _ _ _
        _ = R.map sndAC ≫
            (R.map (I.map g) ≫ (asIso (adj.unit.app D)).inv) := by
          rw [hUnitG]
        _ = R.map (sndAC ≫ I.map g) ≫
            (asIso (adj.unit.app D)).inv := by
          rw [R.map_comp, Category.assoc]
        _ = R.map (m ≫ sndBD) ≫
            (asIso (adj.unit.app D)).inv := by rw [hmSnd]
        _ = (R.map m ≫ R.map sndBD) ≫
            (asIso (adj.unit.app D)).inv := by
          rw [R.map_comp]
        _ = R.map m ≫
            (R.map sndBD ≫ (asIso (adj.unit.app D)).inv) :=
          Category.assoc _ _ _
        _ = R.map m ≫
            (eBD.hom ≫ CartesianMonoidalCategory.snd B D) := by
          dsimp only [eBD]
          rw [closedEmbeddingBinaryKificationIso_hom_snd]
        _ = (R.map m ≫ eBD.hom) ≫
            CartesianMonoidalCategory.snd B D := (Category.assoc _ _ _).symm
  have hFactor : f ⊗ₘ g = eAC.inv ≫ R.map m ≫ eBD.hom := by
    calc
      f ⊗ₘ g = eAC.inv ≫ eAC.hom ≫ (f ⊗ₘ g) :=
        (Iso.inv_hom_id_assoc eAC (f ⊗ₘ g)).symm
      _ = eAC.inv ≫ (R.map m ≫ eBD.hom) := by rw [hNatural]
      _ = eAC.inv ≫ R.map m ≫ eBD.hom := Category.assoc _ _ _
  have hEAC : IsClosedEmbedding (ConcreteCategory.hom eAC.inv) :=
    (CompactlyGenerated.homeoOfIso eAC.symm).isClosedEmbedding
  have hEBD : IsClosedEmbedding (ConcreteCategory.hom eBD.hom) :=
    (CompactlyGenerated.homeoOfIso eBD).isClosedEmbedding
  rw [hFactor]
  exact hEBD.comp (hRm.comp hEAC)

end CompactlyGenerated
