/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellCoproducts
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellPushouts
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellTransfinite
public import Mathlib.CategoryTheory.SmallObject.Basic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedGeneratorCardinal

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedSmallObject

/-!
# Small-object arguments for closed cells in CGWH

This file transfers the fixed-cardinal small-object arguments for realized
boundary and horn inclusions from compactly generated spaces to CGWH.  The
transfer uses only the closed-cell coproduct, pushout, and injective
transfinite-colimit interfaces, so it installs no global colimit-preservation
or model-category instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open CategoryTheory.TransfiniteCompositionOfShape
open HomotopicalAlgebra Topology

namespace CGWH

private noncomputable def cgwhToCompactlyGeneratedCoyonedaIso
    (A : CGWH.{u, v}) :
    cgwhToCompactlyGenerated.{u, v} ⋙
        coyoneda.obj (Opposite.op (cgwhToCompactlyGenerated.obj A)) ≅
      coyoneda.obj (Opposite.op A) := by
  let h := Functor.FullyFaithful.ofFullyFaithful
    cgwhToCompactlyGenerated.{u, v}
  exact NatIso.ofComponents
    (fun _ => Equiv.toIso h.homEquiv.symm)
    (fun f => by
      ext g
      apply cgwhToCompactlyGenerated.map_injective
      simp [h])

private noncomputable def mapAttachCells
    (P : MorphismProperty CGWH.{u, v})
    (Q : MorphismProperty CompactlyGenerated.{u, v})
    (hPG : P ≤
      (realizedBoundaryInclusions.{u, v} ⊔
        realizedHornInclusions.{u, v}))
    (hPQ : P ≤ Q.inverseImage cgwhToCompactlyGenerated.{u, v})
    {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (a : AttachCells.{v} P.homFamily f) :
    AttachCells.{v} Q.homFamily
      (cgwhToCompactlyGenerated.map f) := by
  let j := cgwhToCompactlyGenerated.{u, v}
  let A : a.ι → CGWH.{u, v} := fun i => (a.π i).1.left
  let B : a.ι → CGWH.{u, v} := fun i => (a.π i).1.right
  let cofan₁ : Cofan (fun i => j.obj (A i)) :=
    Cofan.mk (j.obj a.cofan₁.pt) (fun i => j.map (a.cofan₁.inj i))
  let cofan₂ : Cofan (fun i => j.obj (B i)) :=
    Cofan.mk (j.obj a.cofan₂.pt) (fun i => j.map (a.cofan₂.inj i))
  let eNative₁ : (∐ A) ≅ a.cofan₁.pt :=
    (colimit.isColimit (Discrete.functor A)).coconePointUniqueUpToIso
      a.isColimit₁
  let eNative₂ : (∐ B) ≅ a.cofan₂.pt :=
    (colimit.isColimit (Discrete.functor B)).coconePointUniqueUpToIso
      a.isColimit₂
  let e₁ : (∐ fun i => j.obj (A i)) ≅ j.obj a.cofan₁.pt :=
    coproductComparisonToCompactlyGeneratedIso A ≪≫ j.mapIso eNative₁
  let e₂ : (∐ fun i => j.obj (B i)) ≅ j.obj a.cofan₂.pt :=
    coproductComparisonToCompactlyGeneratedIso B ≪≫ j.mapIso eNative₂
  have he₁ (i : a.ι) :
      Sigma.ι (fun i => j.obj (A i)) i ≫ e₁.hom =
        j.map (a.cofan₁.inj i) := by
    dsimp [e₁]
    rw [coproductComparisonToCompactlyGeneratedIso_hom_ι_assoc]
    rw [← j.map_comp]
    exact j.congr_map
      (CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit (Discrete.functor A)) a.isColimit₁
        (Discrete.mk i))
  have he₂ (i : a.ι) :
      Sigma.ι (fun i => j.obj (B i)) i ≫ e₂.hom =
        j.map (a.cofan₂.inj i) := by
    dsimp [e₂]
    rw [coproductComparisonToCompactlyGeneratedIso_hom_ι_assoc]
    rw [← j.map_comp]
    exact j.congr_map
      (CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit (Discrete.functor B)) a.isColimit₂
        (Discrete.mk i))
  have hcofan₁ : IsColimit cofan₁ :=
    IsColimit.ofIsoColimit
      (colimit.isColimit (Discrete.functor fun i => j.obj (A i)))
      (Cofan.ext e₁ he₁)
  have hcofan₂ : IsColimit cofan₂ :=
    IsColimit.ofIsoColimit
      (colimit.isColimit (Discrete.functor fun i => j.obj (B i)))
      (Cofan.ext e₂ he₂)
  have hmP : coproducts.{v} P a.m := by
    apply colimitsOfShape_le_coproducts P a.ι
    refine colimitsOfShape.mk' (Discrete.functor A) (Discrete.functor B)
      a.cofan₁ a.cofan₂ a.isColimit₁ a.isColimit₂
      (Discrete.natTrans (fun i => (a.π i.as).1.hom))
      (fun i => (a.π i.as).2) a.m ?_
    intro i
    change a.cofan₁.inj i.as ≫ a.m =
      (a.π i.as).1.hom ≫ a.cofan₂.inj i.as
    exact a.hm i.as
  have hmClosed : IsClosedEmbedding
      (cgwhToTop.map a.m).hom :=
    coproducts_realizedGenerators_le_closedEmbeddings _
      (coproducts_monotone hPG _ hmP)
  let _ : PreservesColimit (span a.m a.g₁) j :=
    preservesPushout_of_isClosedEmbedding a.m a.g₁ hmClosed
  let _ : PreservesColimit (span a.g₁ a.m) j :=
    preservesPushout_symmetry j a.m a.g₁
  let mapped : AttachCells.{v}
      (fun p : P.toSet => j.map p.1.hom) (j.map f) :=
    { ι := a.ι
      π := a.π
      cofan₁ := cofan₁
      cofan₂ := cofan₂
      isColimit₁ := hcofan₁
      isColimit₂ := hcofan₂
      m := j.map a.m
      hm i := by
        change j.map (a.cofan₁.inj i) ≫ j.map a.m =
          j.map (P.homFamily (a.π i)) ≫ j.map (a.cofan₂.inj i)
        simpa only [Functor.map_comp] using congrArg j.map (a.hm i)
      g₁ := j.map a.g₁
      g₂ := j.map a.g₂
      isPushout := a.isPushout.map j }
  exact mapped.reindexCellTypes Q.homFamily
    (fun p => ⟨Arrow.mk (j.map p.1.hom), hPQ _ p.2⟩)
    (fun _ => Iso.refl _)

private theorem mapPushoutsCoproducts
    (P : MorphismProperty CGWH.{u, v})
    (Q : MorphismProperty CompactlyGenerated.{u, v})
    (hPG : P ≤
      (realizedBoundaryInclusions.{u, v} ⊔
        realizedHornInclusions.{u, v}))
    (hPQ : P ≤ Q.inverseImage cgwhToCompactlyGenerated.{u, v})
    {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (hf : (coproducts.{v} P).pushouts f) :
    (coproducts.{v} Q).pushouts
        (cgwhToCompactlyGenerated.map f) ∧
      Function.Injective (cgwhToCompactlyGenerated.map f).hom := by
  let j := cgwhToCompactlyGenerated.{u, v}
  let k := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  have hf' : (coproducts.{v} (ofHoms P.homFamily)).pushouts f := by
    simpa only [P.ofHoms_homFamily] using hf
  let a := (nonempty_attachCells_iff P.homFamily f).2 hf' |>.some
  let mapped := mapAttachCells P Q hPG hPQ a
  have hMapped : (coproducts.{v} Q).pushouts (j.map f) := by
    simpa only [Q.ofHoms_homFamily] using mapped.pushouts_coproducts
  have hmP : coproducts.{v} P a.m := by
    let A : a.ι → CGWH.{u, v} := fun i => (a.π i).1.left
    let B : a.ι → CGWH.{u, v} := fun i => (a.π i).1.right
    apply colimitsOfShape_le_coproducts P a.ι
    refine colimitsOfShape.mk' (Discrete.functor A) (Discrete.functor B)
      a.cofan₁ a.cofan₂ a.isColimit₁ a.isColimit₂
      (Discrete.natTrans (fun i => (a.π i.as).1.hom))
      (fun i => (a.π i.as).2) a.m ?_
    intro i
    change a.cofan₁.inj i.as ≫ a.m =
      (a.π i.as).1.hom ≫ a.cofan₂.inj i.as
    exact a.hm i.as
  have hmClosed : IsClosedEmbedding (cgwhToTop.map a.m).hom :=
    coproducts_realizedGenerators_le_closedEmbeddings _
      (coproducts_monotone hPG _ hmP)
  have hsq : IsPushout
      (k.map (j.map a.g₁)) (k.map (j.map a.m))
      (k.map (j.map f)) (k.map (j.map a.g₂)) :=
    mapped.isPushout.map k
  have hfClosed : IsClosedEmbedding (k.map (j.map f)).hom :=
    TopCat.isClosedEmbedding_of_isPushout hsq.flip hmClosed
  exact ⟨hMapped, hfClosed.injective⟩

private noncomputable def mapRelativeCellComplex
    (P : MorphismProperty CGWH.{u, v})
    (Q : MorphismProperty CompactlyGenerated.{u, v})
    (hPG : P ≤
      (realizedBoundaryInclusions.{u, v} ⊔
        realizedHornInclusions.{u, v}))
    (hPQ : P ≤ Q.inverseImage cgwhToCompactlyGenerated.{u, v})
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J]
    {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (c : RelativeCellComplex.{v} (fun (_ : J) => P.homFamily) f) :
    RelativeCellComplex.{v} (fun (_ : J) => Q.homFamily)
      (cgwhToCompactlyGenerated.map f) := by
  let j := cgwhToCompactlyGenerated.{u, v}
  have hSucc : ∀ (a : J) (ha : ¬ IsMax a), Function.Injective
      (j.map (c.F.map (homOfLE (Order.le_succ a)))).hom := by
    intro a ha
    apply (mapPushoutsCoproducts P Q hPG hPQ
      (by
        simpa only [P.ofHoms_homFamily] using
          (c.attachCells a ha).pushouts_coproducts)).2
  exact
    { F := c.F ⋙ j
      isoBot := j.mapIso c.isoBot
      isWellOrderContinuous := by
        constructor
        intro m hm
        let _ : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
        let _ : OrderBot (Set.Iio m) :=
          { bot := ⟨⊥, hm.bot_lt⟩
            bot_le := fun _ => bot_le }
        let _ : IsFiltered (Set.Iio m) := by infer_instance
        let pInit : Set.Iio m ≤i J :=
          { toRelEmbedding := (Set.principalSegIio m).toRelEmbedding
            mem_range_of_rel' := by
              intro a b hb
              exact ⟨⟨b, hb.trans a.property⟩, rfl⟩ }
        let R := (Set.principalSegIio m).monotone.functor ⋙ c.F
        let _ : R.IsWellOrderContinuous := by
          change (pInit.monotone.functor ⋙ c.F).IsWellOrderContinuous
          infer_instance
        have hR : ∀ ⦃a b : Set.Iio m⦄ (g : a ⟶ b), Function.Injective
            (j.map (R.map g)).hom := by
          intro a b g
          change Function.Injective
            (j.map (c.F.map
              ((Set.principalSegIio m).monotone.functor.map g))).hom
          have hg : (Set.principalSegIio m).monotone.functor.map g =
              homOfLE (leOfHom g) := Subsingleton.elim _ _
          rw [hg]
          exact injective_map_of_injective_succ c.F hSucc _
        refine ⟨isColimitMapCoconeOfInjectiveSucc R
          (fun a ha => hR (homOfLE (Order.le_succ a)))
          ((Set.principalSegIio m).cocone c.F)
          (c.F.isColimitOfIsWellOrderContinuous m hm)⟩
      incl := Functor.whiskerRight c.incl j ≫
        (Functor.constComp _ _ _).hom
      isColimit := isColimitMapCoconeOfInjectiveSucc c.F hSucc
        (Cocone.mk _ c.incl) c.isColimit
      fac := by
        dsimp [j]
        simp [← Functor.map_comp]
      attachCells := fun a ha => mapAttachCells P Q hPG hPQ
        (c.attachCells a ha) }

private theorem preservesColimitRelativeCellComplex
    (P : MorphismProperty CGWH.{u, v})
    (Q : MorphismProperty CompactlyGenerated.{u, v})
    (hPG : P ≤
      (realizedBoundaryInclusions.{u, v} ⊔
        realizedHornInclusions.{u, v}))
    (hPQ : P ≤ Q.inverseImage cgwhToCompactlyGenerated.{u, v})
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J]
    {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (c : RelativeCellComplex.{v} (fun (_ : J) => P.homFamily) f) :
    PreservesColimit c.F cgwhToCompactlyGenerated.{u, v} := by
  let j := cgwhToCompactlyGenerated.{u, v}
  have hSucc : ∀ (a : J) (ha : ¬ IsMax a), Function.Injective
      (j.map (c.F.map (homOfLE (Order.le_succ a)))).hom := by
    intro a ha
    apply (mapPushoutsCoproducts P Q hPG hPQ
      (by
        simpa only [P.ofHoms_homFamily] using
          (c.attachCells a ha).pushouts_coproducts)).2
  apply preservesColimit_of_preserves_colimit_cocone c.isColimit
  exact isColimitMapCoconeOfInjectiveSucc c.F hSucc
    (Cocone.mk _ c.incl) c.isColimit

private theorem isCardinalForSmallObjectArgument_of_closedCells
    (P : MorphismProperty CGWH.{u, v})
    (Q : MorphismProperty CompactlyGenerated.{u, v})
    (κ : Cardinal.{v}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType]
    [P.IsSmall.{v}] [LocallySmall.{v} CGWH.{u, v}]
    [HasPushouts CGWH.{u, v}] [HasCoproducts.{v} CGWH.{u, v}]
    [HasIterationOfShape κ.ord.ToType CGWH.{u, v}]
    [Q.IsCardinalForSmallObjectArgument κ]
    (hPG : P ≤
      (realizedBoundaryInclusions.{u, v} ⊔
        realizedHornInclusions.{u, v}))
    (hPQ : P ≤ Q.inverseImage cgwhToCompactlyGenerated.{u, v}) :
    P.IsCardinalForSmallObjectArgument κ where
  preservesColimit {A B X Y} i hi f hf := by
    let j := cgwhToCompactlyGenerated.{u, v}
    let hfD := mapRelativeCellComplex P Q hPG hPQ hf
    have hAmbient : PreservesColimit hfD.F
        (coyoneda.obj (Opposite.op (j.obj A))) :=
      SmallObject.preservesColimit Q κ (j.map i) (hPQ i hi)
        (j.map f) hfD
    have hDiagram : hfD.F = hf.F ⋙ j := rfl
    let _ : PreservesColimit (hf.F ⋙ j)
        (coyoneda.obj (Opposite.op (j.obj A))) :=
      hDiagram ▸ hAmbient
    let _ : PreservesColimit hf.F j :=
      preservesColimitRelativeCellComplex P Q hPG hPQ hf
    let _ : PreservesColimit hf.F
        (j ⋙ coyoneda.obj (Opposite.op (j.obj A))) := inferInstance
    exact preservesColimit_of_natIso hf.F
      (cgwhToCompactlyGeneratedCoyonedaIso A)

private theorem rlp_llp_eq_inverseImage_of_closedCells
    (P : MorphismProperty CGWH.{u, v})
    (Q : MorphismProperty CompactlyGenerated.{u, v})
    [P.HasSmallObjectArgument.{v}]
    (hPG : P ≤
      (realizedBoundaryInclusions.{u, v} ⊔
        realizedHornInclusions.{u, v}))
    (hPQ : P ≤ Q.inverseImage cgwhToCompactlyGenerated.{u, v})
    (hrlp : P.rlp =
      Q.rlp.inverseImage cgwhToCompactlyGenerated.{u, v}) :
    P.rlp.llp =
      Q.rlp.llp.inverseImage cgwhToCompactlyGenerated.{u, v} := by
  let j := cgwhToCompactlyGenerated.{u, v}
  apply le_antisymm
  · intro X Y f hf
    rw [P.llp_rlp_of_hasSmallObjectArgument] at hf
    obtain ⟨Z, W, g, hfg, hg⟩ := hf
    apply Q.retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp
    refine ⟨j.obj Z, j.obj W, j.map g, hfg.map j, ?_⟩
    rw [transfiniteCompositions_iff] at hg ⊢
    obtain ⟨J, _, _, _, _, hc⟩ := hg
    let c := hc.some
    let rc : RelativeCellComplex.{v}
        (fun (_ : J) => P.homFamily) g :=
      { __ := c.toTransfiniteCompositionOfShape
        attachCells := fun a ha =>
          ((nonempty_attachCells_iff P.homFamily _).2
            (by
              simpa only [P.ofHoms_homFamily] using
                c.map_mem a ha)).some }
    let rcD := mapRelativeCellComplex P Q hPG hPQ rc
    refine ⟨J, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨?_⟩⟩
    simpa only [Q.ofHoms_homFamily] using
      rcD.transfiniteCompositionOfShape Q.homFamily
  · intro X Y f hf A B p hp
    rw [hrlp] at hp
    exact (Functor.hasLiftingProperty_map_iff_of_full_faithful
      j f p).mp (hf (j.map p) hp)

/-- The realized boundary inclusions in CGWH satisfy the fixed-cardinal
smallness conditions at `realizedGeneratorCardinal`. -/
noncomputable instance
    instIsCardinalForSmallObjectArgumentRealizedBoundaryInclusions :
    letI : Fact realizedGeneratorCardinal.{v}.IsRegular :=
      ⟨isRegular_realizedGeneratorCardinal.{v}⟩
    letI : Nonempty realizedGeneratorCardinal.{v}.ord.ToType :=
      Ordinal.nonempty_toType_iff.mpr
        (by simpa using isRegular_realizedGeneratorCardinal.{v}.ne_zero)
    letI : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
      WellFoundedLT.toOrderBot realizedGeneratorCardinal.{v}.ord.ToType
    MorphismProperty.IsCardinalForSmallObjectArgument.{v}
      realizedBoundaryInclusions.{u, v}
      realizedGeneratorCardinal.{v} := by
  let _ : Small.{v} ℕ := small_zero ℕ
  let _ : MorphismProperty.IsSmall.{v}
      realizedBoundaryInclusions.{u, v} := by
    unfold realizedBoundaryInclusions
    infer_instance
  have hPQ : realizedBoundaryInclusions.{u, v} ≤
      CompactlyGenerated.realizedBoundaryInclusions.{u, v}.inverseImage
        cgwhToCompactlyGenerated.{u, v} := by
    intro X Y f hf
    obtain ⟨n⟩ := hf
    change CompactlyGenerated.realizedBoundaryInclusions.{u, v}
      (cgwhToCompactlyGenerated.{u, v}.map
        (realizedBoundaryInclusion n))
    rw [cgwhToCompactlyGenerated_map_realizedBoundaryInclusion]
    exact CompactlyGenerated.boundary_mem_realizedBoundaryInclusions n
  exact isCardinalForSmallObjectArgument_of_closedCells
    realizedBoundaryInclusions.{u, v}
    CompactlyGenerated.realizedBoundaryInclusions.{u, v}
    realizedGeneratorCardinal.{v} le_sup_left hPQ

/-- The realized boundary inclusions in CGWH permit the small-object
argument at the literal `realizedGeneratorCardinal`. -/
noncomputable instance
    instHasSmallObjectArgumentRealizedBoundaryInclusions :
    MorphismProperty.HasSmallObjectArgument.{v}
      realizedBoundaryInclusions.{u, v} := by
  let _ : Fact realizedGeneratorCardinal.{v}.IsRegular :=
    ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  let _ : Nonempty realizedGeneratorCardinal.{v}.ord.ToType :=
    Ordinal.nonempty_toType_iff.mpr
      (by simpa using isRegular_realizedGeneratorCardinal.{v}.ne_zero)
  let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
    WellFoundedLT.toOrderBot realizedGeneratorCardinal.{v}.ord.ToType
  exact ⟨realizedGeneratorCardinal.{v}, inferInstance, inferInstance,
    inferInstance⟩

/-- The realized horn inclusions in CGWH satisfy the fixed-cardinal
smallness conditions at `realizedGeneratorCardinal`. -/
noncomputable instance
    instIsCardinalForSmallObjectArgumentRealizedHornInclusions :
    letI : Fact realizedGeneratorCardinal.{v}.IsRegular :=
      ⟨isRegular_realizedGeneratorCardinal.{v}⟩
    letI : Nonempty realizedGeneratorCardinal.{v}.ord.ToType :=
      Ordinal.nonempty_toType_iff.mpr
        (by simpa using isRegular_realizedGeneratorCardinal.{v}.ne_zero)
    letI : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
      WellFoundedLT.toOrderBot realizedGeneratorCardinal.{v}.ord.ToType
    MorphismProperty.IsCardinalForSmallObjectArgument.{v}
      realizedHornInclusions.{u, v}
      realizedGeneratorCardinal.{v} := by
  let _ : Small.{v} ℕ := small_zero ℕ
  let _ : ∀ n : ℕ, Small.{v} (Fin (n + 2)) := fun _ => small_zero _
  let _ : MorphismProperty.IsSmall.{v}
      realizedHornInclusions.{u, v} := by
    unfold realizedHornInclusions
    infer_instance
  have hPQ : realizedHornInclusions.{u, v} ≤
      CompactlyGenerated.realizedHornInclusions.{u, v}.inverseImage
        cgwhToCompactlyGenerated.{u, v} := by
    intro X Y f hf
    unfold realizedHornInclusions at hf
    rw [MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨i⟩⟩ := hf
    change CompactlyGenerated.realizedHornInclusions.{u, v}
      (cgwhToCompactlyGenerated.{u, v}.map
        (realizedHornInclusion n i))
    rw [cgwhToCompactlyGenerated_map_realizedHornInclusion]
    exact CompactlyGenerated.horn_mem_realizedHornInclusions n i
  exact isCardinalForSmallObjectArgument_of_closedCells
    realizedHornInclusions.{u, v}
    CompactlyGenerated.realizedHornInclusions.{u, v}
    realizedGeneratorCardinal.{v} le_sup_right hPQ

/-- The realized horn inclusions in CGWH permit the small-object argument at
the literal `realizedGeneratorCardinal`. -/
noncomputable instance instHasSmallObjectArgumentRealizedHornInclusions :
    MorphismProperty.HasSmallObjectArgument.{v}
      realizedHornInclusions.{u, v} := by
  let _ : Fact realizedGeneratorCardinal.{v}.IsRegular :=
    ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  let _ : Nonempty realizedGeneratorCardinal.{v}.ord.ToType :=
    Ordinal.nonempty_toType_iff.mpr
      (by simpa using isRegular_realizedGeneratorCardinal.{v}.ne_zero)
  let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
    WellFoundedLT.toOrderBot realizedGeneratorCardinal.{v}.ord.ToType
  exact ⟨realizedGeneratorCardinal.{v}, inferInstance, inferInstance,
    inferInstance⟩

/-- The generated left class of the realized boundary inclusions is created
by the inclusion into compactly generated spaces. -/
theorem realizedBoundaryInclusions_rlp_llp :
    realizedBoundaryInclusions.{u, v}.rlp.llp =
      MorphismProperty.inverseImage
        (CompactlyGenerated.realizedBoundaryInclusions.{u, v}.rlp.llp)
        cgwhToCompactlyGenerated.{u, v} := by
  have hPQ : realizedBoundaryInclusions.{u, v} ≤
      CompactlyGenerated.realizedBoundaryInclusions.{u, v}.inverseImage
        cgwhToCompactlyGenerated.{u, v} := by
    intro X Y f hf
    obtain ⟨n⟩ := hf
    change CompactlyGenerated.realizedBoundaryInclusions.{u, v}
      (cgwhToCompactlyGenerated.{u, v}.map
        (realizedBoundaryInclusion n))
    rw [cgwhToCompactlyGenerated_map_realizedBoundaryInclusion]
    exact CompactlyGenerated.boundary_mem_realizedBoundaryInclusions n
  exact rlp_llp_eq_inverseImage_of_closedCells
    realizedBoundaryInclusions.{u, v}
    CompactlyGenerated.realizedBoundaryInclusions.{u, v}
    le_sup_left hPQ realizedBoundaryInclusions_rlp

/-- The generated left class of the realized horn inclusions is created by
the inclusion into compactly generated spaces. -/
theorem realizedHornInclusions_rlp_llp :
    realizedHornInclusions.{u, v}.rlp.llp =
      MorphismProperty.inverseImage
        (CompactlyGenerated.realizedHornInclusions.{u, v}.rlp.llp)
        cgwhToCompactlyGenerated.{u, v} := by
  have hPQ : realizedHornInclusions.{u, v} ≤
      CompactlyGenerated.realizedHornInclusions.{u, v}.inverseImage
        cgwhToCompactlyGenerated.{u, v} := by
    intro X Y f hf
    unfold realizedHornInclusions at hf
    rw [MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨i⟩⟩ := hf
    change CompactlyGenerated.realizedHornInclusions.{u, v}
      (cgwhToCompactlyGenerated.{u, v}.map
        (realizedHornInclusion n i))
    rw [cgwhToCompactlyGenerated_map_realizedHornInclusion]
    exact CompactlyGenerated.horn_mem_realizedHornInclusions n i
  exact rlp_llp_eq_inverseImage_of_closedCells
    realizedHornInclusions.{u, v}
    CompactlyGenerated.realizedHornInclusions.{u, v}
    le_sup_right hPQ realizedHornInclusions_rlp

end CGWH

namespace CompactlyGenerated

/-- Weak Hausdorffness is inherited by categorical retracts of compactly
generated spaces. -/
theorem uWeakHausdorffSpace_of_retract
    {X Y : CompactlyGenerated.{u, v}} (h : CategoryTheory.Retract X Y)
    [UWeakHausdorffSpace.{u} Y] : UWeakHausdorffSpace.{u} X := by
  rw [uWeakHausdorffSpace_iff_isClosed_equalizer]
  intro K f g
  let fi : C(K, Y) :=
    (ConcreteCategory.hom h.i).comp f
  let gi : C(K, Y) :=
    (ConcreteCategory.hom h.i).comp g
  have hclosed : IsClosed {k : K | fi k = gi k} :=
    (uWeakHausdorffSpace_iff_isClosed_equalizer.mp
      (inferInstance : UWeakHausdorffSpace.{u} Y)) K fi gi
  rw [show {k : K | f k = g k} = {k : K | fi k = gi k} by
    ext k
    constructor
    · intro hk
      exact congrArg (fun x => h.i x) hk
    · intro hk
      have hr := congrArg (fun y => h.r y) hk
      have hif := ConcreteCategory.congr_hom h.retract (f k)
      have hig := ConcreteCategory.congr_hom h.retract (g k)
      simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hif hig
      exact hif.symm.trans (hr.trans hig)]
  exact hclosed

end CompactlyGenerated
