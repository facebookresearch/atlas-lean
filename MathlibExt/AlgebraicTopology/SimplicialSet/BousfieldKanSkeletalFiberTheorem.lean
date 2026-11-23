/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanCellDeformation
public import MathlibExt.Topology.Category.TopCat.FibrationCoproducts
import MathlibExt.Topology.Category.TopCat.HomotopyFiberDeformationDescent
import MathlibExt.Topology.Category.TopCat.HomotopyCartesianOpenCoverDescent
import MathlibExt.Topology.Category.TopCat.HomotopyFiberSkeletalDescent
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatStrictFiberHomotopyFiber

/-!
# Actual BK skeletal fiber comparisons

The new-cell interior projection is an actual disjoint product projection
and hence a selected TopCat fibration. Universe lifts retain the original
native simplex and coefficient coordinates. The actual zero-stage coproduct
dictionary, punctured deformation and two-open-set criterion prove every
canonical skeletal comparison. Actual skeletal descent and strict-point
factorization then prove the original BK point-fiber comparison weak.
-/

public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite Topology
open scoped Simplicial TopCat.modelCategory

universe u v

namespace SSet

private def sigmaLiftHomeomorph {ι : Type u} (T : Type) [TopologicalSpace T] :
    (Σ _i : ι, T) ≃ₜ (Σ _i : ι, ULift.{u} T) where
  toEquiv := Equiv.sigmaCongrRight (fun _ => Equiv.ulift.symm)
  continuous_toFun := continuous_sigma (fun _ =>
    continuous_sigmaMk.comp Homeomorph.ulift.symm.continuous)
  continuous_invFun := continuous_sigma (fun _ =>
    continuous_sigmaMk.comp Homeomorph.ulift.continuous)

private def sigmaProductLiftHomeomorph {ι : Type u} (X : ι → TopCat.{u})
    (T : Type) [TopologicalSpace T] :
    (Σ i, X i × T) ≃ₜ (Σ i, X i × ULift.{u} T) where
  toEquiv := Equiv.sigmaCongrRight (fun _ => (Equiv.refl _).prodCongr Equiv.ulift.symm)
  continuous_toFun := continuous_sigma (fun _ => continuous_sigmaMk.comp
    (continuous_fst.prodMk (Homeomorph.ulift.symm.continuous.comp continuous_snd)))
  continuous_invFun := continuous_sigma (fun _ => continuous_sigmaMk.comp
    (continuous_fst.prodMk (Homeomorph.ulift.continuous.comp continuous_snd)))

private theorem nativeCellInteriorProjection_fibration
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Fibration (bkNativeCellInteriorProjection D n) := by
  let T := {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}
  let X : (nerve J).nonDegenerate (n + 1) → TopCat.{max u v} := fun c => toTop.obj (D.obj c.1.left)
  let B : (nerve J).nonDegenerate (n + 1) → TopCat.{max u v} :=
    fun _ => TopCat.of (ULift.{max u v} T)
  let eX : TopCat.of (Σ c, X c × T) ≅ TopCat.of (Σ c, X c × B c) :=
    TopCat.isoOfHomeo (sigmaProductLiftHomeomorph X T)
  let eB : TopCat.of (Σ _c : (nerve J).nonDegenerate (n + 1), T) ≅ TopCat.of (Σ c, B c) :=
    TopCat.isoOfHomeo (sigmaLiftHomeomorph T)
  let p := TopCat.sigmaProductProjection X B
  let _ : Fibration p := TopCat.fibration_sigmaProductProjection X B
  have he : bkNativeCellInteriorProjection D n ≫ eB.hom = eX.hom ≫ p := by
    apply TopCat.ext
    rintro ⟨c, x, t⟩
    have hn : bkNativeCellInteriorProjection D n ⟨c, x, t⟩ = ⟨c, t⟩ :=
      bkNativeCellInteriorProjection_apply D n c x t
    have hx : eX.hom ⟨c, x, t⟩ = ⟨c, x, ULift.up t⟩ := rfl
    calc
      eB.hom (bkNativeCellInteriorProjection D n ⟨c, x, t⟩) = eB.hom ⟨c, t⟩ := congrArg eB.hom hn
      _ = ⟨c, ULift.up t⟩ := rfl
      _ = TopCat.sigmaProductProjection X B ⟨c, x, ULift.up t⟩ :=
        (TopCat.sigmaProductProjection_apply X B c x (ULift.up t)).symm
      _ = p (eX.hom ⟨c, x, t⟩) := congrArg (fun z => p z) hx.symm
  have hp : bkNativeCellInteriorProjection D n = eX.hom ≫ p ≫ eB.inv := by
    calc
      bkNativeCellInteriorProjection D n =
          bkNativeCellInteriorProjection D n ≫ eB.hom ≫ eB.inv := by simp
      _ = eX.hom ≫ p ≫ eB.inv := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ eB.inv) he
  rw [hp]
  infer_instance

/-- The actual native disjoint new-cell product projection is a selected
TopCat fibration for arbitrary coefficient diagrams. -/
theorem bkNativeCellInteriorProjection_fibration
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Fibration (bkNativeCellInteriorProjection D n) :=
  nativeCellInteriorProjection_fibration D n

/-- The original realized skeletal projection over its actual new-cell
interiors is a selected TopCat fibration through the proved cell charts. -/
theorem bkSkeletalInteriorProjection_fibration
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Fibration (bkSkeletalInteriorProjection D n) := by
  let _ : Fibration (bkNativeCellInteriorProjection D n) :=
      bkNativeCellInteriorProjection_fibration D n
  let eX := bkNondegenerateCellInteriorProductIso D n
  let eB := bkNerveSkeletalCellInteriorIso J n
  have hp : bkSkeletalInteriorProjection D n =
      eX.inv ≫ bkNativeCellInteriorProjection D n ≫ eB.hom := by
    calc
      bkSkeletalInteriorProjection D n =
          eX.inv ≫ eX.hom ≫ bkSkeletalInteriorProjection D n := by simp
      _ = eX.inv ≫ bkNativeCellInteriorProjection D n ≫ eB.hom := by
        rw [bkSkeletalInteriorProjection_chart]
  rw [hp]
  infer_instance

private theorem projection_comp_global
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    toTop.map (bkSkeletalProjection D n) ≫ toTop.map ((nerve J).skeleton (n + 1)).ι =
      toTop.map (bkSkeletalFiltration D n).ι ≫ toTop.map (bkHocolimToNerve D) := by
  simpa only [Functor.map_comp] using congrArg toTop.map (bkSkeletalProjection_comp_ι D n)

private theorem skeletalMap_isPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) :
    IsPullback (toTop.map (bkSkeletalFiltrationMap D h))
      (toTop.map (bkSkeletalProjection D m)) (toTop.map (bkSkeletalProjection D n))
      (bkNerveSkeletalMap J h) := by
  have he : toTop.map (bkSkeletalFiltrationMap D h) ≫ toTop.map (bkSkeletalFiltration D n).ι =
      toTop.map (bkSkeletalFiltration D m).ι := by
    simpa only [Functor.map_comp] using congrArg toTop.map (bkSkeletalFiltrationMap_ι D h)
  have outer : IsPullback
      (toTop.map (bkSkeletalFiltrationMap D h) ≫ toTop.map (bkSkeletalFiltration D n).ι)
      (toTop.map (bkSkeletalProjection D m)) (toTop.map (bkHocolimToNerve D))
      (bkNerveSkeletalMap J h ≫ toTop.map ((nerve J).skeleton (n + 1)).ι) := by
    rw [he, bkNerveSkeletalMap_ι]
    exact bkSkeletalProjection_realized_isPullback D m
  have comm : toTop.map (bkSkeletalFiltrationMap D h) ≫ toTop.map (bkSkeletalProjection D n) =
      toTop.map (bkSkeletalProjection D m) ≫ bkNerveSkeletalMap J h := by
    let _ : Mono (toTop.map ((nerve J).skeleton (n + 1)).ι) := by
      rw [TopCat.mono_iff_injective]
      exact (TopCat.closedT1Embeddings_le_isClosedEmbedding _
        (closedT1Embeddings_toTop_map_of_mono ((nerve J).skeleton (n + 1)).ι)).isEmbedding.injective
    apply (cancel_mono (toTop.map ((nerve J).skeleton (n + 1)).ι)).mp
    rw [Category.assoc, projection_comp_global, ← Category.assoc, he,
      ← projection_comp_global, Category.assoc, bkNerveSkeletalMap_ι]
  exact IsPullback.of_right outer comm (bkSkeletalProjection_realized_isPullback D n)

private theorem oldStage_range_preimage
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))) =
      (toTop.map (bkSkeletalProjection D (n + 1))) ⁻¹'
        Set.range (bkNerveSkeletalMap J (Nat.le_succ n)) := by
  let sq := skeletalMap_isPullback D (Nat.le_succ n)
  let i := sq.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨toTop.map (bkSkeletalProjection D n) a, (ConcreteCategory.congr_hom sq.w a).symm⟩
  · rintro ⟨b, hb⟩
    let z := (TopCat.pullbackIsoProdSubtype (toTop.map (bkSkeletalProjection D (n + 1)))
      (bkNerveSkeletalMap J (Nat.le_succ n))).inv ⟨(x, b), hb.symm⟩
    refine ⟨i.inv z, ?_⟩
    exact (ConcreteCategory.congr_hom (sq.isoIsPullback_inv_fst _ _
      (IsPullback.of_hasPullback _ _)) z).trans
        (TopCat.pullbackIsoProdSubtype_inv_fst_apply _ _ ⟨(x, b), hb.symm⟩)

private theorem interior_preimage
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ =
      (toTop.map (bkSkeletalProjection D (n + 1))) ⁻¹'
        (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ := by
  simpa only [Set.preimage_compl] using congrArg (fun s => sᶜ) (oldStage_range_preimage D n)

private theorem interiorProjection_comp_inclusion
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkSkeletalInteriorProjection D n ≫
      AlgebraicTopology.subspaceIncl (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ =
        AlgebraicTopology.subspaceIncl
            (Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ ≫
          toTop.map (bkSkeletalProjection D (n + 1)) := by
  apply (cancel_epi (bkNondegenerateCellInteriorProductIso D n).hom).mp
  apply TopCat.ext
  rintro ⟨c, x, t⟩
  have hc := ConcreteCategory.congr_hom (bkSkeletalInteriorProjection_chart D n) ⟨c, x, t⟩
  have hn := bkNativeCellInteriorProjection_apply D n c x t
  have hb := bkNerveSkeletalCellInteriorIso_hom_apply J n c t
  have hl := (congrArg Subtype.val hc).trans
    ((congrArg (fun z => ((bkNerveSkeletalCellInteriorIso J n).hom z).1) hn).trans hb)
  have ht := bkNondegenerateCellInteriorProductIso_hom_apply D n c x t
  have hr := (congrArg (fun z => toTop.map (bkSkeletalProjection D (n + 1)) z) ht).trans
    (bkRealizedChainCellToStage_projection_apply D c.1 x t.1)
  exact hl.trans hr.symm

private theorem canonicalInteriorProjection_fibration
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Fibration (TopCat.restrictionProjection (toTop.map (bkSkeletalProjection D (n + 1)))
      (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ) := by
  let p := toTop.map (bkSkeletalProjection D (n + 1))
  let V := (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ
  let T := (Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ
  let e : TopCat.of T ≅ TopCat.of (p ⁻¹' V) :=
      TopCat.isoOfHomeo (Homeomorph.setCongr (interior_preimage D n))
  let q := TopCat.restrictionProjection p V
  let sq := TopCat.restrictionProjection_isPullback p V
  have hi : e.hom ≫ AlgebraicTopology.subspaceIncl (p ⁻¹' V) =
      AlgebraicTopology.subspaceIncl T := by
    apply TopCat.ext
    intro x
    rfl
  have he : e.hom ≫ q = bkSkeletalInteriorProjection D n := by
    apply (cancel_mono (AlgebraicTopology.subspaceIncl V)).mp
    calc
      (e.hom ≫ q) ≫ AlgebraicTopology.subspaceIncl V =
          (e.hom ≫ AlgebraicTopology.subspaceIncl (p ⁻¹' V)) ≫ p := by
            rw [Category.assoc, ← sq.w, ← Category.assoc]
      _ = AlgebraicTopology.subspaceIncl T ≫ p := congrArg (fun f => f ≫ p) hi
      _ = bkSkeletalInteriorProjection D n ≫ AlgebraicTopology.subspaceIncl V :=
        (interiorProjection_comp_inclusion D n).symm
  have hq : q = e.inv ≫ bkSkeletalInteriorProjection D n := by
    calc
      q = e.inv ≫ e.hom ≫ q := by simp
      _ = e.inv ≫ bkSkeletalInteriorProjection D n := by rw [he]
  let _ : Fibration (bkSkeletalInteriorProjection D n) := bkSkeletalInteriorProjection_fibration D n
  change Fibration q
  rw [hq]
  infer_instance

private theorem canonicalInteriorComparison_mem
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : TopCat.of ↥((Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ)) :
    TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (TopCat.restrictionProjection (toTop.map (bkSkeletalProjection D (n + 1)))
        (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ) b) := by
  let q := TopCat.restrictionProjection (toTop.map (bkSkeletalProjection D (n + 1)))
    (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ
  let _ : Fibration q := canonicalInteriorProjection_fibration D n
  exact TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences q b

private theorem canonicalInteriorOverlapProjection_fibration
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (U : Set (toTop.obj ((nerve J).skeleton (n + 2) : SSet.{max u v}))) :
    Fibration (TopCat.restrictionProjection (toTop.map (bkSkeletalProjection D (n + 1)))
      (U ∩ (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ)) := by
  let p := toTop.map (bkSkeletalProjection D (n + 1))
  let V := (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ
  let sq := TopCat.restrictionProjection_nested_isPullback p (Set.inter_subset_right : U ∩ V ⊆ V)
  have hV := canonicalInteriorProjection_fibration D n
  rw [HomotopicalAlgebra.fibration_iff] at hV ⊢
  exact MorphismProperty.of_isPullback sq hV

private theorem canonicalInteriorOverlapComparison_mem
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (U : Set (toTop.obj ((nerve J).skeleton (n + 2) : SSet.{max u v})))
    (b : TopCat.of ↥(U ∩ (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ)) :
    TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (TopCat.restrictionProjection (toTop.map (bkSkeletalProjection D (n + 1)))
        (U ∩ (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ)) b) := by
  let q := TopCat.restrictionProjection (toTop.map (bkSkeletalProjection D (n + 1)))
    (U ∩ (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ)
  let _ : Fibration q := canonicalInteriorOverlapProjection_fibration D n U
  exact TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences q b

private def puncturedBaseSet (J : Type u) [Category.{v} J] (n : ℕ) :
    Set (toTop.obj ((nerve J).skeleton (n + 2) : SSet.{max u v})) :=
  (bkNerveSkeletalCellModelIso J (n + 1)).inv ⁻¹' (bkCellBarycenters (bkPointDiagram J) n)ᶜ

private theorem puncturedBaseSet_isOpen (J : Type u) [Category.{v} J] (n : ℕ) :
    IsOpen (puncturedBaseSet J n) :=
  (bkCellBarycenters_isClosed (bkPointDiagram J) n).isOpen_compl.preimage
    (bkNerveSkeletalCellModelIso J (n + 1)).inv.hom.continuous

private theorem puncturedTotal_preimage
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkCellBarycenters D n)ᶜ =
      (toTop.map (bkSkeletalProjection D (n + 1))) ⁻¹' puncturedBaseSet J n := by
  have h := (congrArg (fun s => sᶜ) (bkCellBarycenters_preimage D n)).symm
  have he : ((toTop.map (bkSkeletalProjection D (n + 1)) ≫
      (bkNerveSkeletalCellModelIso J (n + 1)).inv) ⁻¹' bkCellBarycenters (bkPointDiagram J) n)ᶜ =
        (toTop.map (bkSkeletalProjection D (n + 1))) ⁻¹' puncturedBaseSet J n := by
    ext x
    rfl
  exact h.trans he

private def puncturedBaseHomeomorph (J : Type u) [Category.{v} J] (n : ℕ) :
    bkCellBarycenterComplement (bkPointDiagram J) n ≃ₜ puncturedBaseSet J n where
  toEquiv :=
    { toFun := fun a => ⟨(bkNerveSkeletalCellModelIso J (n + 1)).hom a.1, by
        intro ha
        have he : (bkNerveSkeletalCellModelIso J (n + 1)).inv
            ((bkNerveSkeletalCellModelIso J (n + 1)).hom a.1) = a.1 :=
          ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso J (n + 1)).hom_inv_id a.1
        exact a.2 (he ▸ ha)⟩
      invFun := fun b => ⟨(bkNerveSkeletalCellModelIso J (n + 1)).inv b.1, b.2⟩
      left_inv := fun a => Subtype.ext
        (ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso J (n + 1)).hom_inv_id a.1)
      right_inv := fun b => Subtype.ext
        (ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso J (n + 1)).inv_hom_id b.1) }
  continuous_toFun := ((bkNerveSkeletalCellModelIso J (n + 1)).hom.hom.continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((bkNerveSkeletalCellModelIso J (n + 1)).inv.hom.continuous.comp
    continuous_subtype_val).subtype_mk _

private def puncturedBaseIso (J : Type u) [Category.{v} J] (n : ℕ) :
    bkCellBarycenterComplement (bkPointDiagram J) n ≅ TopCat.of (puncturedBaseSet J n) :=
  TopCat.isoOfHomeo (puncturedBaseHomeomorph J n)

private def puncturedTotalIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellBarycenterComplement D n ≅
      TopCat.of ((toTop.map (bkSkeletalProjection D (n + 1))) ⁻¹' puncturedBaseSet J n) :=
  TopCat.isoOfHomeo (Homeomorph.setCongr (puncturedTotal_preimage D n))

private theorem puncturedBaseIso_hom_inclusion (J : Type u) [Category.{v} J] (n : ℕ) :
    (puncturedBaseIso J n).hom ≫ AlgebraicTopology.subspaceIncl (puncturedBaseSet J n) =
      bkCellBarycenterComplementInclusion (bkPointDiagram J) n ≫
        (bkNerveSkeletalCellModelIso J (n + 1)).hom := by
  apply TopCat.ext
  intro a
  exact (congrArg (fun x => (bkNerveSkeletalCellModelIso J (n + 1)).hom x)
    (bkCellBarycenterComplementInclusion_apply (bkPointDiagram J) n a)).symm

private theorem puncturedTotalIso_hom_inclusion
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (puncturedTotalIso D n).hom ≫
      AlgebraicTopology.subspaceIncl
          ((toTop.map (bkSkeletalProjection D (n + 1))) ⁻¹' puncturedBaseSet J n) =
        bkCellBarycenterComplementInclusion D n := by
  apply TopCat.ext
  intro a
  exact (bkCellBarycenterComplementInclusion_apply D n a).symm

private theorem puncturedProjection_comm
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (puncturedTotalIso D n).hom ≫
      TopCat.restrictionProjection (toTop.map (bkSkeletalProjection D (n + 1)))
          (puncturedBaseSet J n) =
        bkCellPuncturedProjection D n ≫ (puncturedBaseIso J n).hom := by
  apply (cancel_mono (AlgebraicTopology.subspaceIncl (puncturedBaseSet J n))).mp
  rw [Category.assoc, ← (TopCat.restrictionProjection_isPullback
    (toTop.map (bkSkeletalProjection D (n + 1))) (puncturedBaseSet J n)).w,
    ← Category.assoc, puncturedTotalIso_hom_inclusion, Category.assoc,
    puncturedBaseIso_hom_inclusion, bkCellPuncturedProjection_original_projection]

private theorem puncturedModel_isPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsPullback (bkCellBarycenterComplementInclusion D n) (bkCellPuncturedProjection D n)
      (toTop.map (bkSkeletalProjection D (n + 1)))
      (bkCellBarycenterComplementInclusion (bkPointDiagram J) n ≫
        (bkNerveSkeletalCellModelIso J (n + 1)).hom) := by
  apply (TopCat.restrictionProjection_isPullback (toTop.map (bkSkeletalProjection D (n + 1)))
    (puncturedBaseSet J n)).of_iso
      (puncturedTotalIso D n).symm (Iso.refl _) (puncturedBaseIso J n).symm (Iso.refl _)
  · simpa using congrArg (fun f => (puncturedTotalIso D n).inv ≫ f)
      (puncturedTotalIso_hom_inclusion D n)
  · simpa [Category.assoc] using congrArg
      (fun f => (puncturedTotalIso D n).inv ≫ f ≫ (puncturedBaseIso J n).inv)
        (puncturedProjection_comm D n)
  · simp
  · simpa using congrArg (fun f => (puncturedBaseIso J n).inv ≫ f)
      (puncturedBaseIso_hom_inclusion J n)

private def originalOldPuncturedInclusion (J : Type u) [Category.{v} J] (n : ℕ) :
    toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v}) ⟶
      bkCellBarycenterComplement (bkPointDiagram J) n :=
  (bkNerveSkeletalCellModelIso J n).inv ≫ bkCellOldStageInclusion (bkPointDiagram J) n

private theorem originalOldPuncturedInclusion_comp_original
    (J : Type u) [Category.{v} J] (n : ℕ) :
    originalOldPuncturedInclusion J n ≫
      (bkCellBarycenterComplementInclusion (bkPointDiagram J) n ≫
        (bkNerveSkeletalCellModelIso J (n + 1)).hom) = bkNerveSkeletalMap J (Nat.le_succ n) := by
  calc
    originalOldPuncturedInclusion J n ≫
        (bkCellBarycenterComplementInclusion (bkPointDiagram J) n ≫
          (bkNerveSkeletalCellModelIso J (n + 1)).hom) =
      (bkNerveSkeletalCellModelIso J n).inv ≫
        (bkCellOldStageInclusion (bkPointDiagram J) n ≫
          bkCellBarycenterComplementInclusion (bkPointDiagram J) n) ≫
            (bkNerveSkeletalCellModelIso J (n + 1)).hom := by
              simp only [originalOldPuncturedInclusion, Category.assoc]
    _ = (bkNerveSkeletalCellModelIso J n).inv ≫
        toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) (Nat.le_succ n)) ≫
          (bkNerveSkeletalCellModelIso J (n + 1)).hom := by
            rw [bkCellOldStageInclusion_comp_inclusion]
    _ = (bkNerveSkeletalCellModelIso J n).inv ≫ (bkNerveSkeletalCellModelIso J n).hom ≫
        bkNerveSkeletalMap J (Nat.le_succ n) := by
          rw [bkNerveSkeletalCellModelIso_natural]
    _ = bkNerveSkeletalMap J (Nat.le_succ n) := by simp

private theorem originalOldPunctured_isPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsPullback (bkCellOldStageInclusion D n) (toTop.map (bkSkeletalProjection D n))
      (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n) := by
  let h := bkCellBarycenterComplementInclusion (bkPointDiagram J) n ≫
    (bkNerveSkeletalCellModelIso J (n + 1)).hom
  let _ : Mono h := by
    change Mono (bkCellBarycenterComplementInclusion (bkPointDiagram J) n ≫
      (bkNerveSkeletalCellModelIso J (n + 1)).hom)
    rw [← puncturedBaseIso_hom_inclusion]
    infer_instance
  have outer : IsPullback
      (bkCellOldStageInclusion D n ≫ bkCellBarycenterComplementInclusion D n)
      (toTop.map (bkSkeletalProjection D n)) (toTop.map (bkSkeletalProjection D (n + 1)))
      (originalOldPuncturedInclusion J n ≫ h) := by
    rw [bkCellOldStageInclusion_comp_inclusion, originalOldPuncturedInclusion_comp_original]
    exact skeletalMap_isPullback D (Nat.le_succ n)
  have comm : bkCellOldStageInclusion D n ≫ bkCellPuncturedProjection D n =
      toTop.map (bkSkeletalProjection D n) ≫ originalOldPuncturedInclusion J n := by
    apply (cancel_mono h).mp
    rw [Category.assoc, ← (puncturedModel_isPullback D n).w, ← Category.assoc,
      bkCellOldStageInclusion_comp_inclusion, Category.assoc,
      originalOldPuncturedInclusion_comp_original]
    exact (skeletalMap_isPullback D (Nat.le_succ n)).w
  exact IsPullback.of_right outer comm (puncturedModel_isPullback D n)

private def originalOldPullbackIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}) ≅
      pullback (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n) :=
  (originalOldPunctured_isPullback D n).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

private theorem originalOldPullbackIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (originalOldPullbackIso D n).hom ≫
      pullback.fst (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n) =
        bkCellOldStageInclusion D n :=
  (originalOldPunctured_isPullback D n).isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback _ _)

private theorem originalOldPullbackIso_hom_snd
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (originalOldPullbackIso D n).hom ≫
      pullback.snd (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n) =
        toTop.map (bkSkeletalProjection D n) :=
  (originalOldPunctured_isPullback D n).isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback _ _)

private def originalBaseRadialRetraction (J : Type u) [Category.{v} J] (n : ℕ) :
    bkCellBarycenterComplement (bkPointDiagram J) n ⟶
      toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v}) :=
  bkCellRadialRetraction (bkPointDiagram J) n ≫ (bkNerveSkeletalCellModelIso J n).hom

private theorem originalBaseRadialRetraction_retract (J : Type u) [Category.{v} J] (n : ℕ) :
    originalOldPuncturedInclusion J n ≫ originalBaseRadialRetraction J n =
      𝟙 (toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) := by
  simp [originalOldPuncturedInclusion, originalBaseRadialRetraction, Category.assoc,
    bkCellRadialRetraction_retract_assoc]

private def originalBaseRadialHomotopy (J : Type u) [Category.{v} J] (n : ℕ) :
    TopCat.Homotopy (𝟙 (bkCellBarycenterComplement (bkPointDiagram J) n))
      (originalBaseRadialRetraction J n ≫ originalOldPuncturedInclusion J n) := by
  have he : bkCellRadialRetraction (bkPointDiagram J) n ≫
      bkCellOldStageInclusion (bkPointDiagram J) n =
      originalBaseRadialRetraction J n ≫ originalOldPuncturedInclusion J n := by
    simp [originalBaseRadialRetraction, originalOldPuncturedInclusion, Category.assoc]
  exact (bkCellRadialHomotopy (bkPointDiagram J) n).cast rfl (congrArg (fun f => f.hom) he)

private theorem radialHomotopy_covers_original
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (e : bkCellBarycenterComplement D n) :
    bkCellPuncturedProjection D n (bkCellRadialHomotopy D n (t, e)) =
      originalBaseRadialHomotopy J n (t, bkCellPuncturedProjection D n e) :=
  bkCellRadialHomotopy_projection D n t e

private theorem originalBaseRadialHomotopy_on_old (J : Type u) [Category.{v} J] (n : ℕ)
    (t : unitInterval) (a : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) :
    originalBaseRadialHomotopy J n (t, originalOldPuncturedInclusion J n a) =
      originalOldPuncturedInclusion J n a :=
  bkCellRadialHomotopy_on_old (bkPointDiagram J) n t ((bkNerveSkeletalCellModelIso J n).inv a)

private def liftedRadialRetraction
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellBarycenterComplement D n ⟶
      pullback (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n) :=
  TopCat.liftedDeformationRetraction (bkCellPuncturedProjection D n)
    (originalOldPuncturedInclusion J n) (originalBaseRadialRetraction J n)
    (originalBaseRadialHomotopy J n) (bkCellRadialRetraction D n ≫ bkCellOldStageInclusion D n)
    (bkCellRadialHomotopy D n) (radialHomotopy_covers_original D n)

private theorem liftedRadialRetraction_eq
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    liftedRadialRetraction D n = bkCellRadialRetraction D n ≫ (originalOldPullbackIso D n).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, originalOldPullbackIso_hom_fst]
    exact TopCat.liftedDeformationRetraction_fst _ _ _ _ _ _ _
  · rw [Category.assoc, originalOldPullbackIso_hom_snd]
    have hs := TopCat.liftedDeformationRetraction_snd (bkCellPuncturedProjection D n)
      (originalOldPuncturedInclusion J n) (originalBaseRadialRetraction J n)
      (originalBaseRadialHomotopy J n) (bkCellRadialRetraction D n ≫ bkCellOldStageInclusion D n)
      (bkCellRadialHomotopy D n) (radialHomotopy_covers_original D n)
    exact hs.trans (by
      simpa only [originalBaseRadialRetraction, Category.assoc] using
        (bkCellRadialRetraction_original_projection D n).symm)

private theorem originalOldPullbackIso_inv_snd
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (originalOldPullbackIso D n).inv ≫ toTop.map (bkSkeletalProjection D n) =
      pullback.snd (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n) :=
  (originalOldPunctured_isPullback D n).isoIsPullback_inv_snd _ _ (IsPullback.of_hasPullback _ _)

private def originalOldForwardFiberMap
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) :=
  TopCat.strictFiberMapOfSquare (originalOldPullbackIso D n).hom (𝟙 _)
    (by simpa only [Category.comp_id] using (originalOldPullbackIso_hom_snd D n).symm) b

private theorem originalOldForwardFiberMap_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) :
    originalOldForwardFiberMap D n b ≫
      pullback.fst
          (pullback.snd (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n))
        (TopCat.const (X := TopCat.of PUnit) b) =
      pullback.fst (toTop.map (bkSkeletalProjection D n)) (TopCat.const (X := TopCat.of PUnit) b) ≫
        (originalOldPullbackIso D n).hom :=
  TopCat.strictFiberMapOfSquare_fst _ _ _ b

private theorem originalOldForwardFiberMap_isIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) :
    IsIso (originalOldForwardFiberMap D n b) := by
  have sq : IsPullback (originalOldPullbackIso D n).hom (toTop.map (bkSkeletalProjection D n))
      (pullback.snd (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n)) (𝟙 _) :=
    IsPullback.of_horiz_isIso
        ⟨by simpa only [Category.comp_id] using originalOldPullbackIso_hom_snd D n⟩
  exact TopCat.isIso_strictFiberMapOfSquare_of_isPullback sq b

private theorem oldCanonicalPullbackComparison_mem
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (ih : ∀ b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v}),
      TopCat.weakHomotopyEquivalences
          (TopCat.strictFiberToHomotopyFiber (toTop.map (bkSkeletalProjection D n)) b))
    (b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) :
    TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (pullback.snd (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n)) b) := by
  let s := (originalOldPullbackIso D n).inv
  let q := pullback.snd (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n)
  have comm : q ≫ 𝟙 _ = s ≫ toTop.map (bkSkeletalProjection D n) := by
    simpa only [Category.comp_id] using (originalOldPullbackIso_inv_snd D n).symm
  have sq : IsPullback s q (toTop.map (bkSkeletalProjection D n)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨comm.symm⟩
  let _ : IsIso (TopCat.strictFiberMapOfSquare s (𝟙 _) comm b) :=
    TopCat.isIso_strictFiberMapOfSquare_of_isPullback sq b
  exact TopCat.strictFiberToHomotopyFiber_mem_of_square s (𝟙 _) comm b
    (TopCat.weakHomotopyEquivalences.of_isIso _) (TopCat.weakHomotopyEquivalences.of_isIso _)
    (TopCat.weakHomotopyEquivalences.of_isIso _) (ih b)

private theorem liftedRadialRetraction_snd
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    liftedRadialRetraction D n ≫
      pullback.snd (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n) =
        bkCellPuncturedProjection D n ≫ originalBaseRadialRetraction J n :=
  TopCat.liftedDeformationRetraction_snd _ _ _ _ _ _ _

private def liftedRadialFiberMap
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :=
  TopCat.strictFiberMapOfSquare (liftedRadialRetraction D n) (originalBaseRadialRetraction J n)
    (liftedRadialRetraction_snd D n).symm a

private theorem liftedRadialFiberMap_eq
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    liftedRadialFiberMap D n a = bkCellRadialStrictFiberMap D n a ≫
      originalOldForwardFiberMap D n (originalBaseRadialRetraction J n a) := by
  apply pullback.hom_ext
  · calc
      liftedRadialFiberMap D n a ≫
          pullback.fst
              (pullback.snd (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n))
            (TopCat.const (X := TopCat.of PUnit) (originalBaseRadialRetraction J n a)) =
        pullback.fst (bkCellPuncturedProjection D n) (TopCat.const (X := TopCat.of PUnit) a) ≫
          liftedRadialRetraction D n := TopCat.strictFiberMapOfSquare_fst _ _ _ a
      _ = (pullback.fst (bkCellPuncturedProjection D n) (TopCat.const (X := TopCat.of PUnit) a) ≫
          bkCellRadialRetraction D n) ≫ (originalOldPullbackIso D n).hom := by
            rw [liftedRadialRetraction_eq, ← Category.assoc]
      _ = (bkCellRadialStrictFiberMap D n a ≫
          pullback.fst (toTop.map (bkSkeletalProjection D n))
            (TopCat.const (X := TopCat.of PUnit) (originalBaseRadialRetraction J n a))) ≫
              (originalOldPullbackIso D n).hom :=
                congrArg (fun f => f ≫ (originalOldPullbackIso D n).hom)
                  (bkCellRadialStrictFiberMap_fst D n a).symm
      _ = (bkCellRadialStrictFiberMap D n a ≫
          originalOldForwardFiberMap D n (originalBaseRadialRetraction J n a)) ≫
          pullback.fst
              (pullback.snd (bkCellPuncturedProjection D n) (originalOldPuncturedInclusion J n))
            (TopCat.const (X := TopCat.of PUnit) (originalBaseRadialRetraction J n a)) := by
              simpa only [Category.assoc] using (congrArg
                (fun f => bkCellRadialStrictFiberMap D n a ≫ f)
                  (originalOldForwardFiberMap_fst D n (originalBaseRadialRetraction J n a))).symm
  · apply TopCat.isTerminalPUnit.hom_ext

private theorem puncturedModelComparison_mem
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (ih : ∀ b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v}),
      TopCat.weakHomotopyEquivalences
          (TopCat.strictFiberToHomotopyFiber (toTop.map (bkSkeletalProjection D n)) b))
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber (bkCellPuncturedProjection D n) a) := by
  let _ : IsIso (originalOldForwardFiberMap D n (originalBaseRadialRetraction J n a)) :=
    originalOldForwardFiberMap_isIso D n _
  have hf : TopCat.weakHomotopyEquivalences (liftedRadialFiberMap D n a) := by
    rw [liftedRadialFiberMap_eq]
    exact TopCat.weakHomotopyEquivalences.comp_mem _ _
      (bkCellRadialStrictFiberMap_mem_weakHomotopyEquivalences D n hD a)
      (TopCat.weakHomotopyEquivalences.of_isIso _)
  exact TopCat.strictFiberToHomotopyFiber_mem_of_liftedDeformation (bkCellPuncturedProjection D n)
    (originalOldPuncturedInclusion J n) (originalBaseRadialRetraction J n)
    (originalBaseRadialRetraction_retract J n) (originalBaseRadialHomotopy J n)
    (bkCellRadialRetraction D n ≫ bkCellOldStageInclusion D n) (bkCellRadialHomotopy D n)
    (radialHomotopy_covers_original D n) (originalBaseRadialHomotopy_on_old J n) a hf
    (oldCanonicalPullbackComparison_mem D n ih _)

private theorem canonicalPuncturedComparison_mem
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (ih : ∀ b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v}),
      TopCat.weakHomotopyEquivalences
          (TopCat.strictFiberToHomotopyFiber (toTop.map (bkSkeletalProjection D n)) b))
    (b : TopCat.of (puncturedBaseSet J n)) :
    TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (TopCat.restrictionProjection (toTop.map (bkSkeletalProjection D (n + 1)))
          (puncturedBaseSet J n)) b) := by
  let q := TopCat.restrictionProjection (toTop.map (bkSkeletalProjection D (n + 1)))
      (puncturedBaseSet J n)
  let s := (puncturedTotalIso D n).inv
  let h := (puncturedBaseIso J n).inv
  have comm : q ≫ h = s ≫ bkCellPuncturedProjection D n := by
    simpa [Category.assoc] using congrArg
      (fun f => (puncturedTotalIso D n).inv ≫ f ≫
          (puncturedBaseIso J n).inv) (puncturedProjection_comm D n)
  have sq : IsPullback s q (bkCellPuncturedProjection D n) h :=
      IsPullback.of_horiz_isIso ⟨comm.symm⟩
  let _ : IsIso (TopCat.strictFiberMapOfSquare s h comm b) :=
    TopCat.isIso_strictFiberMapOfSquare_of_isPullback sq b
  exact TopCat.strictFiberToHomotopyFiber_mem_of_square s h comm b
    (TopCat.weakHomotopyEquivalences.of_isIso _) (TopCat.weakHomotopyEquivalences.of_isIso _)
    (TopCat.weakHomotopyEquivalences.of_isIso _) (puncturedModelComparison_mem D n hD ih (h b))

private theorem nerveSkeletalMap_isClosedEmbedding (J : Type u) [Category.{v} J] {m n : ℕ}
    (h : m ≤ n) :
    IsClosedEmbedding (bkNerveSkeletalMap J h) := by
  have he : bkNerveSkeletalMap J h =
      toTop.map (Subcomplex.homOfLE ((nerve J).skeleton.monotone (Nat.add_le_add_right h 1))) := by
    let _ : Mono (toTop.map ((nerve J).skeleton (n + 1)).ι) := by
      rw [TopCat.mono_iff_injective]
      exact (TopCat.closedT1Embeddings_le_isClosedEmbedding _
        (closedT1Embeddings_toTop_map_of_mono ((nerve J).skeleton (n + 1)).ι)).isEmbedding.injective
    apply (cancel_mono (toTop.map ((nerve J).skeleton (n + 1)).ι)).mp
    rw [bkNerveSkeletalMap_ι, ← Functor.map_comp, Subcomplex.homOfLE_ι]
  rw [he]
  exact TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (closedT1Embeddings_toTop_map_of_mono (Subcomplex.homOfLE
      ((nerve J).skeleton.monotone (Nat.add_le_add_right h 1))))

private def interiorBaseOpen (J : Type u) [Category.{v} J] (n : ℕ) :
    TopologicalSpace.Opens (toTop.obj ((nerve J).skeleton (n + 2) : SSet.{max u v})) :=
  ⟨(Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ,
    (nerveSkeletalMap_isClosedEmbedding J (Nat.le_succ n)).isClosed_range.isOpen_compl⟩

private def puncturedBaseOpen (J : Type u) [Category.{v} J] (n : ℕ) :
    TopologicalSpace.Opens (toTop.obj ((nerve J).skeleton (n + 2) : SSet.{max u v})) :=
  ⟨puncturedBaseSet J n, puncturedBaseSet_isOpen J n⟩

private theorem punctured_interior_cover (J : Type u) [Category.{v} J] (n : ℕ) :
    (puncturedBaseOpen J n : Set (toTop.obj ((nerve J).skeleton (n + 2) : SSet.{max u v}))) ∪
      (interiorBaseOpen J n : Set (toTop.obj ((nerve J).skeleton (n + 2) : SSet.{max u v}))) =
          Set.univ := by
  ext b
  constructor
  · intro _
    trivial
  · intro _
    by_cases hb : b ∈ Set.range (bkNerveSkeletalMap J (Nat.le_succ n))
    · obtain ⟨a, rfl⟩ := hb
      left
      let q := originalOldPuncturedInclusion J n a
      have hs : (bkNerveSkeletalCellModelIso J (n + 1)).hom q.1 =
          bkNerveSkeletalMap J (Nat.le_succ n) a := by
        have h := ConcreteCategory.congr_hom (originalOldPuncturedInclusion_comp_original J n) a
        exact (congrArg (fun x => (bkNerveSkeletalCellModelIso J (n + 1)).hom x)
          (bkCellBarycenterComplementInclusion_apply (bkPointDiagram J) n q)).symm.trans h
      have he : (bkNerveSkeletalCellModelIso J (n + 1)).inv
          (bkNerveSkeletalMap J (Nat.le_succ n) a) = q.1 :=
        (congrArg (fun x => (bkNerveSkeletalCellModelIso J (n + 1)).inv x) hs).symm.trans
          (ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso J (n + 1)).hom_inv_id q.1)
      change (bkNerveSkeletalCellModelIso J (n + 1)).inv
        (bkNerveSkeletalMap J (Nat.le_succ n) a) ∉ bkCellBarycenters (bkPointDiagram J) n
      exact he ▸ q.2
    · exact Or.inr hb

private theorem successorComparison_mem
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (ih : ∀ b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v}),
      TopCat.weakHomotopyEquivalences
          (TopCat.strictFiberToHomotopyFiber (toTop.map (bkSkeletalProjection D n)) b))
    (b : toTop.obj ((nerve J).skeleton (n + 2) : SSet.{max u v})) :
    TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber (toTop.map (bkSkeletalProjection D (n + 1))) b) := by
  exact TopCat.strictFiberToHomotopyFiber_mem_of_twoSetOpenCover
    (toTop.map (bkSkeletalProjection D (n + 1))) (puncturedBaseOpen J n) (interiorBaseOpen J n)
    (punctured_interior_cover J n) (canonicalPuncturedComparison_mem D n hD ih)
    (canonicalInteriorComparison_mem D n)
    (canonicalInteriorOverlapComparison_mem D n (puncturedBaseSet J n)) b

private def zeroUnitProductIso (X : SSet.{u}) : X ⊗ (Δ[0] : SSet.{u}) ≅ X where
  hom := CartesianMonoidalCategory.fst X (Δ[0] : SSet.{u})
  inv := CartesianMonoidalCategory.lift (𝟙 X) (stdSimplex.isTerminalObj₀.from X)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply stdSimplex.ext₀
  inv_hom_id := by
    simp

private theorem zeroUnitProductIso_inv_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ (zeroUnitProductIso Y).inv = (zeroUnitProductIso X).inv ≫ (f ▷ (Δ[0] : SSet.{u})) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [zeroUnitProductIso]
  · apply stdSimplex.ext₀

private def zeroWeightedStageIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).obj (op ⦋0⦌) ⊗
        (Δ[0] : SSet.{max u v}) ≅ (bkSkeletalFiltration D 0 : SSet.{max u v}) := by
  let X := StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D
  let _ : Mono (diagonalCellMap X 0) := diagonalCellMap_zero_mono X
  let h : bkSkeletalFiltration D 0 = Subcomplex.range (diagonalCellMap X 0) :=
    (bkSkeletalFiltration_eq_diagonalFiltration D 0).trans (diagonalFiltration_zero X)
  exact asIso (Subcomplex.toRange (diagonalCellMap X 0)) ≪≫ Subcomplex.eqToIso h.symm

private theorem zeroWeightedStageIso_hom_inclusion
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    (zeroWeightedStageIso D).hom ≫ (bkSkeletalFiltration D 0).ι =
      diagonalCellMap (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D) 0 := by
  dsimp only [zeroWeightedStageIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι, Subcomplex.toRange_ι]

private def zeroBarStageIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).obj (op ⦋0⦌) ≅
      (bkSkeletalFiltration D 0 : SSet.{max u v}) :=
  (zeroUnitProductIso _).symm ≪≫ zeroWeightedStageIso D

private theorem zeroBarStageIso_hom_inclusion
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    (zeroBarStageIso D).hom ≫ (bkSkeletalFiltration D 0).ι =
      (zeroUnitProductIso _).inv ≫
        diagonalCellMap
            (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D) 0 := by
  simp only [zeroBarStageIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    zeroWeightedStageIso_hom_inclusion]

private def zeroWeightedIndexEquiv (J : Type u) [Category.{v} J] :
    StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) 0 ≃ J where
  toFun p := p.1.left
  invFun j := bkPointWeightedIndex j 0
  left_inv := by
    rintro ⟨c, w⟩
    obtain ⟨j, rfl⟩ := ComposableArrows.mk₀_surjective c
    cases w
    rfl
  right_inv := fun _ => rfl

private def zeroCoefficientBarIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).obj (op ⦋0⦌) ≅
      ∐ (fun j : J => D.obj j) :=
  Sigma.reindex (zeroWeightedIndexEquiv J) (fun j => D.obj j)

private theorem zeroCoefficientBarIso_ι_inv
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (j : J) :
    Sigma.ι (fun j : J => D.obj j) j ≫ (zeroCoefficientBarIso D).inv =
      bkPointOuterComponent D j 0 :=
  Sigma.ι_reindex_inv (zeroWeightedIndexEquiv J) (fun j => D.obj j) (bkPointWeightedIndex j 0)

private def zeroSigmaStageIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    ∐ (fun j : J => D.obj j) ≅ (bkSkeletalFiltration D 0 : SSet.{max u v}) :=
  (zeroCoefficientBarIso D).symm ≪≫ zeroBarStageIso D

private theorem zeroSigmaStageIso_point_inclusion
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (j : J) :
    Sigma.ι (fun j : J => D.obj j) j ≫ (zeroSigmaStageIso D).hom ≫ (bkSkeletalFiltration D 0).ι =
      bkPointInclusion D j := by
  have he : Sigma.ι (fun j : J => D.obj j) j ≫ (zeroSigmaStageIso D).hom ≫
      (bkSkeletalFiltration D 0).ι =
      bkPointOuterComponent D j 0 ≫ (zeroUnitProductIso _).inv ≫
        diagonalCellMap
            (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D) 0 := by
    calc
      Sigma.ι (fun j : J => D.obj j) j ≫ (zeroSigmaStageIso D).hom ≫ (bkSkeletalFiltration D 0).ι =
          (Sigma.ι (fun j : J => D.obj j) j ≫ (zeroCoefficientBarIso D).inv) ≫
            ((zeroBarStageIso D).hom ≫ (bkSkeletalFiltration D 0).ι) := by
              simp only [zeroSigmaStageIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
      _ = bkPointOuterComponent D j 0 ≫ (zeroUnitProductIso _).inv ≫
          diagonalCellMap
              (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D) 0 := by
            rw [zeroCoefficientBarIso_ι_inv, zeroBarStageIso_hom_inclusion]
            rfl
  rw [he]
  ext a x
  obtain ⟨⟨m⟩⟩ := a
  let X := StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D
  let y := (bkPointOuterComponent D j 0).app (op ⦋m⦌) x
  let θ := (stdSimplex.isTerminalObj₀.from (X.obj (op ⦋0⦌))).app (op ⦋m⦌) y
  change (diagonalCellMap X 0).app (op ⦋m⦌) (y, θ) = (bkPointInclusion D j).app (op ⦋m⦌) x
  rw [diagonalCellMap_app_apply, bkPointInclusion_app_mk]
  have hn := (bkPointOuterMap D j).naturality (stdSimplex.objEquiv θ).op
  simp only [bkPointOuterMap_app_mk, SimplicialObject.Data.constData_toSimplicialObject_map] at hn
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hn (op ⦋m⦌)) x).symm

private def zeroTopSigmaStageIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    TopCat.of (Σ j : J, toTop.obj (D.obj j)) ≅
      toTop.obj (bkSkeletalFiltration D 0 : SSet.{max u v}) :=
  (TopCat.sigmaIsoSigma.{u, v} (fun j : J => toTop.obj (D.obj j))).symm ≪≫
    asIso (sigmaComparison toTop (fun j : J => D.obj j)) ≪≫ toTop.mapIso (zeroSigmaStageIso D)

private def zeroTopBaseIso (J : Type u) [Category.{v} J] :
    TopCat.of (Σ j : J, toTop.obj ((bkPointDiagram J).obj j)) ≅
      toTop.obj ((nerve J).skeleton 1 : SSet.{max u v}) :=
  zeroTopSigmaStageIso (bkPointDiagram J) ≪≫ bkNerveSkeletalCellModelIso J 0

private theorem zeroTopSigmaStageIso_point_global
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (j : J) :
    Sigma.ι (fun j : J => toTop.obj (D.obj j)) j ≫
      (TopCat.sigmaIsoSigma.{u, v} (fun j : J => toTop.obj (D.obj j))).hom ≫
        (zeroTopSigmaStageIso D).hom ≫ toTop.map (bkSkeletalFiltration D 0).ι =
          toTop.map (bkPointInclusion D j) := by
  dsimp only [zeroTopSigmaStageIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [ι_comp_sigmaComparison_assoc, ← Functor.map_comp, ← Functor.map_comp,
    zeroSigmaStageIso_point_inclusion]

private theorem pointProjection_eq_iso (J : Type u) [Category.{v} J] :
    bkHocolimToNerve (bkPointDiagram J) = (bkPointIsoNerve J).hom := by
  have h : bkDiagramToPoint (bkPointDiagram J) = 𝟙 (bkPointDiagram J) := by
    apply NatTrans.ext
    funext j
    exact stdSimplex.ext₀
  rw [bkHocolimToNerve, h, bkHocolimMap_id, Category.id_comp]

private theorem zeroTopBaseIso_point_global (J : Type u) [Category.{v} J] (j : J) :
    Sigma.ι (fun j : J => toTop.obj ((bkPointDiagram J).obj j)) j ≫
      (TopCat.sigmaIsoSigma.{u, v} (fun j : J => toTop.obj ((bkPointDiagram J).obj j))).hom ≫
        (zeroTopBaseIso J).hom ≫ toTop.map ((nerve J).skeleton 1).ι =
          TopCat.const (X := toTop.obj ((bkPointDiagram J).obj j)) (bkPointRealizedVertex j) := by
  calc
    Sigma.ι (fun j : J => toTop.obj ((bkPointDiagram J).obj j)) j ≫
        (TopCat.sigmaIsoSigma.{u, v} (fun j : J => toTop.obj ((bkPointDiagram J).obj j))).hom ≫
          (zeroTopBaseIso J).hom ≫ toTop.map ((nerve J).skeleton 1).ι =
      (Sigma.ι (fun j : J => toTop.obj ((bkPointDiagram J).obj j)) j ≫
        (TopCat.sigmaIsoSigma.{u, v} (fun j : J => toTop.obj ((bkPointDiagram J).obj j))).hom ≫
          (zeroTopSigmaStageIso (bkPointDiagram J)).hom ≫
            toTop.map (bkSkeletalFiltration (bkPointDiagram J) 0).ι) ≫
                toTop.map (bkPointIsoNerve J).hom := by
              apply TopCat.ext
              intro x
              exact ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso_hom_ι J 0)
                ((zeroTopSigmaStageIso (bkPointDiagram J)).hom
                  ((TopCat.sigmaIsoSigma.{u, v}
                    (fun j : J => toTop.obj ((bkPointDiagram J).obj j))).hom
                    (Sigma.ι (fun j : J => toTop.obj ((bkPointDiagram J).obj j)) j x)))
    _ = toTop.map (bkPointInclusion (bkPointDiagram J) j) ≫ toTop.map (bkPointIsoNerve J).hom := by
      rw [zeroTopSigmaStageIso_point_global]
    _ = toTop.map (bkPointInclusion (bkPointDiagram J) j) ≫
        toTop.map (bkHocolimToNerve (bkPointDiagram J)) := by
      rw [pointProjection_eq_iso]
    _ = TopCat.const (X := toTop.obj ((bkPointDiagram J).obj j)) (bkPointRealizedVertex j) :=
      bkPointInclusion_realized_projection (bkPointDiagram J) j

private def zeroNativeProjection
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    TopCat.of (Σ j : J, toTop.obj (D.obj j)) ⟶
      TopCat.of (Σ j : J, toTop.obj ((bkPointDiagram J).obj j)) :=
  (TopCat.sigmaIsoSigma.{u, v} (fun j : J => toTop.obj (D.obj j))).inv ≫
    Limits.Sigma.map (fun j => toTop.map ((bkDiagramToPoint D).app j)) ≫
      (TopCat.sigmaIsoSigma.{u, v} (fun j : J => toTop.obj ((bkPointDiagram J).obj j))).hom

open scoped SSet.modelCategoryQuillen in
private theorem everySpace_isFibrant (X : TopCat.{u}) : IsFibrant X := by
  rw [isFibrant_iff, HomotopicalAlgebra.fibration_iff]
  change TopCat.realizedHornInclusions.rlp (terminal.from X)
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp, ← SSet.modelCategoryQuillen.fibration_iff]
  exact (isFibrant_iff_of_isTerminal (C := SSet.{u})
    (TopCat.toSSet.map (terminal.from X))
    (IsTerminal.isTerminalObj TopCat.toSSet (⊤_ TopCat.{u}) terminalIsTerminal)).mp
      (TopCat.toSSet_obj_kanComplex X)

private def realizedZero_isTerminal : IsTerminal (toTop.obj (Δ[0] : SSet.{u})) := by
  let _ : ∀ Y : TopCat.{u}, Unique (Y ⟶ toTop.obj (Δ[0] : SSet.{u})) := fun _ =>
    { default := TopCat.const default
      uniq := by
        intro f
        apply TopCat.ext
        intro y
        exact Subsingleton.elim _ _ }
  exact IsTerminal.ofUnique _

private theorem zeroCoproductReindex_naturality
    {J : Type u} [Category.{v} J] (X Y : J → TopCat.{max u v})
    (q : ∀ j, X j ⟶ Y j) :
    (Sigma.reindex (zeroWeightedIndexEquiv J) X).hom ≫ CategoryTheory.Limits.Sigma.map q =
      CategoryTheory.Limits.Sigma.map (fun p => q (zeroWeightedIndexEquiv J p)) ≫
        (Sigma.reindex (zeroWeightedIndexEquiv J) Y).hom := by
  apply Sigma.hom_ext
  intro p
  let e := zeroWeightedIndexEquiv J
  have hX := Sigma.ι_reindex_hom e X p
  have hY := Sigma.ι_reindex_hom e Y p
  have hQ := CategoryTheory.Limits.Sigma.ι_map q (e p)
  have hSmall := CategoryTheory.Limits.Sigma.ι_map (fun t => q (e t)) p
  exact (Category.assoc (Sigma.ι (X ∘ e) p) (Sigma.reindex e X).hom
      (CategoryTheory.Limits.Sigma.map q)).symm.trans
    ((congrArg (· ≫ CategoryTheory.Limits.Sigma.map q) hX).trans
      (hQ.trans
        ((congrArg (q (e p) ≫ ·) hY.symm).trans
          ((Category.assoc (q (e p)) (Sigma.ι (Y ∘ e) p) (Sigma.reindex e Y).hom).symm.trans
            ((congrArg (· ≫ (Sigma.reindex e Y).hom) hSmall.symm).trans
              (Category.assoc (Sigma.ι (X ∘ e) p)
                (CategoryTheory.Limits.Sigma.map (fun t => q (e t)))
                  (Sigma.reindex e Y).hom))))))

private theorem zeroReindexedSigmaMap_fibration
    {J : Type u} [Category.{v} J] (X Y : J → TopCat.{max u v})
    (q : ∀ j, X j ⟶ Y j) (hq : ∀ j, Fibration (q j)) :
    Fibration (CategoryTheory.Limits.Sigma.map q) := by
  let e := zeroWeightedIndexEquiv J
  let eX := Sigma.reindex e X
  let eY := Sigma.reindex e Y
  have hI : Fibration (CategoryTheory.Limits.Sigma.map (fun p => q (e p))) :=
    TopCat.fibration_sigmaMap (fun p => q (e p)) (fun p => hq (e p))
  have hn : eX.hom ≫ CategoryTheory.Limits.Sigma.map q =
      CategoryTheory.Limits.Sigma.map (fun p => q (e p)) ≫ eY.hom :=
    zeroCoproductReindex_naturality X Y q
  have hp : CategoryTheory.Limits.Sigma.map q =
      eX.inv ≫ CategoryTheory.Limits.Sigma.map (fun p => q (e p)) ≫ eY.hom := by
    exact (Iso.eq_inv_comp eX).mpr hn
  have hX : Fibration eX.inv := inferInstance
  have hY : Fibration eY.hom := inferInstance
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  rw [hp]
  exact (fibrations TopCat.{max u v}).comp_mem _ _ hX.mem
    ((fibrations TopCat.{max u v}).comp_mem _ _ hI.mem hY.mem)

private theorem zeroNativeProjection_fibration
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    Fibration (zeroNativeProjection D) := by
  let X : J → TopCat.{max u v} := fun j => toTop.obj (D.obj j)
  let Y : J → TopCat.{max u v} := fun j => toTop.obj ((bkPointDiagram J).obj j)
  let q : ∀ j, X j ⟶ Y j := fun j => toTop.map ((bkDiagramToPoint D).app j)
  have hq : ∀ j, Fibration (q j) := by
    intro j
    have ht : IsTerminal (Y j) := realizedZero_isTerminal.{max u v}
    exact (isFibrant_iff_of_isTerminal (q j) ht).mp (everySpace_isFibrant (X j))
  have hSigma : Fibration (CategoryTheory.Limits.Sigma.map q) :=
    zeroReindexedSigmaMap_fibration X Y q hq
  let eX := TopCat.sigmaIsoSigma.{u, v} X
  let eY := TopCat.sigmaIsoSigma.{u, v} Y
  have hx : Fibration eX.inv := inferInstance
  have hy : Fibration eY.hom := inferInstance
  have hp : zeroNativeProjection D = eX.inv ≫ CategoryTheory.Limits.Sigma.map q ≫ eY.hom := rfl
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  rw [hp]
  exact (fibrations TopCat.{max u v}).comp_mem _ _ hx.mem
    ((fibrations TopCat.{max u v}).comp_mem _ _ hSigma.mem hy.mem)

private theorem zeroProjection_chart
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    (zeroTopSigmaStageIso D).hom ≫ toTop.map (bkSkeletalProjection D 0) =
      zeroNativeProjection D ≫ (zeroTopBaseIso J).hom := by
  let eX := TopCat.sigmaIsoSigma.{u, v} (fun j : J => toTop.obj (D.obj j))
  let _ : Mono (toTop.map ((nerve J).skeleton 1).ι) := by
    rw [TopCat.mono_iff_injective]
    exact (TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (closedT1Embeddings_toTop_map_of_mono ((nerve J).skeleton 1).ι)).isEmbedding.injective
  apply (cancel_mono (toTop.map ((nerve J).skeleton 1).ι)).mp
  apply (cancel_epi eX.hom).mp
  apply Sigma.hom_ext
  intro j
  have hl : Sigma.ι (fun j : J => toTop.obj (D.obj j)) j ≫ eX.hom ≫
      (zeroTopSigmaStageIso D).hom ≫ toTop.map (bkSkeletalProjection D 0) ≫
        toTop.map ((nerve J).skeleton 1).ι =
          TopCat.const (X := toTop.obj (D.obj j)) (bkPointRealizedVertex j) := by
    calc
      Sigma.ι (fun j : J => toTop.obj (D.obj j)) j ≫ eX.hom ≫
          (zeroTopSigmaStageIso D).hom ≫ toTop.map (bkSkeletalProjection D 0) ≫
            toTop.map ((nerve J).skeleton 1).ι =
        (Sigma.ι (fun j : J => toTop.obj (D.obj j)) j ≫ eX.hom ≫
          (zeroTopSigmaStageIso D).hom ≫ toTop.map (bkSkeletalFiltration D 0).ι) ≫
            toTop.map
                (bkHocolimToNerve D) := by rw [projection_comp_global]; simp only [Category.assoc]
      _ = toTop.map (bkPointInclusion D j) ≫ toTop.map (bkHocolimToNerve D) := by
        rw [zeroTopSigmaStageIso_point_global]
      _ = TopCat.const (X := toTop.obj (D.obj j)) (bkPointRealizedVertex j) :=
        bkPointInclusion_realized_projection D j
  have hr : Sigma.ι (fun j : J => toTop.obj (D.obj j)) j ≫ eX.hom ≫
      zeroNativeProjection D ≫ (zeroTopBaseIso J).hom ≫ toTop.map ((nerve J).skeleton 1).ι =
        TopCat.const (X := toTop.obj (D.obj j)) (bkPointRealizedVertex j) := by
    dsimp only [zeroNativeProjection, eX]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Limits.Sigma.ι_map_assoc]
    rw [zeroTopBaseIso_point_global]
    apply TopCat.ext
    intro x
    rfl
  simpa only [Category.assoc] using hl.trans hr.symm

private theorem zeroProjection_fibration
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    Fibration (toTop.map (bkSkeletalProjection D 0)) := by
  let _ : Fibration (zeroNativeProjection D) := zeroNativeProjection_fibration D
  have hp : toTop.map (bkSkeletalProjection D 0) =
      (zeroTopSigmaStageIso D).inv ≫ zeroNativeProjection D ≫ (zeroTopBaseIso J).hom := by
    calc
      toTop.map (bkSkeletalProjection D 0) =
        (zeroTopSigmaStageIso D).inv ≫ (zeroTopSigmaStageIso D).hom ≫
          toTop.map (bkSkeletalProjection D 0) := by simp
      _ = (zeroTopSigmaStageIso D).inv ≫ zeroNativeProjection D ≫ (zeroTopBaseIso J).hom := by
        rw [zeroProjection_chart]
  rw [hp]
  infer_instance

private theorem zeroProjectionComparison_mem
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v})
    (b : toTop.obj ((nerve J).skeleton 1 : SSet.{max u v})) :
    TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber (toTop.map (bkSkeletalProjection D 0)) b) := by
  let _ : Fibration (toTop.map (bkSkeletalProjection D 0)) := zeroProjection_fibration D
  exact TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences _ b

/-- Every actual original skeletal projection has weak canonical
strict-to-homotopy-fiber comparisons when all diagram arrows realize weakly.
The proof derives the zero, punctured and interior comparisons and applies
the complete two-open-set criterion at each successor stage. -/
theorem bkSkeletalProjection_strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v})
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (n : ℕ) (b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) :
    TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber (toTop.map (bkSkeletalProjection D n)) b) := by
  revert b
  induction n with
  | zero => exact zeroProjectionComparison_mem D
  | succ n ih => exact successorComparison_mem D n hD ih

private theorem canonicalSkeletalPullbackComparison_mem
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v})
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (n : ℕ) (b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) :
    TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (pullback.snd (toTop.map (bkHocolimToNerve D)) (toTop.map ((nerve J).skeleton (n + 1)).ι))
          b) := by
  let q := pullback.snd (toTop.map (bkHocolimToNerve D)) (toTop.map ((nerve J).skeleton (n + 1)).ι)
  let s := (bkSkeletalRestrictionIso D n).inv
  have comm : q ≫ 𝟙 _ = s ≫ toTop.map (bkSkeletalProjection D n) := by
    simpa only [Category.comp_id] using (bkSkeletalRestrictionIso_inv_snd D n).symm
  have sq : IsPullback s q (toTop.map (bkSkeletalProjection D n)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨comm.symm⟩
  let _ : IsIso (TopCat.strictFiberMapOfSquare s (𝟙 _) comm b) :=
    TopCat.isIso_strictFiberMapOfSquare_of_isPullback sq b
  exact TopCat.strictFiberToHomotopyFiber_mem_of_square s (𝟙 _) comm b
    (TopCat.weakHomotopyEquivalences.of_isIso _) (TopCat.weakHomotopyEquivalences.of_isIso _)
    (TopCat.weakHomotopyEquivalences.of_isIso _)
    (bkSkeletalProjection_strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences D hD n b)

/-- The actual realized BK projection has weak canonical strict-to-homotopy
fiber comparisons at every original nerve point. This uses the proved
skeletal comparisons and the actual compact-controlled skeletal descent. -/
theorem bkHocolimToNerve_strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v})
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (b : toTop.obj (nerve J)) :
    TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber (toTop.map (bkHocolimToNerve D)) b) :=
  TopCat.strictFiberToHomotopyFiber_mem_of_skeletons (toTop.map (bkHocolimToNerve D))
    (canonicalSkeletalPullbackComparison_mem D hD) b

/-- The BK point-fiber theorem for the actual constant-chain, constant-path
comparison. The sole geometric hypothesis is realized weakness of every
diagram arrow; local products, radial endpoint weakness and all skeletal
comparisons are derived in the proof. -/
theorem bkPointFiberComparison_mem_weakHomotopyEquivalences
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v})
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (j : J) : TopCat.weakHomotopyEquivalences (bkPointFiberComparison D j) := by
  rw [← bkPointStrictFiberIso_hom_comp_strictFiberToHomotopyFiber]
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ (TopCat.weakHomotopyEquivalences.of_isIso _)
    (bkHocolimToNerve_strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences D hD
        (bkPointRealizedVertex j))

end SSet
