/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanCellRestriction
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import MathlibExt.Topology.Convenient.StdSimplexRadialBoundary
import MathlibExt.Topology.Category.TopCat.QuotientHomotopy
import MathlibExt.Topology.Category.TopCat.HomotopyFiberRestriction

/-!
# Actual BK cell radial deformations

This module constructs the actual base and total interior charts, the
punctured-attachment radial retractions, and their compatible homotopies.
It retains the original skeletal projection and closed-cell endpoint maps,
including degenerate faces. Dimension-decreasing normalization constructs
one endpoint arrow uniformly for every coefficient diagram.

The all-dimensional strict-fiber charts retain the original nerve target.
The actual radial endpoint fiber map is weak when every diagram transition
realizes to a weak equivalence. Local product comparisons and the full BK
skeletal induction remain separate obligations.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Topology
open scoped Simplicial

universe u v

namespace SSet

private theorem bkPointProjection_eq_iso (J : Type u) [Category.{v} J] :
    bkHocolimToNerve (bkPointDiagram J) = (bkPointIsoNerve J).hom := by
  have h : bkDiagramToPoint (bkPointDiagram J) = 𝟙 (bkPointDiagram J) := by
    apply NatTrans.ext
    funext j
    exact stdSimplex.ext₀
  rw [bkHocolimToNerve, h, bkHocolimMap_id, Category.id_comp]

private theorem bkPointSkeletalProjection_isIso (J : Type u) [Category.{v} J] (n : ℕ) :
    IsIso (bkSkeletalProjection (bkPointDiagram J) n) := by
  have hi : IsIso (bkHocolimToNerve (bkPointDiagram J)) := by
    rw [bkPointProjection_eq_iso]
    infer_instance
  exact (bkSkeletalProjection_isPullback (bkPointDiagram J) n).isIso_snd_of_isIso hi

/-- The actual point-diagram cell model is isomorphic to the original
realized nerve skeleton through its canonical skeletal projection. -/
def bkNerveSkeletalCellModelIso (J : Type u) [Category.{v} J] (n : ℕ) :
    toTop.obj (bkSkeletalFiltration (bkPointDiagram J) n : SSet.{max u v}) ≅
      toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v}) := by
  let _ : IsIso (bkSkeletalProjection (bkPointDiagram J) n) :=
    bkPointSkeletalProjection_isIso J n
  exact asIso (toTop.map (bkSkeletalProjection (bkPointDiagram J) n))

private theorem bkNerveSkeletalCellModelIso_hom_ι_aux
    (J : Type u) [Category.{v} J] (n : ℕ) :
    (bkNerveSkeletalCellModelIso J n).hom ≫ toTop.map ((nerve J).skeleton (n + 1)).ι =
      toTop.map (bkSkeletalFiltration (bkPointDiagram J) n).ι ≫ toTop.map (bkPointIsoNerve J).hom
        := by
  have h := congrArg toTop.map (bkSkeletalProjection_comp_ι (bkPointDiagram J) n)
  rw [Functor.map_comp, Functor.map_comp, bkPointProjection_eq_iso] at h
  exact h

/-- The cell model retains the original nerve inclusion after the actual
point-carrier isomorphism; this characteristic does not unfold its value. -/
@[reassoc]
theorem bkNerveSkeletalCellModelIso_hom_ι
    (J : Type u) [Category.{v} J] (n : ℕ) :
    (bkNerveSkeletalCellModelIso J n).hom ≫ toTop.map ((nerve J).skeleton (n + 1)).ι =
      toTop.map (bkSkeletalFiltration (bkPointDiagram J) n).ι ≫ toTop.map (bkPointIsoNerve J).hom :=
  bkNerveSkeletalCellModelIso_hom_ι_aux J n

private def pointCellCoefficient (J : Type u) [Category.{v} J] (j : J) :
    toTop.obj ((bkPointDiagram J).obj j) := by
  change toTop.obj (Δ[0] : SSet.{max u v})
  exact default

/-- The actual nerve characteristic cell in its realized skeleton. A native
continuous map permits its zero-universe simplex domain and arbitrary
indexing-object universe. -/
def bkNerveSkeletalCell (J : Type u) [Category.{v} J] {n : ℕ}
    (c : ComposableArrows J n) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)),
      toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) where
  toFun t := (bkNerveSkeletalCellModelIso J n).hom
    (bkRealizedChainCellToStage (bkPointDiagram J) c (pointCellCoefficient J c.left, t))
  continuous_toFun := (bkNerveSkeletalCellModelIso J n).hom.hom.continuous.comp
    ((bkRealizedChainCellToStage (bkPointDiagram J) c).hom.continuous.comp
      (continuous_const.prodMk continuous_id))

/-- The native skeletal cell has the original characteristic map as its
literal coordinate in the original nerve realization. -/
theorem bkNerveSkeletalCell_ι_apply (J : Type u) [Category.{v} J] {n : ℕ}
    (c : ComposableArrows J n) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    toTop.map ((nerve J).skeleton (n + 1)).ι (bkNerveSkeletalCell J c t) =
      toTop.map (yonedaEquiv.symm c : (Δ[n] : SSet.{max u v}) ⟶ nerve J)
        ((SimplexCategory.toTopHomeo.{max u v} ⦋n⦌).symm t) := by
  let x := pointCellCoefficient J c.left
  have hm := ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso_hom_ι J n)
    (bkRealizedChainCellToStage (bkPointDiagram J) c (x, t))
  have hc := ConcreteCategory.congr_hom
    (bkRealizedChainCellToStage_ι (bkPointDiagram J) c) (x, t)
  have hp := bkRealizedChainCell_projection_apply (bkPointDiagram J) c x t
  have he := ConcreteCategory.congr_hom (congrArg toTop.map (bkPointProjection_eq_iso J))
    (bkRealizedChainCell (bkPointDiagram J) c (x, t))
  exact hm.trans ((congrArg (fun q => toTop.map (bkPointIsoNerve J).hom q) hc).trans
    (he.symm.trans hp))

/-- The actual inclusion between realized nerve skeleta. -/
def bkNerveSkeletalMap (J : Type u) [Category.{v} J] {m n : ℕ} (h : m ≤ n) :
    toTop.obj ((nerve J).skeleton (m + 1) : SSet.{max u v}) ⟶
      toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v}) :=
  toTop.map (Subcomplex.homOfLE ((nerve J).skeleton.monotone (Nat.add_le_add_right h 1)))

private theorem bkNerveSkeletalMap_ι_aux
    (J : Type u) [Category.{v} J] {m n : ℕ} (h : m ≤ n) :
    bkNerveSkeletalMap J h ≫ toTop.map ((nerve J).skeleton (n + 1)).ι =
      toTop.map ((nerve J).skeleton (m + 1)).ι := by
  dsimp only [bkNerveSkeletalMap]
  rw [← Functor.map_comp, Subcomplex.homOfLE_ι]

@[reassoc]
theorem bkNerveSkeletalMap_ι
    (J : Type u) [Category.{v} J] {m n : ℕ} (h : m ≤ n) :
    bkNerveSkeletalMap J h ≫ toTop.map ((nerve J).skeleton (n + 1)).ι =
      toTop.map ((nerve J).skeleton (m + 1)).ι :=
  bkNerveSkeletalMap_ι_aux J h

/-- The point-diagram cell models commute with the actual inclusions of
the original nerve skeleta. -/
@[reassoc]
theorem bkNerveSkeletalCellModelIso_natural
    (J : Type u) [Category.{v} J] {m n : ℕ} (h : m ≤ n) :
    toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) h) ≫
      (bkNerveSkeletalCellModelIso J n).hom =
    (bkNerveSkeletalCellModelIso J m).hom ≫ bkNerveSkeletalMap J h := by
  apply TopCat.ext
  intro x
  have hi := (TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (closedT1Embeddings_toTop_map_of_mono ((nerve J).skeleton (n + 1)).ι)).isEmbedding.injective
  apply hi
  have hm := congrArg toTop.map (bkSkeletalFiltrationMap_ι (bkPointDiagram J) h)
  simp only [Functor.map_comp] at hm
  have hl := ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso_hom_ι J n)
    (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) h) x)
  have hl' := ConcreteCategory.congr_hom hm x
  have hr := ConcreteCategory.congr_hom (bkNerveSkeletalMap_ι J h)
    ((bkNerveSkeletalCellModelIso J m).hom x)
  have hr' := ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso_hom_ι J m) x
  exact (hl.trans (congrArg (fun q => toTop.map (bkPointIsoNerve J).hom q) hl')).trans
    (hr.trans hr').symm

private theorem bkNerveSkeletalCellModelIso_mem_range_iff
    (J : Type u) [Category.{v} J] (n : ℕ)
    (x : toTop.obj (bkSkeletalFiltration (bkPointDiagram J) (n + 1) : SSet.{max u v})) :
    (bkNerveSkeletalCellModelIso J (n + 1)).hom x ∈
      Set.range (bkNerveSkeletalMap J (Nat.le_succ n)) ↔
    x ∈ Set.range (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) (Nat.le_succ n))) := by
  have h := bkNerveSkeletalCellModelIso_natural J (Nat.le_succ n)
  constructor
  · rintro ⟨y, hy⟩
    let z := (bkNerveSkeletalCellModelIso J n).inv y
    have hz : (bkNerveSkeletalCellModelIso J n).hom z = y :=
      ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso J n).inv_hom_id y
    refine ⟨z, (TopCat.homeoOfIso (bkNerveSkeletalCellModelIso J (n + 1))).injective ?_⟩
    exact (ConcreteCategory.congr_hom h z).trans
      ((congrArg (fun q => bkNerveSkeletalMap J (Nat.le_succ n) q) hz).trans hy)
  · rintro ⟨z, rfl⟩
    exact ⟨(bkNerveSkeletalCellModelIso J n).hom z,
      (ConcreteCategory.congr_hom h z).symm⟩

private theorem bkNerveSkeletalCellModelIso_image_compl
    (J : Type u) [Category.{v} J] (n : ℕ) :
    (TopCat.homeoOfIso (bkNerveSkeletalCellModelIso J (n + 1))) ''
      (Set.range (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) (Nat.le_succ n))))ᶜ =
    (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact fun hy => hx ((bkNerveSkeletalCellModelIso_mem_range_iff J n x).mp hy)
  · intro hy
    let x := (bkNerveSkeletalCellModelIso J (n + 1)).inv y
    have hx : (bkNerveSkeletalCellModelIso J (n + 1)).hom x = y :=
      ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso J (n + 1)).inv_hom_id y
    refine ⟨x, ?_, hx⟩
    intro hbad
    exact hy (hx ▸ (bkNerveSkeletalCellModelIso_mem_range_iff J n x).mpr hbad)

private abbrev nativeNerveCellInteriors (J : Type u) [Category.{v} J] (n : ℕ) :=
  Σ _c : (nerve J).nonDegenerate (n + 1),
    {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}

private abbrev pointNativeCellInteriors (J : Type u) [Category.{v} J] (n : ℕ) :=
  Σ c : (nerve J).nonDegenerate (n + 1),
    toTop.obj ((bkPointDiagram J).obj c.1.left) ×
      {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}

private def forgetPointCellCoefficient (J : Type u) [Category.{v} J] (n : ℕ) :
    pointNativeCellInteriors J n → nativeNerveCellInteriors J n :=
  Sigma.map id (fun _ => Prod.snd)

private theorem forgetPointCellCoefficient_isHomeomorph
    (J : Type u) [Category.{v} J] (n : ℕ) :
    IsHomeomorph (forgetPointCellCoefficient J n) := by
  apply IsHomeomorph.sigmaMap Function.bijective_id
  intro c
  let _ : Unique (toTop.obj ((bkPointDiagram J).obj c.1.left)) := by
    change Unique (toTop.obj (Δ[0] : SSet.{max u v}))
    infer_instance
  exact (Homeomorph.uniqueProd (toTop.obj ((bkPointDiagram J).obj c.1.left))
    {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}).isHomeomorph

private def pointCellCoefficientHomeomorph (J : Type u) [Category.{v} J] (n : ℕ) :
    pointNativeCellInteriors J n ≃ₜ nativeNerveCellInteriors J n :=
  (forgetPointCellCoefficient_isHomeomorph J n).homeomorph (forgetPointCellCoefficient J n)

private def nerveCellInteriorHomeomorph (J : Type u) [Category.{v} J] (n : ℕ) :
    nativeNerveCellInteriors J n ≃ₜ ↥((Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ) :=
  (pointCellCoefficientHomeomorph J n).symm.trans
    ((TopCat.homeoOfIso (bkNondegenerateCellInteriorProductIso (bkPointDiagram J) n)).trans
      (((TopCat.homeoOfIso (bkNerveSkeletalCellModelIso J (n + 1))).image
        (Set.range (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) (Nat.le_succ n))))ᶜ).trans
          (Homeomorph.setCongr (bkNerveSkeletalCellModelIso_image_compl J n))))

/-- The actual new part of the realized nerve skeleton is the native
disjoint union of its positive-coordinate simplex interiors. -/
def bkNerveSkeletalCellInteriorIso (J : Type u) [Category.{v} J] (n : ℕ) :
    TopCat.of (Σ _c : (nerve J).nonDegenerate (n + 1),
      {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) ≅
      TopCat.of ↥((Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ) :=
  TopCat.isoOfHomeo (nerveCellInteriorHomeomorph J n)

private theorem pointCellCoefficientHomeomorph_symm_apply
    (J : Type u) [Category.{v} J] (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (t : {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :
    (pointCellCoefficientHomeomorph J n).symm ⟨c, t⟩ =
      ⟨c, pointCellCoefficient J c.1.left, t⟩ := by
  apply (pointCellCoefficientHomeomorph J n).injective
  exact (pointCellCoefficientHomeomorph J n).apply_symm_apply ⟨c, t⟩

private theorem bkNerveSkeletalCellInteriorIso_hom_aux
    (J : Type u) [Category.{v} J] (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (t : {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :
    ((bkNerveSkeletalCellInteriorIso J n).hom ⟨c, t⟩).1 =
      (bkNerveSkeletalCellModelIso J (n + 1)).hom
        (((bkNondegenerateCellInteriorProductIso (bkPointDiagram J) n).hom
          ((pointCellCoefficientHomeomorph J n).symm ⟨c, t⟩)).1) := rfl

/-- The actual base interior chart is the original nerve characteristic
cell at the given positive coordinate. -/
theorem bkNerveSkeletalCellInteriorIso_hom_apply
    (J : Type u) [Category.{v} J] (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (t : {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :
    ((bkNerveSkeletalCellInteriorIso J n).hom ⟨c, t⟩).1 =
      bkNerveSkeletalCell J c.1 t.1 := by
  have h := bkNerveSkeletalCellInteriorIso_hom_aux J n c t
  rw [pointCellCoefficientHomeomorph_symm_apply] at h
  have hc := bkNondegenerateCellInteriorProductIso_hom_apply (bkPointDiagram J) n c
    (pointCellCoefficient J c.1.left) t
  exact h.trans (congrArg (fun q => (bkNerveSkeletalCellModelIso J (n + 1)).hom q) hc)

/-- The original skeletal projection of the actual realized coefficient
cell is the original base skeletal cell at its native coordinate. -/
theorem bkRealizedChainCellToStage_projection_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : ComposableArrows J n) (x : toTop.obj (D.obj c.left))
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    toTop.map (bkSkeletalProjection D n) (bkRealizedChainCellToStage D c (x, t)) =
      bkNerveSkeletalCell J c t := by
  have hi := (TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (closedT1Embeddings_toTop_map_of_mono ((nerve J).skeleton (n + 1)).ι)).isEmbedding.injective
  apply hi
  have hm := congrArg toTop.map (bkSkeletalProjection_comp_ι D n)
  simp only [Functor.map_comp] at hm
  have hp := ConcreteCategory.congr_hom hm (bkRealizedChainCellToStage D c (x, t))
  have hc := ConcreteCategory.congr_hom (bkRealizedChainCellToStage_ι D c) (x, t)
  exact (hp.trans ((congrArg (fun q => toTop.map (bkHocolimToNerve D) q) hc).trans
    (bkRealizedChainCell_projection_apply D c x t))).trans
      (bkNerveSkeletalCell_ι_apply J c t).symm

private theorem skeletalProjection_mem_baseInterior
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (q : ↥((Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ)) :
    toTop.map (bkSkeletalProjection D (n + 1)) q.1 ∈
      (Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ := by
  let e := bkNondegenerateCellInteriorProductIso D n
  let z := e.inv q
  have hz : e.hom z = q := ConcreteCategory.congr_hom e.inv_hom_id q
  obtain ⟨c, x, t⟩ := z
  have ht := bkNondegenerateCellInteriorProductIso_hom_apply D n c x t
  have hp := bkRealizedChainCellToStage_projection_apply D c.1 x t.1
  have hb := bkNerveSkeletalCellInteriorIso_hom_apply J n c t
  have heq : toTop.map (bkSkeletalProjection D (n + 1)) q.1 =
      ((bkNerveSkeletalCellInteriorIso J n).hom ⟨c, t⟩).1 := by
    have hq : (e.hom ⟨c, x, t⟩).1 = q.1 := congrArg Subtype.val hz
    exact (congrArg (fun y => toTop.map (bkSkeletalProjection D (n + 1)) y) hq).symm.trans
      ((congrArg (fun y => toTop.map (bkSkeletalProjection D (n + 1)) y) ht).trans
        (hp.trans hb.symm))
  exact heq.symm ▸ ((bkNerveSkeletalCellInteriorIso J n).hom ⟨c, t⟩).2

/-- The actual skeletal projection restricted to the new-cell interiors. -/
def bkSkeletalInteriorProjection {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    TopCat.of ↥((Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ) ⟶
      TopCat.of ↥((Set.range (bkNerveSkeletalMap J (Nat.le_succ n)))ᶜ) :=
  TopCat.ofHom
    ⟨fun q => ⟨toTop.map (bkSkeletalProjection D (n + 1)) q.1,
        skeletalProjection_mem_baseInterior D n q⟩,
      ((toTop.map (bkSkeletalProjection D (n + 1))).hom.continuous.comp
        continuous_subtype_val).subtype_mk _⟩

/-- The native interior product projection retains the exact chain and
drops only the coefficient coordinate. -/
def bkNativeCellInteriorProjection {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    TopCat.of (Σ c : (nerve J).nonDegenerate (n + 1),
      toTop.obj (D.obj c.1.left) ×
        {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) ⟶
      TopCat.of (Σ _c : (nerve J).nonDegenerate (n + 1),
        {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :=
  TopCat.ofHom ⟨Sigma.map id (fun _ => Prod.snd),
    continuous_sigma (fun _ => continuous_sigmaMk.comp continuous_snd)⟩

/-- The two actual interior charts commute with the original skeletal
projection and the native disjoint product projection. -/
@[reassoc]
theorem bkSkeletalInteriorProjection_chart
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkNondegenerateCellInteriorProductIso D n).hom ≫ bkSkeletalInteriorProjection D n =
      bkNativeCellInteriorProjection D n ≫ (bkNerveSkeletalCellInteriorIso J n).hom := by
  apply TopCat.ext
  rintro ⟨c, x, t⟩
  apply Subtype.ext
  have ht := bkNondegenerateCellInteriorProductIso_hom_apply D n c x t
  have hp := bkRealizedChainCellToStage_projection_apply D c.1 x t.1
  have hb := bkNerveSkeletalCellInteriorIso_hom_apply J n c t
  exact (congrArg (fun y => toTop.map (bkSkeletalProjection D (n + 1)) y) ht).trans
    (hp.trans hb.symm)

private abbrev nativeCoefficientCells {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :=
  Σ c : (nerve J).nonDegenerate (n + 1),
    toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 2))

private def nativeCoefficientCellStageMap {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    TopCat.of (nativeCoefficientCells D n) ⟶
      toTop.obj (bkSkeletalFiltration D (n + 1) : SSet.{max u v}) :=
  (bkNondegenerateCellsProductIso D (n + 1)).inv ≫
    toTop.map (bkNondegenerateCellToStage D (n + 1))

private theorem nativeCoefficientCellStageMap_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (t : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    nativeCoefficientCellStageMap D n ⟨c, x, t⟩ =
      bkRealizedChainCellToStage D c.1 (x, t) := by
  have hr := ConcreteCategory.congr_hom (bkRealizedChainCellToStage_eq D c.1) (x, t)
  have hi := bkNondegenerateCellsProductIso_inv_cell_apply D (n + 1) c x t
  have hcell : Sigma.ι (fun c : (nerve J).nonDegenerate (n + 1) =>
      D.obj c.1.left ⊗ (Δ[n + 1] : SSet.{max u v})) c ≫
      bkNondegenerateCellToStage D (n + 1) = bkChainCellToStage D c.1 := by
    apply (cancel_mono (bkSkeletalFiltration D (n + 1)).ι).mp
    rw [Category.assoc, bkNondegenerateCellToStage_ι, bkNondegenerateCellMap_ι]
    exact (bkChainCellToStage_ι D c.1).symm
  have hm := congrArg toTop.map hcell
  simp only [Functor.map_comp] at hm
  exact ((congrArg (fun q => toTop.map (bkNondegenerateCellToStage D (n + 1)) q) hi).trans
    (ConcreteCategory.congr_hom hm ((bkChainCellProductIso D c.1).inv (x, t)))).trans hr.symm

private def nativeCoefficientAttachmentQuotient
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    C(toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}) ⊕ nativeCoefficientCells D n,
      toTop.obj (bkSkeletalFiltration D (n + 1) : SSet.{max u v})) :=
  ⟨Sum.elim (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n)))
      (nativeCoefficientCellStageMap D n),
    Continuous.sumElim (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))).hom.continuous
      (nativeCoefficientCellStageMap D n).hom.continuous⟩

private theorem nativeCoefficientAttachmentQuotient_isQuotientMap
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsQuotientMap (nativeCoefficientAttachmentQuotient D n) := by
  have hq := TopCat.isQuotientMap_sumElim_of_isPushout
    (bkSkeletalFiltrationSucc_nonDegenerate_realized_isPushout D n)
  let e := (Homeomorph.refl (toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}))).sumCongr
    (TopCat.homeoOfIso (bkNondegenerateCellsProductIso D (n + 1))).symm
  convert hq.comp e.isQuotientMap using 1
  ext z
  cases z <;> rfl

private theorem simplexBarycenter_weights_pos (n : ℕ) (i : Fin (n + 2)) :
    0 < (Convexity.StdSimplex.barycenter :
      Convexity.StdSimplex ℝ (Fin (n + 2))).weights i := by
  rw [Convexity.StdSimplex.weights_barycenter_apply, Fintype.card_fin]
  exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.zero_lt_succ (n + 1)))

private theorem nativeBarycenter_not_mem_boundary
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left)) :
    (bkNondegenerateCellsProductIso D (n + 1)).inv ⟨c, x, Convexity.StdSimplex.barycenter⟩ ∉
      Set.range (toTop.map (bkNondegenerateCellBoundaryInclusion D (n + 1))) := by
  rw [bkNondegenerateCellsProductIso_inv_mem_boundary_iff]
  rintro ⟨i, hi⟩
  exact (ne_of_gt (simplexBarycenter_weights_pos n i)) hi

private def coefficientCellCenters {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Set (toTop.obj (bkSkeletalFiltration D (n + 1) : SSet.{max u v})) :=
  Set.range (fun z : Σ c : (nerve J).nonDegenerate (n + 1),
      toTop.obj (D.obj c.1.left) =>
    nativeCoefficientCellStageMap D n ⟨z.1, z.2, Convexity.StdSimplex.barycenter⟩)

private theorem oldStage_not_mem_coefficientCellCenters
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (x : toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) :
    toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n)) x ∉ coefficientCellCenters D n := by
  rintro ⟨⟨c, y⟩, hy⟩
  exact (Types.pushoutCocone_inl_ne_inr_of_not_mem_range_of_isColimit
    ((bkSkeletalFiltrationSucc_nonDegenerate_realized_isPushout D n).map
      (forget TopCat)).isColimit (nativeBarycenter_not_mem_boundary D n c y)) hy.symm

private theorem nativeCoefficientCell_mem_centers_iff
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : nativeCoefficientCells D n) :
    nativeCoefficientCellStageMap D n z ∈ coefficientCellCenters D n ↔
      z.2.2 = Convexity.StdSimplex.barycenter := by
  constructor
  · rintro ⟨⟨c, x⟩, hx⟩
    have he := Types.pushoutCocone_inr_eq_inr_of_not_mem_range_of_isColimit
      ((bkSkeletalFiltrationSucc_nonDegenerate_realized_isPushout D n).map
        (forget TopCat)).isColimit (nativeBarycenter_not_mem_boundary D n c x) hx
    have hnative := (TopCat.homeoOfIso (bkNondegenerateCellsProductIso D (n + 1))).symm.injective he
    exact congrArg (fun q : nativeCoefficientCells D n => q.2.2) hnative.symm
  · intro hz
    refine ⟨⟨z.1, z.2.1⟩, ?_⟩
    obtain ⟨c, x, t⟩ := z
    dsimp only at hz
    subst t
    rfl

private theorem coefficientCellCenters_isClosed
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsClosed (coefficientCellCenters D n) := by
  apply (nativeCoefficientAttachmentQuotient_isQuotientMap D n).isCoinducing.isClosed_preimage.mp
  rw [isClosed_sum_iff]
  constructor
  · have h : (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))) ⁻¹'
      coefficientCellCenters D n = ∅ := by
      ext x
      exact iff_false_intro (oldStage_not_mem_coefficientCellCenters D n x)
    change IsClosed ((toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))) ⁻¹'
      coefficientCellCenters D n)
    rw [h]
    exact isClosed_empty
  · change IsClosed ((nativeCoefficientCellStageMap D n) ⁻¹' coefficientCellCenters D n)
    rw [isClosed_sigma_iff]
    intro c
    have h : (Sigma.mk c) ⁻¹' ((nativeCoefficientCellStageMap D n) ⁻¹'
        coefficientCellCenters D n) =
        Prod.snd ⁻¹' {Convexity.StdSimplex.barycenter} := by
      ext z
      exact nativeCoefficientCell_mem_centers_iff D n ⟨c, z⟩
    rw [h]
    have hc : IsClosed ({Convexity.StdSimplex.barycenter} :
        Set (Convexity.StdSimplex ℝ (Fin (n + 2)))) := by
      have he : ({Convexity.StdSimplex.barycenter} :
          Set (Convexity.StdSimplex ℝ (Fin (n + 2)))) =
          ⋂ i : Fin (n + 2), {t | t.weights i =
            (Convexity.StdSimplex.barycenter : Convexity.StdSimplex ℝ (Fin (n + 2))).weights i} :=
              by
        ext t
        simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
        exact ⟨fun ht i => congrArg (fun q => q.weights i) ht,
          fun ht => by
            apply Convexity.StdSimplex.ext
            ext i
            exact ht i⟩
      rw [he]
      exact isClosed_iInter (fun i => isClosed_eq
        (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i) continuous_const)
    exact hc.preimage continuous_snd

private abbrev puncturedNativeCoefficientCells {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :=
  {z : nativeCoefficientCells D n // z.2.2 ≠ Convexity.StdSimplex.barycenter}

private abbrev puncturedCoefficientStage {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) := ↥((coefficientCellCenters D n)ᶜ)

private abbrev puncturedAttachmentSource {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :=
  toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}) ⊕ puncturedNativeCoefficientCells D n

private def puncturedAttachmentSourceInclusion
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    puncturedAttachmentSource D n →
      ↥((nativeCoefficientAttachmentQuotient D n) ⁻¹' (coefficientCellCenters D n)ᶜ) :=
  Sum.elim
    (fun x => ⟨Sum.inl x, oldStage_not_mem_coefficientCellCenters D n x⟩)
    (fun z => ⟨Sum.inr z.1, fun hz => z.2
      ((nativeCoefficientCell_mem_centers_iff D n z.1).mp hz)⟩)

private theorem puncturedNativeCoefficientCells_isOpen
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsOpen ({z | z.2.2 ≠ Convexity.StdSimplex.barycenter} : Set (nativeCoefficientCells D n)) := by
  have h := (coefficientCellCenters_isClosed D n).isOpen_compl.preimage
    (nativeCoefficientCellStageMap D n).hom.continuous
  have he : (nativeCoefficientCellStageMap D n) ⁻¹' (coefficientCellCenters D n)ᶜ =
      {z | z.2.2 ≠ Convexity.StdSimplex.barycenter} := by
    ext z
    exact not_congr (nativeCoefficientCell_mem_centers_iff D n z)
  exact he ▸ h

private theorem puncturedAttachmentSourceInclusion_isOpenEmbedding
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsOpenEmbedding (puncturedAttachmentSourceInclusion D n) := by
  have hi : IsOpenEmbedding (Sum.map
      (id : toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}) →
        toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}))
      (Subtype.val : puncturedNativeCoefficientCells D n → nativeCoefficientCells D n)) := by
    apply IsOpenEmbedding.inl.sumElim
      (IsOpenEmbedding.inr.comp (puncturedNativeCoefficientCells_isOpen D
        n).isOpenEmbedding_subtypeVal)
    exact Sum.map_injective.mpr ⟨Function.injective_id, Subtype.val_injective⟩
  have hpre := (coefficientCellCenters_isClosed D n).isOpen_compl.preimage
    (nativeCoefficientAttachmentQuotient D n).continuous
  have he : Subtype.val ∘ puncturedAttachmentSourceInclusion D n =
      Sum.map id Subtype.val := by
    funext z
    cases z <;> rfl
  apply IsOpenEmbedding.of_comp (puncturedAttachmentSourceInclusion D n)
    hpre.isOpenEmbedding_subtypeVal
  rw [he]
  exact hi

private theorem puncturedAttachmentSourceInclusion_surjective
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Function.Surjective (puncturedAttachmentSourceInclusion D n) := by
  rintro ⟨x | z, hx⟩
  · exact ⟨Sum.inl x, rfl⟩
  · refine ⟨Sum.inr ⟨z, ?_⟩, rfl⟩
    intro hz
    exact hx ((nativeCoefficientCell_mem_centers_iff D n z).mpr hz)

private def puncturedAttachmentSourceHomeomorph
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    puncturedAttachmentSource D n ≃ₜ
      ↥((nativeCoefficientAttachmentQuotient D n) ⁻¹' (coefficientCellCenters D n)ᶜ) :=
  (Equiv.ofBijective (puncturedAttachmentSourceInclusion D n)
    ⟨(puncturedAttachmentSourceInclusion_isOpenEmbedding D n).injective,
      puncturedAttachmentSourceInclusion_surjective D n⟩).toHomeomorphOfContinuousOpen
        (puncturedAttachmentSourceInclusion_isOpenEmbedding D n).continuous
        (puncturedAttachmentSourceInclusion_isOpenEmbedding D n).isOpenMap

private def puncturedAttachmentQuotient
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    C(puncturedAttachmentSource D n, puncturedCoefficientStage D n) :=
  ⟨fun z => ((coefficientCellCenters D n)ᶜ).restrictPreimage
      (nativeCoefficientAttachmentQuotient D n) (puncturedAttachmentSourceInclusion D n z),
    (nativeCoefficientAttachmentQuotient D n).continuous.restrictPreimage.comp
      (puncturedAttachmentSourceInclusion_isOpenEmbedding D n).continuous⟩

private theorem puncturedAttachmentQuotient_isQuotientMap
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsQuotientMap (puncturedAttachmentQuotient D n) :=
  ((nativeCoefficientAttachmentQuotient_isQuotientMap D n).restrictPreimage_isOpen
    (coefficientCellCenters_isClosed D n).isOpen_compl).comp
      (puncturedAttachmentSourceHomeomorph D n).isQuotientMap

private abbrev factoredPuncturedNativeCells {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :=
  Σ c : (nerve J).nonDegenerate (n + 1), toTop.obj (D.obj c.1.left) ×
    {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // t ≠ Convexity.StdSimplex.barycenter}

private def factoredPuncturedCellInclusion
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    factoredPuncturedNativeCells D n → puncturedNativeCoefficientCells D n :=
  fun z => ⟨⟨z.1, z.2.1, z.2.2.1⟩, z.2.2.2⟩

private theorem factoredPuncturedCellInclusion_isEmbedding
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsEmbedding (factoredPuncturedCellInclusion D n) := by
  let _ : T2Space (Convexity.StdSimplex ℝ (Fin (n + 2))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).t2Space
  have he : IsOpenEmbedding (fun z : factoredPuncturedNativeCells D n =>
      (⟨z.1, z.2.1, z.2.2.1⟩ : nativeCoefficientCells D n)) := by
    rw [isOpenEmbedding_iff_continuous_injective_isOpenMap]
    refine ⟨continuous_sigma (fun _ => continuous_sigmaMk.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))), ?_, ?_⟩
    · rintro ⟨c, x, t⟩ ⟨d, y, s⟩ h
      have hcd : c = d := congrArg Sigma.fst h
      subst d
      have hp : (x, t.1) = (y, s.1) := eq_of_heq (Sigma.mk.inj h).2
      have hxy : x = y := congrArg Prod.fst hp
      have hts := Subtype.ext (congrArg Prod.snd hp)
      subst y
      subst s
      rfl
    · exact isOpenMap_sigma.2 (fun _ => isOpenMap_sigmaMk.comp
        (IsOpenMap.id.prodMap isClosed_singleton.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap))
  have hs : IsEmbedding (Subtype.val : puncturedNativeCoefficientCells D n →
      nativeCoefficientCells D n) := IsEmbedding.subtypeVal
  exact (hs.of_comp_iff).mp he.isEmbedding

private def factoredPuncturedCellsHomeomorph
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    factoredPuncturedNativeCells D n ≃ₜ puncturedNativeCoefficientCells D n where
  toFun := factoredPuncturedCellInclusion D n
  invFun z := ⟨z.1.1, z.1.2.1, ⟨z.1.2.2, z.2⟩⟩
  left_inv := by rintro ⟨c, x, t⟩; rfl
  right_inv := by rintro ⟨⟨c, x, t⟩, ht⟩; rfl
  continuous_toFun := (factoredPuncturedCellInclusion_isEmbedding D n).continuous
  continuous_invFun := by
    apply (factoredPuncturedCellInclusion_isEmbedding D n).continuous_iff.mpr
    exact continuous_id

private def factoredCoefficientRadialFamily
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    C(factoredPuncturedNativeCells D n × unitInterval, factoredPuncturedNativeCells D n) := by
  let h : C(Σ c : (nerve J).nonDegenerate (n + 1),
      (toTop.obj (D.obj c.1.left) ×
        {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // t ≠ Convexity.StdSimplex.barycenter}) ×
          unitInterval, factoredPuncturedNativeCells D n) :=
    ⟨fun z => ⟨z.1, z.2.1.1,
      StdSimplexRadialBoundary.radialHomotopy (n + 1) (z.2.2, z.2.1.2)⟩,
      continuous_sigma (fun _ => continuous_sigmaMk.comp
        ((continuous_fst.comp continuous_fst).prodMk
          ((StdSimplexRadialBoundary.radialHomotopy (n + 1)).continuous.comp
            (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))))⟩
  exact h.comp ⟨Homeomorph.sigmaProdDistrib, Homeomorph.sigmaProdDistrib.continuous⟩

private def coefficientRadialFamily
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    C(unitInterval × puncturedNativeCoefficientCells D n, puncturedNativeCoefficientCells D n) :=
  ⟨fun z => factoredPuncturedCellsHomeomorph D n
      (factoredCoefficientRadialFamily D n
        ((factoredPuncturedCellsHomeomorph D n).symm z.2, z.1)),
    (factoredPuncturedCellsHomeomorph D n).continuous.comp
      ((factoredCoefficientRadialFamily D n).continuous.comp
        (((factoredPuncturedCellsHomeomorph D n).symm.continuous.comp continuous_snd).prodMk
          continuous_fst))⟩

private theorem coefficientRadialFamily_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (z : puncturedNativeCoefficientCells D n) :
    (coefficientRadialFamily D n (t, z)).1 =
      ⟨z.1.1, z.1.2.1,
        StdSimplexRadialBoundary.homotopyPoint (n + 1) t z.1.2.2 z.2⟩ := by
  obtain ⟨⟨c, x, s⟩, hs⟩ := z
  simp [coefficientRadialFamily, factoredCoefficientRadialFamily,
    factoredPuncturedCellsHomeomorph, factoredPuncturedCellInclusion,
    StdSimplexRadialBoundary.radialHomotopy]
  rfl

private theorem coefficientRadialFamily_zero
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : puncturedNativeCoefficientCells D n) : coefficientRadialFamily D n (0, z) = z := by
  apply Subtype.ext
  rw [coefficientRadialFamily_apply, StdSimplexRadialBoundary.homotopyPoint_zero]

private theorem coefficientRadialFamily_fixed_on_boundary
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (z : puncturedNativeCoefficientCells D n)
    (hz : ∃ i, z.1.2.2.weights i = 0) : coefficientRadialFamily D n (t, z) = z := by
  obtain ⟨i, hi⟩ := hz
  apply Subtype.ext
  rw [coefficientRadialFamily_apply,
    StdSimplexRadialBoundary.homotopyPoint_eq_of_has_zero (n + 1) t ⟨z.1.2.2, z.2⟩ i hi]

private theorem coefficientRadialFamily_one_has_zero
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : puncturedNativeCoefficientCells D n) :
    ∃ i, (coefficientRadialFamily D n (1, z)).1.2.2.weights i = 0 := by
  rw [coefficientRadialFamily_apply, StdSimplexRadialBoundary.homotopyPoint_one]
  exact StdSimplexRadialBoundary.exists_radialMap_weights_eq_zero (n + 1) ⟨z.1.2.2, z.2⟩

private theorem nativeCoefficientCellStageMap_mem_old_iff
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : nativeCoefficientCells D n) :
    nativeCoefficientCellStageMap D n z ∈
        Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))) ↔
      ∃ i, z.2.2.weights i = 0 := by
  have h := Set.ext_iff.mp (bkNondegenerateCellToStage_preimage_compl_range D n)
    ((bkNondegenerateCellsProductIso D (n + 1)).inv z)
  change (nativeCoefficientCellStageMap D n z ∉
      Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n)))) ↔
    (bkNondegenerateCellsProductIso D (n + 1)).inv z ∉
      Set.range (toTop.map (bkNondegenerateCellBoundaryInclusion D (n + 1))) at h
  exact (not_iff_not.mp h).trans
    (bkNondegenerateCellsProductIso_inv_mem_boundary_iff D (n + 1) z)

private def prequotientCoefficientRadialFamily
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    C(unitInterval × puncturedAttachmentSource D n, puncturedCoefficientStage D n) := by
  let h : C((unitInterval × toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) ⊕
      (unitInterval × puncturedNativeCoefficientCells D n), puncturedCoefficientStage D n) :=
    ⟨Sum.elim (fun z => puncturedAttachmentQuotient D n (Sum.inl z.2))
        (fun z => puncturedAttachmentQuotient D n
          (Sum.inr (coefficientRadialFamily D n z))),
      ((puncturedAttachmentQuotient D n).continuous.comp
        (continuous_inl.comp continuous_snd)).sumElim
          ((puncturedAttachmentQuotient D n).continuous.comp
            (continuous_inr.comp (coefficientRadialFamily D n).continuous))⟩
  exact h.comp ⟨Homeomorph.prodSumDistrib, Homeomorph.prodSumDistrib.continuous⟩

private theorem prequotientCoefficientRadialFamily_inl
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (x : toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) :
    prequotientCoefficientRadialFamily D n (t, Sum.inl x) =
      puncturedAttachmentQuotient D n (Sum.inl x) := rfl

private theorem prequotientCoefficientRadialFamily_inr
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (z : puncturedNativeCoefficientCells D n) :
    prequotientCoefficientRadialFamily D n (t, Sum.inr z) =
      puncturedAttachmentQuotient D n (Sum.inr (coefficientRadialFamily D n (t, z))) := rfl

private theorem prequotientCoefficientRadialFamily_zero
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : puncturedAttachmentSource D n) :
    prequotientCoefficientRadialFamily D n (0, z) = puncturedAttachmentQuotient D n z := by
  cases z with
  | inl x => exact prequotientCoefficientRadialFamily_inl D n 0 x
  | inr z => rw [prequotientCoefficientRadialFamily_inr, coefficientRadialFamily_zero]

private theorem prequotientCoefficientRadialFamily_factors
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) :
    Function.FactorsThrough (fun z => prequotientCoefficientRadialFamily D n (t, z))
      (puncturedAttachmentQuotient D n) := by
  have hfixed (z : puncturedNativeCoefficientCells D n)
      (hz : ∃ i, z.1.2.2.weights i = 0) :
      prequotientCoefficientRadialFamily D n (t, Sum.inr z) =
        puncturedAttachmentQuotient D n (Sum.inr z) :=
    (prequotientCoefficientRadialFamily_inr D n t z).trans
      (congrArg (fun q => puncturedAttachmentQuotient D n (Sum.inr q))
        (coefficientRadialFamily_fixed_on_boundary D n t z hz))
  intro x y h
  change prequotientCoefficientRadialFamily D n (t, x) =
    prequotientCoefficientRadialFamily D n (t, y)
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact (prequotientCoefficientRadialFamily_inl D n t x).trans
        (h.trans (prequotientCoefficientRadialFamily_inl D n t y).symm)
    | inr y =>
      have hy : ∃ i, y.1.2.2.weights i = 0 :=
        (nativeCoefficientCellStageMap_mem_old_iff D n y.1).mp
          ⟨x, congrArg Subtype.val h⟩
      exact (prequotientCoefficientRadialFamily_inl D n t x).trans (h.trans (hfixed y hy).symm)
  | inr x =>
    cases y with
    | inl y =>
      have hx : ∃ i, x.1.2.2.weights i = 0 :=
        (nativeCoefficientCellStageMap_mem_old_iff D n x.1).mp
          ⟨y, (congrArg Subtype.val h).symm⟩
      exact (hfixed x hx).trans (h.trans (prequotientCoefficientRadialFamily_inl D n t y).symm)
    | inr y =>
      by_cases hx : ∃ i, x.1.2.2.weights i = 0
      · obtain ⟨a, ha⟩ := (nativeCoefficientCellStageMap_mem_old_iff D n x.1).mpr hx
        have hy := (nativeCoefficientCellStageMap_mem_old_iff D n y.1).mp
          ⟨a, ha.trans (congrArg Subtype.val h)⟩
        exact (hfixed x hx).trans (h.trans (hfixed y hy).symm)
      · have hb : (bkNondegenerateCellsProductIso D (n + 1)).inv x.1 ∉
            Set.range (toTop.map (bkNondegenerateCellBoundaryInclusion D (n + 1))) := by
          rw [bkNondegenerateCellsProductIso_inv_mem_boundary_iff]
          exact hx
        have he := Types.pushoutCocone_inr_eq_inr_of_not_mem_range_of_isColimit
          ((bkSkeletalFiltrationSucc_nonDegenerate_realized_isPushout D n).map
            (forget TopCat)).isColimit hb (congrArg Subtype.val h)
        have hxy : x = y := Subtype.ext
          ((TopCat.homeoOfIso (bkNondegenerateCellsProductIso D (n + 1))).symm.injective he)
        subst y
        rfl

private def puncturedCoefficientRadialEnd
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    C(puncturedCoefficientStage D n, puncturedCoefficientStage D n) :=
  (puncturedAttachmentQuotient_isQuotientMap D n).lift
    ⟨fun z => prequotientCoefficientRadialFamily D n (1, z),
      (prequotientCoefficientRadialFamily D n).continuous.comp
        (continuous_const.prodMk continuous_id)⟩
    (prequotientCoefficientRadialFamily_factors D n 1)

private theorem puncturedCoefficientRadialEnd_quotient_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : puncturedAttachmentSource D n) :
    puncturedCoefficientRadialEnd D n (puncturedAttachmentQuotient D n z) =
      prequotientCoefficientRadialFamily D n (1, z) := by
  let g : C(puncturedAttachmentSource D n, puncturedCoefficientStage D n) :=
    ⟨fun z => prequotientCoefficientRadialFamily D n (1, z),
      (prequotientCoefficientRadialFamily D n).continuous.comp
        (continuous_const.prodMk continuous_id)⟩
  exact congrArg (fun f : C(puncturedAttachmentSource D n, puncturedCoefficientStage D n) => f z)
    ((puncturedAttachmentQuotient_isQuotientMap D n).lift_comp g
      (prequotientCoefficientRadialFamily_factors D n 1))

private def puncturedCoefficientRadialHomotopy
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    TopCat.Homotopy (𝟙 (TopCat.of (puncturedCoefficientStage D n)))
      (TopCat.ofHom (puncturedCoefficientRadialEnd D n)) :=
  TopCat.Homotopy.ofQuotientMap (TopCat.ofHom (puncturedAttachmentQuotient D n))
    (puncturedAttachmentQuotient_isQuotientMap D n)
    (prequotientCoefficientRadialFamily D n)
    (prequotientCoefficientRadialFamily_zero D n)
    (fun z => (puncturedCoefficientRadialEnd_quotient_apply D n z).symm)
    (prequotientCoefficientRadialFamily_factors D n)

private def oldStagePuncturedInclusion
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    C(toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}), puncturedCoefficientStage D n) :=
  ⟨fun x => puncturedAttachmentQuotient D n (Sum.inl x),
    (puncturedAttachmentQuotient D n).continuous.comp continuous_inl⟩

private theorem oldStagePuncturedInclusion_isEmbedding
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsEmbedding (oldStagePuncturedInclusion D n) := by
  have hg : IsEmbedding (Subtype.val : puncturedCoefficientStage D n →
      toTop.obj (bkSkeletalFiltration D (n + 1) : SSet.{max u v})) := IsEmbedding.subtypeVal
  exact (hg.of_comp_iff).mp
    (TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (closedT1Embeddings_toTop_map_of_mono
        (bkSkeletalFiltrationMap D (Nat.le_succ n)))).isEmbedding

private theorem puncturedCoefficientRadialEnd_mem_old
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (y : puncturedCoefficientStage D n) :
    puncturedCoefficientRadialEnd D n y ∈ Set.range (oldStagePuncturedInclusion D n) := by
  obtain ⟨x | z, rfl⟩ := (puncturedAttachmentQuotient_isQuotientMap D n).surjective y
  · exact ⟨x, ((puncturedCoefficientRadialEnd_quotient_apply D n (Sum.inl x)).trans
      (prequotientCoefficientRadialFamily_inl D n 1 x)).symm⟩
  · obtain ⟨a, ha⟩ := (nativeCoefficientCellStageMap_mem_old_iff D n
        (coefficientRadialFamily D n (1, z)).1).mpr (coefficientRadialFamily_one_has_zero D n z)
    refine ⟨a, Subtype.ext ?_⟩
    exact ha.trans (congrArg Subtype.val
      ((puncturedCoefficientRadialEnd_quotient_apply D n (Sum.inr z)).trans
        (prequotientCoefficientRadialFamily_inr D n 1 z))).symm

private theorem puncturedCoefficientRadialEnd_on_old
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (x : toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) :
    puncturedCoefficientRadialEnd D n (oldStagePuncturedInclusion D n x) =
      oldStagePuncturedInclusion D n x :=
  (puncturedCoefficientRadialEnd_quotient_apply D n (Sum.inl x)).trans
    (prequotientCoefficientRadialFamily_inl D n 1 x)

private def puncturedCoefficientRadialRetraction
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    C(puncturedCoefficientStage D n, toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) :=
  ⟨fun y => (oldStagePuncturedInclusion_isEmbedding D n).toHomeomorph.symm
      ⟨puncturedCoefficientRadialEnd D n y, puncturedCoefficientRadialEnd_mem_old D n y⟩,
    (oldStagePuncturedInclusion_isEmbedding D n).toHomeomorph.symm.continuous.comp
      ((puncturedCoefficientRadialEnd D n).continuous.subtype_mk
        (puncturedCoefficientRadialEnd_mem_old D n))⟩

private theorem puncturedCoefficientRadialRetraction_inclusion_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (y : puncturedCoefficientStage D n) :
    oldStagePuncturedInclusion D n (puncturedCoefficientRadialRetraction D n y) =
      puncturedCoefficientRadialEnd D n y :=
  congrArg Subtype.val ((oldStagePuncturedInclusion_isEmbedding D n).toHomeomorph.apply_symm_apply
    ⟨puncturedCoefficientRadialEnd D n y, puncturedCoefficientRadialEnd_mem_old D n y⟩)

private theorem puncturedCoefficientRadialRetraction_on_old
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (x : toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) :
    puncturedCoefficientRadialRetraction D n (oldStagePuncturedInclusion D n x) = x := by
  apply (oldStagePuncturedInclusion_isEmbedding D n).injective
  exact (puncturedCoefficientRadialRetraction_inclusion_apply D n
    (oldStagePuncturedInclusion D n x)).trans (puncturedCoefficientRadialEnd_on_old D n x)

private theorem puncturedCoefficientRadialHomotopy_quotient_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (z : puncturedAttachmentSource D n) :
    puncturedCoefficientRadialHomotopy D n (t, puncturedAttachmentQuotient D n z) =
      prequotientCoefficientRadialFamily D n (t, z) :=
  TopCat.Homotopy.ofQuotientMap_apply (TopCat.ofHom (puncturedAttachmentQuotient D n))
    (f := 𝟙 (TopCat.of (puncturedCoefficientStage D n)))
    (g := TopCat.ofHom (puncturedCoefficientRadialEnd D n))
    (puncturedAttachmentQuotient_isQuotientMap D n) (prequotientCoefficientRadialFamily D n)
    (prequotientCoefficientRadialFamily_zero D n)
    (fun z => (puncturedCoefficientRadialEnd_quotient_apply D n z).symm)
    (prequotientCoefficientRadialFamily_factors D n) t z

private theorem puncturedCoefficientRadialHomotopy_on_old
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (x : toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) :
    puncturedCoefficientRadialHomotopy D n (t, oldStagePuncturedInclusion D n x) =
      oldStagePuncturedInclusion D n x :=
  (puncturedCoefficientRadialHomotopy_quotient_apply D n t (Sum.inl x)).trans
    (prequotientCoefficientRadialFamily_inl D n t x)

/-- The actual new-cell barycenter locus in a successor BK stage, including
every coefficient over each nondegenerate base-cell barycenter. -/
def bkCellBarycenters {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Set (toTop.obj (bkSkeletalFiltration D (n + 1) : SSet.{max u v})) :=
  coefficientCellCenters D n

/-- The actual cell-barycenter locus is closed without a countability
or regular-cell hypothesis. -/
theorem bkCellBarycenters_isClosed {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) : IsClosed (bkCellBarycenters D n) :=
  coefficientCellCenters_isClosed D n

/-- The actual successor stage with its new-cell barycenters removed. -/
abbrev bkCellBarycenterComplement {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) : TopCat.{max u v} :=
  TopCat.of ↥((bkCellBarycenters D n)ᶜ)

/-- The actual inclusion of the punctured successor stage. -/
def bkCellBarycenterComplementInclusion {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellBarycenterComplement D n ⟶
      toTop.obj (bkSkeletalFiltration D (n + 1) : SSet.{max u v}) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The original old-stage inclusion with codomain in the actual
barycenter complement. -/
def bkCellOldStageInclusion {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}) ⟶ bkCellBarycenterComplement D n :=
  TopCat.ofHom (oldStagePuncturedInclusion D n)

private theorem bkCellOldStageInclusion_comp_inclusion_aux {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellOldStageInclusion D n ≫ bkCellBarycenterComplementInclusion D n =
      toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n)) := rfl

/-- The literal original coordinate of the old-stage inclusion. -/
@[reassoc]
theorem bkCellOldStageInclusion_comp_inclusion {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellOldStageInclusion D n ≫ bkCellBarycenterComplementInclusion D n =
      toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n)) :=
  bkCellOldStageInclusion_comp_inclusion_aux D n

/-- The actual radial retraction to the old stage, descended through the
coefficient-cell attachment quotient. -/
def bkCellRadialRetraction {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellBarycenterComplement D n ⟶ toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}) :=
  TopCat.ofHom (puncturedCoefficientRadialRetraction D n)

/-- The descended radial map is a retraction of the original old stage. -/
@[reassoc]
theorem bkCellRadialRetraction_retract {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellOldStageInclusion D n ≫ bkCellRadialRetraction D n =
      𝟙 (toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) := by
  apply TopCat.ext
  exact puncturedCoefficientRadialRetraction_on_old D n

/-- The actual quotient radial homotopy from the identity to the
old-stage retraction followed by its original inclusion. -/
def bkCellRadialHomotopy {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    TopCat.Homotopy (𝟙 (bkCellBarycenterComplement D n))
      (bkCellRadialRetraction D n ≫ bkCellOldStageInclusion D n) where
  toFun := puncturedCoefficientRadialHomotopy D n
  continuous_toFun := (puncturedCoefficientRadialHomotopy D n).continuous
  map_zero_left := (puncturedCoefficientRadialHomotopy D n).map_zero_left
  map_one_left y := ((puncturedCoefficientRadialHomotopy D n).map_one_left y).trans
    (puncturedCoefficientRadialRetraction_inclusion_apply D n y).symm

/-- The actual radial homotopy fixes the entire original old stage at
every parameter, including all identified boundary representatives. -/
theorem bkCellRadialHomotopy_on_old {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) (t : unitInterval)
    (x : toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) :
    bkCellRadialHomotopy D n (t, bkCellOldStageInclusion D n x) =
      bkCellOldStageInclusion D n x :=
  puncturedCoefficientRadialHomotopy_on_old D n t x

/-- The actual coefficient characteristic map on a punctured
nondegenerate simplex, with codomain in the actual barycenter complement. -/
def bkPuncturedNondegenerateCell {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) (c : (nerve J).nonDegenerate (n + 1)) :
    TopCat.of (toTop.obj (D.obj c.1.left) ×
      {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) ⟶
        bkCellBarycenterComplement D n :=
  TopCat.ofHom ⟨fun z => puncturedAttachmentQuotient D n
      (Sum.inr ⟨⟨c, z.1, z.2.1⟩, z.2.2⟩),
    (puncturedAttachmentQuotient D n).continuous.comp
      (continuous_inr.comp ((continuous_sigmaMk.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
          (fun z => z.2.2)))⟩

/-- The punctured-cell map has the literal original closed-cell
characteristic as its coordinate in the actual successor stage. -/
theorem bkPuncturedNondegenerateCell_inclusion_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) :
    bkCellBarycenterComplementInclusion D n (bkPuncturedNondegenerateCell D n c (x, s)) =
      bkRealizedChainCellToStage D c.1 (x, s.1) :=
  nativeCoefficientCellStageMap_apply D n c x s.1

/-- On each actual punctured cell, the descended homotopy keeps the
coefficient fixed and uses the standard-simplex radial homotopy. -/
theorem bkCellRadialHomotopy_cell_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (t : unitInterval)
    (x : toTop.obj (D.obj c.1.left))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) :
    bkCellRadialHomotopy D n (t, bkPuncturedNondegenerateCell D n c (x, s)) =
      bkPuncturedNondegenerateCell D n c
        (x, StdSimplexRadialBoundary.radialHomotopy (n + 1) (t, s)) := by
  let z : puncturedNativeCoefficientCells D n := ⟨⟨c, x, s.1⟩, s.2⟩
  have hz : coefficientRadialFamily D n (t, z) =
      ⟨⟨c, x, (StdSimplexRadialBoundary.radialHomotopy (n + 1) (t, s)).1⟩,
        (StdSimplexRadialBoundary.radialHomotopy (n + 1) (t, s)).2⟩ := by
    apply Subtype.ext
    exact coefficientRadialFamily_apply D n t z
  exact ((puncturedCoefficientRadialHomotopy_quotient_apply D n t (Sum.inr z)).trans
    (prequotientCoefficientRadialFamily_inr D n t z)).trans
      (congrArg (fun q => puncturedAttachmentQuotient D n (Sum.inr q)) hz)

/-- The endpoint retraction on an actual cell is the original closed-cell
map at the standard radial boundary point. This identifies the actual total
map before reducing its boundary point to a forward diagram arrow. -/
theorem bkCellRadialRetraction_cell_endpoint
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) :
    toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))
        (bkCellRadialRetraction D n (bkPuncturedNondegenerateCell D n c (x, s))) =
      bkRealizedChainCellToStage D c.1 (x, StdSimplexRadialBoundary.radialMap (n + 1) s) := by
  have he := (bkCellRadialHomotopy D n).map_one_left
    (bkPuncturedNondegenerateCell D n c (x, s))
  have hc := bkCellRadialHomotopy_cell_apply D n c 1 x s
  have hi := ConcreteCategory.congr_hom (bkCellOldStageInclusion_comp_inclusion D n)
    (bkCellRadialRetraction D n (bkPuncturedNondegenerateCell D n c (x, s)))
  have hp := bkPuncturedNondegenerateCell_inclusion_apply D n c x
    (StdSimplexRadialBoundary.radialHomotopy (n + 1) (1, s))
  have hr : (StdSimplexRadialBoundary.radialHomotopy (n + 1) (1, s)).1 =
      StdSimplexRadialBoundary.radialMap (n + 1) s :=
    congrArg Subtype.val ((StdSimplexRadialBoundary.radialHomotopy (n + 1)).map_one_left s)
  exact hi.symm.trans ((congrArg (fun q => bkCellBarycenterComplementInclusion D n q)
    (he.symm.trans hc)).trans (hp.trans (congrArg
      (fun q => bkRealizedChainCellToStage D c.1 (x, q)) hr)))

private theorem exists_simplex_face_of_zero {n : ℕ}
    (s : Convexity.StdSimplex ℝ (Fin (n + 2))) (i : Fin (n + 2)) (hi : s.weights i = 0) :
    ∃ q : Convexity.StdSimplex ℝ (Fin (n + 1)), stdSimplex.toTopMap (SimplexCategory.δ i) q = s :=
      by
  have hs : s ∈ Set.range (Convexity.StdSimplex.map (Fin.succAbove i)) := by
    rw [Convexity.StdSimplex.mem_range_map_iff]
    intro j hj
    rw [Fin.range_succAbove] at hj
    have hji : j = i := by simpa using hj
    exact hji ▸ hi
  obtain ⟨q, hq⟩ := hs
  exact ⟨q, hq⟩

private theorem realizedChainCell_reindex_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ}
    (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (x : toTop.obj (D.obj c.left)) (s : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    bkRealizedChainCell D c (x, stdSimplex.toTopMap θ s) =
      bkRealizedChainCell D ((nerve J).map θ.op c)
        (toTop.map (D.map (bkChainFirstArrow c θ)) x, s) :=
  ConcreteCategory.congr_hom (bkRealizedChainCell_reindex D c θ) (x, s)

private theorem realizedChainCell_zero_face
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : ComposableArrows J (n + 1)) (s : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (i : Fin (n + 2)) (hi : s.weights i = 0) :
    ∃ q : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∀ x : toTop.obj (D.obj c.left),
        bkRealizedChainCell D c (x, s) =
          bkRealizedChainCell D ((nerve J).map (SimplexCategory.δ i).op c)
            (toTop.map (D.map (bkChainFirstArrow c (SimplexCategory.δ i))) x, q) := by
  obtain ⟨q, hq⟩ := exists_simplex_face_of_zero s i hi
  refine ⟨q, fun x => ?_⟩
  exact (congrArg (fun t => bkRealizedChainCell D c (x, t)) hq).symm.trans
    (realizedChainCell_reindex_apply D c (SimplexCategory.δ i) x q)

private theorem realizedChainCell_positive_nondegenerate_presentation
    {J : Type u} [Category.{v} J] {n : ℕ} (c : ComposableArrows J n)
    (s : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ∃ (m : ℕ) (d : (nerve J).nonDegenerate m)
      (q : Convexity.StdSimplex ℝ (Fin (m + 1))) (g : c.left ⟶ d.1.left),
      m ≤ n ∧ (∀ i, 0 < q.weights i) ∧
        ∀ (D : J ⥤ SSet.{max u v}) (x : toTop.obj (D.obj c.left)),
          bkRealizedChainCell D c (x, s) =
            bkRealizedChainCell D d.1 (toTop.map (D.map g) x, q) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n hn =>
    by_cases hc : c ∈ (nerve J).nonDegenerate n
    · by_cases hs : ∀ i, 0 < s.weights i
      · refine ⟨n, ⟨c, hc⟩, s, 𝟙 c.left, le_rfl, hs, fun D x => ?_⟩
        have hi : toTop.map (D.map (𝟙 c.left)) x = x := by
          rw [D.map_id, toTop.map_id]
          rfl
        exact congrArg (fun y => bkRealizedChainCell D c (y, s)) hi.symm
      · obtain ⟨i, hi⟩ := not_forall.mp hs
        have hz : s.weights i = 0 := le_antisymm (le_of_not_gt hi) (s.weights_nonneg i)
        cases n with
        | zero =>
          have hsum := s.total_of_fintype
          have hu : (Finset.univ : Finset (Fin 1)) = {i} := by
            ext j
            simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
            exact Subsingleton.elim j i
          rw [hu, Finset.sum_singleton, hz] at hsum
          exact (zero_ne_one hsum).elim
        | succ n =>
          obtain ⟨p, hp⟩ := exists_simplex_face_of_zero s i hz
          let θ := SimplexCategory.δ i
          let e : ComposableArrows J n := (nerve J).map θ.op c
          obtain ⟨m, d, q, g, hm, hq, hg⟩ := hn n (Nat.lt_succ_self n) e p
          refine ⟨m, d, q, bkChainFirstArrow c θ ≫ g, hm.trans (Nat.le_succ n), hq, fun D x => ?_⟩
          have hf := realizedChainCell_reindex_apply D c θ x p
          have hfirst := (congrArg (fun t => bkRealizedChainCell D c (x, t)) hp).symm.trans hf
          have hcomp : toTop.map (D.map (bkChainFirstArrow c θ ≫ g)) x =
              toTop.map (D.map g) (toTop.map (D.map (bkChainFirstArrow c θ)) x) := by
            rw [D.map_comp, toTop.map_comp]
            rfl
          exact hfirst.trans ((hg D (toTop.map (D.map (bkChainFirstArrow c θ)) x)).trans
            (congrArg (fun y => bkRealizedChainCell D d.1 (y, q)) hcomp.symm))
    · have hdeg := ((nerve J).mem_degenerate_iff_notMem_nonDegenerate c).mpr hc
      obtain ⟨k, hk, θ, hθ, y, rfl⟩ := ((nerve J).mem_degenerate_iff c).mp hdeg
      let _ : Epi θ := hθ
      let f := bkChainFirstArrow y θ
      let _ : IsIso f := bkChainFirstArrow_isIso_of_epi y θ
      obtain ⟨m, d, q, g, hm, hq, hg⟩ := hn k hk y (stdSimplex.toTopMap θ s)
      refine ⟨m, d, q, inv f ≫ g, hm.trans (Nat.le_of_lt hk), hq, fun D x => ?_⟩
      let x' := toTop.map (D.map (inv f)) x
      have hi : toTop.map (D.map f) x' = x := by
        have h : D.map (inv f) ≫ D.map f = 𝟙 _ := by
          rw [← D.map_comp, IsIso.inv_hom_id, D.map_id]
        have ht := congrArg toTop.map h
        rw [toTop.map_comp, toTop.map_id] at ht
        exact ConcreteCategory.congr_hom ht x
      have hf := realizedChainCell_reindex_apply D y θ x' s
      have hcomp : toTop.map (D.map (inv f ≫ g)) x = toTop.map (D.map g) x' := by
        rw [D.map_comp, toTop.map_comp]
        rfl
      exact (congrArg (fun z => bkRealizedChainCell D ((nerve J).map θ.op y) (z, s)) hi).symm.trans
        (hf.symm.trans ((hg D x').trans
          (congrArg (fun z => bkRealizedChainCell D d.1 (z, q)) hcomp.symm)))

private theorem skeletalProjection_natural
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) :
    bkSkeletalFiltrationMap D h ≫ bkSkeletalProjection D n =
      bkSkeletalProjection D m ≫
        Subcomplex.homOfLE ((nerve J).skeleton.monotone (Nat.add_le_add_right h 1)) := by
  apply (cancel_mono ((nerve J).skeleton (n + 1)).ι).mp
  rw [Category.assoc, bkSkeletalProjection_comp_ι, ← Category.assoc,
    bkSkeletalFiltrationMap_ι, Category.assoc, Subcomplex.homOfLE_ι,
    bkSkeletalProjection_comp_ι]

private def coefficientPointStageProjection
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}) ⟶
      toTop.obj (bkSkeletalFiltration (bkPointDiagram J) n : SSet.{max u v}) :=
  toTop.map (bkSkeletalProjection D n) ≫ (bkNerveSkeletalCellModelIso J n).inv

private theorem coefficientPointStageProjection_natural
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) :
    toTop.map (bkSkeletalFiltrationMap D h) ≫ coefficientPointStageProjection D n =
      coefficientPointStageProjection D m ≫ toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J)
        h) := by
  apply (cancel_mono (bkNerveSkeletalCellModelIso J n).hom).mp
  have ht := congrArg toTop.map (skeletalProjection_natural D h)
  simp only [Functor.map_comp] at ht
  calc
    toTop.map (bkSkeletalFiltrationMap D h) ≫ coefficientPointStageProjection D n ≫
        (bkNerveSkeletalCellModelIso J n).hom =
      toTop.map (bkSkeletalFiltrationMap D h) ≫ toTop.map (bkSkeletalProjection D n) := by
        simp [coefficientPointStageProjection, Category.assoc]
    _ = toTop.map (bkSkeletalProjection D m) ≫ bkNerveSkeletalMap J h := ht
    _ = coefficientPointStageProjection D m ≫
        (bkNerveSkeletalCellModelIso J m).hom ≫ bkNerveSkeletalMap J h := by
          simp [coefficientPointStageProjection, Category.assoc]
    _ = coefficientPointStageProjection D m ≫
        toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) h) ≫
          (bkNerveSkeletalCellModelIso J n).hom := by
            rw [bkNerveSkeletalCellModelIso_natural]

private theorem coefficientPointStageProjection_native_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (s : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    coefficientPointStageProjection D (n + 1) (nativeCoefficientCellStageMap D n ⟨c, x, s⟩) =
      nativeCoefficientCellStageMap (bkPointDiagram J) n ⟨c, pointCellCoefficient J c.1.left, s⟩
        := by
  let y := bkRealizedChainCellToStage (bkPointDiagram J) c.1
    (pointCellCoefficient J c.1.left, s)
  have hp := (congrArg (fun q => toTop.map (bkSkeletalProjection D (n + 1)) q)
    (nativeCoefficientCellStageMap_apply D n c x s)).trans
      (bkRealizedChainCellToStage_projection_apply D c.1 x s)
  have hi : (bkNerveSkeletalCellModelIso J (n + 1)).inv (bkNerveSkeletalCell J c.1 s) = y :=
    ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso J (n + 1)).hom_inv_id y
  exact (congrArg (fun q => (bkNerveSkeletalCellModelIso J (n + 1)).inv q) hp).trans
    (hi.trans (nativeCoefficientCellStageMap_apply (bkPointDiagram J) n c
      (pointCellCoefficient J c.1.left) s).symm)

private theorem coefficientPointStageProjection_mem_centers_iff
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (x : toTop.obj (bkSkeletalFiltration D (n + 1) : SSet.{max u v})) :
    coefficientPointStageProjection D (n + 1) x ∈ coefficientCellCenters (bkPointDiagram J) n ↔
      x ∈ coefficientCellCenters D n := by
  obtain ⟨a | z, rfl⟩ := (nativeCoefficientAttachmentQuotient_isQuotientMap D n).surjective x
  · have hn := ConcreteCategory.congr_hom
      (coefficientPointStageProjection_natural D (Nat.le_succ n)) a
    constructor
    · intro h
      exact ((oldStage_not_mem_coefficientCellCenters (bkPointDiagram J) n
        (coefficientPointStageProjection D n a)) (hn ▸ h)).elim
    · intro h
      exact (oldStage_not_mem_coefficientCellCenters D n a h).elim
  · obtain ⟨c, x, s⟩ := z
    have hp := coefficientPointStageProjection_native_apply D n c x s
    exact (Iff.of_eq (congrArg (fun q => q ∈ coefficientCellCenters (bkPointDiagram J) n) hp)).trans
      ((nativeCoefficientCell_mem_centers_iff (bkPointDiagram J) n
        ⟨c, pointCellCoefficient J c.1.left, s⟩).trans
          (nativeCoefficientCell_mem_centers_iff D n ⟨c, x, s⟩).symm)

private def puncturedCoefficientProjection
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    C(puncturedCoefficientStage D n, puncturedCoefficientStage (bkPointDiagram J) n) :=
  ⟨fun x => ⟨coefficientPointStageProjection D (n + 1) x.1, fun hx => x.2
      ((coefficientPointStageProjection_mem_centers_iff D n x.1).mp hx)⟩,
    ((coefficientPointStageProjection D (n + 1)).hom.continuous.comp
      continuous_subtype_val).subtype_mk _⟩

private def puncturedNativeCellToPoint
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : puncturedNativeCoefficientCells D n) :
    puncturedNativeCoefficientCells (bkPointDiagram J) n :=
  ⟨⟨z.1.1, pointCellCoefficient J z.1.1.1.left, z.1.2.2⟩, z.2⟩

private theorem puncturedCoefficientProjection_old_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (x : toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})) :
    puncturedCoefficientProjection D n (oldStagePuncturedInclusion D n x) =
      oldStagePuncturedInclusion (bkPointDiagram J) n (coefficientPointStageProjection D n x) :=
  Subtype.ext (ConcreteCategory.congr_hom
    (coefficientPointStageProjection_natural D (Nat.le_succ n)) x)

private theorem puncturedCoefficientProjection_native_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : puncturedNativeCoefficientCells D n) :
    puncturedCoefficientProjection D n (puncturedAttachmentQuotient D n (Sum.inr z)) =
      puncturedAttachmentQuotient (bkPointDiagram J) n (Sum.inr (puncturedNativeCellToPoint D n
        z)) :=
  Subtype.ext (coefficientPointStageProjection_native_apply D n z.1.1 z.1.2.1 z.1.2.2)

private theorem coefficientRadialFamily_point
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (z : puncturedNativeCoefficientCells D n) :
    puncturedNativeCellToPoint D n (coefficientRadialFamily D n (t, z)) =
      coefficientRadialFamily (bkPointDiagram J) n (t, puncturedNativeCellToPoint D n z) := by
  let f : nativeCoefficientCells D n → nativeCoefficientCells (bkPointDiagram J) n :=
    fun q => ⟨q.1, pointCellCoefficient J q.1.1.left, q.2.2⟩
  apply Subtype.ext
  exact (congrArg f (coefficientRadialFamily_apply D n t z)).trans
    (coefficientRadialFamily_apply (bkPointDiagram J) n t (puncturedNativeCellToPoint D n z)).symm

private theorem puncturedCoefficientRadialHomotopy_projection
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (x : puncturedCoefficientStage D n) :
    puncturedCoefficientProjection D n (puncturedCoefficientRadialHomotopy D n (t, x)) =
      puncturedCoefficientRadialHomotopy (bkPointDiagram J) n
        (t, puncturedCoefficientProjection D n x) := by
  obtain ⟨a | z, rfl⟩ := (puncturedAttachmentQuotient_isQuotientMap D n).surjective x
  · have hp := puncturedCoefficientProjection_old_apply D n a
    exact (congrArg (puncturedCoefficientProjection D n)
      (puncturedCoefficientRadialHomotopy_on_old D n t a)).trans
        (hp.trans ((puncturedCoefficientRadialHomotopy_on_old (bkPointDiagram J) n t
          (coefficientPointStageProjection D n a)).symm.trans
            (congrArg (fun y => puncturedCoefficientRadialHomotopy (bkPointDiagram J) n (t, y))
              hp.symm)))
  · have hd := (puncturedCoefficientRadialHomotopy_quotient_apply D n t (Sum.inr z)).trans
      (prequotientCoefficientRadialFamily_inr D n t z)
    have hp := puncturedCoefficientProjection_native_apply D n z
    have hr := (puncturedCoefficientRadialHomotopy_quotient_apply (bkPointDiagram J) n t
      (Sum.inr (puncturedNativeCellToPoint D n z))).trans
        (prequotientCoefficientRadialFamily_inr (bkPointDiagram J) n t (puncturedNativeCellToPoint
          D n z))
    exact (congrArg (puncturedCoefficientProjection D n) hd).trans
      ((puncturedCoefficientProjection_native_apply D n (coefficientRadialFamily D n (t, z))).trans
        ((congrArg (fun q => puncturedAttachmentQuotient (bkPointDiagram J) n (Sum.inr q))
          (coefficientRadialFamily_point D n t z)).trans
            (hr.symm.trans (congrArg
              (fun y => puncturedCoefficientRadialHomotopy (bkPointDiagram J) n (t, y)) hp.symm))))

private theorem puncturedCoefficientRadialRetraction_projection
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (x : puncturedCoefficientStage D n) :
    coefficientPointStageProjection D n (puncturedCoefficientRadialRetraction D n x) =
      puncturedCoefficientRadialRetraction (bkPointDiagram J) n (puncturedCoefficientProjection D
        n x) := by
  apply (oldStagePuncturedInclusion_isEmbedding (bkPointDiagram J) n).injective
  have hp := puncturedCoefficientProjection_old_apply D n (puncturedCoefficientRadialRetraction D
    n x)
  have hd := (puncturedCoefficientRadialRetraction_inclusion_apply D n x).trans
    ((puncturedCoefficientRadialHomotopy D n).map_one_left x).symm
  have hr := (puncturedCoefficientRadialRetraction_inclusion_apply (bkPointDiagram J) n
    (puncturedCoefficientProjection D n x)).trans
      ((puncturedCoefficientRadialHomotopy (bkPointDiagram J) n).map_one_left
        (puncturedCoefficientProjection D n x)).symm
  exact hp.symm.trans ((congrArg (puncturedCoefficientProjection D n) hd).trans
    ((puncturedCoefficientRadialHomotopy_projection D n 1 x).trans hr.symm))

/-- The actual punctured projection to the point-diagram model of the
original nerve skeleton. Its original base coordinate is recorded below. -/
def bkCellPuncturedProjection {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellBarycenterComplement D n ⟶ bkCellBarycenterComplement (bkPointDiagram J) n :=
  TopCat.ofHom (puncturedCoefficientProjection D n)

private theorem bkCellPuncturedProjection_original_projection_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellPuncturedProjection D n ≫ bkCellBarycenterComplementInclusion (bkPointDiagram J) n ≫
        (bkNerveSkeletalCellModelIso J (n + 1)).hom =
      bkCellBarycenterComplementInclusion D n ≫ toTop.map (bkSkeletalProjection D (n + 1)) := by
  apply TopCat.ext
  intro x
  exact ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso J (n + 1)).inv_hom_id
    (toTop.map (bkSkeletalProjection D (n + 1)) x.1)

/-- The punctured projection retains the literal original skeletal
projection under the actual point-diagram model isomorphism. -/
@[reassoc]
theorem bkCellPuncturedProjection_original_projection
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellPuncturedProjection D n ≫ bkCellBarycenterComplementInclusion (bkPointDiagram J) n ≫
        (bkNerveSkeletalCellModelIso J (n + 1)).hom =
      bkCellBarycenterComplementInclusion D n ≫ toTop.map (bkSkeletalProjection D (n + 1)) :=
  bkCellPuncturedProjection_original_projection_aux D n

/-- The actual coefficient-fixed lift covers the actual base radial
homotopy at every parameter. Compatibility is derived on the actual
attachment quotient, including all boundary identifications. -/
theorem bkCellRadialHomotopy_projection
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (t : unitInterval) (x : bkCellBarycenterComplement D n) :
    bkCellPuncturedProjection D n (bkCellRadialHomotopy D n (t, x)) =
      bkCellRadialHomotopy (bkPointDiagram J) n (t, bkCellPuncturedProjection D n x) :=
  puncturedCoefficientRadialHomotopy_projection D n t x

private theorem bkCellRadialRetraction_original_projection_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellRadialRetraction D n ≫ toTop.map (bkSkeletalProjection D n) =
      bkCellPuncturedProjection D n ≫ bkCellRadialRetraction (bkPointDiagram J) n ≫
        (bkNerveSkeletalCellModelIso J n).hom := by
  apply TopCat.ext
  intro x
  have hp := puncturedCoefficientRadialRetraction_projection D n x
  have hi : (bkNerveSkeletalCellModelIso J n).hom
      (coefficientPointStageProjection D n (puncturedCoefficientRadialRetraction D n x)) =
        toTop.map (bkSkeletalProjection D n) (puncturedCoefficientRadialRetraction D n x) :=
    ConcreteCategory.congr_hom (bkNerveSkeletalCellModelIso J n).inv_hom_id
      (toTop.map (bkSkeletalProjection D n) (puncturedCoefficientRadialRetraction D n x))
  exact hi.symm.trans (congrArg (fun q => (bkNerveSkeletalCellModelIso J n).hom q) hp)

/-- The derived total and base retractions commute with the original
old-stage skeletal projection. -/
@[reassoc]
theorem bkCellRadialRetraction_original_projection
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellRadialRetraction D n ≫ toTop.map (bkSkeletalProjection D n) =
      bkCellPuncturedProjection D n ≫ bkCellRadialRetraction (bkPointDiagram J) n ≫
        (bkNerveSkeletalCellModelIso J n).hom :=
  bkCellRadialRetraction_original_projection_aux D n

private def pointFiberSubtypeHomeomorph {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    {z : E × PUnit.{u + 1} // p z.1 = b} ≃ₜ {e : E // p e = b} where
  toFun z := ⟨z.1.1, z.2⟩
  invFun e := ⟨(e.1, PUnit.unit), e.2⟩
  left_inv := by
    rintro ⟨⟨e, v⟩, he⟩
    apply Subtype.ext
    exact Prod.ext rfl (Subsingleton.elim _ _)
  right_inv := by intro e; rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.prodMk continuous_const).subtype_mk _

private def pointFiberSubtypeIso {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    pullback p (TopCat.const (X := TopCat.of PUnit) b) ≅ TopCat.of {e : E // p e = b} :=
  TopCat.pullbackIsoProdSubtype p (TopCat.const (X := TopCat.of PUnit) b) ≪≫
    TopCat.isoOfHomeo (pointFiberSubtypeHomeomorph p b)

private theorem pointFiberSubtypeIso_hom_fst {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    (pointFiberSubtypeIso p b).hom ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ =
      pullback.fst p (TopCat.const (X := TopCat.of PUnit) b) := by
  apply TopCat.ext
  intro z
  exact ConcreteCategory.congr_hom (TopCat.pullbackIsoProdSubtype_hom_fst p
    (TopCat.const (X := TopCat.of PUnit) b)) z

private theorem positiveCoefficientCell_isEmbedding
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i}) :
    IsEmbedding (fun x : toTop.obj (D.obj c.1.left) =>
      nativeCoefficientCellStageMap D n ⟨c, x, s.1⟩) := by
  let e := TopCat.homeoOfIso (bkNondegenerateCellInteriorProductIso D n)
  have he : IsEmbedding (fun x : toTop.obj (D.obj c.1.left) =>
      ((bkNondegenerateCellInteriorProductIso D n).hom ⟨c, x, s⟩).1) :=
    IsEmbedding.subtypeVal.comp
      (e.isEmbedding.comp (IsEmbedding.sigmaMk.comp (isEmbedding_prodMkLeft s)))
  have h : (fun x : toTop.obj (D.obj c.1.left) => nativeCoefficientCellStageMap D n ⟨c, x, s.1⟩) =
      (fun x => ((bkNondegenerateCellInteriorProductIso D n).hom ⟨c, x, s⟩).1) := by
    funext x
    exact (nativeCoefficientCellStageMap_apply D n c x s.1).trans
      (bkNondegenerateCellInteriorProductIso_hom_apply D n c x s).symm
  exact h.symm ▸ he

private theorem positivePointCell_not_mem_old
    (J : Type u) [Category.{v} J] (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i}) :
    nativeCoefficientCellStageMap (bkPointDiagram J) n
      ⟨c, pointCellCoefficient J c.1.left, s.1⟩ ∉
        Set.range (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) (Nat.le_succ n))) := by
  let y := (bkNondegenerateCellInteriorProductIso (bkPointDiagram J) n).hom
    ⟨c, pointCellCoefficient J c.1.left, s⟩
  have he : y.1 = nativeCoefficientCellStageMap (bkPointDiagram J) n
      ⟨c, pointCellCoefficient J c.1.left, s.1⟩ :=
    (bkNondegenerateCellInteriorProductIso_hom_apply (bkPointDiagram J) n c
      (pointCellCoefficient J c.1.left) s).trans
        (nativeCoefficientCellStageMap_apply (bkPointDiagram J) n c
          (pointCellCoefficient J c.1.left) s.1).symm
  exact he ▸ y.2

private theorem positiveCoefficientCell_surjective_onto_fiber
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i})
    (e : toTop.obj (bkSkeletalFiltration D (n + 1) : SSet.{max u v}))
    (hpe : coefficientPointStageProjection D (n + 1) e =
      nativeCoefficientCellStageMap (bkPointDiagram J) n
        ⟨c, pointCellCoefficient J c.1.left, s.1⟩) :
    ∃ x : toTop.obj (D.obj c.1.left), nativeCoefficientCellStageMap D n ⟨c, x, s.1⟩ = e := by
  have hout : e ∉ Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))) := by
    rintro ⟨a, ha⟩
    have hn := ConcreteCategory.congr_hom
      (coefficientPointStageProjection_natural D (Nat.le_succ n)) a
    exact (positivePointCell_not_mem_old J n c s)
      ⟨coefficientPointStageProjection D n a,
        hn.symm.trans ((congrArg (fun q => coefficientPointStageProjection D (n + 1) q) ha).trans
          hpe)⟩
  let i := bkNondegenerateCellInteriorProductIso D n
  let z := i.inv ⟨e, hout⟩
  have hz : i.hom z = ⟨e, hout⟩ := ConcreteCategory.congr_hom i.inv_hom_id ⟨e, hout⟩
  obtain ⟨d, x, t⟩ := z
  have hd : nativeCoefficientCellStageMap D n ⟨d, x, t.1⟩ = e :=
    ((nativeCoefficientCellStageMap_apply D n d x t.1).trans
      (bkNondegenerateCellInteriorProductIso_hom_apply D n d x t).symm).trans
        (congrArg Subtype.val hz)
  have hb := (coefficientPointStageProjection_native_apply D n d x t.1).symm.trans
    ((congrArg (fun q => coefficientPointStageProjection D (n + 1) q) hd).trans hpe)
  let j := bkNondegenerateCellInteriorProductIso (bkPointDiagram J) n
  have hD : (j.hom ⟨d, pointCellCoefficient J d.1.left, t⟩).1 =
      nativeCoefficientCellStageMap (bkPointDiagram J) n
        ⟨d, pointCellCoefficient J d.1.left, t.1⟩ :=
    (bkNondegenerateCellInteriorProductIso_hom_apply (bkPointDiagram J) n d
      (pointCellCoefficient J d.1.left) t).trans
        (nativeCoefficientCellStageMap_apply (bkPointDiagram J) n d
          (pointCellCoefficient J d.1.left) t.1).symm
  have hC : (j.hom ⟨c, pointCellCoefficient J c.1.left, s⟩).1 =
      nativeCoefficientCellStageMap (bkPointDiagram J) n
        ⟨c, pointCellCoefficient J c.1.left, s.1⟩ :=
    (bkNondegenerateCellInteriorProductIso_hom_apply (bkPointDiagram J) n c
      (pointCellCoefficient J c.1.left) s).trans
        (nativeCoefficientCellStageMap_apply (bkPointDiagram J) n c
          (pointCellCoefficient J c.1.left) s.1).symm
  have hsame : (⟨d, pointCellCoefficient J d.1.left, t⟩ : pointNativeCellInteriors J n) =
      ⟨c, pointCellCoefficient J c.1.left, s⟩ :=
    (TopCat.homeoOfIso j).injective (Subtype.ext (hD.trans (hb.trans hC.symm)))
  have hdc : d = c := congrArg Sigma.fst hsame
  subst d
  have hp : (pointCellCoefficient J c.1.left, t) = (pointCellCoefficient J c.1.left, s) :=
    eq_of_heq (Sigma.mk.inj hsame).2
  have ht : t = s := congrArg Prod.snd hp
  subst t
  exact ⟨x, hd⟩

private theorem positiveCoefficientCell_range
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i}) :
    Set.range (fun x : toTop.obj (D.obj c.1.left) => nativeCoefficientCellStageMap D n ⟨c, x,
      s.1⟩) =
      {e | coefficientPointStageProjection D (n + 1) e =
        nativeCoefficientCellStageMap (bkPointDiagram J) n
          ⟨c, pointCellCoefficient J c.1.left, s.1⟩} := by
  ext e
  constructor
  · rintro ⟨x, rfl⟩
    exact coefficientPointStageProjection_native_apply D n c x s.1
  · intro he
    exact positiveCoefficientCell_surjective_onto_fiber D n c s e he

private def positiveCoefficientFiberHomeomorph
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i}) :
    toTop.obj (D.obj c.1.left) ≃ₜ
      {e : toTop.obj (bkSkeletalFiltration D (n + 1) : SSet.{max u v}) //
        coefficientPointStageProjection D (n + 1) e =
          nativeCoefficientCellStageMap (bkPointDiagram J) n
            ⟨c, pointCellCoefficient J c.1.left, s.1⟩} :=
  (positiveCoefficientCell_isEmbedding D n c s).toHomeomorph.trans
    (Homeomorph.setCongr (positiveCoefficientCell_range D n c s))

private theorem positiveCoefficientFiberHomeomorph_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i})
    (x : toTop.obj (D.obj c.1.left)) :
    (positiveCoefficientFiberHomeomorph D n c s x).1 =
      nativeCoefficientCellStageMap D n ⟨c, x, s.1⟩ := rfl

private def positiveCoefficientFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i}) :
    toTop.obj (D.obj c.1.left) ≅
      pullback (coefficientPointStageProjection D (n + 1))
        (TopCat.const (X := TopCat.of PUnit)
          (nativeCoefficientCellStageMap (bkPointDiagram J) n
            ⟨c, pointCellCoefficient J c.1.left, s.1⟩)) :=
  TopCat.isoOfHomeo (positiveCoefficientFiberHomeomorph D n c s) ≪≫
    (pointFiberSubtypeIso (coefficientPointStageProjection D (n + 1))
      (nativeCoefficientCellStageMap (bkPointDiagram J) n
        ⟨c, pointCellCoefficient J c.1.left, s.1⟩)).symm

private theorem positiveCoefficientFiberIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i}) :
    (positiveCoefficientFiberIso D n c s).hom ≫
      pullback.fst (coefficientPointStageProjection D (n + 1))
        (TopCat.const (X := TopCat.of PUnit)
          (nativeCoefficientCellStageMap (bkPointDiagram J) n
            ⟨c, pointCellCoefficient J c.1.left, s.1⟩)) =
      TopCat.ofHom ⟨fun x => nativeCoefficientCellStageMap D n ⟨c, x, s.1⟩,
        (nativeCoefficientCellStageMap D n).hom.continuous.comp
          (continuous_sigmaMk.comp (continuous_id.prodMk continuous_const))⟩ := by
  let p := coefficientPointStageProjection D (n + 1)
  let b := nativeCoefficientCellStageMap (bkPointDiagram J) n
    ⟨c, pointCellCoefficient J c.1.left, s.1⟩
  rw [← pointFiberSubtypeIso_hom_fst p b]
  dsimp only [p, b]
  simp only [positiveCoefficientFiberIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  apply TopCat.ext
  exact positiveCoefficientFiberHomeomorph_apply D n c s

private theorem coefficientPointStageProjection_comp_model
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    coefficientPointStageProjection D n ≫ (bkNerveSkeletalCellModelIso J n).hom =
      toTop.map (bkSkeletalProjection D n) := by
  simp only [coefficientPointStageProjection, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem originalPointFiber_isPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : toTop.obj (bkSkeletalFiltration (bkPointDiagram J) n : SSet.{max u v})) :
    IsPullback
      (pullback.fst (coefficientPointStageProjection D n) (TopCat.const (X := TopCat.of PUnit) b))
      (pullback.snd (coefficientPointStageProjection D n) (TopCat.const (X := TopCat.of PUnit) b))
      (toTop.map (bkSkeletalProjection D n))
      (TopCat.const (X := TopCat.of PUnit) ((bkNerveSkeletalCellModelIso J n).hom b)) := by
  have sq : IsPullback (𝟙 (toTop.obj (bkSkeletalFiltration D n : SSet.{max u v})))
      (coefficientPointStageProjection D n) (toTop.map (bkSkeletalProjection D n))
      (bkNerveSkeletalCellModelIso J n).hom :=
    IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans
      (coefficientPointStageProjection_comp_model D n).symm⟩
  have outer := (IsPullback.of_hasPullback (coefficientPointStageProjection D n)
    (TopCat.const (X := TopCat.of PUnit) b)).paste_horiz sq
  have hc : TopCat.const (X := TopCat.of PUnit) b ≫ (bkNerveSkeletalCellModelIso J n).hom =
      TopCat.const (X := TopCat.of PUnit) ((bkNerveSkeletalCellModelIso J n).hom b) := by
    apply TopCat.ext
    intro v
    rfl
  simpa only [Category.comp_id, hc] using outer

private def originalPointFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : toTop.obj (bkSkeletalFiltration (bkPointDiagram J) n : SSet.{max u v})) :
    pullback (coefficientPointStageProjection D n) (TopCat.const (X := TopCat.of PUnit) b) ≅
      pullback (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit) ((bkNerveSkeletalCellModelIso J n).hom b)) :=
  (originalPointFiber_isPullback D n b).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

private theorem originalPointFiberIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : toTop.obj (bkSkeletalFiltration (bkPointDiagram J) n : SSet.{max u v})) :
    (originalPointFiberIso D n b).hom ≫
      pullback.fst (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit) ((bkNerveSkeletalCellModelIso J n).hom b)) =
      pullback.fst (coefficientPointStageProjection D n) (TopCat.const (X := TopCat.of PUnit) b) :=
  (originalPointFiber_isPullback D n b).isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback _ _)

private theorem pointNativeCell_original
    {J : Type u} [Category.{v} J] (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    (bkNerveSkeletalCellModelIso J (n + 1)).hom
      (nativeCoefficientCellStageMap (bkPointDiagram J) n
        ⟨c, pointCellCoefficient J c.1.left, s⟩) = bkNerveSkeletalCell J c.1 s :=
  congrArg (fun x => (bkNerveSkeletalCellModelIso J (n + 1)).hom x)
    (nativeCoefficientCellStageMap_apply (bkPointDiagram J) n c
      (pointCellCoefficient J c.1.left) s)

private theorem positiveOriginalPointFiber_isPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    IsPullback
      (pullback.fst (coefficientPointStageProjection D (n + 1))
        (TopCat.const (X := TopCat.of PUnit)
          (nativeCoefficientCellStageMap (bkPointDiagram J) n
            ⟨c, pointCellCoefficient J c.1.left, s⟩)))
      (pullback.snd (coefficientPointStageProjection D (n + 1))
        (TopCat.const (X := TopCat.of PUnit)
          (nativeCoefficientCellStageMap (bkPointDiagram J) n
            ⟨c, pointCellCoefficient J c.1.left, s⟩)))
      (toTop.map (bkSkeletalProjection D (n + 1)))
      (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s)) := by
  let b := nativeCoefficientCellStageMap (bkPointDiagram J) n
    ⟨c, pointCellCoefficient J c.1.left, s⟩
  exact (congrArg (fun y => IsPullback
    (pullback.fst (coefficientPointStageProjection D (n + 1))
      (TopCat.const (X := TopCat.of PUnit) b))
    (pullback.snd (coefficientPointStageProjection D (n + 1))
      (TopCat.const (X := TopCat.of PUnit) b))
    (toTop.map (bkSkeletalProjection D (n + 1))) (TopCat.const (X := TopCat.of PUnit) y))
    (pointNativeCell_original n c s)).mp (originalPointFiber_isPullback D (n + 1) b)

private def positiveOriginalFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i}) :
    toTop.obj (D.obj c.1.left) ≅
      pullback (toTop.map (bkSkeletalProjection D (n + 1)))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1)) :=
  positiveCoefficientFiberIso D n c s ≪≫
    (positiveOriginalPointFiber_isPullback D n c s.1).isoIsPullback _ _
      (IsPullback.of_hasPullback _ _)

/-- The coefficient space is the actual strict fiber of the original
realized skeletal projection at a positive point of a nondegenerate cell.
No weak transition hypothesis is needed. -/
def bkPositiveCellStrictFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i}) :
    toTop.obj (D.obj c.1.left) ≅
      pullback (toTop.map (bkSkeletalProjection D (n + 1)))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1)) :=
  positiveOriginalFiberIso D n c s

private theorem bkPositiveCellStrictFiberIso_hom_fst_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i})
    (x : toTop.obj (D.obj c.1.left)) :
    pullback.fst (toTop.map (bkSkeletalProjection D (n + 1)))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1))
      ((bkPositiveCellStrictFiberIso D n c s).hom x) =
      bkRealizedChainCellToStage D c.1 (x, s.1) := by
  have ht := (positiveOriginalPointFiber_isPullback D n c s.1).isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback _ _)
  have hc := positiveCoefficientFiberIso_hom_fst D n c s
  exact (ConcreteCategory.congr_hom ht ((positiveCoefficientFiberIso D n c s).hom x)).trans
    ((ConcreteCategory.congr_hom hc x).trans (nativeCoefficientCellStageMap_apply D n c x s.1))

/-- The positive-fiber isomorphism retains the literal closed-cell total
coordinate, including the coefficient point. -/
theorem bkPositiveCellStrictFiberIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i})
    (x : toTop.obj (D.obj c.1.left)) :
    pullback.fst (toTop.map (bkSkeletalProjection D (n + 1)))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1))
      ((bkPositiveCellStrictFiberIso D n c s).hom x) =
      bkRealizedChainCellToStage D c.1 (x, s.1) :=
  bkPositiveCellStrictFiberIso_hom_fst_aux D n c s x

private theorem skeletalProjectionMap_realized_isPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) :
    IsPullback (toTop.map (bkSkeletalFiltrationMap D h))
      (toTop.map (bkSkeletalProjection D m)) (toTop.map (bkSkeletalProjection D n))
      (bkNerveSkeletalMap J h) := by
  have he : toTop.map (bkSkeletalFiltrationMap D h) ≫
      toTop.map (bkSkeletalFiltration D n).ι = toTop.map (bkSkeletalFiltration D m).ι := by
    rw [← toTop.map_comp, bkSkeletalFiltrationMap_ι]
  have hb := bkNerveSkeletalMap_ι J h
  have outer : IsPullback
      (toTop.map (bkSkeletalFiltrationMap D h) ≫ toTop.map (bkSkeletalFiltration D n).ι)
      (toTop.map (bkSkeletalProjection D m)) (toTop.map (bkHocolimToNerve D))
      (bkNerveSkeletalMap J h ≫ toTop.map ((nerve J).skeleton (n + 1)).ι) := by
    rw [he, hb]
    exact bkSkeletalProjection_realized_isPullback D m
  have comm : toTop.map (bkSkeletalFiltrationMap D h) ≫ toTop.map (bkSkeletalProjection D n) =
      toTop.map (bkSkeletalProjection D m) ≫ bkNerveSkeletalMap J h := by
    simpa only [Functor.map_comp, bkNerveSkeletalMap] using
      congrArg toTop.map (skeletalProjection_natural D h)
  exact IsPullback.of_right outer comm (bkSkeletalProjection_realized_isPullback D n)

private def skeletalStrictFiberInclusionIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n)
    (b : toTop.obj ((nerve J).skeleton (m + 1) : SSet.{max u v})) :
    pullback (toTop.map (bkSkeletalProjection D m)) (TopCat.const (X := TopCat.of PUnit) b) ≅
      pullback (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalMap J h b)) :=
  TopCat.strictFiberRestrictionIso (skeletalProjectionMap_realized_isPullback D h) b

private theorem skeletalStrictFiberInclusionIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n)
    (b : toTop.obj ((nerve J).skeleton (m + 1) : SSet.{max u v})) :
    (skeletalStrictFiberInclusionIso D h b).hom ≫
      pullback.fst (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalMap J h b)) =
      pullback.fst (toTop.map (bkSkeletalProjection D m))
        (TopCat.const (X := TopCat.of PUnit) b) ≫ toTop.map (bkSkeletalFiltrationMap D h) :=
  TopCat.strictFiberRestrictionIso_hom_fst (skeletalProjectionMap_realized_isPullback D h) b

private def skeletalStrictFiberToGlobalIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) :
    pullback (toTop.map (bkSkeletalProjection D n)) (TopCat.const (X := TopCat.of PUnit) b) ≅
      pullback (toTop.map (bkHocolimToNerve D))
        (TopCat.const (X := TopCat.of PUnit) (toTop.map ((nerve J).skeleton (n + 1)).ι b)) :=
  TopCat.strictFiberRestrictionIso (bkSkeletalProjection_realized_isPullback D n) b

private theorem skeletalStrictFiberToGlobalIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : toTop.obj ((nerve J).skeleton (n + 1) : SSet.{max u v})) :
    (skeletalStrictFiberToGlobalIso D n b).hom ≫
      pullback.fst (toTop.map (bkHocolimToNerve D))
        (TopCat.const (X := TopCat.of PUnit) (toTop.map ((nerve J).skeleton (n + 1)).ι b)) =
      pullback.fst (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit) b) ≫ toTop.map (bkSkeletalFiltration D n).ι :=
  TopCat.strictFiberRestrictionIso_hom_fst (bkSkeletalProjection_realized_isPullback D n) b

section ZeroCellFiber

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem chainCell_zero_eq_pointInclusion
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v})
  (j : J) :
    bkChainCellMap D (ComposableArrows.mk₀ j) =
      CartesianMonoidalCategory.fst (D.obj j) (Δ[0] : SSet.{max u v}) ≫ bkPointInclusion D j := by
  ext a z
  obtain ⟨⟨m⟩⟩ := a
  obtain ⟨x, θ⟩ := z
  change (bkChainCellMap D (ComposableArrows.mk₀ j)).app (op ⦋m⦌) (x, θ) =
    (bkPointInclusion D j).app (op ⦋m⦌) x
  rw [bkChainCellMap_app_apply, bkPointInclusion_app_mk]
  have h := (bkPointOuterMap D j).naturality (stdSimplex.objEquiv θ).op
  simp only [bkPointOuterMap_app_mk, SimplicialObject.Data.constData_toSimplicialObject_map] at h
  have h' := ConcreteCategory.congr_hom (NatTrans.congr_app h (op ⦋m⦌)) x
  exact h'.symm

private theorem realizedChainCell_eq_product {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v})
    {n : ℕ} (c : ComposableArrows J n) :
    bkRealizedChainCell D c = (bkChainCellProductIso D c).inv ≫ toTop.map (bkChainCellMap D c) := by
  rw [← bkRealizedChainCellToStage_ι, bkRealizedChainCellToStage_eq, Category.assoc,
    ← Functor.map_comp, bkChainCellToStage_ι]

private theorem realizedChainCell_zero_apply {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v})
    (j : J) (x : toTop.obj (D.obj j)) (s : Convexity.StdSimplex ℝ (Fin 1)) :
    bkRealizedChainCell D (ComposableArrows.mk₀ j) (x, s) = toTop.map (bkPointInclusion D j) x := by
  let e := bkChainCellProductIso D (ComposableArrows.mk₀ j)
  have hp := ConcreteCategory.congr_hom e.inv_hom_id (x, s)
  have hc := bkChainCellProductIso_hom_apply D (ComposableArrows.mk₀ j) (e.inv (x, s))
  have hx := congrArg Prod.fst (hc.symm.trans hp)
  have hm := congrArg toTop.map (chainCell_zero_eq_pointInclusion D j)
  simp only [Functor.map_comp] at hm
  exact (ConcreteCategory.congr_hom (realizedChainCell_eq_product D (ComposableArrows.mk₀ j)) (x,
    s)).trans
    ((ConcreteCategory.congr_hom hm (e.inv (x, s))).trans
      (congrArg (fun y => toTop.map (bkPointInclusion D j) y) hx))

private theorem zeroNerveCell_vertex {J : Type u} [Category.{v} J] (j : J)
    (s : Convexity.StdSimplex ℝ (Fin 1)) :
    toTop.map ((nerve J).skeleton 1).ι (bkNerveSkeletalCell J (ComposableArrows.mk₀ j) s) =
      bkPointRealizedVertex j := by
  have hy : (yonedaEquiv.symm (ComposableArrows.mk₀ j) : (Δ[0] : SSet.{max u v}) ⟶ nerve J) =
      SSet.const (X := Δ[0]) (ComposableArrows.mk₀ j) :=
    yonedaEquiv_symm_zero (X := nerve J) (ComposableArrows.mk₀ j)
  rw [bkNerveSkeletalCell_ι_apply, hy]
  exact DFunLike.congr_fun (toTop_map_const_hom (A := Δ[0]) (Y := nerve J) (ComposableArrows.mk₀
    j)) _


private theorem realizedChainCell_zero_apply_chain
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (c : ComposableArrows J 0)
    (x : toTop.obj (D.obj c.left)) (s : Convexity.StdSimplex ℝ (Fin 1)) :
    bkRealizedChainCell D c (x, s) = toTop.map (bkPointInclusion D c.left) x := by
  obtain ⟨j, rfl⟩ := ComposableArrows.mk₀_surjective c
  exact realizedChainCell_zero_apply D j x s

private theorem zeroNerveCell_vertex_chain
    {J : Type u} [Category.{v} J] (c : ComposableArrows J 0)
    (s : Convexity.StdSimplex ℝ (Fin 1)) :
    toTop.map ((nerve J).skeleton 1).ι (bkNerveSkeletalCell J c s) =
      bkPointRealizedVertex c.left := by
  obtain ⟨j, rfl⟩ := ComposableArrows.mk₀_surjective c
  exact zeroNerveCell_vertex j s

private theorem zeroStagePointPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (c : ComposableArrows J 0)
    (s : Convexity.StdSimplex ℝ (Fin 1)) :
    IsPullback
      (pullback.fst (toTop.map (bkSkeletalProjection D 0))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c s)) ≫
          toTop.map (bkSkeletalFiltration D 0).ι)
      (pullback.snd (toTop.map (bkSkeletalProjection D 0))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c s)))
      (toTop.map (bkHocolimToNerve D))
      (TopCat.const (X := TopCat.of PUnit) (bkPointRealizedVertex c.left)) := by
  let b := bkNerveSkeletalCell J c s
  have outer := (IsPullback.of_hasPullback (toTop.map (bkSkeletalProjection D 0))
    (TopCat.const (X := TopCat.of PUnit) b)).paste_horiz
      (bkSkeletalProjection_realized_isPullback D 0)
  have hc : TopCat.const (X := TopCat.of PUnit) b ≫ toTop.map ((nerve J).skeleton 1).ι =
      TopCat.const (X := TopCat.of PUnit) (bkPointRealizedVertex c.left) := by
    apply TopCat.ext
    intro q
    exact zeroNerveCell_vertex_chain c s
  rw [hc] at outer
  exact outer

private def zeroStageFiberToGlobalIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (c : ComposableArrows J 0)
    (s : Convexity.StdSimplex ℝ (Fin 1)) :
    pullback (toTop.map (bkSkeletalProjection D 0))
      (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c s)) ≅
        pullback (toTop.map (bkHocolimToNerve D))
          (TopCat.const (X := TopCat.of PUnit) (bkPointRealizedVertex c.left)) :=
  (zeroStagePointPullback D c s).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

private def zeroCellFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (c : ComposableArrows J 0)
    (s : Convexity.StdSimplex ℝ (Fin 1)) :
    toTop.obj (D.obj c.left) ≅ pullback (toTop.map (bkSkeletalProjection D 0))
      (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c s)) :=
  bkPointStrictFiberIso D c.left ≪≫ (zeroStageFiberToGlobalIso D c s).symm

private theorem zeroCellFiberIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (c : ComposableArrows J 0)
    (s : Convexity.StdSimplex ℝ (Fin 1)) (x : toTop.obj (D.obj c.left)) :
    pullback.fst (toTop.map (bkSkeletalProjection D 0))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c s))
      ((zeroCellFiberIso D c s).hom x) =
        bkRealizedChainCellToStage D c (x, s) := by
  have hi := (TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (closedT1Embeddings_toTop_map_of_mono (bkSkeletalFiltration D 0).ι)).isEmbedding.injective
  apply hi
  have hf := (zeroStagePointPullback D c s).isoIsPullback_inv_fst _ _
    (IsPullback.of_hasPullback _ _)
  have hp := ConcreteCategory.congr_hom (bkPointStrictFiberIso_hom_fst D c.left) x
  have hr := (ConcreteCategory.congr_hom
    (bkRealizedChainCellToStage_ι D c) (x, s)).trans
      (realizedChainCell_zero_apply_chain D c x s)
  exact (ConcreteCategory.congr_hom hf ((bkPointStrictFiberIso D c.left).hom x)).trans
    (hp.trans hr.symm)

private def allDimensionalCellFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : (nerve J).nonDegenerate n)
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < s.weights i}) :
    toTop.obj (D.obj c.1.left) ≅ pullback (toTop.map (bkSkeletalProjection D n))
      (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1)) := by
  cases n with
  | zero => exact zeroCellFiberIso D c.1 s.1
  | succ n => exact bkPositiveCellStrictFiberIso D n c s

/-- The actual strict fiber over a positive point of a nondegenerate nerve
cell is its first coefficient realization, in every dimension including zero. -/
def bkCellStrictFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : (nerve J).nonDegenerate n)
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < s.weights i}) :
    toTop.obj (D.obj c.1.left) ≅ pullback (toTop.map (bkSkeletalProjection D n))
      (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1)) :=
  allDimensionalCellFiberIso D c s

private theorem bkCellStrictFiberIso_hom_fst_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : (nerve J).nonDegenerate n)
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < s.weights i})
    (x : toTop.obj (D.obj c.1.left)) :
    pullback.fst (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1))
      ((bkCellStrictFiberIso D c s).hom x) = bkRealizedChainCellToStage D c.1 (x, s.1) := by
  cases n with
  | zero => exact zeroCellFiberIso_hom_fst D c.1 s.1 x
  | succ n => exact bkPositiveCellStrictFiberIso_hom_fst D n c s x

/-- The all-dimensional fiber dictionary retains the actual closed-cell total
coordinate, so subsequent fiber maps can be checked through the original projection. -/
theorem bkCellStrictFiberIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : (nerve J).nonDegenerate n)
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < s.weights i})
    (x : toTop.obj (D.obj c.1.left)) :
    pullback.fst (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1))
      ((bkCellStrictFiberIso D c s).hom x) = bkRealizedChainCellToStage D c.1 (x, s.1) :=
  bkCellStrictFiberIso_hom_fst_aux D c s x

end ZeroCellFiber

section RadialEndpointFibers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def pointModelCellPoint
    {J : Type u} [Category.{v} J] {n : ℕ} (c : ComposableArrows J n)
    (s : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    toTop.obj (bkSkeletalFiltration (bkPointDiagram J) n : SSet.{max u v}) :=
  bkRealizedChainCellToStage (bkPointDiagram J) c (pointCellCoefficient J c.left, s)

private def pointModelCellFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : (nerve J).nonDegenerate n)
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < s.weights i}) :
    toTop.obj (D.obj c.1.left) ≅ pullback (coefficientPointStageProjection D n)
      (TopCat.const (X := TopCat.of PUnit) (pointModelCellPoint c.1 s.1)) :=
  bkCellStrictFiberIso D c s ≪≫ (originalPointFiberIso D n (pointModelCellPoint c.1 s.1)).symm

private theorem pointModelCellFiberIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : (nerve J).nonDegenerate n)
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < s.weights i})
    (x : toTop.obj (D.obj c.1.left)) :
    pullback.fst (coefficientPointStageProjection D n)
        (TopCat.const (X := TopCat.of PUnit) (pointModelCellPoint c.1 s.1))
      ((pointModelCellFiberIso D c s).hom x) = bkRealizedChainCellToStage D c.1 (x, s.1) := by
  have hf := (originalPointFiber_isPullback D n (pointModelCellPoint c.1 s.1)).isoIsPullback_inv_fst
    _ _ (IsPullback.of_hasPullback _ _)
  exact (ConcreteCategory.congr_hom hf ((bkCellStrictFiberIso D c s).hom x)).trans
    (bkCellStrictFiberIso_hom_fst D c s x)

private theorem pointModelSkeletalMap_isPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) :
    IsPullback (toTop.map (bkSkeletalFiltrationMap D h))
      (coefficientPointStageProjection D m) (coefficientPointStageProjection D n)
      (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) h)) := by
  apply (skeletalProjectionMap_realized_isPullback D h).of_iso'
    (Iso.refl _) (Iso.refl _) (bkNerveSkeletalCellModelIso J m) (bkNerveSkeletalCellModelIso J n)
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientPointStageProjection_comp_model D m).symm
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientPointStageProjection_comp_model D n).symm
  · exact (bkNerveSkeletalCellModelIso_natural J h).symm

private theorem puncturedCoefficientProjection_isPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsPullback (bkCellBarycenterComplementInclusion D n) (bkCellPuncturedProjection D n)
      (coefficientPointStageProjection D (n + 1))
      (bkCellBarycenterComplementInclusion (bkPointDiagram J) n) := by
  let p := coefficientPointStageProjection D (n + 1)
  let W := (coefficientCellCenters (bkPointDiagram J) n)ᶜ
  have hs : (coefficientCellCenters D n)ᶜ = p ⁻¹' W := by
    ext x
    exact not_congr (coefficientPointStageProjection_mem_centers_iff D n x).symm
  let e : TopCat.of ↥((coefficientCellCenters D n)ᶜ) ≅ TopCat.of ↥(p ⁻¹' W) :=
    TopCat.isoOfHomeo (Homeomorph.setCongr hs)
  have sq := TopCat.restrictionProjection_isPullback p W
  apply sq.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · apply TopCat.ext
    intro x
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    apply (cancel_mono (AlgebraicTopology.subspaceIncl W)).mp
    exact sq.w.symm.trans (by
      apply TopCat.ext
      intro x
      rfl)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · apply TopCat.ext
    intro x
    rfl

private theorem oldPuncturedCoefficientProjection_isPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsPullback (bkCellOldStageInclusion D n) (coefficientPointStageProjection D n)
      (bkCellPuncturedProjection D n) (bkCellOldStageInclusion (bkPointDiagram J) n) := by
  have outer : IsPullback
      (bkCellOldStageInclusion D n ≫ bkCellBarycenterComplementInclusion D n)
      (coefficientPointStageProjection D n) (coefficientPointStageProjection D (n + 1))
      (bkCellOldStageInclusion (bkPointDiagram J) n ≫
        bkCellBarycenterComplementInclusion (bkPointDiagram J) n) := by
    rw [bkCellOldStageInclusion_comp_inclusion, bkCellOldStageInclusion_comp_inclusion]
    exact pointModelSkeletalMap_isPullback D (Nat.le_succ n)
  have comm : bkCellOldStageInclusion D n ≫ bkCellPuncturedProjection D n =
      coefficientPointStageProjection D n ≫ bkCellOldStageInclusion (bkPointDiagram J) n := by
    apply TopCat.ext
    intro x
    exact puncturedCoefficientProjection_old_apply D n x
  exact IsPullback.of_right outer comm (puncturedCoefficientProjection_isPullback D n)

private theorem radialRetraction_comm
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkCellRadialRetraction D n ≫ coefficientPointStageProjection D n =
      bkCellPuncturedProjection D n ≫ bkCellRadialRetraction (bkPointDiagram J) n := by
  apply TopCat.ext
  intro x
  exact puncturedCoefficientRadialRetraction_projection D n x

private theorem pointFiberEq_isPullback {E B : TopCat.{u}} (p : E ⟶ B)
    (b b' : B) (h : b = b') :
    IsPullback (pullback.fst p (TopCat.const (X := TopCat.of PUnit) b))
      (pullback.snd p (TopCat.const (X := TopCat.of PUnit) b)) p
      (TopCat.const (X := TopCat.of PUnit) b') :=
  (congrArg (fun y => IsPullback
    (pullback.fst p (TopCat.const (X := TopCat.of PUnit) b))
    (pullback.snd p (TopCat.const (X := TopCat.of PUnit) b)) p
    (TopCat.const (X := TopCat.of PUnit) y)) h).mp (IsPullback.of_hasPullback _ _)

private def pointFiberEqIso {E B : TopCat.{u}} (p : E ⟶ B) (b b' : B) (h : b = b') :
    pullback p (TopCat.const (X := TopCat.of PUnit) b) ≅
      pullback p (TopCat.const (X := TopCat.of PUnit) b') :=
  (pointFiberEq_isPullback p b b' h).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

private theorem pointFiberEqIso_hom_fst {E B : TopCat.{u}} (p : E ⟶ B)
    (b b' : B) (h : b = b') :
    (pointFiberEqIso p b b' h).hom ≫ pullback.fst p (TopCat.const (X := TopCat.of PUnit) b') =
      pullback.fst p (TopCat.const (X := TopCat.of PUnit) b) :=
  (pointFiberEq_isPullback p b b' h).isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback _ _)

private def radialPointModelStrictFiberMap
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    pullback (bkCellPuncturedProjection D n) (TopCat.const (X := TopCat.of PUnit) a) ⟶
      pullback (coefficientPointStageProjection D n)
        (TopCat.const (X := TopCat.of PUnit) (bkCellRadialRetraction (bkPointDiagram J) n a)) :=
  TopCat.strictFiberMapOfSquare (bkCellRadialRetraction D n)
    (bkCellRadialRetraction (bkPointDiagram J) n) (radialRetraction_comm D n).symm a

private theorem radialPointModelStrictFiberMap_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    radialPointModelStrictFiberMap D n a ≫
      pullback.fst (coefficientPointStageProjection D n)
        (TopCat.const (X := TopCat.of PUnit) (bkCellRadialRetraction (bkPointDiagram J) n a)) =
      pullback.fst (bkCellPuncturedProjection D n) (TopCat.const (X := TopCat.of PUnit) a) ≫
        bkCellRadialRetraction D n :=
  TopCat.strictFiberMapOfSquare_fst (bkCellRadialRetraction D n)
    (bkCellRadialRetraction (bkPointDiagram J) n) (radialRetraction_comm D n).symm a

private theorem radialPointModelStrictFiberMap_mem_on_old
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (b : toTop.obj (bkSkeletalFiltration (bkPointDiagram J) n : SSet.{max u v})) :
    TopCat.weakHomotopyEquivalences (radialPointModelStrictFiberMap D n
      (bkCellOldStageInclusion (bkPointDiagram J) n b)) := by
  let a := bkCellOldStageInclusion (bkPointDiagram J) n b
  let i := TopCat.strictFiberRestrictionIso (oldPuncturedCoefficientProjection_isPullback D n) b
  have hb : b = bkCellRadialRetraction (bkPointDiagram J) n a :=
    (ConcreteCategory.congr_hom (bkCellRadialRetraction_retract (bkPointDiagram J) n) b).symm
  let t := pointFiberEqIso (coefficientPointStageProjection D n) b
    (bkCellRadialRetraction (bkPointDiagram J) n a) hb
  have he : i.hom ≫ radialPointModelStrictFiberMap D n a = t.hom := by
    apply pullback.hom_ext
    · calc
        (i.hom ≫ radialPointModelStrictFiberMap D n a) ≫
            pullback.fst (coefficientPointStageProjection D n)
              (TopCat.const (X := TopCat.of PUnit) (bkCellRadialRetraction (bkPointDiagram J) n
                a)) =
          (pullback.fst (coefficientPointStageProjection D n)
            (TopCat.const (X := TopCat.of PUnit) b) ≫ bkCellOldStageInclusion D n) ≫
              bkCellRadialRetraction D n := by
                rw [Category.assoc, radialPointModelStrictFiberMap_fst, ← Category.assoc,
                  TopCat.strictFiberRestrictionIso_hom_fst]
        _ = pullback.fst (coefficientPointStageProjection D n)
            (TopCat.const (X := TopCat.of PUnit) b) := by
              rw [Category.assoc, bkCellRadialRetraction_retract, Category.comp_id]
        _ = t.hom ≫ pullback.fst (coefficientPointStageProjection D n)
            (TopCat.const (X := TopCat.of PUnit) (bkCellRadialRetraction (bkPointDiagram J) n a)) :=
              (pointFiberEqIso_hom_fst _ _ _ hb).symm
    · apply TopCat.isTerminalPUnit.hom_ext
  have hi : TopCat.weakHomotopyEquivalences i.hom := TopCat.weakHomotopyEquivalences.of_isIso _
  have he' : TopCat.weakHomotopyEquivalences (i.hom ≫ radialPointModelStrictFiberMap D n a) := by
    rw [he]
    exact TopCat.weakHomotopyEquivalences.of_isIso _
  exact TopCat.weakHomotopyEquivalences.of_precomp _ _ hi he'

private theorem radialEndpoint_nondegenerate_presentation
    {J : Type u} [Category.{v} J] (n : ℕ) (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) :
    ∃ (m : ℕ) (d : (nerve J).nonDegenerate m)
      (q : Convexity.StdSimplex ℝ (Fin (m + 1))) (g : c.1.left ⟶ d.1.left),
      m ≤ n ∧ (∀ i, 0 < q.weights i) ∧
        ∀ (D : J ⥤ SSet.{max u v}) (x : toTop.obj (D.obj c.1.left)),
          bkRealizedChainCell D c.1 (x, StdSimplexRadialBoundary.radialMap (n + 1) s) =
            bkRealizedChainCell D d.1 (toTop.map (D.map g) x, q) := by
  obtain ⟨i, hi⟩ := StdSimplexRadialBoundary.exists_radialMap_weights_eq_zero (n + 1) s
  obtain ⟨p, hp⟩ := exists_simplex_face_of_zero
    (StdSimplexRadialBoundary.radialMap (n + 1) s) i hi
  let θ := SimplexCategory.δ i
  let e : ComposableArrows J n := (nerve J).map θ.op c.1
  obtain ⟨m, d, q, g, hm, hq, hg⟩ := realizedChainCell_positive_nondegenerate_presentation e p
  refine ⟨m, d, q, bkChainFirstArrow c.1 θ ≫ g, hm, hq, fun D x => ?_⟩
  have hf := (congrArg (fun t => bkRealizedChainCell D c.1 (x, t)) hp).symm.trans
    (realizedChainCell_reindex_apply D c.1 θ x p)
  have hcomp : toTop.map (D.map (bkChainFirstArrow c.1 θ ≫ g)) x =
      toTop.map (D.map g) (toTop.map (D.map (bkChainFirstArrow c.1 θ)) x) := by
    rw [D.map_comp, toTop.map_comp]
    rfl
  exact hf.trans ((hg D (toTop.map (D.map (bkChainFirstArrow c.1 θ)) x)).trans
    (congrArg (fun y => bkRealizedChainCell D d.1 (y, q)) hcomp.symm))

private theorem radialRetraction_cell_global_endpoint
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) :
    toTop.map (bkSkeletalFiltration D n).ι
      (bkCellRadialRetraction D n (bkPuncturedNondegenerateCell D n c (x, s))) =
      bkRealizedChainCell D c.1 (x, StdSimplexRadialBoundary.radialMap (n + 1) s) := by
  have hs := bkCellRadialRetraction_cell_endpoint D n c x s
  have him := congrArg toTop.map (bkSkeletalFiltrationMap_ι D (Nat.le_succ n))
  rw [Functor.map_comp] at him
  have hi := ConcreteCategory.congr_hom him
      (bkCellRadialRetraction D n (bkPuncturedNondegenerateCell D n c (x, s)))
  have hc := ConcreteCategory.congr_hom (bkRealizedChainCellToStage_ι D c.1)
    (x, StdSimplexRadialBoundary.radialMap (n + 1) s)
  exact hi.symm.trans ((congrArg (fun z => toTop.map (bkSkeletalFiltration D (n + 1)).ι z)
    hs).trans hc)

private def puncturedCellPoint
    {J : Type u} [Category.{v} J] (n : ℕ) (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) :
    bkCellBarycenterComplement (bkPointDiagram J) n :=
  bkPuncturedNondegenerateCell (bkPointDiagram J) n c (pointCellCoefficient J c.1.left, s)

private theorem puncturedCellPointPullback
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) :
    IsPullback
      (pullback.fst (bkCellPuncturedProjection D n)
        (TopCat.const (X := TopCat.of PUnit) (puncturedCellPoint n c s)) ≫
          bkCellBarycenterComplementInclusion D n)
      (pullback.snd (bkCellPuncturedProjection D n)
        (TopCat.const (X := TopCat.of PUnit) (puncturedCellPoint n c s)))
      (coefficientPointStageProjection D (n + 1))
      (TopCat.const (X := TopCat.of PUnit) (pointModelCellPoint c.1 s.1)) := by
  have outer := (IsPullback.of_hasPullback (bkCellPuncturedProjection D n)
    (TopCat.const (X := TopCat.of PUnit) (puncturedCellPoint n c s))).paste_horiz
      (puncturedCoefficientProjection_isPullback D n)
  have hc : TopCat.const (X := TopCat.of PUnit) (puncturedCellPoint n c s) ≫
      bkCellBarycenterComplementInclusion (bkPointDiagram J) n =
        TopCat.const (X := TopCat.of PUnit) (pointModelCellPoint c.1 s.1) := by
    apply TopCat.ext
    intro q
    exact bkPuncturedNondegenerateCell_inclusion_apply (bkPointDiagram J) n c
      (pointCellCoefficient J c.1.left) s
  rw [hc] at outer
  exact outer

private def puncturedCellFiberToStageIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) :
    pullback (bkCellPuncturedProjection D n)
      (TopCat.const (X := TopCat.of PUnit) (puncturedCellPoint n c s)) ≅
        pullback (coefficientPointStageProjection D (n + 1))
          (TopCat.const (X := TopCat.of PUnit) (pointModelCellPoint c.1 s.1)) :=
  (puncturedCellPointPullback D n c s).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

private def puncturedPositiveCellFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter})
    (hpos : ∀ i, 0 < s.1.weights i) :
    toTop.obj (D.obj c.1.left) ≅ pullback (bkCellPuncturedProjection D n)
      (TopCat.const (X := TopCat.of PUnit) (puncturedCellPoint n c s)) :=
  pointModelCellFiberIso D c ⟨s.1, hpos⟩ ≪≫ (puncturedCellFiberToStageIso D n c s).symm

private theorem puncturedPositiveCellFiberIso_hom_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter})
    (hpos : ∀ i, 0 < s.1.weights i) (x : toTop.obj (D.obj c.1.left)) :
    pullback.fst (bkCellPuncturedProjection D n)
        (TopCat.const (X := TopCat.of PUnit) (puncturedCellPoint n c s))
      ((puncturedPositiveCellFiberIso D n c s hpos).hom x) =
      bkPuncturedNondegenerateCell D n c (x, s) := by
  apply Subtype.ext
  have hf := (puncturedCellPointPullback D n c s).isoIsPullback_inv_fst _ _
    (IsPullback.of_hasPullback _ _)
  exact (ConcreteCategory.congr_hom hf ((pointModelCellFiberIso D c ⟨s.1, hpos⟩).hom x)).trans
    ((pointModelCellFiberIso_hom_fst D c ⟨s.1, hpos⟩ x).trans
      (bkPuncturedNondegenerateCell_inclusion_apply D n c x s).symm)

private def pointModelSkeletalCellFiberIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n)
    (d : (nerve J).nonDegenerate m)
    (q : {q : Convexity.StdSimplex ℝ (Fin (m + 1)) // ∀ i, 0 < q.weights i}) :
    toTop.obj (D.obj d.1.left) ≅ pullback (coefficientPointStageProjection D n)
      (TopCat.const (X := TopCat.of PUnit)
        (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) h) (pointModelCellPoint d.1 q.1))) :=
  pointModelCellFiberIso D d q ≪≫ TopCat.strictFiberRestrictionIso
    (pointModelSkeletalMap_isPullback D h) (pointModelCellPoint d.1 q.1)

private theorem pointModelSkeletalCellPoint_global
    {J : Type u} [Category.{v} J] {m n : ℕ} (h : m ≤ n)
    (d : ComposableArrows J m) (q : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    toTop.map (bkSkeletalFiltration (bkPointDiagram J) n).ι
      (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) h) (pointModelCellPoint d q)) =
        bkRealizedChainCell (bkPointDiagram J) d (pointCellCoefficient J d.left, q) := by
  have hm := congrArg toTop.map (bkSkeletalFiltrationMap_ι (bkPointDiagram J) h)
  rw [Functor.map_comp] at hm
  exact (ConcreteCategory.congr_hom hm (pointModelCellPoint d q)).trans
    (ConcreteCategory.congr_hom (bkRealizedChainCellToStage_ι (bkPointDiagram J) d)
      (pointCellCoefficient J d.left, q))

private theorem pointModelSkeletalCellFiberIso_hom_fst_global
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n)
    (d : (nerve J).nonDegenerate m)
    (q : {q : Convexity.StdSimplex ℝ (Fin (m + 1)) // ∀ i, 0 < q.weights i})
    (x : toTop.obj (D.obj d.1.left)) :
    toTop.map (bkSkeletalFiltration D n).ι
      (pullback.fst (coefficientPointStageProjection D n)
        (TopCat.const (X := TopCat.of PUnit)
          (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) h) (pointModelCellPoint d.1 q.1)))
        ((pointModelSkeletalCellFiberIso D h d q).hom x)) = bkRealizedChainCell D d.1 (x, q.1) := by
  have ht := ConcreteCategory.congr_hom
    (TopCat.strictFiberRestrictionIso_hom_fst (pointModelSkeletalMap_isPullback D h)
      (pointModelCellPoint d.1 q.1)) ((pointModelCellFiberIso D d q).hom x)
  have hc := pointModelCellFiberIso_hom_fst D d q x
  have hm := congrArg toTop.map (bkSkeletalFiltrationMap_ι D h)
  rw [Functor.map_comp] at hm
  exact (congrArg (fun z => toTop.map (bkSkeletalFiltration D n).ι z) ht).trans
    ((congrArg (fun z => toTop.map (bkSkeletalFiltration D n).ι
      (toTop.map (bkSkeletalFiltrationMap D h) z)) hc).trans
      ((ConcreteCategory.congr_hom hm (bkRealizedChainCellToStage D d.1 (x, q.1))).trans
        (ConcreteCategory.congr_hom (bkRealizedChainCellToStage_ι D d.1) (x, q.1))))

private theorem pointCellCoefficient_map
    {J : Type u} [Category.{v} J] {j k : J} (g : j ⟶ k) :
    toTop.map ((bkPointDiagram J).map g) (pointCellCoefficient J j) =
      pointCellCoefficient J k := by
  change (_ : toTop.obj (Δ[0] : SSet.{max u v})) = _
  exact Subsingleton.elim _ _

private theorem radialPointModelStrictFiberMap_mem_on_cell
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter})
    (hpos : ∀ i, 0 < s.1.weights i)
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g))) :
    TopCat.weakHomotopyEquivalences (radialPointModelStrictFiberMap D n (puncturedCellPoint n c
      s)) := by
  obtain ⟨m, d, q, g, hm, hq, hg⟩ := radialEndpoint_nondegenerate_presentation n c s
  let a := puncturedCellPoint n c s
  let b := toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) hm) (pointModelCellPoint d.1 q)
  let b' := bkCellRadialRetraction (bkPointDiagram J) n a
  have hb : b = b' := by
    have hi := (TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (closedT1Embeddings_toTop_map_of_mono (bkSkeletalFiltration (bkPointDiagram J)
        n).ι)).isEmbedding.injective
    apply hi
    have hl := pointModelSkeletalCellPoint_global hm d.1 q
    have hr := (radialRetraction_cell_global_endpoint (bkPointDiagram J) n c
      (pointCellCoefficient J c.1.left) s).trans (hg (bkPointDiagram J) (pointCellCoefficient J
        c.1.left))
    have he := congrArg (fun y => bkRealizedChainCell (bkPointDiagram J) d.1 (y, q))
      (pointCellCoefficient_map g)
    exact hl.trans (hr.trans he).symm
  let sourceIso := puncturedPositiveCellFiberIso D n c s hpos
  let stageIso := pointModelSkeletalCellFiberIso D hm d ⟨q, hq⟩
  let targetIso := stageIso ≪≫ pointFiberEqIso (coefficientPointStageProjection D n) b b' hb
  have ht : ∀ y : toTop.obj (D.obj d.1.left),
      toTop.map (bkSkeletalFiltration D n).ι
        (pullback.fst (coefficientPointStageProjection D n)
          (TopCat.const (X := TopCat.of PUnit) b') (targetIso.hom y)) =
            bkRealizedChainCell D d.1 (y, q) := by
    intro y
    have hf := ConcreteCategory.congr_hom (pointFiberEqIso_hom_fst
      (coefficientPointStageProjection D n) b b' hb) (stageIso.hom y)
    exact (congrArg (fun z => toTop.map (bkSkeletalFiltration D n).ι z) hf).trans
      (pointModelSkeletalCellFiberIso_hom_fst_global D hm d ⟨q, hq⟩ y)
  have he : sourceIso.hom ≫ radialPointModelStrictFiberMap D n a =
      toTop.map (D.map g) ≫ targetIso.hom := by
    apply pullback.hom_ext
    · apply TopCat.ext
      intro x
      have hi := (TopCat.closedT1Embeddings_le_isClosedEmbedding _
        (closedT1Embeddings_toTop_map_of_mono (bkSkeletalFiltration D n).ι)).isEmbedding.injective
      apply hi
      have hf := ConcreteCategory.congr_hom (radialPointModelStrictFiberMap_fst D n a)
        (sourceIso.hom x)
      have hc := puncturedPositiveCellFiberIso_hom_fst D n c s hpos x
      exact (congrArg (fun z => toTop.map (bkSkeletalFiltration D n).ι z) hf).trans
        ((congrArg (fun z => toTop.map (bkSkeletalFiltration D n).ι (bkCellRadialRetraction D n
          z)) hc).trans
          ((radialRetraction_cell_global_endpoint D n c x s).trans
            ((hg D x).trans (ht (toTop.map (D.map g) x)).symm)))
    · apply TopCat.isTerminalPUnit.hom_ext
  have hs : TopCat.weakHomotopyEquivalences sourceIso.hom :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have ht' : TopCat.weakHomotopyEquivalences targetIso.hom :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hw : TopCat.weakHomotopyEquivalences (sourceIso.hom ≫ radialPointModelStrictFiberMap D n a)
    := by
    rw [he]
    exact TopCat.weakHomotopyEquivalences.comp_mem _ _ (hD c.1.left d.1.left g) ht'
  exact TopCat.weakHomotopyEquivalences.of_precomp _ _ hs hw

private theorem radialPointModelStrictFiberMap_mem
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    TopCat.weakHomotopyEquivalences (radialPointModelStrictFiberMap D n a) := by
  classical
  by_cases ho : a.1 ∈ Set.range (toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J)
    (Nat.le_succ n)))
  · obtain ⟨b, hb⟩ := ho
    have ha : a = bkCellOldStageInclusion (bkPointDiagram J) n b := Subtype.ext hb.symm
    exact (congrArg (fun z => TopCat.weakHomotopyEquivalences (radialPointModelStrictFiberMap D n
      z)) ha).mpr
      (radialPointModelStrictFiberMap_mem_on_old D n b)
  · let e := bkNondegenerateCellInteriorProductIso (bkPointDiagram J) n
    obtain ⟨⟨c, x, t⟩, hz⟩ := (TopCat.homeoOfIso e).surjective ⟨a.1, ho⟩
    have hx : x = pointCellCoefficient J c.1.left := by
      change (_ : toTop.obj (Δ[0] : SSet.{max u v})) = _
      exact Subsingleton.elim _ _
    have hc : pointModelCellPoint c.1 t.1 = a.1 :=
      (congrArg (fun y => bkRealizedChainCellToStage (bkPointDiagram J) c.1 (y, t.1)) hx).symm.trans
        ((bkNondegenerateCellInteriorProductIso_hom_apply (bkPointDiagram J) n c x t).symm.trans
          (congrArg Subtype.val hz))
    have hnb : t.1 ≠ Convexity.StdSimplex.barycenter := by
      intro ht
      have hm := (nativeCoefficientCell_mem_centers_iff (bkPointDiagram J) n
        ⟨c, pointCellCoefficient J c.1.left, t.1⟩).mpr ht
      have he := (nativeCoefficientCellStageMap_apply (bkPointDiagram J) n c
        (pointCellCoefficient J c.1.left) t.1).trans hc
      exact a.2 (he ▸ hm)
    let s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter} :=
      ⟨t.1, hnb⟩
    have hp : (puncturedCellPoint n c s).1 = pointModelCellPoint c.1 t.1 :=
      bkPuncturedNondegenerateCell_inclusion_apply (bkPointDiagram J) n c
        (pointCellCoefficient J c.1.left) s
    have ha : a = puncturedCellPoint n c s := Subtype.ext (hc.symm.trans hp.symm)
    exact (congrArg (fun z => TopCat.weakHomotopyEquivalences (radialPointModelStrictFiberMap D n
      z)) ha).mpr
      (radialPointModelStrictFiberMap_mem_on_cell D n c s t.2 hD)

private def originalRadialStrictFiberMap
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    pullback (bkCellPuncturedProjection D n) (TopCat.const (X := TopCat.of PUnit) a) ⟶
      pullback (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit)
          ((bkNerveSkeletalCellModelIso J n).hom (bkCellRadialRetraction (bkPointDiagram J) n a)))
            :=
  TopCat.strictFiberMapOfSquare (bkCellRadialRetraction D n)
    (bkCellRadialRetraction (bkPointDiagram J) n ≫ (bkNerveSkeletalCellModelIso J n).hom)
    (by simpa only [Category.assoc] using (bkCellRadialRetraction_original_projection D n).symm) a

/-- The actual endpoint map of the lifted radial deformation on strict
fibers, with its target in the original realized nerve-skeletal projection.
The point-diagram punctured base is related to that original base by the
canonical cell-model isomorphism. -/
def bkCellRadialStrictFiberMap
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    pullback (bkCellPuncturedProjection D n) (TopCat.const (X := TopCat.of PUnit) a) ⟶
      pullback (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit)
          ((bkNerveSkeletalCellModelIso J n).hom (bkCellRadialRetraction (bkPointDiagram J) n a)))
            :=
  originalRadialStrictFiberMap D n a

private theorem bkCellRadialStrictFiberMap_fst_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    bkCellRadialStrictFiberMap D n a ≫
      pullback.fst (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit)
          ((bkNerveSkeletalCellModelIso J n).hom (bkCellRadialRetraction (bkPointDiagram J) n a))) =
      pullback.fst (bkCellPuncturedProjection D n) (TopCat.const (X := TopCat.of PUnit) a) ≫
        bkCellRadialRetraction D n :=
  TopCat.strictFiberMapOfSquare_fst (bkCellRadialRetraction D n)
    (bkCellRadialRetraction (bkPointDiagram J) n ≫ (bkNerveSkeletalCellModelIso J n).hom)
    (by simpa only [Category.assoc] using (bkCellRadialRetraction_original_projection D n).symm) a

/-- The endpoint fiber map retains the actual lifted total retraction. -/
@[reassoc]
theorem bkCellRadialStrictFiberMap_fst
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    bkCellRadialStrictFiberMap D n a ≫
      pullback.fst (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit)
          ((bkNerveSkeletalCellModelIso J n).hom (bkCellRadialRetraction (bkPointDiagram J) n a))) =
      pullback.fst (bkCellPuncturedProjection D n) (TopCat.const (X := TopCat.of PUnit) a) ≫
        bkCellRadialRetraction D n :=
  bkCellRadialStrictFiberMap_fst_aux D n a

private theorem bkCellRadialStrictFiberMap_eq_pointModel
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    bkCellRadialStrictFiberMap D n a = radialPointModelStrictFiberMap D n a ≫
      (originalPointFiberIso D n (bkCellRadialRetraction (bkPointDiagram J) n a)).hom := by
  apply pullback.hom_ext
  · rw [bkCellRadialStrictFiberMap_fst, Category.assoc, originalPointFiberIso_hom_fst,
      radialPointModelStrictFiberMap_fst]
  · apply TopCat.isTerminalPUnit.hom_ext

/-- If every diagram arrow realizes to a weak equivalence, the actual radial
endpoint map of strict fibers is weak at every punctured base point. The
proof constructs the forward endpoint arrow from its zero face, including
degenerate faces and zero-dimensional target cells. -/
theorem bkCellRadialStrictFiberMap_mem_weakHomotopyEquivalences
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    TopCat.weakHomotopyEquivalences (bkCellRadialStrictFiberMap D n a) := by
  rw [bkCellRadialStrictFiberMap_eq_pointModel]
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ (radialPointModelStrictFiberMap_mem D n hD a)
    (TopCat.weakHomotopyEquivalences.of_isIso _)

-- BEGIN approved proof-only stage-consumer characteristics

private theorem bkNativeCellInteriorProjection_apply_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (t : {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :
    bkNativeCellInteriorProjection D n ⟨c, x, t⟩ = ⟨c, t⟩ := rfl

/-- The native interior projection retains its chain and simplex coordinate. -/
theorem bkNativeCellInteriorProjection_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (t : {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :
    bkNativeCellInteriorProjection D n ⟨c, x, t⟩ = ⟨c, t⟩ :=
  bkNativeCellInteriorProjection_apply_aux D n c x t

private theorem bkCellBarycenterComplementInclusion_apply_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement D n) :
    bkCellBarycenterComplementInclusion D n a = a.1 := rfl

/-- The punctured inclusion retains the literal subspace point. -/
theorem bkCellBarycenterComplementInclusion_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : bkCellBarycenterComplement D n) :
    bkCellBarycenterComplementInclusion D n a = a.1 :=
  bkCellBarycenterComplementInclusion_apply_aux D n a

private theorem bkCellBarycenters_preimage_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (toTop.map (bkSkeletalProjection D (n + 1)) ≫ (bkNerveSkeletalCellModelIso J (n + 1)).inv) ⁻¹'
        bkCellBarycenters (bkPointDiagram J) n = bkCellBarycenters D n := by
  ext x
  exact coefficientPointStageProjection_mem_centers_iff D n x

/-- The actual skeletal projection, transported to the canonical point
model, has exactly the actual total barycenters as its center preimage. -/
theorem bkCellBarycenters_preimage
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (toTop.map (bkSkeletalProjection D (n + 1)) ≫ (bkNerveSkeletalCellModelIso J (n + 1)).inv) ⁻¹'
        bkCellBarycenters (bkPointDiagram J) n = bkCellBarycenters D n :=
  bkCellBarycenters_preimage_aux D n

-- END approved proof-only stage-consumer characteristics

end RadialEndpointFibers

end SSet
