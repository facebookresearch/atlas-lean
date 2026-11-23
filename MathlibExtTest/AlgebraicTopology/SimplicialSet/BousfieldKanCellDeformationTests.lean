/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanCellDeformation

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped Simplicial

universe u

namespace SSet

noncomputable section

variable (J : Type u) [Category.{0} J]

example (n : ℕ) :
    (bkNerveSkeletalCellModelIso J n).hom ≫ toTop.map ((nerve J).skeleton (n + 1)).ι =
      toTop.map (bkSkeletalFiltration (bkPointDiagram J) n).ι ≫ toTop.map (bkPointIsoNerve J).hom :=
  bkNerveSkeletalCellModelIso_hom_ι J n

example {m n : ℕ} (h : m ≤ n) :
    toTop.map (bkSkeletalFiltrationMap (bkPointDiagram J) h) ≫
      (bkNerveSkeletalCellModelIso J n).hom =
    (bkNerveSkeletalCellModelIso J m).hom ≫ bkNerveSkeletalMap J h :=
  bkNerveSkeletalCellModelIso_natural J h

example {n : ℕ} (c : ComposableArrows J n)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    toTop.map ((nerve J).skeleton (n + 1)).ι (bkNerveSkeletalCell J c t) =
      toTop.map (yonedaEquiv.symm c : (Δ[n] : SSet.{u}) ⟶ nerve J)
        ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm t) :=
  bkNerveSkeletalCell_ι_apply J c t

example (n : ℕ) (c : (nerve J).nonDegenerate (n + 1))
    (t : {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :
    ((bkNerveSkeletalCellInteriorIso J n).hom ⟨c, t⟩).1 = bkNerveSkeletalCell J c.1 t.1 :=
  bkNerveSkeletalCellInteriorIso_hom_apply J n c t

example (D : J ⥤ SSet.{u}) {n : ℕ} (c : ComposableArrows J n)
    (x : toTop.obj (D.obj c.left)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    toTop.map (bkSkeletalProjection D n) (bkRealizedChainCellToStage D c (x, t)) =
      bkNerveSkeletalCell J c t :=
  bkRealizedChainCellToStage_projection_apply D c x t

example (D : J ⥤ SSet.{u}) (n : ℕ) :
    (bkNondegenerateCellInteriorProductIso D n).hom ≫ bkSkeletalInteriorProjection D n =
      bkNativeCellInteriorProjection D n ≫ (bkNerveSkeletalCellInteriorIso J n).hom :=
  bkSkeletalInteriorProjection_chart D n

example (D : J ⥤ SSet.{u}) (n : ℕ) :
    bkCellOldStageInclusion D n ≫ bkCellRadialRetraction D n =
      𝟙 (toTop.obj (bkSkeletalFiltration D n : SSet.{u})) :=
  bkCellRadialRetraction_retract D n

example (D : J ⥤ SSet.{u}) (n : ℕ) (t : unitInterval)
    (x : toTop.obj (bkSkeletalFiltration D n : SSet.{u})) :
    bkCellRadialHomotopy D n (t, bkCellOldStageInclusion D n x) =
      bkCellOldStageInclusion D n x :=
  bkCellRadialHomotopy_on_old D n t x

example (D : J ⥤ SSet.{u}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // s ≠ Convexity.StdSimplex.barycenter}) :
    toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))
        (bkCellRadialRetraction D n (bkPuncturedNondegenerateCell D n c (x, s))) =
      bkRealizedChainCellToStage D c.1 (x, StdSimplexRadialBoundary.radialMap (n + 1) s) :=
  bkCellRadialRetraction_cell_endpoint D n c x s

example (D : J ⥤ SSet.{u}) (n : ℕ) (t : unitInterval) (x : bkCellBarycenterComplement D n) :
    bkCellPuncturedProjection D n (bkCellRadialHomotopy D n (t, x)) =
      bkCellRadialHomotopy (bkPointDiagram J) n (t, bkCellPuncturedProjection D n x) :=
  bkCellRadialHomotopy_projection D n t x

example (D : J ⥤ SSet.{u}) (n : ℕ) :
    bkCellPuncturedProjection D n ≫ bkCellBarycenterComplementInclusion (bkPointDiagram J) n ≫
        (bkNerveSkeletalCellModelIso J (n + 1)).hom =
      bkCellBarycenterComplementInclusion D n ≫ toTop.map (bkSkeletalProjection D (n + 1)) :=
  bkCellPuncturedProjection_original_projection D n

example (D : J ⥤ SSet.{u}) (n : ℕ) (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i}) :
    toTop.obj (D.obj c.1.left) ≅
      pullback (toTop.map (bkSkeletalProjection D (n + 1)))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1)) :=
  bkPositiveCellStrictFiberIso D n c s

example (D : J ⥤ SSet.{u}) (n : ℕ) (c : (nerve J).nonDegenerate (n + 1))
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < s.weights i})
    (x : toTop.obj (D.obj c.1.left)) :
    pullback.fst (toTop.map (bkSkeletalProjection D (n + 1)))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1))
      ((bkPositiveCellStrictFiberIso D n c s).hom x) =
      bkRealizedChainCellToStage D c.1 (x, s.1) :=
  bkPositiveCellStrictFiberIso_hom_fst D n c s x

example (D : J ⥤ SSet.{u}) {n : ℕ} (c : (nerve J).nonDegenerate n)
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < s.weights i}) :
    toTop.obj (D.obj c.1.left) ≅ pullback (toTop.map (bkSkeletalProjection D n))
      (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1)) :=
  bkCellStrictFiberIso D c s

example (D : J ⥤ SSet.{u}) {n : ℕ} (c : (nerve J).nonDegenerate n)
    (s : {s : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < s.weights i})
    (x : toTop.obj (D.obj c.1.left)) :
    pullback.fst (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit) (bkNerveSkeletalCell J c.1 s.1))
      ((bkCellStrictFiberIso D c s).hom x) = bkRealizedChainCellToStage D c.1 (x, s.1) :=
  bkCellStrictFiberIso_hom_fst D c s x

example (D : J ⥤ SSet.{u}) (n : ℕ) (a : bkCellBarycenterComplement (bkPointDiagram J) n)
    (x : (pullback (bkCellPuncturedProjection D n)
      (TopCat.const (X := TopCat.of PUnit) a) : TopCat.{u})) :
    pullback.fst (toTop.map (bkSkeletalProjection D n))
        (TopCat.const (X := TopCat.of PUnit)
          ((bkNerveSkeletalCellModelIso J n).hom (bkCellRadialRetraction (bkPointDiagram J) n a)))
      (bkCellRadialStrictFiberMap D n a x) =
        bkCellRadialRetraction D n
          (pullback.fst (bkCellPuncturedProjection D n) (TopCat.const (X := TopCat.of PUnit) a) x) :=
  ConcreteCategory.congr_hom (bkCellRadialStrictFiberMap_fst D n a) x

example (D : J ⥤ SSet.{u}) (n : ℕ)
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (toTop.map (D.map g)))
    (a : bkCellBarycenterComplement (bkPointDiagram J) n) :
    TopCat.weakHomotopyEquivalences (bkCellRadialStrictFiberMap D n a) :=
  bkCellRadialStrictFiberMap_mem_weakHomotopyEquivalences D n hD a

end

end SSet
