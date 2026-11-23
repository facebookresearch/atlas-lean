/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowGroupCompletion
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpaceFundamentalGroup
public import MathlibExt.Topology.Category.TopCat.HomotopyExtension
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# The actual stable BGL map from the original opposite-row stages

The computed row successor homotopies extend across the original realized
matrix-stabilization cofibrations. Their endpoints form a strict cofan.
The original finite-BGL colimit then gives an ordinary continuous map to
the existing small-projective zero-component realization. Every original
stage map is homotopic to the restriction of this map, so the induced
homology maps agree in every degree and for every fixed coefficient group.

No homology isomorphism, telescope inverse, cofan, or homotopy is supplied
as an input. All-degree invertibility is a subsequent zero-grade fraction
comparison, rather than a conclusion of homotopy extension alone.
-/

noncomputable section

open CategoryTheory Limits Topology
open scoped unitInterval

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private abbrev rowTopDiagram : ℕ ⥤ TopCat.{u} :=
  finiteBGLNerveDiagram R ⋙ SSet.toTop

private abbrev rowZeroTarget : TopCat.{u} :=
  SSet.toTop.obj
    (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))

private abbrev rowOriginalTopStage (n : ℕ) :
    (rowTopDiagram R).obj n ⟶ rowZeroTarget R :=
  SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n)

private theorem rowTopDiagram_successor (n : ℕ) :
    (rowTopDiagram R).map (homOfLE (Nat.le_succ n)) =
      SSet.toTop.map (nerveMap (finiteOppositeGLRowStabilizationFunctor R n)) := by
  change SSet.toTop.map
    ((finiteBGLNerveDiagram R).map (homOfLE (Nat.le_succ n))) = _
  exact congrArg (fun f => SSet.toTop.map f)
    (finiteFreeRowOriginalNerveSuccessor_eq R n)

private def rowOriginalStepHomotopy (n : ℕ) :
    TopCat.Homotopy (rowOriginalTopStage R n)
      ((rowTopDiagram R).map (homOfLE (Nat.le_succ n)) ≫
        rowOriginalTopStage R (n + 1)) := by
  let H := finiteFreeRowSuccessorTopHomotopy R n
  have he :
      (SSet.toTop.map (nerveMap (finiteOppositeGLRowStabilizationFunctor R n)) ≫
        rowOriginalTopStage R (n + 1)).hom =
      ((rowTopDiagram R).map (homOfLE (Nat.le_succ n)) ≫
        rowOriginalTopStage R (n + 1)).hom := by
    exact congrArg (fun f => f.hom)
      (congrArg (fun f => f ≫ rowOriginalTopStage R (n + 1))
        (rowTopDiagram_successor R n).symm)
  exact H.cast rfl he

private structure RowStrictificationStage (n : ℕ) where
  map : (rowTopDiagram R).obj n ⟶ rowZeroTarget R
  homotopy : TopCat.Homotopy (rowOriginalTopStage R n) map

private def rowStrictificationExtension (n : ℕ)
    (previous : RowStrictificationStage R n) :
    HomotopyExtensionData
      ((rowTopDiagram R).map (homOfLE (Nat.le_succ n))).hom
      (rowOriginalTopStage R (n + 1)).hom
      ((rowOriginalStepHomotopy R n).symm.trans previous.homotopy)
      (fun x => ((rowOriginalStepHomotopy R n).symm.trans
        previous.homotopy).map_zero_left x) := by
  have hi : TopCat.IsHurewiczCofibration
      ((rowTopDiagram R).map (homOfLE (Nat.le_succ n))) := by
    rw [rowTopDiagram_successor]
    exact finiteFreeRowSuccessorTop_isHurewiczCofibration R n
  exact Classical.choice (hi (rowOriginalTopStage R (n + 1)).hom
    ((rowOriginalStepHomotopy R n).symm.trans previous.homotopy)
    (fun x => ((rowOriginalStepHomotopy R n).symm.trans
      previous.homotopy).map_zero_left x))

private def rowStrictificationData : (n : ℕ) → RowStrictificationStage R n
  | 0 =>
      { map := rowOriginalTopStage R 0
        homotopy := TopCat.Homotopy.refl (rowOriginalTopStage R 0) }
  | n + 1 =>
      let previous := rowStrictificationData n
      let e := rowStrictificationExtension R n previous
      { map := TopCat.ofHom e.endpoint
        homotopy := e.toHomotopy }

private theorem rowStrictification_successor (n : ℕ) :
    (rowTopDiagram R).map (homOfLE (Nat.le_succ n)) ≫
        (rowStrictificationData R (n + 1)).map =
      (rowStrictificationData R n).map := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  let previous := rowStrictificationData R n
  let e := rowStrictificationExtension R n previous
  change e.endpoint
      ((rowTopDiagram R).map (homOfLE (Nat.le_succ n)) x) = previous.map x
  exact (e.extension_subspace 1 x).trans
    (((rowOriginalStepHomotopy R n).symm.trans previous.homotopy).map_one_left x)

private def rowStrictCocone : Cocone (rowTopDiagram R) where
  pt := rowZeroTarget R
  ι := NatTrans.ofSequence
    (fun n => (rowStrictificationData R n).map)
    (fun n => by
      rw [rowStrictification_successor, Functor.const_obj_map]
      exact (Category.comp_id _).symm)

private abbrev rowOriginalTopCocone : Cocone (rowTopDiagram R) :=
  SSet.toTop.mapCocone (finiteBGLNerveCocone R)

private def rowOriginalTopCoconeIsColimit :
    IsColimit (rowOriginalTopCocone R) :=
  isColimitOfPreserves SSet.toTop (finiteBGLNerveCoconeIsColimit R)

/-- The continuous stable comparison obtained from the computed row
homotopies, their actual Hurewicz extensions, and the ORIGINAL finite-BGL
cofan. The scalar ring and the original stable classifying nerve are unchanged. -/
public def finiteFreeRowStableZeroComparison :
    ordinaryBGL R ⟶
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) :=
  (rowOriginalTopCoconeIsColimit R).desc (rowStrictCocone R)

private theorem rowStableComparison_stage (n : ℕ) :
    SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor) ≫
        finiteFreeRowStableZeroComparison R =
      (rowStrictificationData R n).map := by
  have h := (rowOriginalTopCoconeIsColimit R).fac (rowStrictCocone R) n
  change SSet.toTop.map ((finiteBGLNerveCocone R).ι.app n) ≫
      finiteFreeRowStableZeroComparison R = (rowStrictificationData R n).map at h
  exact (congrArg (fun f => SSet.toTop.map f ≫ finiteFreeRowStableZeroComparison R)
    (finiteBGLNerveCocone_ι R n)).symm.trans h

/-- A WHOLE homotopy from every original row stage map to the restriction of
the stable comparison along the SAME original finite-to-stable inclusion. -/
public def finiteFreeRowStableZeroComparisonStageHomotopy (n : ℕ) :
    TopCat.Homotopy (SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n))
      (SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor) ≫
        finiteFreeRowStableZeroComparison R) :=
  (rowStrictificationData R n).homotopy.cast rfl
    (congrArg (fun f => f.hom) (rowStableComparison_stage R n).symm)

/-- In every homological degree, the restriction of the actual stable map
is the ORIGINAL row-stage homology map. No homology-isomorphism input is used. -/
public theorem finiteFreeRowStableZeroComparison_homology_stage
    (A : AddCommGrpCat.{u}) (q n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
        (SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n)) =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
          (SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor)) ≫
        ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
          (finiteFreeRowStableZeroComparison R) := by
  let H := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A
  let K := finiteFreeRowStableZeroComparisonStageHomotopy R n
  have h : H.map (SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n)) =
      H.map (SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor) ≫
        finiteFreeRowStableZeroComparison R) :=
    K.congr_homologyMap_singularChainComplexFunctor A q
  exact h.trans (H.map_comp _ _)

/-- The same actual stage comparison for universe-sized integral coefficients,
in every degree, without changing the original Ring or any stage map. -/
public theorem finiteFreeRowStableZeroComparison_integral_stage (q n : ℕ) :
    (AlgebraicTopology.singularIntegralHomologyFunctor q).map
        (SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n)) =
      (AlgebraicTopology.singularIntegralHomologyFunctor q).map
          (SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor)) ≫
        (AlgebraicTopology.singularIntegralHomologyFunctor q).map
          (finiteFreeRowStableZeroComparison R) :=
  finiteFreeRowStableZeroComparison_homology_stage R
    AlgebraicTopology.singularIntegralCoefficients q n

/-- The original stable basepoint is sent to the SAME actual rank-zero row
vertex. This follows from the original cofan and the initial HEP stage. -/
public theorem finiteFreeRowStableZeroComparison_basepoint :
    finiteFreeRowStableZeroComparison R (ordinaryBGLBasepoint R) =
      SSet.realizedVertex
        (ComposableArrows.mk₀ ((finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _))) := by
  let v := ComposableArrows.mk₀ (SingleObj.star
    (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ)
  let i := nerveMap (finiteToStableCategoryMap R 0).toFunctor
  have hVertex : i.app (Opposite.op (SimplexCategory.mk 0)) v = classifyingVertex R := by
    apply ComposableArrows.ext₀
    rfl
  have hBase : SSet.toTop.map i (SSet.realizedVertex v) = ordinaryBGLBasepoint R :=
    (SSet.realizedVertex_naturality i v).symm.trans
      (congrArg SSet.realizedVertex hVertex)
  have hStage := ConcreteCategory.congr_hom (rowStableComparison_stage R 0)
    (SSet.realizedVertex v)
  change finiteFreeRowStableZeroComparison R
      (SSet.toTop.map i (SSet.realizedVertex v)) =
    SSet.toTop.map (finiteFreeRowStageZeroNerveMap R 0) (SSet.realizedVertex v) at hStage
  have hZero := SSet.realizedVertex_naturality (finiteFreeRowStageZeroNerveMap R 0) v
  exact (congrArg (finiteFreeRowStableZeroComparison R) hBase).symm.trans
    (hStage.trans (hZero.symm.trans (congrArg SSet.realizedVertex
      (finiteFreeRowStageZeroNerveMap_app_mk₀ R 0 (SingleObj.star _)))))


/-- The actual stable-row stage homotopies retain their whole original HEP
successor boundary on every original finite-stage point and interval time. -/
public theorem finiteFreeRowStableZeroComparisonStageHomotopy_successor
    (n : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj
      (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))) :
    (finiteFreeRowStableZeroComparisonStageHomotopy R (n + 1)).toContinuousMap
        (t, SSet.toTop.map
          (nerveMap (finiteOppositeGLRowStabilizationFunctor R n)) x) =
      ((finiteFreeRowSuccessorTopHomotopy R n).symm.trans
        (finiteFreeRowStableZeroComparisonStageHomotopy R n)).toContinuousMap (t, x) := by
  let previous := rowStrictificationData R n
  let e := rowStrictificationExtension R n previous
  have hInput : (rowTopDiagram R).map (homOfLE (Nat.le_succ n)) x =
      SSet.toTop.map (nerveMap (finiteOppositeGLRowStabilizationFunctor R n)) x :=
    ConcreteCategory.congr_hom (rowTopDiagram_successor R n) x
  have hBoundary :
      e.extension (t, (rowTopDiagram R).map (homOfLE (Nat.le_succ n)) x) =
        ((rowOriginalStepHomotopy R n).symm.trans previous.homotopy).toContinuousMap (t, x) :=
    e.extension_subspace t x
  change e.extension
      (t, SSet.toTop.map (nerveMap (finiteOppositeGLRowStabilizationFunctor R n)) x) =
    ((rowOriginalStepHomotopy R n).symm.trans previous.homotopy).toContinuousMap (t, x)
  exact (congrArg (fun y => e.extension (t, y)) hInput).symm.trans hBoundary

end AlgebraicKTheory.StableGL


noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The ORIGINAL initial stable-row family is the original reflexive
row-stage map on EVERY original rank-zero point and interval time. -/
public theorem finiteFreeRowStableZeroComparisonStageHomotopy_zero
    (t : unitInterval)
    (x : SSet.toTop.obj
      (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ))) :
    (finiteFreeRowStableZeroComparisonStageHomotopy R 0).toContinuousMap (t, x) =
      SSet.toTop.map (finiteFreeRowStageZeroNerveMap R 0) x := by
  rfl

end AlgebraicKTheory.StableGL

end
