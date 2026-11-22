/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FiberEvaluation
import MathlibExt.Topology.Category.PointedCGWH.SerreSequence.FiberSingular
import MathlibExt.Topology.Category.PointedCGWH.Singular.CubeHomotopyComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.GroupFunctors

/-!
# Homotopy exactness for the original chosen fiber at every enriched level

The original evaluated Serre fibration gives its actual pointed singular
fibration sequence. The caller's chosen enriched pullback is compared with
that sequence using its original total and zero projections. The connecting
functions are those of the original fibration sequence, transported through
the actual cube and singular comparison maps.

All positive homotopy groups and all three adjacent exact pairs are retained.
No exactness, stabilization, localization or model comparison outcome is an
input. This level result applies to each of the three native spectrum indices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory Simplicial

namespace HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry

open PointedCGWH.SerreSequenceGeometry
open PointedCGWH.SingularHomotopyGeometry (singularFunctor singularPoint singularPoint_naturality
  piFunctor)
open PointedCGWH.CubeSingularGeometry

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (p : X ⟶ Y)
  (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c) (a : A)
  (hp : fibrations PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation a).map p))

/-- The level Arrow is the original evaluated map with its original Serre membership. -/
def chosenFiberLevelFibrationArrow : PointedCGWH.SerreSequenceGeometry.FibrationArrow.{u, v} :=
  ⟨Arrow.mk ((EnrichedFunctorCat.evaluation a).map p), hp⟩

/-- The original evaluated Serre map constructs its actual singular fibration sequence. -/
def chosenFiberLevelSequence : SSet.FibrationSequence.{v} :=
  sequence (chosenFiberLevelFibrationArrow p a hp)

/-- Both full comparison maps retain the caller's original evaluated chosen fiber. -/
def chosenFiberLevelSingularIso :
    singularFunctor.obj ((EnrichedFunctorCat.evaluation a).obj c.pt) ≅
      (chosenFiberLevelSequence p a hp).fiber :=
  singularFunctor.mapIso (chosenFiberComponentIso a p c hc) ≪≫
    nativeFiberSingularIso (chosenFiberLevelFibrationArrow p a hp)

/-- The forward comparison preserves the exact original selected fiber point. -/
theorem chosenFiberLevelSingularIso_hom_point :
    (chosenFiberLevelSingularIso p c hc a hp).hom.app _
        (singularPoint ((EnrichedFunctorCat.evaluation a).obj c.pt)) =
      (chosenFiberLevelSequence p a hp).fiberPoint := by
  exact (congrArg ((nativeFiberSingularIso
      (chosenFiberLevelFibrationArrow p a hp)).hom.app _)
    (singularPoint_naturality (chosenFiberComponentIso a p c hc).hom)).trans
      (nativeFiberSingularIso_hom_point (chosenFiberLevelFibrationArrow p a hp))

/-- The inverse comparison preserves that same original fiber point. -/
theorem chosenFiberLevelSingularIso_inv_point :
    (chosenFiberLevelSingularIso p c hc a hp).inv.app _
        (chosenFiberLevelSequence p a hp).fiberPoint =
      singularPoint ((EnrichedFunctorCat.evaluation a).obj c.pt) := by
  rw [← chosenFiberLevelSingularIso_hom_point p c hc a hp]
  exact ConcreteCategory.congr_hom
    (congr_app (chosenFiberLevelSingularIso p c hc a hp).hom_inv_id _) _

/-- The whole forward singular comparison keeps the caller's actual total projection. -/
theorem chosenFiberLevelSingularIso_hom_projection :
    (chosenFiberLevelSingularIso p c hc a hp).hom ≫
        (chosenFiberLevelSequence p a hp).fiberIncl =
      singularFunctor.map ((EnrichedFunctorCat.evaluation a).map c.fst) := by
  let e := chosenFiberComponentIso a p c hc
  let F := chosenFiberLevelFibrationArrow p a hp
  change (singularFunctor.map e.hom ≫ (nativeFiberSingularIso F).hom) ≫
      (sequence F).fiberIncl = _
  rw [Category.assoc, nativeFiberSingularIso_hom_projection]
  change singularFunctor.map e.hom ≫
      singularFunctor.map (PointedCGWH.StrictFiberGeometry.fiberToTotal
        ((EnrichedFunctorCat.evaluation a).map p)) = _
  rw [← singularFunctor.map_comp, chosenFiberComponentIso_hom_fst]

/-- Every literal singular homotopy degree has both original chosen-fiber comparison functions. -/
def chosenFiberLevelPiEquiv (k : ℕ) :
    (piFunctor k).obj ((EnrichedFunctorCat.evaluation a).obj c.pt) ≃
      SSet.KanComplex.π k (chosenFiberLevelSequence p a hp).fiber
        (chosenFiberLevelSequence p a hp).fiberPoint :=
  SSet.KanComplex.π.equivOfIso (chosenFiberLevelSingularIso p c hc a hp)
    (chosenFiberLevelSingularIso_hom_point p c hc a hp) k

/-- All singular homotopy comparisons preserve the actual constant class, including degree zero. -/
theorem chosenFiberLevelPiEquiv_one (k : ℕ) :
    chosenFiberLevelPiEquiv p c hc a hp k 1 = 1 :=
  SSet.KanComplex.π.map_one (chosenFiberLevelSingularIso p c hc a hp).hom
    (chosenFiberLevelSingularIso_hom_point p c hc a hp) k

/-- The full inverse homotopy comparison preserves that same original constant class. -/
theorem chosenFiberLevelPiEquiv_symm_one (k : ℕ) :
    (chosenFiberLevelPiEquiv p c hc a hp k).symm 1 = 1 := by
  apply (chosenFiberLevelPiEquiv p c hc a hp k).injective
  rw [Equiv.apply_symm_apply, chosenFiberLevelPiEquiv_one]

/-- Every whole original fiber projection commutes with both homotopy comparisons. -/
theorem chosenFiberLevelPiEquiv_inclusion (k : ℕ)
    (x : (piFunctor k).obj ((EnrichedFunctorCat.evaluation a).obj c.pt)) :
    SSet.KanComplex.π.map (chosenFiberLevelSequence p a hp).fiberIncl rfl k
        (chosenFiberLevelPiEquiv p c hc a hp k x) =
      (piFunctor k).map ((EnrichedFunctorCat.evaluation a).map c.fst) x := by
  have hPoint :
      ((chosenFiberLevelSingularIso p c hc a hp).hom ≫
        (chosenFiberLevelSequence p a hp).fiberIncl).app _
        (singularPoint ((EnrichedFunctorCat.evaluation a).obj c.pt)) =
      (chosenFiberLevelSequence p a hp).e :=
    congrArg ((chosenFiberLevelSequence p a hp).fiberIncl.app _)
      (chosenFiberLevelSingularIso_hom_point p c hc a hp)
  have h := SSet.KanComplex.π.map_comp_apply
    (chosenFiberLevelSingularIso p c hc a hp).hom
    (chosenFiberLevelSequence p a hp).fiberIncl
    (chosenFiberLevelSingularIso_hom_point p c hc a hp) rfl
    hPoint x
  exact h.symm.trans (congrFun (SSet.KanComplex.π.map_congr
    (chosenFiberLevelSingularIso_hom_projection p c hc a hp) _ _ k) x)

/-- Every original degree has its actual chosen-fiber singular connecting function. -/
def chosenFiberLevelSingularConnectingMap (k : ℕ) :
    (piFunctor (k + 1)).obj ((EnrichedFunctorCat.evaluation a).obj Y) →
      (piFunctor k).obj ((EnrichedFunctorCat.evaluation a).obj c.pt) :=
  (chosenFiberLevelPiEquiv p c hc a hp k).symm ∘
    (chosenFiberLevelSequence p a hp).connectingMap k

/-- The full original chosen-fiber function reconstructs the strict sequence function. -/
theorem chosenFiberLevelSingularConnectingMap_reconstruction (k : ℕ)
    (x : (piFunctor (k + 1)).obj ((EnrichedFunctorCat.evaluation a).obj Y)) :
    chosenFiberLevelPiEquiv p c hc a hp k
        (chosenFiberLevelSingularConnectingMap p c hc a hp k x) =
      (chosenFiberLevelSequence p a hp).connectingMap k x :=
  (chosenFiberLevelPiEquiv p c hc a hp k).apply_symm_apply _

include hc hp in
/-- The original singular sequence is exact at every total-space homotopy type. -/
theorem chosenFiberLevelSingularExact_at_total (k : ℕ) :
    Function.MulExact
      ((piFunctor k).map ((EnrichedFunctorCat.evaluation a).map c.fst))
      ((piFunctor k).map ((EnrichedFunctorCat.evaluation a).map p)) := by
  intro x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (chosenFiberLevelSequence p a hp).exactness_at_E x hx
    refine ⟨(chosenFiberLevelPiEquiv p c hc a hp k).symm z, ?_⟩
    rw [← chosenFiberLevelPiEquiv_inclusion p c hc a hp k, Equiv.apply_symm_apply, hz]
  · rintro ⟨z, rfl⟩
    rw [← chosenFiberLevelPiEquiv_inclusion p c hc a hp k]
    exact (chosenFiberLevelSequence p a hp).map_p_comp_fiberIncl_eq_one _

/-- Exactness at every original fiber homotopy type includes degree-zero components. -/
theorem chosenFiberLevelSingularExact_at_fiber (k : ℕ) :
    Function.MulExact (chosenFiberLevelSingularConnectingMap p c hc a hp k)
      ((piFunctor k).map ((EnrichedFunctorCat.evaluation a).map c.fst)) := by
  intro x
  constructor
  · intro hx
    have h : SSet.KanComplex.π.map (chosenFiberLevelSequence p a hp).fiberIncl rfl k
        (chosenFiberLevelPiEquiv p c hc a hp k x) = 1 := by
      rw [chosenFiberLevelPiEquiv_inclusion p c hc a hp k, hx]
    obtain ⟨z, hz⟩ := (chosenFiberLevelSequence p a hp).exactness_at_fiber _ h
    refine ⟨z, ?_⟩
    apply (chosenFiberLevelPiEquiv p c hc a hp k).injective
    rw [chosenFiberLevelSingularConnectingMap_reconstruction, hz]
  · rintro ⟨z, rfl⟩
    rw [← chosenFiberLevelPiEquiv_inclusion p c hc a hp k,
      chosenFiberLevelSingularConnectingMap_reconstruction]
    exact (chosenFiberLevelSequence p a hp).fiberIncl_map_connectingMap_eq_one z

/-- Every base homotopy type uses the same actual projection and chosen connecting function. -/
theorem chosenFiberLevelSingularExact_at_base (k : ℕ) :
    Function.MulExact
      ((piFunctor (k + 1)).map ((EnrichedFunctorCat.evaluation a).map p))
      (chosenFiberLevelSingularConnectingMap p c hc a hp k) := by
  intro x
  constructor
  · intro hx
    have h : (chosenFiberLevelSequence p a hp).connectingMap k x = 1 := by
      rw [← chosenFiberLevelSingularConnectingMap_reconstruction p c hc a hp k,
        hx, chosenFiberLevelPiEquiv_one]
    exact (chosenFiberLevelSequence p a hp).exactness_at_B x h
  · rintro ⟨z, rfl⟩
    apply (chosenFiberLevelPiEquiv p c hc a hp k).injective
    rw [chosenFiberLevelSingularConnectingMap_reconstruction,
      chosenFiberLevelPiEquiv_one]
    exact (chosenFiberLevelSequence p a hp).connectingMap_map_eq_one z

/-- The same positive singular comparison is a genuine group equivalence. -/
def chosenFiberLevelPiMulEquiv (k : ℕ) :
    (piFunctor (k + 1)).obj ((EnrichedFunctorCat.evaluation a).obj c.pt) ≃*
      SSet.KanComplex.π (k + 1) (chosenFiberLevelSequence p a hp).fiber
        (chosenFiberLevelSequence p a hp).fiberPoint where
  toEquiv := chosenFiberLevelPiEquiv p c hc a hp (k + 1)
  map_mul' := SSet.KanComplex.π.map_mul (chosenFiberLevelSingularIso p c hc a hp).hom
    (chosenFiberLevelSingularIso_hom_point p c hc a hp) k

/-- Every original positive cube group is compared with the same actual sequence fiber group. -/
def chosenFiberLevelCubeMulEquiv (k : ℕ) :
    PointedCGWH.piN (k + 1) ((EnrichedFunctorCat.evaluation a).obj c.pt) ≃*
      SSet.KanComplex.π (k + 1) (chosenFiberLevelSequence p a hp).fiber
        (chosenFiberLevelSequence p a hp).fiberPoint :=
  (cubeSingularMulEquiv k ((EnrichedFunctorCat.evaluation a).obj c.pt)).trans
    (chosenFiberLevelPiMulEquiv p c hc a hp k)

/-- The complete original cube inclusion function uses the actual chosen total projection. -/
theorem chosenFiberLevelCubeMulEquiv_inclusion (k : ℕ)
    (x : PointedCGWH.piN (k + 1) ((EnrichedFunctorCat.evaluation a).obj c.pt)) :
    SSet.KanComplex.π.map (chosenFiberLevelSequence p a hp).fiberIncl rfl (k + 1)
        (chosenFiberLevelCubeMulEquiv p c hc a hp k x) =
      cubeSingularMulEquiv k ((EnrichedFunctorCat.evaluation a).obj X)
        (PointedCGWH.piNMap (k + 1) ((EnrichedFunctorCat.evaluation a).map c.fst) x) := by
  exact (chosenFiberLevelPiEquiv_inclusion p c hc a hp (k + 1)
    (cubeSingularMulEquiv k ((EnrichedFunctorCat.evaluation a).obj c.pt) x)).trans
      (cubeSingularMulEquiv_naturality k ((EnrichedFunctorCat.evaluation a).map c.fst) x).symm

/-- The original cube projection is the original sequence projection under the full comparison. -/
theorem chosenFiberLevelCube_projection (k : ℕ)
    (x : PointedCGWH.piN (k + 1) ((EnrichedFunctorCat.evaluation a).obj X)) :
    SSet.KanComplex.π.map (chosenFiberLevelSequence p a hp).p
        (chosenFiberLevelSequence p a hp).hb (k + 1)
        (cubeSingularMulEquiv k ((EnrichedFunctorCat.evaluation a).obj X) x) =
      cubeSingularMulEquiv k ((EnrichedFunctorCat.evaluation a).obj Y)
        (PointedCGWH.piNMap (k + 1) ((EnrichedFunctorCat.evaluation a).map p) x) :=
  (cubeSingularMulEquiv_naturality k ((EnrichedFunctorCat.evaluation a).map p) x).symm

/-- The actual original connecting function is transported to the caller's positive cube group. -/
def chosenFiberLevelConnectingHom (k : ℕ) :
    PointedCGWH.piN (k + 2) ((EnrichedFunctorCat.evaluation a).obj Y) →*
      PointedCGWH.piN (k + 1) ((EnrichedFunctorCat.evaluation a).obj c.pt) :=
  (chosenFiberLevelCubeMulEquiv p c hc a hp k).symm.toMonoidHom.comp
    ((SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom
      (chosenFiberLevelSequence p a hp) k).comp
        (cubeSingularMulEquiv (k + 1) ((EnrichedFunctorCat.evaluation a).obj Y)).toMonoidHom)

/-- Its whole comparison reconstructs the unchanged original sequence connecting function. -/
theorem chosenFiberLevelConnectingHom_reconstruction (k : ℕ)
    (x : PointedCGWH.piN (k + 2) ((EnrichedFunctorCat.evaluation a).obj Y)) :
    chosenFiberLevelCubeMulEquiv p c hc a hp k
        (chosenFiberLevelConnectingHom p c hc a hp k x) =
      (chosenFiberLevelSequence p a hp).connectingMap (k + 1)
        (cubeSingularMulEquiv (k + 1) ((EnrichedFunctorCat.evaluation a).obj Y) x) :=
  (chosenFiberLevelCubeMulEquiv p c hc a hp k).apply_symm_apply _

include hc hp in
/-- Exactness at every original positive total-space group retains the actual evaluated maps. -/
theorem chosenFiberLevelPositiveExact_at_total (k : ℕ) :
    Function.MulExact
      (PointedCGWH.piNMap (k + 1) ((EnrichedFunctorCat.evaluation a).map c.fst))
      (PointedCGWH.piNMap (k + 1) ((EnrichedFunctorCat.evaluation a).map p)) := by
  intro x
  constructor
  · intro hx
    have h : SSet.KanComplex.π.map (chosenFiberLevelSequence p a hp).p
        (chosenFiberLevelSequence p a hp).hb (k + 1)
        (cubeSingularMulEquiv k ((EnrichedFunctorCat.evaluation a).obj X) x) = 1 := by
      rw [chosenFiberLevelCube_projection p a hp k, hx, map_one]
    obtain ⟨z, hz⟩ := (chosenFiberLevelSequence p a hp).exactness_at_E _ h
    refine ⟨(chosenFiberLevelCubeMulEquiv p c hc a hp k).symm z, ?_⟩
    apply (cubeSingularMulEquiv k ((EnrichedFunctorCat.evaluation a).obj X)).injective
    rw [← chosenFiberLevelCubeMulEquiv_inclusion p c hc a hp k,
      MulEquiv.apply_symm_apply, hz]
  · rintro ⟨z, rfl⟩
    apply (cubeSingularMulEquiv k ((EnrichedFunctorCat.evaluation a).obj Y)).injective
    rw [← chosenFiberLevelCube_projection p a hp k,
      ← chosenFiberLevelCubeMulEquiv_inclusion p c hc a hp k,
      (chosenFiberLevelSequence p a hp).map_p_comp_fiberIncl_eq_one, map_one]

/-- Exactness at the same original positive fiber group uses the actual connecting homomorphism. -/
theorem chosenFiberLevelPositiveExact_at_fiber (k : ℕ) :
    Function.MulExact (chosenFiberLevelConnectingHom p c hc a hp k)
      (PointedCGWH.piNMap (k + 1) ((EnrichedFunctorCat.evaluation a).map c.fst)) := by
  intro x
  constructor
  · intro hx
    have h : SSet.KanComplex.π.map (chosenFiberLevelSequence p a hp).fiberIncl rfl (k + 1)
        (chosenFiberLevelCubeMulEquiv p c hc a hp k x) = 1 := by
      rw [chosenFiberLevelCubeMulEquiv_inclusion p c hc a hp k, hx, map_one]
    obtain ⟨z, hz⟩ := (chosenFiberLevelSequence p a hp).exactness_at_fiber _ h
    refine ⟨(cubeSingularMulEquiv (k + 1) ((EnrichedFunctorCat.evaluation a).obj Y)).symm z, ?_⟩
    apply (chosenFiberLevelCubeMulEquiv p c hc a hp k).injective
    rw [chosenFiberLevelConnectingHom_reconstruction p c hc a hp k,
      MulEquiv.apply_symm_apply, hz]
  · rintro ⟨z, rfl⟩
    apply (cubeSingularMulEquiv k ((EnrichedFunctorCat.evaluation a).obj X)).injective
    rw [← chosenFiberLevelCubeMulEquiv_inclusion p c hc a hp k,
      chosenFiberLevelConnectingHom_reconstruction p c hc a hp k,
      (chosenFiberLevelSequence p a hp).fiberIncl_map_connectingMap_eq_one, map_one]

/-- Exactness at the same original base group keeps its original positive projection. -/
theorem chosenFiberLevelPositiveExact_at_base (k : ℕ) :
    Function.MulExact
      (PointedCGWH.piNMap (k + 2) ((EnrichedFunctorCat.evaluation a).map p))
      (chosenFiberLevelConnectingHom p c hc a hp k) := by
  intro x
  constructor
  · intro hx
    have h : (chosenFiberLevelSequence p a hp).connectingMap (k + 1)
        (cubeSingularMulEquiv (k + 1) ((EnrichedFunctorCat.evaluation a).obj Y) x) = 1 := by
      rw [← chosenFiberLevelConnectingHom_reconstruction p c hc a hp k, hx, map_one]
    obtain ⟨z, hz⟩ := (chosenFiberLevelSequence p a hp).exactness_at_B _ h
    refine ⟨(cubeSingularMulEquiv (k + 1) ((EnrichedFunctorCat.evaluation a).obj X)).symm z, ?_⟩
    apply (cubeSingularMulEquiv (k + 1) ((EnrichedFunctorCat.evaluation a).obj Y)).injective
    rw [← chosenFiberLevelCube_projection p a hp (k + 1), MulEquiv.apply_symm_apply, hz]
  · rintro ⟨z, rfl⟩
    apply (chosenFiberLevelCubeMulEquiv p c hc a hp k).injective
    rw [chosenFiberLevelConnectingHom_reconstruction p c hc a hp k,
      ← chosenFiberLevelCube_projection p a hp (k + 1),
      (chosenFiberLevelSequence p a hp).connectingMap_map_eq_one, map_one]

section Naturality

variable {X' Y' : EnrichedFunctorCat PointedCGWH.{u, v} A} {p' : X' ⟶ Y'}
  (d : PullbackCone p' (zeroTo Y')) (hd : IsLimit d)
  (hp' : fibrations PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation a).map p'))

/-- Every whole original Arrow square gives its actual evaluated singular sequence square. -/
def chosenFiberLevelSequenceMap (q : Arrow.mk p ⟶ Arrow.mk p') :
    SSet.FibrationSequenceHom (chosenFiberLevelSequence p a hp)
      (chosenFiberLevelSequence p' a hp') where
  totalMap := singularFunctor.map ((EnrichedFunctorCat.evaluation a).map q.left)
  baseMap := singularFunctor.map ((EnrichedFunctorCat.evaluation a).map q.right)
  comm := by
    let E : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤ PointedCGWH.{u, v} :=
      EnrichedFunctorCat.evaluation a
    have h : E.map q.left ≫ E.map p' = E.map p ≫ E.map q.right :=
      (E.map_comp q.left p').symm.trans
        ((E.congr_map (Arrow.w q)).trans (E.map_comp p q.right))
    exact (singularFunctor.map_comp _ _).symm.trans
      ((singularFunctor.congr_map h).trans (singularFunctor.map_comp _ _))
  total_pt := singularPoint_naturality ((EnrichedFunctorCat.evaluation a).map q.left)
  base_pt := singularPoint_naturality ((EnrichedFunctorCat.evaluation a).map q.right)

/-- The same whole source square commutes with both original chosen-fiber comparison maps. -/
theorem chosenFiberLevelSingularIso_naturality (q : Arrow.mk p ⟶ Arrow.mk p') :
    singularFunctor.map ((EnrichedFunctorCat.evaluation a).map (chosenFiberMap q c d hd)) ≫
        (chosenFiberLevelSingularIso p' d hd a hp').hom =
      (chosenFiberLevelSingularIso p c hc a hp).hom ≫
        (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap := by
  let E : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤ PointedCGWH.{u, v} :=
    EnrichedFunctorCat.evaluation a
  have h : E.map (chosenFiberMap q c d hd) ≫ E.map d.fst = E.map c.fst ≫ E.map q.left :=
    (E.map_comp _ _).symm.trans
      ((E.congr_map (chosenFiberMap_fst q c d hd)).trans (E.map_comp _ _))
  apply (cancel_mono (chosenFiberLevelSequence p' a hp').fiberIncl).mp
  have hLeft :
      (singularFunctor.map (E.map (chosenFiberMap q c d hd)) ≫
        (chosenFiberLevelSingularIso p' d hd a hp').hom) ≫
          (chosenFiberLevelSequence p' a hp').fiberIncl =
      singularFunctor.map (E.map c.fst) ≫ singularFunctor.map (E.map q.left) := by
    rw [Category.assoc, chosenFiberLevelSingularIso_hom_projection p' d hd a hp',
      ← singularFunctor.map_comp, h, singularFunctor.map_comp]
  have hRight :
      ((chosenFiberLevelSingularIso p c hc a hp).hom ≫
        (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap) ≫
          (chosenFiberLevelSequence p' a hp').fiberIncl =
      singularFunctor.map (E.map c.fst) ≫ (chosenFiberLevelSequenceMap p a hp hp' q).totalMap := by
    rw [Category.assoc, SSet.FibrationSequenceHom.fiberMap_ι, ← Category.assoc,
      chosenFiberLevelSingularIso_hom_projection p c hc a hp]
  exact hLeft.trans hRight.symm

/-- Every literal degree retains the complete naturality of the original chosen-fiber Iso. -/
theorem chosenFiberLevelPiEquiv_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (k : ℕ)
    (x : (piFunctor k).obj ((EnrichedFunctorCat.evaluation a).obj c.pt)) :
    chosenFiberLevelPiEquiv p' d hd a hp' k
        ((piFunctor k).map ((EnrichedFunctorCat.evaluation a).map (chosenFiberMap q c d hd)) x) =
      SSet.KanComplex.π.map (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap
        (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap_app_basePoint k
          (chosenFiberLevelPiEquiv p c hc a hp k x) :=
  SSet.KanComplex.π.map_square
    (chosenFiberLevelSingularIso p c hc a hp).hom
    (chosenFiberLevelSingularIso p' d hd a hp').hom
    (singularFunctor.map ((EnrichedFunctorCat.evaluation a).map (chosenFiberMap q c d hd)))
    (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap
    (chosenFiberLevelSingularIso_naturality p c hc a hp d hd hp' q)
    (chosenFiberLevelSingularIso_hom_point p c hc a hp)
    (chosenFiberLevelSingularIso_hom_point p' d hd a hp')
    (singularPoint_naturality ((EnrichedFunctorCat.evaluation a).map (chosenFiberMap q c d hd)))
    (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap_app_basePoint k x

/-- Both original inverse comparison functions retain the same complete Arrow naturality. -/
theorem chosenFiberLevelPiEquiv_symm_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (k : ℕ)
    (x : SSet.KanComplex.π k (chosenFiberLevelSequence p a hp).fiber
      (chosenFiberLevelSequence p a hp).fiberPoint) :
    (chosenFiberLevelPiEquiv p' d hd a hp' k).symm
        (SSet.KanComplex.π.map (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap
          (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap_app_basePoint k x) =
      (piFunctor k).map ((EnrichedFunctorCat.evaluation a).map (chosenFiberMap q c d hd))
        ((chosenFiberLevelPiEquiv p c hc a hp k).symm x) := by
  apply (chosenFiberLevelPiEquiv p' d hd a hp' k).injective
  rw [Equiv.apply_symm_apply,
    chosenFiberLevelPiEquiv_naturality p c hc a hp d hd hp' q k,
    Equiv.apply_symm_apply]

/-- The original all-degree connecting map is natural, including its degree-zero target. -/
theorem chosenFiberLevelSingularConnectingMap_naturality
    (q : Arrow.mk p ⟶ Arrow.mk p') (k : ℕ)
    (x : (piFunctor (k + 1)).obj ((EnrichedFunctorCat.evaluation a).obj Y)) :
    (piFunctor k).map ((EnrichedFunctorCat.evaluation a).map (chosenFiberMap q c d hd))
        (chosenFiberLevelSingularConnectingMap p c hc a hp k x) =
      chosenFiberLevelSingularConnectingMap p' d hd a hp' k
        ((piFunctor (k + 1)).map ((EnrichedFunctorCat.evaluation a).map q.right) x) := by
  apply (chosenFiberLevelPiEquiv p' d hd a hp' k).injective
  rw [chosenFiberLevelPiEquiv_naturality p c hc a hp d hd hp' q k,
    chosenFiberLevelSingularConnectingMap_reconstruction p c hc a hp k,
    chosenFiberLevelSingularConnectingMap_reconstruction p' d hd a hp' k]
  exact SSet.FibrationSequence.connectingMap_naturality
    (chosenFiberLevelSequenceMap p a hp hp' q) x

/-- The entire positive cube comparison retains every original whole Arrow map. -/
theorem chosenFiberLevelCubeMulEquiv_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (k : ℕ)
    (x : PointedCGWH.piN (k + 1) ((EnrichedFunctorCat.evaluation a).obj c.pt)) :
    chosenFiberLevelCubeMulEquiv p' d hd a hp' k
        (PointedCGWH.piNMap (k + 1)
          ((EnrichedFunctorCat.evaluation a).map (chosenFiberMap q c d hd)) x) =
      SSet.KanComplex.π.map (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap
        (chosenFiberLevelSequenceMap p a hp hp' q).fiberMap_app_basePoint (k + 1)
          (chosenFiberLevelCubeMulEquiv p c hc a hp k x) :=
  (congrArg (chosenFiberLevelPiEquiv p' d hd a hp' (k + 1))
    (cubeSingularMulEquiv_naturality k
      ((EnrichedFunctorCat.evaluation a).map (chosenFiberMap q c d hd)) x)).trans
    (chosenFiberLevelPiEquiv_naturality p c hc a hp d hd hp' q (k + 1) _)

/-- The actual chosen connecting homomorphism is natural under every original spectrum square. -/
theorem chosenFiberLevelConnectingHom_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (k : ℕ)
    (x : PointedCGWH.piN (k + 2) ((EnrichedFunctorCat.evaluation a).obj Y)) :
    PointedCGWH.piNMap (k + 1)
        ((EnrichedFunctorCat.evaluation a).map (chosenFiberMap q c d hd))
        (chosenFiberLevelConnectingHom p c hc a hp k x) =
      chosenFiberLevelConnectingHom p' d hd a hp' k
        (PointedCGWH.piNMap (k + 2) ((EnrichedFunctorCat.evaluation a).map q.right) x) := by
  apply (chosenFiberLevelCubeMulEquiv p' d hd a hp' k).injective
  rw [chosenFiberLevelCubeMulEquiv_naturality p c hc a hp d hd hp' q k,
    chosenFiberLevelConnectingHom_reconstruction p c hc a hp k,
    chosenFiberLevelConnectingHom_reconstruction p' d hd a hp' k]
  exact (SSet.FibrationSequence.connectingMap_naturality
    (chosenFiberLevelSequenceMap p a hp hp' q)
    (cubeSingularMulEquiv (k + 1) ((EnrichedFunctorCat.evaluation a).obj Y) x)).trans
      (congrArg ((chosenFiberLevelSequence p' a hp').connectingMap (k + 1))
        (cubeSingularMulEquiv_naturality (k + 1)
          ((EnrichedFunctorCat.evaluation a).map q.right) x).symm)

end Naturality

end HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
