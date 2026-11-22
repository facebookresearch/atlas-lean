/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkPowerOperatorDK
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalEquivalenceFibreWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The SAME original full-power core endpoint relative comparison

Only the original operator and an RF Segal space are supplied. The actual
mapping-fibre weakness is constructed by Power15; no weak or homotopy outcome
is a caller input. Completeness and diagonal homotopy-fibre preservation are
not premises of this whole row comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SSet.modelCategoryQuillen.modelCategory
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory

namespace SimplicialSpace.RezkPowerCoreRelativeComparison
open RezkPowerOperatorDK SegalHomotopy

/-- The source-pair to target-pair map uses the same zero-level operator twice. -/
abbrev pairMap {n m : SimplexCategory} (δ : n ⟶ m) (W : SimplicialSpace.{u}) :=
  prod.map ((powerMap δ W).hom.app (op ⦋0⦌))
    ((powerMap δ W).hom.app (op ⦋0⦌))

/-- The target is the full pullback of the original target core endpoint. -/
abbrev relativeTarget {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) : SSet.{u} :=
  pullback (coreEndpoint (power n W) (power_segal n W hW)) (pairMap δ W)

/-- Both component endpoints commute with the SAME power operator. -/
theorem coreMap_endpoint {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    equivalenceMap (powerMap δ W) (power_segal m W hW) (power_segal n W hW) ≫
      coreEndpoint (power n W) (power_segal n W hW) =
    coreEndpoint (power m W) (power_segal m W hW) ≫ pairMap δ W := by
  apply prod.hom_ext
  · simpa only [coreEndpoint, pairMap, Category.assoc, prod.lift_fst,
      prod.lift_fst_assoc, prod.map_fst] using
      (equivalenceSource_naturality (powerMap δ W)
        (power_segal m W hW) (power_segal n W hW))
  · simpa only [coreEndpoint, pairMap, Category.assoc, prod.lift_snd,
      prod.lift_snd_assoc, prod.map_snd] using
      (equivalenceTarget_naturality (powerMap δ W)
        (power_segal m W hW) (power_segal n W hW))

/-- The relative comparison is the actual entire pullback lift. -/
def relativeMap {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (equivalenceSubcomplex (power m W) (power_segal m W hW) : SSet.{u}) ⟶
      relativeTarget δ W hW :=
  pullback.lift
    (equivalenceMap (powerMap δ W) (power_segal m W hW) (power_segal n W hW))
    (coreEndpoint (power m W) (power_segal m W hW)) (coreMap_endpoint δ W hW)

/-- The total and base projections are the two original maps, in the original order. -/
theorem relativeMap_legs {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    relativeMap δ W hW ≫
      pullback.fst (coreEndpoint (power n W) (power_segal n W hW)) (pairMap δ W) =
        equivalenceMap (powerMap δ W) (power_segal m W hW) (power_segal n W hW) ∧
    relativeMap δ W hW ≫
      pullback.snd (coreEndpoint (power n W) (power_segal n W hW)) (pairMap δ W) =
        coreEndpoint (power m W) (power_segal m W hW) := by
  exact ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- Every inner operator commutes with the whole relative comparison. -/
theorem relativeMap_naturality {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {a b : SimplexCategoryᵒᵖ} (θ : a ⟶ b) :
    (equivalenceSubcomplex (power m W) (power_segal m W hW)).toSSet.map θ ≫
      (relativeMap δ W hW).app b =
    (relativeMap δ W hW).app a ≫ (relativeTarget δ W hW).map θ :=
  (relativeMap δ W hW).naturality θ

/-- Native pullback pasting followed by the genuine original point-pair naturality. -/
def pointTargetIso {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : ((power m W).diagram _⦋0⦌) _⦋0⦌) :
    pullback
      (pullback.snd (coreEndpoint (power n W) (power_segal n W hW)) (pairMap δ W))
      (mappingPointPair (power m W) x y) ≅
    equivalenceFibre (power n W) (power_segal n W hW)
      (mappingVertexMap (powerMap δ W) x) (mappingVertexMap (powerMap δ W) y) :=
  pullbackLeftPullbackSndIso
      (coreEndpoint (power n W) (power_segal n W hW)) (pairMap δ W)
      (mappingPointPair (power m W) x y) ≪≫
    pullback.congrHom rfl (mappingPointPair_naturality (powerMap δ W) x y)

/-- The point map is the full same-base pullback map of the SAME relative comparison. -/
def pointMap {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : ((power m W).diagram _⦋0⦌) _⦋0⦌) :=
  pullback.map
    (coreEndpoint (power m W) (power_segal m W hW)) (mappingPointPair (power m W) x y)
    (pullback.snd (coreEndpoint (power n W) (power_segal n W hW)) (pairMap δ W))
    (mappingPointPair (power m W) x y) (relativeMap δ W hW) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact (relativeMap_legs δ W hW).2.symm) (by simp)

/-- The two forward and two inverse target-fibre projections are whole-map equations. -/
theorem pointTargetIso_legs {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : ((power m W).diagram _⦋0⦌) _⦋0⦌) :
    let q := coreEndpoint (power n W) (power_segal n W hW)
    let a := mappingPointPair (power m W) x y
    let b := mappingPointPair (power n W)
      (mappingVertexMap (powerMap δ W) x) (mappingVertexMap (powerMap δ W) y)
    let e := pointTargetIso δ W hW x y
    e.hom ≫ pullback.fst q b = pullback.fst (pullback.snd q (pairMap δ W)) a ≫
      pullback.fst q (pairMap δ W) ∧
    e.hom ≫ pullback.snd q b = pullback.snd (pullback.snd q (pairMap δ W)) a ∧
    e.inv ≫ pullback.fst (pullback.snd q (pairMap δ W)) a ≫
      pullback.fst q (pairMap δ W) = pullback.fst q b ∧
    e.inv ≫ pullback.snd (pullback.snd q (pairMap δ W)) a = pullback.snd q b := by
  dsimp only
  let q := coreEndpoint (power n W) (power_segal n W hW)
  let a := mappingPointPair (power m W) x y
  let b := mappingPointPair (power n W)
    (mappingVertexMap (powerMap δ W) x) (mappingVertexMap (powerMap δ W) y)
  let c : pullback q (a ≫ pairMap δ W) ≅ pullback q b :=
    pullback.congrHom rfl (mappingPointPair_naturality (powerMap δ W) x y)
  have hcF : c.hom ≫ pullback.fst q b = pullback.fst q (a ≫ pairMap δ W) := by
    change pullback.lift _ _ _ ≫ pullback.fst q b = _
    rw [pullback.lift_fst, Category.comp_id]
  have hcS : c.hom ≫ pullback.snd q b = pullback.snd q (a ≫ pairMap δ W) := by
    change pullback.lift _ _ _ ≫ pullback.snd q b = _
    rw [pullback.lift_snd, Category.comp_id]
  have hF : (pointTargetIso δ W hW x y).hom ≫ pullback.fst q b =
      pullback.fst (pullback.snd q (pairMap δ W)) a ≫ pullback.fst q (pairMap δ W) := by
    change ((pullbackLeftPullbackSndIso q (pairMap δ W) a).hom ≫ c.hom) ≫ pullback.fst q b = _
    rw [Category.assoc, hcF, pullbackLeftPullbackSndIso_hom_fst]
  have hS : (pointTargetIso δ W hW x y).hom ≫ pullback.snd q b =
      pullback.snd (pullback.snd q (pairMap δ W)) a := by
    change ((pullbackLeftPullbackSndIso q (pairMap δ W) a).hom ≫ c.hom) ≫ pullback.snd q b = _
    rw [Category.assoc, hcS, pullbackLeftPullbackSndIso_hom_snd]
  refine ⟨hF, hS, ?_, ?_⟩
  · rw [Iso.inv_comp_eq]
    exact hF.symm
  · rw [Iso.inv_comp_eq]
    exact hS.symm

/-- Composing with the exact point-target Iso is the original equivalence-fibre map. -/
theorem pointMap_comp_targetIso {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : ((power m W).diagram _⦋0⦌) _⦋0⦌) :
    pointMap δ W hW x y ≫ (pointTargetIso δ W hW x y).hom =
      equivalenceFibreMap (powerMap δ W) (power_segal m W hW)
        (power_segal n W hW) (x := x) (y := y) rfl rfl := by
  apply pullback.hom_ext
  · rw [Category.assoc, (pointTargetIso_legs δ W hW x y).1]
    simp only [pointMap, pullback.map, ← Category.assoc, pullback.lift_fst,
      relativeMap, equivalenceFibreMap]
    rw [Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, (pointTargetIso_legs δ W hW x y).2.1]
    simp only [pointMap, equivalenceFibreMap, pullback.map, pullback.lift_snd,
      Category.comp_id]

/-- Every original point-fibre map is weak by internally constructed MF weakness. -/
theorem pointMap_weak {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : ((power m W).diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (pointMap δ W hW x y) := by
  have hm := powerMap_mappingFibre_weak δ (0 : Fin (n.len + 1)) W hW
  have he := equivalenceFibreMap_weak_of_mappingFibreWeak
    (powerMap δ W) (power_segal m W hW) (power_segal n W hW) hm x y
  apply (SSet.realizationWeakEquivalences.cancel_right_of_respectsIso
    (pointMap δ W hW x y) (pointTargetIso δ W hW x y).hom).mp
  rw [pointMap_comp_targetIso]
  exact he

private theorem powerZero_kan (n : SimplexCategory) (W : SimplicialSpace.{u})
    (hW : segalSpaces W) : SSet.KanComplex ((power n W).diagram _⦋0⦌) := by
  let A := power n W
  let X := ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[0] : SSet.{u}))
  have hK := ReedyModel.innerHom_kanComplex X A (ReedyModel.isCofibrant X)
    (power_segal n W hW).1
  change SSet.KanComplex ((discreteSourceMapping A).obj (op (Δ[0] : SSet.{u}))) at hK
  let _ : IsFibrant ((discreteSourceMapping A).obj (op (Δ[0] : SSet.{u}))) := hK
  exact isFibrant_of_fibration (discreteYonedaIso A 0).inv

private theorem pair_kan {A : SSet.{u}} (hA : SSet.KanComplex A) :
    SSet.KanComplex (A ⨯ A) := by
  let _ : IsFibrant A := hA
  have hPull : IsPullback (prod.snd : A ⨯ A ⟶ A)
      (prod.fst : A ⨯ A ⟶ A) (terminal.from A) (terminal.from A) :=
    (IsPullback.of_isLimit_binaryFan_of_isTerminal (limit.isLimit (pair A A))
      terminalIsTerminal).flip
  let _ : Fibration (prod.fst : A ⨯ A ⟶ A) := by
    rw [HomotopicalAlgebra.fibration_iff]
    exact (fibrations SSet.{u}).of_isPullback hPull
      ((HomotopicalAlgebra.fibration_iff _).mp (inferInstanceAs (Fibration (terminal.from A))))
  exact isFibrant_of_fibration (prod.fst : A ⨯ A ⟶ A)

/-- The entire original core-relative row map is weak; its own fibration is not assumed. -/
theorem relativeMap_weak {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (relativeMap δ W hW) := by
  let A := power m W
  let B := power n W
  let qA := coreEndpoint A (power_segal m W hW)
  let qB := coreEndpoint B (power_segal n W hW)
  let _ : Fibration qA := coreEndpoint_fibration A (power_segal m W hW)
  let _ : Fibration (pullback.snd qB (pairMap δ W)) := by
    rw [HomotopicalAlgebra.fibration_iff]
    exact (fibrations SSet.{u}).of_isPullback (IsPullback.of_hasPullback _ _)
      ((HomotopicalAlgebra.fibration_iff _).mp
        (coreEndpoint_fibration B (power_segal n W hW)))
  let _ : SSet.KanComplex (A.diagram _⦋0⦌ ⨯ A.diagram _⦋0⦌) :=
    pair_kan (powerZero_kan m W hW)
  apply (SSet.realizationWeakEquivalence_iff_pullbackFibrewise_of_base_fibrations
    (relativeMap δ W hW) qA (pullback.snd qB (pairMap δ W))
    (relativeMap_legs δ W hW).2).mpr
  intro b
  obtain ⟨x, y, rfl⟩ : ∃ x y : (A.diagram _⦋0⦌) _⦋0⦌,
      mappingPointPair A x y = b := by
    let x : (A.diagram _⦋0⦌) _⦋0⦌ :=
      (prod.fst : A.diagram _⦋0⦌ ⨯ A.diagram _⦋0⦌ ⟶ A.diagram _⦋0⦌).app (op ⦋0⦌)
        (SSet.yonedaEquiv b)
    let y : (A.diagram _⦋0⦌) _⦋0⦌ :=
      (prod.snd : A.diagram _⦋0⦌ ⨯ A.diagram _⦋0⦌ ⟶ A.diagram _⦋0⦌).app (op ⦋0⦌)
        (SSet.yonedaEquiv b)
    refine ⟨x, y, ?_⟩
    apply prod.hom_ext
    · rw [mappingPointPair_fst]
      simpa only [x, Equiv.symm_apply_apply] using
        (SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv b)
          (prod.fst : A.diagram _⦋0⦌ ⨯ A.diagram _⦋0⦌ ⟶ A.diagram _⦋0⦌)).symm
    · rw [mappingPointPair_snd]
      simpa only [y, Equiv.symm_apply_apply] using
        (SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv b)
          (prod.snd : A.diagram _⦋0⦌ ⨯ A.diagram _⦋0⦌ ⟶ A.diagram _⦋0⦌)).symm
  exact pointMap_weak δ W hW x y

end SimplicialSpace.RezkPowerCoreRelativeComparison
