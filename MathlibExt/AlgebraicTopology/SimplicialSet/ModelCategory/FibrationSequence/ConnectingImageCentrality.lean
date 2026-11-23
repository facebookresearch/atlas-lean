/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BetaPairTrivialCofibration
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Loop.OriginalConnectingLiftRepresentation
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.GroupFunctors
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWProduct
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Connecting images in the fundamental group of a strict fiber

The original constant based path gives a trivial cofibration after taking
its product with the actual strict fiber. Lifting against the original
fibration gives a fiberwise path-lifting operation whose constant-path unit
is strict. Restricting that same lift to the chosen fiber point represents
the original connecting map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FibrationSequence.Geometry

open SSet.OriginalBasedPathConnectingGeometry
open SSet.OriginalConnectingLiftRepresentationGeometry
open SSet.LoopShiftOriginalGeometry (originalLoopPoint loopConnectingEquiv)

/-- The original constant-path point inclusion, with the whole strict fiber as its first factor. -/
def fiberPathPointMap (S : SSet.FibrationSequence.{u}) :
    S.fiber ⨯ (Δ[0] : SSet.{u}) ⟶ S.fiber ⨯ basedPath S.B S.b :=
  prod.map (𝟙 S.fiber) (basedPathPointMap S.B S.b)

/-- The actual product point inclusion is a trivial cofibration in the existing Kan model. -/
theorem fiberPathPointMap_trivialCofibration (S : SSet.FibrationSequence.{u}) :
    trivialCofibrations SSet.{u} (fiberPathPointMap S) :=
  SSet.trivialCofibration_prodMap_id_left S.fiber (basedPathPointMap S.B S.b)
    ((mem_trivialCofibrations_iff _).mpr
      ⟨basedPathPointMap_cofibration S.B S.b, basedPathPointMap_weakEquivalence S.B S.b⟩)

/-- The product lifting square retains the original fiber inclusion and endpoint projection. -/
theorem fiberPathLiftSquare (S : SSet.FibrationSequence.{u}) :
    CommSq ((prod.fst : S.fiber ⨯ (Δ[0] : SSet.{u}) ⟶ S.fiber) ≫ S.fiberIncl)
      (fiberPathPointMap S) S.p
      ((prod.snd : S.fiber ⨯ basedPath S.B S.b ⟶ basedPath S.B S.b) ≫ basedPathProj S.B S.b) := by
  refine ⟨?_⟩
  calc
    (prod.fst ≫ S.fiberIncl) ≫ S.p = SSet.const S.b := by
      rw [Category.assoc, S.fiberIncl_comp, SSet.comp_const]
    _ = fiberPathPointMap S ≫ (prod.snd ≫ basedPathProj S.B S.b) := by
      rw [fiberPathPointMap, ← Category.assoc, prod.map_snd, Category.assoc,
        basedPathPointMap_projection, SSet.comp_const]

/-- CM4 lifts the actual product square against the original fibration. -/
theorem fiberPathLiftSquare_hasLift (S : SSet.FibrationSequence.{u}) :
    (fiberPathLiftSquare S).HasLift := by
  obtain ⟨hcof, hweak⟩ := (mem_trivialCofibrations_iff _).mp
    (fiberPathPointMap_trivialCofibration S)
  let := hcof
  let := hweak
  let := S.fibration_p
  infer_instance

/-- A whole fiberwise based-path lift chosen from the actual product lifting square. -/
def fiberPathLift (S : SSet.FibrationSequence.{u}) :
    S.fiber ⨯ basedPath S.B S.b ⟶ S.E := by
  letI := fiberPathLiftSquare_hasLift S
  exact (fiberPathLiftSquare S).lift

/-- The lift covers the entire original endpoint projection. -/
@[reassoc]
theorem fiberPathLift_projection (S : SSet.FibrationSequence.{u}) :
    fiberPathLift S ≫ S.p = prod.snd ≫ basedPathProj S.B S.b := by
  let := fiberPathLiftSquare_hasLift S
  exact (fiberPathLiftSquare S).fac_right

/-- The lift agrees with the original inclusion on every fiber simplex over the constant path. -/
@[reassoc]
theorem fiberPathLift_point_map (S : SSet.FibrationSequence.{u}) :
    fiberPathPointMap S ≫ fiberPathLift S = prod.fst ≫ S.fiberIncl := by
  let := fiberPathLiftSquare_hasLift S
  exact (fiberPathLiftSquare S).fac_left

/-- The original constant based path restricts the full lift to the original fiber inclusion. -/
@[reassoc]
theorem fiberPathLift_unit (S : SSet.FibrationSequence.{u}) :
    prod.lift (𝟙 S.fiber) (SSet.const (basedPathPoint S.B S.b)) ≫ fiberPathLift S =
      S.fiberIncl := by
  let q : S.fiber ⟶ (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.from S.fiber
  have h : prod.lift (𝟙 S.fiber) q ≫ fiberPathPointMap S =
      prod.lift (𝟙 S.fiber) (SSet.const (basedPathPoint S.B S.b)) := by
    apply prod.hom_ext
    · simp only [fiberPathPointMap, Category.assoc, prod.map_fst, prod.lift_fst,
        Category.comp_id]
    · simp only [fiberPathPointMap, Category.assoc, prod.map_snd, prod.lift_snd,
        basedPathPointMap, SSet.comp_const]
  rw [← h, Category.assoc, fiberPathLift_point_map, ← Category.assoc, prod.lift_fst,
    Category.id_comp]

/-- Restrict the fiberwise path lift to loops and factor through the original strict fiber. -/
def fiberLoopAction (S : SSet.FibrationSequence.{u}) :
    S.fiber ⨯ loopSpace S.B S.b ⟶ S.fiber :=
  S.fiber_isPullback.lift
    (prod.map (𝟙 S.fiber) (loopSpaceIncl S.B S.b) ≫ fiberPathLift S)
    (stdSimplex.isTerminalObj₀.from (S.fiber ⨯ loopSpace S.B S.b)) (by
      have hloop : loopSpaceIncl S.B S.b ≫ basedPathProj S.B S.b = SSet.const S.b :=
        (loopFibrationSequence S.B S.b).fiberIncl_comp
      rw [SSet.comp_const, Category.assoc, fiberPathLift_projection,
        ← Category.assoc, prod.map_snd, Category.assoc, hloop, SSet.comp_const])

/-- The entire loop operation keeps the original lifted total-space map. -/
@[reassoc]
theorem fiberLoopAction_projection (S : SSet.FibrationSequence.{u}) :
    fiberLoopAction S ≫ S.fiberIncl =
      prod.map (𝟙 S.fiber) (loopSpaceIncl S.B S.b) ≫ fiberPathLift S :=
  S.fiber_isPullback.lift_fst _ _ _

/-- The original constant loop is a strict right unit for the fiberwise loop operation. -/
@[reassoc]
theorem fiberLoopAction_unit (S : SSet.FibrationSequence.{u}) :
    prod.lift (𝟙 S.fiber) (SSet.const (originalLoopPoint S.B S.b)) ≫ fiberLoopAction S =
      𝟙 S.fiber := by
  let : Mono S.fiberIncl := inferInstanceAs (Mono (Subcomplex.fiber S.p S.b).ι)
  apply (cancel_mono S.fiberIncl).mp
  have h : prod.lift (𝟙 S.fiber) (SSet.const (originalLoopPoint S.B S.b)) ≫
      prod.map (𝟙 S.fiber) (loopSpaceIncl S.B S.b) =
      prod.lift (𝟙 S.fiber) (SSet.const (basedPathPoint S.B S.b)) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id]
    · simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc, prod.lift_snd,
        SSet.const_comp]
      rfl
  rw [Category.assoc, fiberLoopAction_projection, ← Category.assoc, h,
    fiberPathLift_unit, Category.id_comp]

/-- The same fiberwise path lift restricted to the original selected fiber vertex. -/
def fiberPathOrbitLift (S : SSet.FibrationSequence.{u}) : basedPath S.B S.b ⟶ S.E :=
  prod.lift (SSet.const S.fiberPoint) (𝟙 (basedPath S.B S.b)) ≫ fiberPathLift S

/-- The selected-vertex lift retains the entire original endpoint projection. -/
@[reassoc]
theorem fiberPathOrbitLift_projection (S : SSet.FibrationSequence.{u}) :
    fiberPathOrbitLift S ≫ S.p = basedPathProj S.B S.b := by
  rw [fiberPathOrbitLift, Category.assoc, fiberPathLift_projection,
    ← Category.assoc, prod.lift_snd, Category.id_comp]

/-- The selected-vertex lift retains the original full constant-point map. -/
theorem fiberPathOrbitLift_point_map (S : SSet.FibrationSequence.{u}) :
    basedPathPointMap S.B S.b ≫ fiberPathOrbitLift S = SSet.const (X := Δ[0]) S.e := by
  have h : basedPathPointMap S.B S.b ≫
      prod.lift (SSet.const S.fiberPoint) (𝟙 (basedPath S.B S.b)) =
      SSet.const (X := Δ[0]) S.fiberPoint ≫
        prod.lift (𝟙 S.fiber) (SSet.const (basedPathPoint S.B S.b)) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, SSet.comp_const, Category.comp_id]
    · simp only [Category.assoc, prod.lift_snd, SSet.comp_const, Category.comp_id,
        basedPathPointMap]
  rw [fiberPathOrbitLift, ← Category.assoc, h, Category.assoc, fiberPathLift_unit,
    SSet.const_comp]
  rfl

/-- The selected-vertex lift preserves the same original constant-path vertex. -/
theorem fiberPathOrbitLift_point (S : SSet.FibrationSequence.{u}) :
    (fiberPathOrbitLift S).app _ (basedPathPoint S.B S.b) = S.e := by
  have h := fiberPathOrbitLift_point_map S
  change SSet.const (X := Δ[0]) (basedPathPoint S.B S.b) ≫ fiberPathOrbitLift S =
    SSet.const S.e at h
  rw [SSet.const_comp] at h
  simpa only [SSet.yonedaEquiv_const] using
    congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ S.E => SSet.yonedaEquiv f) h

/-- The selected fiber vertex gives a whole original pointed sequence map over identity. -/
def fiberPathOrbitSequenceHom (S : SSet.FibrationSequence.{u}) :
    SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S where
  totalMap := fiberPathOrbitLift S
  baseMap := 𝟙 S.B
  comm := (fiberPathOrbitLift_projection S).trans (Category.comp_id (basedPathProj S.B S.b)).symm
  total_pt := fiberPathOrbitLift_point S
  base_pt := rfl

/-- The second axis of the loop operation is the original loop map of the same whole lift. -/
@[reassoc]
theorem fiberLoopAction_orbit (S : SSet.FibrationSequence.{u}) :
    prod.lift (SSet.const S.fiberPoint) (𝟙 (loopSpace S.B S.b)) ≫ fiberLoopAction S =
      originalConnectingLoopMapOfLift S (fiberPathOrbitSequenceHom S) := by
  let : Mono S.fiberIncl := inferInstanceAs (Mono (Subcomplex.fiber S.p S.b).ι)
  apply (cancel_mono S.fiberIncl).mp
  have h : prod.lift (SSet.const S.fiberPoint) (𝟙 (loopSpace S.B S.b)) ≫
      prod.map (𝟙 S.fiber) (loopSpaceIncl S.B S.b) =
      loopSpaceIncl S.B S.b ≫
        prod.lift (SSet.const S.fiberPoint) (𝟙 (basedPath S.B S.b)) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, prod.lift_fst, SSet.comp_const,
        Category.comp_id]
    · simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc, prod.lift_snd,
        Category.id_comp, Category.comp_id]
  rw [Category.assoc, fiberLoopAction_projection, ← Category.assoc, h, Category.assoc]
  exact (originalConnectingLoopMapOfLift_projection S (fiberPathOrbitSequenceHom S)).symm

end SSet.FibrationSequence.Geometry

attribute [local instance] SSet.KanComplex.prod_kanComplex

namespace SSet.KanComplex

private theorem constant_vertex {X Y : SSet.{u}} (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (SSet.const (X := X) y).app _ x = y := by
  apply SSet.yonedaEquiv.symm.injective
  rw [SSet.yonedaEquiv_symm_zero, SSet.yonedaEquiv_symm_zero,
    ← SSet.const_comp (X := Δ[0]) x (SSet.const (X := X) y), SSet.comp_const]

private theorem pi_map_const_eq_one {X Y : SSet.{u}} {x : X _⦋0⦌}
    (y : Y _⦋0⦌) (h : (SSet.const (X := X) y).app _ x = y) (n : ℕ)
    (q : π n X x) : π.map (SSet.const y) h n q = 1 := by
  induction q using π.rec with
  | mk p =>
    rw [π.map_mk]
    change π.mk _ = π.mk (RelativeMorphism.const : Y.PtSimplex n y)
    apply congrArg π.mk
    apply RelativeMorphism.ext
    exact SSet.comp_const (RelativeMorphism.map p) y

/-- Classes of a product with trivial opposite projections commute in every positive degree. -/
theorem commute_of_product_projections_eq_one {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (n : ℕ) (z : (X ⨯ Y) _⦋0⦌)
    {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (hx : (prod.fst : X ⨯ Y ⟶ X).app _ z = x)
    (hy : (prod.snd : X ⨯ Y ⟶ Y).app _ z = y)
    (a b : π (n + 1) (X ⨯ Y) z)
    (ha : π.map (prod.snd : X ⨯ Y ⟶ Y) hy (n + 1) a = 1)
    (hb : π.map (prod.fst : X ⨯ Y ⟶ X) hx (n + 1) b = 1) : Commute a b := by
  subst x
  subst y
  change a * b = b * a
  apply (bijective_piProdComparison (X := X) (A := Y) (n + 1) z).1
  apply Prod.ext
  · change π.map (prod.fst : X ⨯ Y ⟶ X) rfl (n + 1) (a * b) =
      π.map (prod.fst : X ⨯ Y ⟶ X) rfl (n + 1) (b * a)
    simp only [π.map_mul, hb]
    exact (_root_.mul_one _).trans (_root_.one_mul _).symm
  · change π.map (prod.snd : X ⨯ Y ⟶ Y) rfl (n + 1) (a * b) =
      π.map (prod.snd : X ⨯ Y ⟶ Y) rfl (n + 1) (b * a)
    simp only [π.map_mul, ha]
    exact (_root_.one_mul _).trans (_root_.mul_one _).symm

/-- The second axis of a product operation with a strict first-axis unit induces a central image. -/
theorem map_mem_center_of_product_unit {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (x : X _⦋0⦌) (y : Y _⦋0⦌) (μ : X ⨯ Y ⟶ X) (f : Y ⟶ X) (hf : f.app _ y = x)
    (hunit : prod.lift (𝟙 X) (SSet.const y) ≫ μ = 𝟙 X)
    (horbit : prod.lift (SSet.const x) (𝟙 Y) ≫ μ = f) (b : π 1 Y y) :
    π.map f hf 1 b ∈ Subgroup.center (π 1 X x) := by
  apply Subgroup.mem_center_iff.mpr
  intro a
  let iX : X ⟶ X ⨯ Y := prod.lift (𝟙 X) (SSet.const y)
  let iY : Y ⟶ X ⨯ Y := prod.lift (SSet.const x) (𝟙 Y)
  let z : (X ⨯ Y) _⦋0⦌ := iX.app _ x
  have hpair : SSet.const (X := Δ[0]) x ≫ iX = SSet.const (X := Δ[0]) y ≫ iY := by
    apply prod.hom_ext
    · simp only [iX, iY, Category.assoc, prod.lift_fst, Category.comp_id, SSet.comp_const]
    · simp only [iX, iY, Category.assoc, prod.lift_snd, Category.comp_id, SSet.comp_const]
  have hiY : iY.app _ y = z := by
    rw [SSet.const_comp, SSet.const_comp] at hpair
    simpa only [SSet.yonedaEquiv_const] using
      congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ X ⨯ Y => SSet.yonedaEquiv f) hpair.symm
  have hx : (prod.fst : X ⨯ Y ⟶ X).app _ z = x := by
    change (iX ≫ prod.fst).app _ x = x
    rw [show iX ≫ prod.fst = 𝟙 X from prod.lift_fst _ _]
    rfl
  have hy : (prod.snd : X ⨯ Y ⟶ Y).app _ z = y := by
    change (iX ≫ prod.snd).app _ x = y
    rw [show iX ≫ prod.snd = SSet.const y from prod.lift_snd _ _]
    exact constant_vertex x y
  have hμ : μ.app _ z = x := by
    change (iX ≫ μ).app _ x = x
    rw [hunit]
    rfl
  let A : π 1 (X ⨯ Y) z := π.map iX rfl 1 a
  let B : π 1 (X ⨯ Y) z := π.map iY hiY 1 b
  have hA : π.map (prod.snd : X ⨯ Y ⟶ Y) hy 1 A = 1 := by
    have hp : (iX ≫ prod.snd).app _ x = y := hy
    calc
      π.map prod.snd hy 1 A = π.map (iX ≫ prod.snd) hp 1 a :=
        (π.map_comp_apply iX prod.snd rfl hy hp a).symm
      _ = π.map (SSet.const y) (constant_vertex x y) 1 a :=
        congrFun (π.map_congr (prod.lift_snd _ _) hp (constant_vertex x y) 1) a
      _ = 1 := pi_map_const_eq_one y (constant_vertex x y) 1 a
  have hB : π.map (prod.fst : X ⨯ Y ⟶ X) hx 1 B = 1 := by
    have hp : (iY ≫ prod.fst).app _ y = x := by
      change (prod.fst : X ⨯ Y ⟶ X).app _ (iY.app _ y) = x
      rw [hiY]
      exact hx
    calc
      π.map prod.fst hx 1 B = π.map (iY ≫ prod.fst) hp 1 b :=
        (π.map_comp_apply iY prod.fst hiY hx hp b).symm
      _ = π.map (SSet.const x) (constant_vertex y x) 1 b :=
        congrFun (π.map_congr (prod.lift_fst _ _) hp (constant_vertex y x) 1) b
      _ = 1 := pi_map_const_eq_one x (constant_vertex y x) 1 b
  have haxes := commute_of_product_projections_eq_one 0 z hx hy A B hA hB
  have hm := congrArg (π.map μ hμ 1) haxes.eq
  rw [π.map_mul μ hμ 0 A B, π.map_mul μ hμ 0 B A] at hm
  have hfirst : π.map μ hμ 1 A = a := by
    have hp : (iX ≫ μ).app _ x = x := hμ
    calc
      π.map μ hμ 1 A = π.map (iX ≫ μ) hp 1 a :=
        (π.map_comp_apply iX μ rfl hμ hp a).symm
      _ = π.map (𝟙 X) rfl 1 a := congrFun (π.map_congr hunit hp rfl 1) a
      _ = a := π.map_id_apply a
  have hsecond : π.map μ hμ 1 B = π.map f hf 1 b := by
    have hp : (iY ≫ μ).app _ y = x := by
      change μ.app _ (iY.app _ y) = x
      rw [hiY]
      exact hμ
    calc
      π.map μ hμ 1 B = π.map (iY ≫ μ) hp 1 b :=
        (π.map_comp_apply iY μ hiY hμ hp b).symm
      _ = π.map f hf 1 b := congrFun (π.map_congr horbit hp hf 1) b
  simpa only [hfirst, hsecond] using hm

end SSet.KanComplex

namespace SSet.FibrationSequence.Geometry

open SSet.OriginalConnectingLiftRepresentationGeometry
open SSet.LoopShiftOriginalGeometry (originalLoopPoint loopConnectingEquiv)

/-- The image of the original connecting homomorphism is central in the original strict fiber. -/
theorem sequenceConnectingGroupHom_range_le_center (S : SSet.FibrationSequence.{u}) :
    (sequenceConnectingGroupHom S 0).range ≤
      Subgroup.center (SSet.KanComplex.π 1 S.fiber S.fiberPoint) := by
  rintro z ⟨q, rfl⟩
  have h := SSet.KanComplex.map_mem_center_of_product_unit
    S.fiberPoint (originalLoopPoint S.B S.b) (fiberLoopAction S)
    (originalConnectingLoopMapOfLift S (fiberPathOrbitSequenceHom S))
    (originalConnectingLoopMapOfLift_point S (fiberPathOrbitSequenceHom S))
    (fiberLoopAction_unit S) (fiberLoopAction_orbit S) (loopConnectingEquiv 1 S.B S.b q)
  rw [originalConnectingLoopMapOfLift_pi_then_shift S (fiberPathOrbitSequenceHom S) rfl 1 q] at h
  exact h

end SSet.FibrationSequence.Geometry
