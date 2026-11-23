/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.HomotopyTraceAction
public import MathlibExt.Topology.Homotopy.CGWHWeakHSpacePositiveGroups
public import MathlibExt.Topology.Homotopy.TopCat.HomotopyGroupIso
public import MathlibExt.Topology.Category.TopCat.WeakHomotopySingleton
public import MathlibExt.AlgebraicTopology.SimplicialSet.ConullWeakHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveRealizedIsoPath
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Tactic.NormNum

/-!
# Semantic tests for the canonical topology APIs

The ten named tests evaluate a shifted weak unit and its root from `1` to
`0`, the reversed native representative product, complete relative boundary
maps and a nonconstant homotopy trace. A disconnected two-point space tests
the component condition. Inverse categorical edges are tested at distinct
endpoints.

The generic consumers keep compact-probe, carrier, category-object and Hom
universes independent. The six canonical public imports provide the actual
trace, native positive-group, Iso-transport, singleton, conull and inverse
edge APIs. Locally constant maps and numeric normalization support the
concrete controls. Fixture helpers remain private.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe wTest kTest uTest vTest

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial unitInterval Topology Topology.Homotopy

namespace CanonicalGenericTopologyConsumers

section ShiftedWeakUnit

private abbrev realCGWH : CGWH.{0, 0} := CGWH.of ℝ

private def shiftPlusOne : C(ℝ, ℝ) :=
  ⟨fun x => x + 1, continuous_id.add continuous_const⟩

private def ordinaryShiftMul : C(ℝ × ℝ, ℝ) :=
  ⟨fun xy => xy.1 + xy.2 + 1,
    (continuous_fst.add continuous_snd).add continuous_const⟩

/-- Only the continuous native-to-ordinary comparison is used. -/
private def shiftedMul : realCGWH ⨯ realCGWH ⟶ realCGWH :=
  ConcreteCategory.ofHom
    (ordinaryShiftMul.comp (CGWH.prodComparisonToTop realCGWH realCGWH).hom)

private theorem shiftedMul_prodPoint (x y : ℝ) :
    shiftedMul (CGWH.prodPoint realCGWH realCGWH x y) = x + y + 1 := by
  change
    ordinaryShiftMul
        (CGWH.prodComparisonToTop realCGWH realCGWH
          (CGWH.prodPoint realCGWH realCGWH x y)) =
      x + y + 1
  rewrite [CGWH.prodComparisonToTop_prodPoint]
  rfl

private theorem shiftedLeftUnit_map :
    (CGWH.cgwhToTop.{0, 0}.map
      (CGWH.hspaceLeftUnitMap realCGWH shiftedMul (0 : ℝ))).hom =
      shiftPlusOne := by
  apply ContinuousMap.ext
  intro x
  let xR : ℝ := x
  change CGWH.hspaceLeftUnitMap realCGWH shiftedMul (0 : ℝ) xR = xR + 1
  rw [CGWH.hspaceLeftUnitMap_apply, shiftedMul_prodPoint, zero_add]

private theorem shiftedRightUnit_map :
    (CGWH.cgwhToTop.{0, 0}.map
      (CGWH.hspaceRightUnitMap realCGWH shiftedMul (0 : ℝ))).hom =
      shiftPlusOne := by
  apply ContinuousMap.ext
  intro x
  let xR : ℝ := x
  change CGWH.hspaceRightUnitMap realCGWH shiftedMul (0 : ℝ) xR = xR + 1
  rw [CGWH.hspaceRightUnitMap_apply, shiftedMul_prodPoint, add_zero]

private def shiftUnitHomotopy :
    ContinuousMap.Homotopy shiftPlusOne (ContinuousMap.id ℝ) where
  toFun tx := tx.2 + 1 - (tx.1 : ℝ)
  continuous_toFun :=
    (continuous_snd.add continuous_const).sub
      (continuous_subtype_val.comp continuous_fst)
  map_zero_left x := by
    change x + 1 - (0 : ℝ) = x + 1
    exact sub_zero _
  map_one_left x := by
    change x + 1 - (1 : ℝ) = x
    exact add_sub_cancel_right x 1

private def shiftedLeftUnit :
    ContinuousMap.Homotopy
      (CGWH.cgwhToTop.{0, 0}.map
        (CGWH.hspaceLeftUnitMap realCGWH shiftedMul (0 : ℝ))).hom
      (ContinuousMap.id ℝ) :=
  shiftUnitHomotopy.cast shiftedLeftUnit_map.symm rfl

private def shiftedRightUnit :
    ContinuousMap.Homotopy
      (CGWH.cgwhToTop.{0, 0}.map
        (CGWH.hspaceRightUnitMap realCGWH shiftedMul (0 : ℝ))).hom
      (ContinuousMap.id ℝ) :=
  shiftUnitHomotopy.cast shiftedRightUnit_map.symm rfl

private theorem shiftedUnitPaths_eq :
    CGWH.hspaceRightUnitPath realCGWH shiftedMul (0 : ℝ) shiftedRightUnit =
      CGWH.hspaceLeftUnitPath realCGWH shiftedMul (0 : ℝ) shiftedLeftUnit := by
  apply Path.ext
  funext t
  rfl

private def shiftedWeakHSpace : CGWH.WeakHSpaceData realCGWH where
  mul := shiftedMul
  e := 0
  rootPath :=
    CGWH.hspaceLeftUnitPath realCGWH shiftedMul (0 : ℝ) shiftedLeftUnit
  leftUnit := shiftedLeftUnit
  rightUnit := shiftedRightUnit
  leftUnit_root := Path.Homotopic.refl _
  rightUnit_root := by
    rewrite [shiftedUnitPaths_eq]
    exact Path.Homotopic.refl _

private theorem shifted_mulUnit :
    shiftedWeakHSpace.mulUnit = (1 : ℝ) := by
  change shiftedMul (CGWH.prodPoint realCGWH realCGWH (0 : ℝ) 0) = 1
  exact (shiftedMul_prodPoint 0 0).trans (by norm_num)

private theorem shifted_root_apply (t : unitInterval) :
    shiftedWeakHSpace.rootPath t = 1 - (t : ℝ) := by
  change (0 : ℝ) + 1 - (t : ℝ) = 1 - (t : ℝ)
  rw [zero_add]

private theorem shifted_raw_boundary (n : ℕ)
    (p q : GenLoop (Fin (n + 1)) realCGWH shiftedWeakHSpace.e)
    (t : Fin (n + 1) → unitInterval) (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace (n + 1) p q t = (1 : ℝ) :=
  (GenLoop.boundary
    (CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace (n + 1) p q) t ht).trans
      shifted_mulUnit

private def ordinaryDouble : C(ℝ, ℝ) :=
  ⟨fun x => x + x + 1, (continuous_id.add continuous_id).add continuous_const⟩

private theorem shiftedDoubling_map :
    (CGWH.cgwhToTop.{0, 0}.map
      (CGWH.WeakHSpaceData.nativeDoubling shiftedWeakHSpace)).hom =
      ordinaryDouble := by
  apply ContinuousMap.ext
  intro x
  let xR : ℝ := x
  change CGWH.WeakHSpaceData.nativeDoubling shiftedWeakHSpace xR = xR + xR + 1
  rewrite [CGWH.WeakHSpaceData.nativeDoubling, CategoryTheory.comp_apply,
    CGWH.prod_lift_apply]
  exact shiftedMul_prodPoint x x

private def ordinaryDiagonalHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id ℝ) ordinaryDouble where
  toFun tx := tx.2 + (tx.1 : ℝ) * (tx.2 + 1)
  continuous_toFun :=
    continuous_snd.add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_snd.add continuous_const))
  map_zero_left x := by
    change x + (0 : ℝ) * (x + 1) = x
    simp only [zero_mul, add_zero]
  map_one_left x := by
    change x + (1 : ℝ) * (x + 1) = x + x + 1
    simp only [one_mul, add_assoc]

private def shiftedDiagonalHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id realCGWH)
      (CGWH.cgwhToTop.{0, 0}.map
        (CGWH.WeakHSpaceData.nativeDoubling shiftedWeakHSpace)).hom :=
  ordinaryDiagonalHomotopy.cast rfl shiftedDoubling_map.symm

private theorem shiftedDiagonal_trace :
    ((shiftedDiagonalHomotopy.evalAt shiftedWeakHSpace.e).cast rfl
      (CGWH.WeakHSpaceData.nativeDoubling_unit shiftedWeakHSpace).symm).Homotopic
        shiftedWeakHSpace.rootPath.symm := by
  have hPath :
      (shiftedDiagonalHomotopy.evalAt shiftedWeakHSpace.e).cast rfl
          (CGWH.WeakHSpaceData.nativeDoubling_unit shiftedWeakHSpace).symm =
        shiftedWeakHSpace.rootPath.symm := by
    apply Path.ext
    funext t
    have hTrace :
        ((shiftedDiagonalHomotopy.evalAt shiftedWeakHSpace.e).cast rfl
          (CGWH.WeakHSpaceData.nativeDoubling_unit shiftedWeakHSpace).symm) t =
            (t : ℝ) := by
      change (0 : ℝ) + (t : ℝ) * ((0 : ℝ) + 1) = (t : ℝ)
      simp only [zero_add, mul_one]
    have hReverse :
        shiftedWeakHSpace.rootPath.symm t = 1 - (unitInterval.symm t : ℝ) := by
      change shiftedWeakHSpace.rootPath (unitInterval.symm t) = _
      exact shifted_root_apply (unitInterval.symm t)
    have hScalar : (t : ℝ) = 1 - (unitInterval.symm t : ℝ) := by
      rw [unitInterval.coe_symm_eq, sub_sub_cancel]
    exact hTrace.trans (hScalar.trans hReverse.symm)
  exact hPath ▸ Path.Homotopic.refl _

/-!
Case 1: the weak-unit fixture has a genuinely different raw product point.
Every raw cube boundary is 1, and the root path returns from 1 to 0.
The transported unit laws are consumed at arbitrary positive degree.
-/
theorem shifted_weak_unit_and_transport :
    ∃ H : CGWH.WeakHSpaceData (CGWH.of ℝ : CGWH.{0, 0}),
      H.e = 0 ∧ H.mulUnit = 1 ∧ H.mulUnit ≠ H.e ∧
      (∀ t : unitInterval, H.rootPath t = 1 - (t : ℝ)) ∧
      (∀ (n : ℕ) (p q : GenLoop (Fin (n + 1)) (CGWH.of ℝ : CGWH.{0, 0}) H.e)
        (t : Fin (n + 1) → unitInterval), t ∈ Cube.boundary (Fin (n + 1)) →
          CGWH.WeakHSpaceData.rawCubeMul H (n + 1) p q t = 1) ∧
      (∀ (n : ℕ)
        (a : HomotopyGroup.Pi (n + 1) (CGWH.of ℝ : CGWH.{0, 0}) H.e),
        CGWH.WeakHSpaceData.cubeMul H n 1 a = a ∧
          CGWH.WeakHSpaceData.cubeMul H n a 1 = a) := by
  refine ⟨shiftedWeakHSpace, rfl, shifted_mulUnit, ?_,
    shifted_root_apply, shifted_raw_boundary, ?_⟩
  · intro h
    have h10 : (1 : ℝ) = 0 := shifted_mulUnit.symm.trans h
    exact (one_ne_zero : (1 : ℝ) ≠ 0) h10
  · intro n a
    exact ⟨CGWH.WeakHSpaceData.cubeMul_one_left shiftedWeakHSpace n a,
      CGWH.WeakHSpaceData.cubeMul_one_right shiftedWeakHSpace n a⟩

/-!
Case 2: Id-to-doubling has the reverse root trace 0 to 1. Triviality follows
from the public transported diagonal/Eckmann-Hilton theorem, not an assumed
inverse, connectedness, or contractibility result.
-/
theorem shifted_diagonal_cancels_positive_groups :
    ∃ H : CGWH.WeakHSpaceData (CGWH.of ℝ : CGWH.{0, 0}),
      H.e = 0 ∧ H.mulUnit = 1 ∧
      ∃ J : ContinuousMap.Homotopy (ContinuousMap.id (CGWH.of ℝ : CGWH.{0, 0}))
          (CGWH.cgwhToTop.{0, 0}.map
            (CGWH.WeakHSpaceData.nativeDoubling H)).hom,
        ((J.evalAt H.e).cast rfl
          (CGWH.WeakHSpaceData.nativeDoubling_unit H).symm).Homotopic H.rootPath.symm ∧
        ∀ (n : ℕ) (a : HomotopyGroup.Pi (n + 1) (CGWH.of ℝ : CGWH.{0, 0}) H.e),
          a = 1 := by
  refine ⟨shiftedWeakHSpace, rfl, shifted_mulUnit,
    shiftedDiagonalHomotopy, shiftedDiagonal_trace, ?_⟩
  intro n a
  exact CGWH.WeakHSpaceData.positiveGroup_eq_one
    shiftedWeakHSpace shiftedDiagonalHomotopy shiftedDiagonal_trace n a

/-!
Case 3: the homotopy trace is nonconstant, evaluates to 1 at time 0,
to 0 at time 1, and to 1/2 halfway. The induced group-map equation uses
the actual trace in the forward 1-to-0 direction.
-/
theorem nonconstant_trace_transports_group_map :
    ∃ (f : C(ℝ, ℝ)) (H : ContinuousMap.Homotopy f (ContinuousMap.id ℝ)),
      f 0 = 1 ∧
      (H.evalAt 0) 0 = 1 ∧ (H.evalAt 0) 1 = 0 ∧
      (H.evalAt 0) (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval) = 1 / 2 ∧
      (∀ (n : ℕ) (a : HomotopyGroup.Pi (n + 1) ℝ 0),
        TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of ℝ)
          (H.evalAt 0) (HomotopyGroup.map f a) = a) := by
  refine ⟨shiftPlusOne, shiftUnitHomotopy, ?_, ?_, ?_, ?_, ?_⟩
  · change (0 : ℝ) + 1 = 1
    exact zero_add 1
  · change (0 : ℝ) + 1 - 0 = 1
    norm_num
  · change (0 : ℝ) + 1 - 1 = 0
    norm_num
  · change (0 : ℝ) + 1 - (1 / 2 : ℝ) = 1 / 2
    norm_num
  · intro n a
    let Z : TopCat.{0} := TopCat.of ℝ
    let H : TopCat.Homotopy (TopCat.ofHom shiftPlusOne : Z ⟶ Z) (𝟙 Z) :=
      shiftUnitHomotopy
    have hTrace := TopCat.homotopyGroup_map_homotopy_trace n H (0 : ℝ) a
    exact hTrace.trans (HomotopyGroup.map_id a)

end ShiftedWeakUnit

section RepresentativeOrder

private def firstExcursion : GenLoop (Fin 1) ℝ (0 : ℝ) :=
  ⟨⟨fun t => (t 0 : ℝ) * (1 - (t 0 : ℝ)),
      (continuous_subtype_val.comp (continuous_apply 0)).mul
        (continuous_const.sub (continuous_subtype_val.comp (continuous_apply 0)))⟩, by
    intro t ht
    change (t 0 : ℝ) * (1 - (t 0 : ℝ)) = 0
    obtain ⟨i, hi⟩ := ht
    have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rcases hi with h0 | h1
    · have h0' : (t 0 : ℝ) = 0 := congrArg (fun z : unitInterval => (z : ℝ)) h0
      simp only [h0', zero_mul]
    · have h1' : (t 0 : ℝ) = 1 := congrArg (fun z : unitInterval => (z : ℝ)) h1
      simp only [h1', sub_self, mul_zero]⟩

private def secondExcursion : GenLoop (Fin 1) ℝ (0 : ℝ) :=
  ⟨⟨fun t => 2 * firstExcursion t,
      continuous_const.mul firstExcursion.val.continuous⟩, by
    intro t ht
    change 2 * firstExcursion t = 0
    rw [GenLoop.boundary firstExcursion t ht, mul_zero]⟩

private def quarter : unitInterval :=
  ⟨1 / 4, by constructor <;> norm_num⟩

private def half : unitInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

private def quarterCube : Fin 1 → unitInterval := fun _ => quarter

private theorem quarter_cut : (quarterCube 0 : ℝ) ≤ 1 / 2 := by
  change (1 / 4 : ℝ) ≤ 1 / 2
  norm_num

private theorem quarter_update :
    Function.update quarterCube (0 : Fin 1)
        (Set.projIcc 0 1 zero_le_one (2 * (quarterCube 0 : ℝ))) =
      (fun _ : Fin 1 => half) := by
  have hClip :
      Set.projIcc 0 1 zero_le_one (2 * (quarterCube 0 : ℝ)) = half := by
    apply Subtype.ext
    norm_num [Set.coe_projIcc, quarterCube, quarter, half]
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact (Function.update_self (0 : Fin 1)
    (Set.projIcc 0 1 zero_le_one (2 * (quarterCube 0 : ℝ))) quarterCube).trans hClip

private theorem second_then_first_at_quarter :
    GenLoop.transAt (0 : Fin 1) secondExcursion firstExcursion quarterCube =
      (1 / 2 : ℝ) := by
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  rw [ite_eq_left quarter_cut, quarter_update]
  change 2 * ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))) = 1 / 2
  norm_num

private theorem first_then_second_at_quarter :
    GenLoop.transAt (0 : Fin 1) firstExcursion secondExcursion quarterCube =
      (1 / 4 : ℝ) := by
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  rw [ite_eq_left quarter_cut, quarter_update]
  change (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) = 1 / 4
  norm_num

/-!
Case 4: multiplication of the two classes uses q then p. The two possible
representatives have different quarter-point values, even though these
real-line classes themselves are trivial. Quotient commutativity cannot
hide a mistaken representative convention in this test.
-/
theorem representative_product_uses_second_then_first :
    ∃ p q : GenLoop (Fin 1) ℝ (0 : ℝ),
      HomotopyGroup.mk p * HomotopyGroup.mk q =
        HomotopyGroup.mk (GenLoop.transAt (0 : Fin 1) q p) ∧
      GenLoop.transAt (0 : Fin 1) q p
          (fun _ => (⟨1 / 4, by constructor <;> norm_num⟩ : unitInterval)) = 1 / 2 ∧
      GenLoop.transAt (0 : Fin 1) p q
          (fun _ => (⟨1 / 4, by constructor <;> norm_num⟩ : unitInterval)) = 1 / 4 ∧
      GenLoop.transAt (0 : Fin 1) q p
          (fun _ => (⟨1 / 4, by constructor <;> norm_num⟩ : unitInterval)) ≠
        GenLoop.transAt (0 : Fin 1) p q
          (fun _ => (⟨1 / 4, by constructor <;> norm_num⟩ : unitInterval)) := by
  refine ⟨firstExcursion, secondExcursion,
    HomotopyGroup.mul_mk (0 : Fin 1) firstExcursion secondExcursion,
    second_then_first_at_quarter, first_then_second_at_quarter, ?_⟩
  intro h
  have hHalfQuarter : (1 / 2 : ℝ) = 1 / 4 :=
    second_then_first_at_quarter.symm.trans (h.trans first_then_second_at_quarter)
  norm_num at hHalfQuarter

/-- The canonical native cube operation also observes the q-then-p order
before quotienting or root transport, with raw boundary point 1. -/
private theorem shifted_native_concat_order :
    let c : GenLoop (Fin 1) ℝ (0 : ℝ) := GenLoop.const
    CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace 1
        (GenLoop.transAt 0 secondExcursion firstExcursion) (GenLoop.transAt 0 c c) =
      GenLoop.transAt 0
        (CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace 1 secondExcursion c)
        (CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace 1 firstExcursion c) ∧
      CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace 1
          (GenLoop.transAt 0 secondExcursion firstExcursion)
          (GenLoop.transAt 0 c c) quarterCube = (3 / 2 : ℝ) ∧
      CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace 1
          (GenLoop.transAt 0 firstExcursion secondExcursion)
          (GenLoop.transAt 0 c c) quarterCube = (5 / 4 : ℝ) := by
  let c : GenLoop (Fin 1) ℝ (0 : ℝ) := GenLoop.const
  have hConst : GenLoop.transAt (0 : Fin 1) c c quarterCube = (0 : ℝ) := by
    change (if (quarterCube 0 : ℝ) ≤ 1 / 2 then (0 : ℝ) else 0) = 0
    exact ite_eq_left quarter_cut
  have hQP :
      CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace 1
          (GenLoop.transAt 0 secondExcursion firstExcursion)
          (GenLoop.transAt 0 c c) quarterCube = (3 / 2 : ℝ) :=
    (CGWH.WeakHSpaceData.rawCubeMul_apply shiftedWeakHSpace 1
      (GenLoop.transAt 0 secondExcursion firstExcursion)
      (GenLoop.transAt 0 c c) quarterCube).trans
      ((shiftedMul_prodPoint
        (GenLoop.transAt 0 secondExcursion firstExcursion quarterCube)
        (GenLoop.transAt 0 c c quarterCube)).trans
        ((congrArg₂ (fun x y : ℝ => x + y + 1)
          second_then_first_at_quarter hConst).trans (by norm_num)))
  have hPQ :
      CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace 1
          (GenLoop.transAt 0 firstExcursion secondExcursion)
          (GenLoop.transAt 0 c c) quarterCube = (5 / 4 : ℝ) :=
    (CGWH.WeakHSpaceData.rawCubeMul_apply shiftedWeakHSpace 1
      (GenLoop.transAt 0 firstExcursion secondExcursion)
      (GenLoop.transAt 0 c c) quarterCube).trans
      ((shiftedMul_prodPoint
        (GenLoop.transAt 0 firstExcursion secondExcursion quarterCube)
        (GenLoop.transAt 0 c c quarterCube)).trans
        ((congrArg₂ (fun x y : ℝ => x + y + 1)
          first_then_second_at_quarter hConst).trans (by norm_num)))
  exact ⟨CGWH.WeakHSpaceData.rawCubeMul_transAt shiftedWeakHSpace 1 (0 : Fin 1)
      secondExcursion firstExcursion c c, hQP, hPQ⟩

private def shrinkExcursion (p : GenLoop (Fin 1) ℝ (0 : ℝ)) :
    p.val.HomotopyRel
      (GenLoop.const : GenLoop (Fin 1) ℝ (0 : ℝ)).val (Cube.boundary (Fin 1)) where
  toFun tx := (1 - (tx.1 : ℝ)) * p tx.2
  continuous_toFun :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (p.val.continuous.comp continuous_snd)
  map_zero_left t := by
    change (1 - (0 : ℝ)) * p t = p t
    simp only [sub_zero, one_mul]
  map_one_left t := by
    change (1 - (1 : ℝ)) * p t = 0
    simp only [sub_self, zero_mul]
  prop' s t ht := by
    change (1 - (s : ℝ)) * p t = p t
    rw [GenLoop.boundary p t ht, mul_zero]

/-!
Case 5: multiplying genuinely changing relative cube homotopies fixes
the entire boundary at the raw product point 1 at every homotopy time.
-/
private theorem shifted_relative_boundary (s : unitInterval) (t : Fin 1 → unitInterval)
    (ht : t ∈ Cube.boundary (Fin 1)) :
    CGWH.WeakHSpaceData.rawCubeMulHomotopy shiftedWeakHSpace 1
        (shrinkExcursion firstExcursion) (shrinkExcursion secondExcursion) (s, t) =
      (1 : ℝ) := by
  let M := CGWH.WeakHSpaceData.rawCubeMulHomotopy shiftedWeakHSpace 1
    (shrinkExcursion firstExcursion) (shrinkExcursion secondExcursion)
  have hFix :
      M (s, t) =
        CGWH.WeakHSpaceData.rawCubeMul shiftedWeakHSpace 1
          firstExcursion secondExcursion t := M.eq_fst s ht
  exact hFix.trans (shifted_raw_boundary 0 firstExcursion secondExcursion t ht)

end RepresentativeOrder

section TwoPointNegativeControl

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩
local instance : TopologicalSpace PUnit := ⊥

private theorem bool_cube_const (n : ℕ) (b : Bool)
    (p : GenLoop (Fin (n + 1)) Bool b) :
    p = (GenLoop.const : GenLoop (Fin (n + 1)) Bool b) := by
  apply GenLoop.ext
  intro t
  have hLoc : IsLocallyConstant (fun z : Fin (n + 1) → unitInterval => p z) :=
    (IsLocallyConstant.iff_continuous _).mpr p.val.continuous
  have hAtZero : p t = p (fun _ => 0) :=
    hLoc.apply_eq_of_preconnectedSpace t (fun _ => 0)
  exact hAtZero.trans
    (GenLoop.boundary p (fun _ => 0) ⟨(0 : Fin (n + 1)), Or.inl rfl⟩)

private theorem bool_positive_groups (n : ℕ) (b : Bool) :
    Subsingleton (HomotopyGroup.Pi (n + 1) Bool b) := by
  constructor
  intro a c
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  obtain ⟨q, rfl⟩ := HomotopyGroup.mk_surjective c
  exact congrArg HomotopyGroup.mk
    ((bool_cube_const n b p).trans (bool_cube_const n b q).symm)

private theorem bool_not_joined :
    ¬ Joined (false : Bool) true := by
  rintro ⟨p⟩
  have hLoc : IsLocallyConstant (fun t : unitInterval => p t) :=
    (IsLocallyConstant.iff_continuous _).mpr p.continuous
  have hEnds : p (0 : unitInterval) = p 1 :=
    hLoc.apply_eq_of_preconnectedSpace 0 1
  have hFalseTrue : (false : Bool) = true :=
    p.source.symm.trans (hEnds.trans p.target)
  cases hFalseTrue

private theorem bool_not_pathConnected : ¬ PathConnectedSpace Bool := by
  intro h
  exact bool_not_joined (h.joined false true)

/-- The actual map to a point fails on connected components. -/
private theorem bool_to_point_not_weak :
    ¬ TopCat.weakHomotopyEquivalences
      (TopCat.ofHom (ContinuousMap.const Bool PUnit.unit) :
        TopCat.of Bool ⟶ TopCat.of PUnit) := by
  intro hf
  let X : TopCat.{0} := TopCat.of Bool
  let Z : TopCat.{0} := TopCat.of PUnit
  let f : X ⟶ Z := TopCat.ofHom (ContinuousMap.const Bool PUnit.unit)
  let s := TopCat.toSSet.map f
  have hW : SSet.KanComplex.W s :=
    (TopCat.mem_weakHomotopyEquivalences_iff f).mp hf
  have hInjective : Function.Injective (SSet.mapπ₀ s) := hW.bijective_mapπ₀.1
  let v₀ : (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm false
  let v₁ : (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm true
  have hVertices : s.app _ v₀ = s.app _ v₁ := by
    apply (TopCat.toSSetObj₀Equiv (X := Z)).injective
    exact Subsingleton.elim _ _
  have hImages : SSet.mapπ₀ s (SSet.π₀.mk v₀) = SSet.mapπ₀ s (SSet.π₀.mk v₁) :=
    (SSet.mapπ₀_mk s v₀).trans
      ((congrArg SSet.π₀.mk hVertices).trans (SSet.mapπ₀_mk s v₁).symm)
  have hComponents : SSet.π₀.mk v₀ = SSet.π₀.mk v₁ := hInjective hImages
  have hZeroth : ZerothHomotopy.mk (false : Bool) = ZerothHomotopy.mk true := by
    apply (TopCat.zerothHomotopyEquiv (X := X)).injective
    exact hComponents
  exact bool_not_joined (_root_.Quotient.exact hZeroth)

/-!
Case 6 is the negative control for the singleton-target criterion.
It derives all positive groups of both components as subsingletons and
disproves the component premise. No connectedness or weak equivalence
witness is supplied for this disconnected source; its literal map to a
point is proved not to be a weak equivalence by failure of π0 injectivity.
-/
theorem disconnected_positive_groups_do_not_make_conull_weak :
    (∀ (n : ℕ) (b : Bool), Subsingleton (HomotopyGroup.Pi (n + 1) Bool b)) ∧
      ¬ PathConnectedSpace Bool ∧
      ¬ TopCat.weakHomotopyEquivalences
        (TopCat.ofHom (ContinuousMap.const Bool PUnit.unit) :
          TopCat.of Bool ⟶ TopCat.of PUnit) :=
  ⟨bool_positive_groups, bool_not_pathConnected, bool_to_point_not_weak⟩

end TwoPointNegativeControl

section SingletonPositiveControl

private theorem group_subsingleton_of_points {X : Type uTest} [TopologicalSpace X]
    (hX : Subsingleton X) (n : ℕ) (x : X) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) := by
  constructor
  intro a b
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  obtain ⟨q, rfl⟩ := HomotopyGroup.mk_surjective b
  exact congrArg HomotopyGroup.mk
    (GenLoop.ext p q (fun t => hX.elim (p t) (q t)))

/-!
Case 7 contrasts the two-point source with the actual realized terminal
simplicial set. Its singleton carrier and inhabitedness are derived from
the zero-simplex Iso; those witnesses are then consumed by the public
component-plus-positive-group criterion.
-/
theorem realized_terminal_has_component_and_positive_groups :
    SSet.realizationWeakEquivalences
      (terminal.from (⊤_ SSet.{uTest})) := by
  let K : SSet.{uTest} := ⊤_ SSet.{uTest}
  let Z : TopCat.{uTest} := SSet.toTop.obj K
  have hZ : Subsingleton Z := SSet.realizedTerminal_subsingleton.{uTest}
  let d : (Δ[0] : SSet.{uTest}) ≅ K :=
    SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso terminalIsTerminal
  have hNonempty : Nonempty Z :=
    ⟨SSet.toTop.map d.hom (default : SSet.toTop.obj (Δ[0] : SSet.{uTest}))⟩
  have hConn : PathConnectedSpace Z := by
    refine ⟨hNonempty, ?_⟩
    intro x y
    have hxy : x = y := hZ.elim x y
    subst y
    exact ⟨Path.refl x⟩
  have hPositive : ∀ (n : ℕ) (x : Z), Subsingleton (HomotopyGroup.Pi (n + 1) Z x) :=
    fun n x => group_subsingleton_of_points hZ n x
  exact SSet.conull_mem_realizationWeakEquivalences_of_pathConnected_positive.{uTest}
    K hConn hPositive

end SingletonPositiveControl

section InverseEdgeOrientation

/-- A two-object groupoid test fixture; it is not substituted into any application. -/
local instance : Category.{0} Bool where
  Hom _ _ := PUnit.{1}
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp := by intros; apply Subsingleton.elim
  comp_id := by intros; apply Subsingleton.elim
  assoc := by intros; apply Subsingleton.elim

private def twoObjectIso : (false : Bool) ≅ true where
  hom := PUnit.unit
  inv := PUnit.unit
  hom_inv_id := by
    change (PUnit.unit : PUnit.{1}) = PUnit.unit
    rfl
  inv_hom_id := by
    change (PUnit.unit : PUnit.{1}) = PUnit.unit
    rfl

/-!
Case 8 uses distinct categorical endpoints and consumes the new public
nerve/realization inverse-edge theorem, rather than replacing the Iso
by an identity edge at a single object.
-/
private theorem inverse_edge_has_correct_endpoints :
    let p : Path.{0}
        (SSet.realizedVertex (X := (nerve Bool : SSet.{0}))
          ((nerveEquiv.{0, 0} (C := Bool)).symm true))
        (SSet.realizedVertex (X := (nerve Bool : SSet.{0}))
          ((nerveEquiv.{0, 0} (C := Bool)).symm false)) :=
      TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk twoObjectIso.inv))
    let q : Path.{0}
        (SSet.realizedVertex (X := (nerve Bool : SSet.{0}))
          ((nerveEquiv.{0, 0} (C := Bool)).symm false))
        (SSet.realizedVertex (X := (nerve Bool : SSet.{0}))
          ((nerveEquiv.{0, 0} (C := Bool)).symm true)) :=
      TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk twoObjectIso.hom))
    (false : Bool) ≠ true ∧
      p 0 = SSet.realizedVertex (X := nerve Bool) (nerveEquiv.symm true) ∧
      p 1 = SSet.realizedVertex (X := nerve Bool) (nerveEquiv.symm false) ∧
      p.Homotopic q.symm := by
  let p : Path.{0}
      (SSet.realizedVertex (X := (nerve Bool : SSet.{0}))
        ((nerveEquiv.{0, 0} (C := Bool)).symm true))
      (SSet.realizedVertex (X := (nerve Bool : SSet.{0}))
        ((nerveEquiv.{0, 0} (C := Bool)).symm false)) :=
    TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk twoObjectIso.inv))
  let q : Path.{0}
      (SSet.realizedVertex (X := (nerve Bool : SSet.{0}))
        ((nerveEquiv.{0, 0} (C := Bool)).symm false))
      (SSet.realizedVertex (X := (nerve Bool : SSet.{0}))
        ((nerveEquiv.{0, 0} (C := Bool)).symm true)) :=
    TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk twoObjectIso.hom))
  exact ⟨by decide, p.source, p.target, CategoryTheory.realizedIso_inv_path twoObjectIso⟩

end InverseEdgeOrientation

section PublicIndependentUniverses

variable {Y : CGWH.{wTest, kTest}} (H : CGWH.WeakHSpaceData Y)

/-!
Case 9 is an imported public-API check with independent compact-probe and
carrier universes. It supplies only ordinary weak-unit data, not a desired
positive-group or weak-equivalence conclusion.
-/
theorem independent_probe_and_carrier_unital_interchange
    (n : ℕ) (a b c d : HomotopyGroup.Pi (n + 1) Y H.e) :
    CGWH.WeakHSpaceData.cubeMul H n (a * b) (c * d) =
        CGWH.WeakHSpaceData.cubeMul H n a c * CGWH.WeakHSpaceData.cubeMul H n b d ∧
      CGWH.WeakHSpaceData.cubeMul H n 1 a = a ∧
      CGWH.WeakHSpaceData.cubeMul H n a 1 = a ∧
      a * b = b * a :=
  ⟨CGWH.WeakHSpaceData.cubeMul_interchange H n a b c d,
    CGWH.WeakHSpaceData.cubeMul_one_left H n a,
    CGWH.WeakHSpaceData.cubeMul_one_right H n a,
    CGWH.WeakHSpaceData.positiveGroup_mul_comm H n a b⟩

theorem independent_probe_and_carrier_diagonal_triviality
    (J : ContinuousMap.Homotopy (ContinuousMap.id Y)
      (CGWH.cgwhToTop.{wTest, kTest}.map
        (CGWH.WeakHSpaceData.nativeDoubling H)).hom)
    (hTrace : ((J.evalAt H.e).cast rfl
      (CGWH.WeakHSpaceData.nativeDoubling_unit H).symm).Homotopic H.rootPath.symm)
    (n : ℕ) (a : HomotopyGroup.Pi (n + 1) Y H.e) :
    a = 1 :=
  CGWH.WeakHSpaceData.positiveGroup_eq_one H J hTrace n a

theorem independent_universes_iso_transports_positive_groups
    (n : ℕ) {A B : TopCat.{kTest}} (d : A ≅ B)
    (hA : ∀ x : A, Subsingleton (HomotopyGroup.Pi (n + 1) A x)) (b : B) :
    Subsingleton (HomotopyGroup.Pi (n + 1) B b) :=
  TopCat.positiveGroup_subsingleton_of_iso n d hA b

theorem independent_universes_inverse_edge_reverses_path
    {D : Type uTest} [Category.{vTest} D] {x y : D} (e : x ≅ y) :
    (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk e.inv))).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk e.hom))).symm :=
  CategoryTheory.realizedIso_inv_path e

end PublicIndependentUniverses

end CanonicalGenericTopologyConsumers

end
