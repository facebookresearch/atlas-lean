/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatRightProper
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Strict point fibers and compact-open homotopy fibers

For a selected TopCat fibration, this file compares the strict point fiber
with the compact-open homotopy fiber. Paths with fixed final endpoint
contract by interval-maximum reparameterization. Right properness then makes
the canonical constant-path comparison a weak homotopy equivalence.

No endpoint evaluation is asserted to be a fibration, and no path-lifting,
Hurewicz, Serre, quasifibration, homeomorphism, or uniqueness claim is made.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits Topology HomotopicalAlgebra MorphismProperty
open scoped TopCat.modelCategory

namespace TopCat

/-- The compact-open family of constant paths. -/
def pathConstant (B : TopCat.{u}) : B ⟶ pathObject B :=
  TopCat.ofHom ContinuousMap.const'

/-- A constant path evaluates to its value at time zero. -/
@[reassoc (attr := simp)]
theorem pathConstant_evalZero (B : TopCat.{u}) :
    pathConstant B ≫ pathEvalZero B = 𝟙 B := by
  ext b
  rfl

/-- A constant path evaluates to its value at time one. -/
@[reassoc (attr := simp)]
theorem pathConstant_evalOne (B : TopCat.{u}) :
    pathConstant B ≫ pathEvalOne B = 𝟙 B := by
  ext b
  rfl

/-- The strict point fiber maps to the compact-open homotopy fiber by the
constant path at the selected point. -/
noncomputable def strictFiberToHomotopyFiber
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    pullback p (TopCat.const (X := TopCat.of PUnit) b) ⟶
      homotopyFiber p b :=
  pullback.lift
    (Limits.prod.lift
      (pullback.fst p (TopCat.const b))
      (pullback.snd p (TopCat.const b)))
    (pullback.snd p (TopCat.const b) ≫
      TopCat.const b ≫ pathConstant B)
    (by
      apply Limits.prod.hom_ext
      · simpa [pathEndpoints, Category.assoc] using
          (pullback.condition :
            pullback.fst p (TopCat.const b) ≫ p =
              pullback.snd p (TopCat.const b) ≫ TopCat.const b)
      · simp [pathEndpoints, Category.assoc])

/-- The strict-to-homotopy-fiber comparison retains the total-space point. -/
@[reassoc (attr := simp)]
theorem strictFiberToHomotopyFiber_toTotal
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    strictFiberToHomotopyFiber p b ≫ homotopyFiberToTotal p b =
      pullback.fst p (TopCat.const b) := by
  rw [strictFiberToHomotopyFiber, ← Category.assoc, pullback.lift_fst]
  simp

/-- The strict-to-homotopy-fiber comparison carries the constant path at the
selected point. -/
@[reassoc (attr := simp)]
theorem strictFiberToHomotopyFiber_path
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    strictFiberToHomotopyFiber p b ≫ homotopyFiberPath p b =
      pullback.snd p (TopCat.const b) ≫
        TopCat.const b ≫ pathConstant B := by
  rw [strictFiberToHomotopyFiber, pullback.lift_snd]

private abbrev endingPath (B : TopCat.{u}) (b : B) : TopCat.{u} :=
  pullback (pathEvalOne B) (TopCat.const b : TopCat.of PUnit ⟶ B)

private abbrev endingPathPath (B : TopCat.{u}) (b : B) :
    endingPath B b ⟶ pathObject B :=
  pullback.fst (pathEvalOne B) (TopCat.const b)

private abbrev endingPathUnit (B : TopCat.{u}) (b : B) :
    endingPath B b ⟶ TopCat.of PUnit :=
  pullback.snd (pathEvalOne B) (TopCat.const b)

private abbrev endingPathEvalZero (B : TopCat.{u}) (b : B) :
    endingPath B b ⟶ B :=
  endingPathPath B b ≫ pathEvalZero B

@[reassoc]
private theorem endingPathPath_evalOne (B : TopCat.{u}) (b : B) :
    endingPathPath B b ≫ pathEvalOne B =
      endingPathUnit B b ≫ TopCat.const b :=
  pullback.condition

private noncomputable def endingPathConstant (B : TopCat.{u}) (b : B) :
    TopCat.of PUnit ⟶ endingPath B b :=
  pullback.lift
    ((TopCat.const b : TopCat.of PUnit ⟶ B) ≫ pathConstant B)
    (𝟙 _)
    (by simp)

@[reassoc (attr := simp)]
private theorem endingPathConstant_path (B : TopCat.{u}) (b : B) :
    endingPathConstant B b ≫ endingPathPath B b =
      (TopCat.const b : TopCat.of PUnit ⟶ B) ≫ pathConstant B := by
  rw [endingPathConstant, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem endingPathConstant_unit (B : TopCat.{u}) (b : B) :
    endingPathConstant B b ≫ endingPathUnit B b = 𝟙 _ := by
  rw [endingPathConstant, pullback.lift_snd]

@[reassoc (attr := simp, nolint simpNF)]
private theorem endingPathConstant_evalZero (B : TopCat.{u}) (b : B) :
    endingPathConstant B b ≫ endingPathEvalZero B b =
      TopCat.const b := by
  simp [endingPathEvalZero]

private def intervalMax :
    C(unitInterval × TopCat.I.{u}, TopCat.I.{u}) where
  toFun z := TopCat.I.homeomorph.symm
    (max z.1 (TopCat.I.homeomorph z.2))
  continuous_toFun := TopCat.I.homeomorph.symm.continuous.comp
    (continuous_fst.max
      (TopCat.I.homeomorph.continuous.comp continuous_snd))

@[simp]
private theorem intervalMax_zero (t : TopCat.I.{u}) :
    intervalMax (0, t) = t := by
  apply TopCat.I.homeomorph.injective
  simp [intervalMax]

@[simp]
private theorem intervalMax_one (t : TopCat.I.{u}) :
    intervalMax (1, t) = 1 := by
  apply TopCat.I.homeomorph.injective
  change max 1 (TopCat.I.homeomorph t) = 1
  exact max_eq_left (TopCat.I.homeomorph t).property.2

@[simp]
private theorem intervalMax_right_one (s : unitInterval) :
    intervalMax (s, (1 : TopCat.I.{u})) = 1 := by
  apply TopCat.I.homeomorph.injective
  change max s 1 = 1
  exact max_eq_right s.property.2

private noncomputable def endingPathContractionPath
    (B : TopCat.{u}) (b : B) :
    TopCat.of (unitInterval × endingPath B b) ⟶ pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z =>
        endingPathPath B b z.1.2 (intervalMax (z.1.1, z.2))
      continuous_toFun := by
        fun_prop }

private theorem endingPathContractionPath_evalOne
    (B : TopCat.{u}) (b : B) :
    endingPathContractionPath B b ≫ pathEvalOne B =
      TopCat.const b := by
  ext z
  change endingPathPath B b z.2 (intervalMax (z.1, 1)) = b
  rw [intervalMax_right_one]
  have h := ConcreteCategory.congr_hom
    (endingPathPath_evalOne B b) z.2
  simpa [pathEvalOne, TopCat.const] using h

private noncomputable def endingPathContractionMap
    (B : TopCat.{u}) (b : B) :
    TopCat.of (unitInterval × endingPath B b) ⟶ endingPath B b :=
  pullback.lift
    (endingPathContractionPath B b)
    (TopCat.const PUnit.unit)
    (by
      rw [endingPathContractionPath_evalOne]
      ext z
      rfl)

private def endingPathAtTime (B : TopCat.{u}) (b : B)
    (s : unitInterval) :
    endingPath B b ⟶ TopCat.of (unitInterval × endingPath B b) :=
  TopCat.ofHom
    { toFun := fun q => (s, q)
      continuous_toFun := continuous_const.prodMk continuous_id }

private theorem endingPathContractionMap_zero
    (B : TopCat.{u}) (b : B) :
    endingPathAtTime B b 0 ≫ endingPathContractionMap B b = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, endingPathContractionMap,
      pullback.lift_fst, Category.id_comp]
    ext q t
    simp [endingPathAtTime, endingPathContractionPath]
  · apply TopCat.isTerminalPUnit.hom_ext

private theorem endingPathContractionMap_one
    (B : TopCat.{u}) (b : B) :
    endingPathAtTime B b 1 ≫ endingPathContractionMap B b =
      TopCat.isTerminalPUnit.from (endingPath B b) ≫
        endingPathConstant B b := by
  apply pullback.hom_ext
  · rw [Category.assoc, endingPathContractionMap, pullback.lift_fst,
      Category.assoc, endingPathConstant_path]
    ext q t
    change endingPathPath B b q (intervalMax (1, t)) = b
    rw [intervalMax_one]
    have h := ConcreteCategory.congr_hom
      (endingPathPath_evalOne B b) q
    simpa [pathEvalOne, TopCat.const] using h
  · apply TopCat.isTerminalPUnit.hom_ext

private noncomputable def endingPathContraction
    (B : TopCat.{u}) (b : B) :
    TopCat.Homotopy (𝟙 (endingPath B b))
      (TopCat.isTerminalPUnit.from (endingPath B b) ≫
        endingPathConstant B b) :=
  ContinuousMap.Homotopy.mk
    (endingPathContractionMap B b).hom
    (fun q => by
      have h := ConcreteCategory.congr_hom
        (endingPathContractionMap_zero B b) q
      simpa [endingPathAtTime] using h)
    (fun q => by
      have h := ConcreteCategory.congr_hom
        (endingPathContractionMap_one B b) q
      simpa [endingPathAtTime] using h)

private noncomputable def endingPathConstantHomotopyEquiv
    (B : TopCat.{u}) (b : B) :
    ContinuousMap.HomotopyEquiv PUnit (endingPath B b) where
  toFun := (endingPathConstant B b).hom
  invFun := (TopCat.isTerminalPUnit.from (endingPath B b)).hom
  left_inv := by
    have h : endingPathConstant B b ≫
        TopCat.isTerminalPUnit.from (endingPath B b) = 𝟙 _ := by
      apply TopCat.isTerminalPUnit.hom_ext
    rw [show (TopCat.isTerminalPUnit.from (endingPath B b)).hom.comp
        (endingPathConstant B b).hom =
      (endingPathConstant B b ≫
        TopCat.isTerminalPUnit.from (endingPath B b)).hom by rfl, h]
    exact ⟨ContinuousMap.Homotopy.refl _⟩
  right_inv := ⟨(endingPathContraction B b).symm⟩

private theorem endingPathConstant_mem_weakHomotopyEquivalences
    (B : TopCat.{u}) (b : B) :
    weakHomotopyEquivalences (endingPathConstant B b) := by
  exact TopCat.homotopyEquiv_toFun_mem
    (endingPathConstantHomotopyEquiv B b)

private noncomputable def homotopyFiberToEndingPath
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    homotopyFiber p b ⟶ endingPath B b :=
  pullback.lift
    (homotopyFiberPath p b)
    (homotopyPullbackRight p (TopCat.const b))
    (homotopyPullbackPath_evalOne p (TopCat.const b))

@[reassoc (attr := simp)]
private theorem homotopyFiberToEndingPath_path
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    homotopyFiberToEndingPath p b ≫ endingPathPath B b =
      homotopyFiberPath p b := by
  rw [homotopyFiberToEndingPath, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem homotopyFiberToEndingPath_unit
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    homotopyFiberToEndingPath p b ≫ endingPathUnit B b =
      homotopyPullbackRight p (TopCat.const b) := by
  rw [homotopyFiberToEndingPath, pullback.lift_snd]

@[reassoc (attr := simp, nolint simpNF)]
private theorem homotopyFiberToEndingPath_evalZero
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    homotopyFiberToEndingPath p b ≫ endingPathEvalZero B b =
      homotopyFiberToTotal p b ≫ p := by
  simp [endingPathEvalZero, Category.assoc,
    homotopyPullbackPath_evalZero]

private theorem homotopyFiber_isPullback_endingPath
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    IsPullback (homotopyFiberToTotal p b)
      (homotopyFiberToEndingPath p b) p (endingPathEvalZero B b) := by
  have hw := (homotopyFiberToEndingPath_evalZero p b).symm
  refine { w := hw, isLimit' := ?_ }
  refine ⟨PullbackCone.IsLimit.mk
    (homotopyFiberToEndingPath_evalZero p b).symm
    (fun s => pullback.lift
      (Limits.prod.lift s.fst (s.snd ≫ endingPathUnit B b))
      (s.snd ≫ endingPathPath B b) ?_)
    (fun s => by
      rw [← Category.assoc, pullback.lift_fst]
      simp)
    (fun s => by
      apply pullback.hom_ext
      · rw [Category.assoc, homotopyFiberToEndingPath_path,
          pullback.lift_snd]
      · rw [Category.assoc, homotopyFiberToEndingPath_unit,
          ← Category.assoc, pullback.lift_fst]
        simp)
    (fun s m h₁ h₂ => by
      apply homotopyPullback_hom_ext
      · rw [h₁]
        symm
        rw [← Category.assoc, pullback.lift_fst]
        simp
      · have h := congrArg (fun k => k ≫ endingPathUnit B b) h₂
        calc
          m ≫ homotopyPullbackRight p (TopCat.const b) =
              (m ≫ homotopyFiberToEndingPath p b) ≫
                endingPathUnit B b := by
            rw [Category.assoc, homotopyFiberToEndingPath_unit]
          _ = s.snd ≫ endingPathUnit B b := h
          _ = pullback.lift
                (Limits.prod.lift s.fst
                  (s.snd ≫ endingPathUnit B b))
                (s.snd ≫ endingPathPath B b) _ ≫
              homotopyPullbackRight p (TopCat.const b) := by
            rw [← Category.assoc, pullback.lift_fst]
            simp
      · have h := congrArg (fun k => k ≫ endingPathPath B b) h₂
        calc
          m ≫ homotopyFiberPath p b =
              (m ≫ homotopyFiberToEndingPath p b) ≫
                endingPathPath B b := by
            rw [Category.assoc, homotopyFiberToEndingPath_path]
          _ = s.snd ≫ endingPathPath B b := h
          _ = pullback.lift
                (Limits.prod.lift s.fst
                  (s.snd ≫ endingPathUnit B b))
                (s.snd ≫ endingPathPath B b) _ ≫
              homotopyFiberPath p b := by
            rw [pullback.lift_snd])⟩
  apply Limits.prod.hom_ext
  · simpa [pathEndpoints, endingPathEvalZero, Category.assoc]
      using s.condition
  · simp [pathEndpoints, Category.assoc, endingPathPath_evalOne]

private theorem strictFiber_comparison_isPullback
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    IsPullback (strictFiberToHomotopyFiber p b)
      (pullback.snd p (TopCat.const b))
      (homotopyFiberToEndingPath p b) (endingPathConstant B b) := by
  have hright := homotopyFiber_isPullback_endingPath p b
  have houter : IsPullback
      (strictFiberToHomotopyFiber p b ≫ homotopyFiberToTotal p b)
      (pullback.snd p (TopCat.const b)) p
      (endingPathConstant B b ≫ endingPathEvalZero B b) := by
    simpa using IsPullback.of_hasPullback p (TopCat.const b)
  apply houter.of_right
  · apply pullback.hom_ext
    · simp [Category.assoc]
    · apply TopCat.isTerminalPUnit.hom_ext
  · exact hright

/-- For a selected TopCat fibration, the strict point fiber maps weakly
equivalently to the compact-open homotopy fiber. -/
theorem strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences
    {E B : TopCat.{u}} (p : E ⟶ B) (b : B) [Fibration p] :
    weakHomotopyEquivalences (strictFiberToHomotopyFiber p b) := by
  let q := homotopyFiberToEndingPath p b
  let k := endingPathConstant B b
  let hq : IsPullback (homotopyFiberToTotal p b) q p
      (endingPathEvalZero B b) :=
    homotopyFiber_isPullback_endingPath p b
  let hk : IsPullback (strictFiberToHomotopyFiber p b)
      (pullback.snd p (TopCat.const b)) q k :=
    strictFiber_comparison_isPullback p b
  let _ : Fibration q := (fibration_iff q).2
    (MorphismProperty.of_isPullback hq
      ((fibration_iff p).1 (inferInstance : Fibration p)))
  let _ : WeakEquivalence k := (weakEquivalence_iff k).2
    (endingPathConstant_mem_weakHomotopyEquivalences B b)
  let _ : IsRightProper TopCat.{u} := TopCat.modelCategory.rightProper
  let hstd := IsPullback.of_hasPullback q k
  let _ : WeakEquivalence (pullback.fst q k) :=
    IsRightProper.weakEquivalence_of_isPullback hstd.flip
  let e := hk.isoIsPullback (homotopyFiber p b) (TopCat.of PUnit) hstd
  have he : WeakEquivalence (e.hom ≫ pullback.fst q k) := inferInstance
  have hj : WeakEquivalence (strictFiberToHomotopyFiber p b) := by
    rw [hk.isoIsPullback_hom_fst
      (homotopyFiber p b) (TopCat.of PUnit) hstd] at he
    exact he
  exact (weakEquivalence_iff _).1 hj

end TopCat
