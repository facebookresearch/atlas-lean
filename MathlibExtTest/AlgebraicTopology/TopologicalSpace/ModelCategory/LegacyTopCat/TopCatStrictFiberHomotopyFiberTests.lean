/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatStrictFiberHomotopyFiber

/-!
# Strict-fiber to homotopy-fiber comparison tests

These clients pin the comparison orientation, conditional weak theorem,
universe polymorphism, and the opposite-endpoint strict-pullback falsifier.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped TopCat.modelCategory

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory

variable {E B : TopCat.{u}} (p : E ⟶ B) (b : B)

example : B ⟶ TopCat.pathObject B := TopCat.pathConstant B

example : TopCat.pathConstant B ≫ TopCat.pathEvalZero B = 𝟙 B :=
  TopCat.pathConstant_evalZero B

example : TopCat.pathConstant B ≫ TopCat.pathEvalOne B = 𝟙 B :=
  TopCat.pathConstant_evalOne B

example : pullback p (TopCat.const (X := TopCat.of PUnit) b) ⟶
    TopCat.homotopyFiber p b :=
  TopCat.strictFiberToHomotopyFiber p b

example : TopCat.strictFiberToHomotopyFiber p b ≫
      TopCat.homotopyFiberToTotal p b =
    pullback.fst p (TopCat.const b) :=
  TopCat.strictFiberToHomotopyFiber_toTotal p b

example : TopCat.strictFiberToHomotopyFiber p b ≫
      TopCat.homotopyFiberPath p b =
    pullback.snd p (TopCat.const b) ≫
      TopCat.const b ≫ TopCat.pathConstant B :=
  TopCat.strictFiberToHomotopyFiber_path p b

example : TopCat.strictFiberToHomotopyFiber p b ≫
      TopCat.homotopyFiberPath p b ≫ TopCat.pathEvalZero B =
    pullback.fst p (TopCat.const b) ≫ p := by
  simp [pullback.condition]

example : TopCat.strictFiberToHomotopyFiber p b ≫
      TopCat.homotopyFiberPath p b ≫ TopCat.pathEvalOne B =
    pullback.snd p (TopCat.const b) ≫ TopCat.const b := by
  simp

example [Fibration p] : TopCat.weakHomotopyEquivalences
    (TopCat.strictFiberToHomotopyFiber p b) :=
  TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences p b

example (X : TopCat.{u}) (x : X) : TopCat.weakHomotopyEquivalences
    (TopCat.strictFiberToHomotopyFiber (𝟙 X) x) :=
  TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences (𝟙 X) x

example : TopCat.weakHomotopyEquivalences
    (TopCat.strictFiberToHomotopyFiber
      (𝟙 (TopCat.of PUnit.{u + 1})) PUnit.unit) :=
  TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences
    (𝟙 (TopCat.of PUnit.{u + 1})) PUnit.unit

section UniverseOne

variable {E₁ B₁ : TopCat.{1}} (p₁ : E₁ ⟶ B₁) (b₁ : B₁)

example : B₁ ⟶ TopCat.pathObject B₁ := TopCat.pathConstant B₁

example : TopCat.pathConstant B₁ ≫ TopCat.pathEvalZero B₁ = 𝟙 B₁ :=
  TopCat.pathConstant_evalZero B₁

example : TopCat.pathConstant B₁ ≫ TopCat.pathEvalOne B₁ = 𝟙 B₁ :=
  TopCat.pathConstant_evalOne B₁

example : pullback p₁ (TopCat.const (X := TopCat.of PUnit) b₁) ⟶
    TopCat.homotopyFiber p₁ b₁ :=
  TopCat.strictFiberToHomotopyFiber p₁ b₁

example : TopCat.strictFiberToHomotopyFiber p₁ b₁ ≫
      TopCat.homotopyFiberToTotal p₁ b₁ =
    pullback.fst p₁ (TopCat.const b₁) :=
  TopCat.strictFiberToHomotopyFiber_toTotal p₁ b₁

example : TopCat.strictFiberToHomotopyFiber p₁ b₁ ≫
      TopCat.homotopyFiberPath p₁ b₁ =
    pullback.snd p₁ (TopCat.const b₁) ≫
      TopCat.const b₁ ≫ TopCat.pathConstant B₁ :=
  TopCat.strictFiberToHomotopyFiber_path p₁ b₁

example [Fibration p₁] : TopCat.weakHomotopyEquivalences
    (TopCat.strictFiberToHomotopyFiber p₁ b₁) :=
  TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences p₁ b₁

end UniverseOne

section UniverseZero

variable {E₀ B₀ : TopCat.{0}} (p₀ : E₀ ⟶ B₀) (b₀ : B₀)

example : B₀ ⟶ TopCat.pathObject B₀ := TopCat.pathConstant B₀

example : TopCat.pathConstant B₀ ≫ TopCat.pathEvalZero B₀ = 𝟙 B₀ :=
  TopCat.pathConstant_evalZero B₀

example : TopCat.pathConstant B₀ ≫ TopCat.pathEvalOne B₀ = 𝟙 B₀ :=
  TopCat.pathConstant_evalOne B₀

example : pullback p₀ (TopCat.const (X := TopCat.of PUnit) b₀) ⟶
    TopCat.homotopyFiber p₀ b₀ :=
  TopCat.strictFiberToHomotopyFiber p₀ b₀

example : TopCat.strictFiberToHomotopyFiber p₀ b₀ ≫
      TopCat.homotopyFiberToTotal p₀ b₀ =
    pullback.fst p₀ (TopCat.const b₀) :=
  TopCat.strictFiberToHomotopyFiber_toTotal p₀ b₀

example : TopCat.strictFiberToHomotopyFiber p₀ b₀ ≫
      TopCat.homotopyFiberPath p₀ b₀ =
    pullback.snd p₀ (TopCat.const b₀) ≫
      TopCat.const b₀ ≫ TopCat.pathConstant B₀ :=
  TopCat.strictFiberToHomotopyFiber_path p₀ b₀

example [Fibration p₀] : TopCat.weakHomotopyEquivalences
    (TopCat.strictFiberToHomotopyFiber p₀ b₀) :=
  TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences p₀ b₀

end UniverseZero

section OppositeEndpoints

private def intervalZero : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u} :=
  TopCat.const 0

private def intervalOne : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u} :=
  TopCat.const 1

example : IsEmpty ↑(pullback intervalZero.{u} intervalOne.{u} : TopCat.{u}) := by
  constructor
  intro z
  have h := ConcreteCategory.congr_hom
    (pullback.condition :
      pullback.fst intervalZero.{u} intervalOne.{u} ≫ intervalZero.{u} =
        pullback.snd intervalZero.{u} intervalOne.{u} ≫ intervalOne.{u}) z
  change (0 : TopCat.I.{u}) = 1 at h
  have hreal : (0 : ℝ) = 1 :=
    congrArg (fun t : TopCat.I.{u} =>
      ((TopCat.I.homeomorph t : unitInterval) : ℝ)) h
  exact zero_ne_one hreal

example : Nonempty (TopCat.homotopyFiber intervalZero.{u} (1 : TopCat.I.{u})) := by
  let q : TopCat.of PUnit.{u + 1} ⟶
      TopCat.homotopyFiber intervalZero.{u} (1 : TopCat.I.{u}) :=
    pullback.lift
      (Limits.prod.lift (𝟙 _) (𝟙 _))
      (TopCat.const (ContinuousMap.id TopCat.I.{u}))
      (by
        apply Limits.prod.hom_ext
        · simp [TopCat.pathEndpoints]
          apply ConcreteCategory.hom_ext
          intro z
          rfl
        · simp [TopCat.pathEndpoints]
          apply ConcreteCategory.hom_ext
          intro z
          rfl)
  exact ⟨q PUnit.unit⟩

example : pullback intervalZero.{u} intervalOne.{u} ⟶
    TopCat.homotopyFiber intervalZero.{u} (1 : TopCat.I.{u}) :=
  TopCat.strictFiberToHomotopyFiber intervalZero.{u} 1

example : True := by
  fail_if_success
    have _ : Fibration intervalZero.{u} := inferInstance
  fail_if_success
    exact TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences
      intervalZero.{u} (1 : TopCat.I.{u})
  trivial

end OppositeEndpoints

section Falsifiers

example : True := by
  fail_if_success
    exact TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences p b
  fail_if_success
    let _ : Fibration (TopCat.pathEvalZero B) := inferInstance
  fail_if_success
    let _ : Fibration (TopCat.pathEvalOne B) := inferInstance
  fail_if_success
    let _ := TopCat.strictFiberToHomotopyFiber_homeomorph
  fail_if_success
    let _ := TopCat.strictFiberToHomotopyFiber_isHomeomorph
  fail_if_success
    let _ := TopCat.strictFiberToHomotopyFiber_unique
  fail_if_success
    let _ := TopCat.strictFiberToHomotopyFiber_quasifibration
  fail_if_success
    let _ := TopCat.PathLiftingData
  fail_if_success
    let _ := TopCat.HurewiczFibration
  fail_if_success
    let _ := TopCat.SerreFibration
  fail_if_success
    let _ := TopCat.strictFiberRealizationComparison
  fail_if_success
    let _ := TopCat.bkStrictFiberComparison
  trivial

end Falsifiers

#print axioms TopCat.pathConstant
#print axioms TopCat.pathConstant_evalZero
#print axioms TopCat.pathConstant_evalOne
#print axioms TopCat.strictFiberToHomotopyFiber
#print axioms TopCat.strictFiberToHomotopyFiber_toTotal
#print axioms TopCat.strictFiberToHomotopyFiber_path
#print axioms TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences

end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
