/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.TorScalarChangeHeight
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# Tor composition and height under nonflat residue restriction

Restriction along ℤ → ℤ/5 sends a free right-ℤ/5 module to a nonflat,
nonprojective integer module. The ring-change map has zero positive-degree
target because the target input is projective over ℤ/5.
The factorization ℤ→ℤ/25→ℤ/5 gives composition and height comparisons
before the terminal projective target.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits MulOpposite
open ModuleCat.BalancedTensorRight ModuleCat.Bimodule.Tensor
open scoped TensorProduct

namespace MathlibExtTest.Bimodule.TorScalarChangeRingMapCoherence

abbrev F5 := ZMod 5
def reduction : ℤ →+* F5 := Int.castRingHom F5

local instance : Module ℤ F5 := AddCommGroup.toIntModule F5
local instance : SMulCommClass F5ᵐᵒᵖ ℤ F5 := Module.intModule_smulCommClass
local instance : SMulCommClass ℤ F5ᵐᵒᵖ F5 := SMulCommClass.symm _ _ _

local instance sourceCoefficientEnveloping : Module (ℤ ⊗[ℤ] F5ᵐᵒᵖ) F5 :=
  ModuleCat.Bimodule.RingChange.moduleOfActions ℤ F5 F5

abbrev sourceCoefficient : coefficientCategory.{0, 0, 0} ℤ F5 :=
  letI := ModuleCat.Bimodule.RingChange.moduleOfActions ℤ F5 F5
  ModuleCat.of (ℤ ⊗[ℤ] F5ᵐᵒᵖ) F5

local instance targetCoefficientEnveloping : Module (F5 ⊗[ℤ] F5ᵐᵒᵖ) F5 :=
  ModuleCat.Bimodule.RingChange.moduleOfActions F5 F5 F5

abbrev targetCoefficient : coefficientCategory.{0, 0, 0} F5 F5 :=
  letI := ModuleCat.Bimodule.RingChange.moduleOfActions F5 F5 F5
  ModuleCat.of (F5 ⊗[ℤ] F5ᵐᵒᵖ) F5

/-- The coefficient identity uses the actual integer-to-residue scalar law. -/
def coefficientIdentity :
    sourceCoefficient →ₛₗ[ModuleCat.Bimodule.RingChange.envelopingRingHom reduction
      (RingHom.id F5)] targetCoefficient := by
  refine ModuleCat.Bimodule.RingChange.ofSemilinearMap reduction (RingHom.id F5)
    sourceCoefficient targetCoefficient (AddMonoidHom.id F5) ?_ ?_
  · intro z x
    change (ModuleCat.Bimodule.RingChange.leftModule ℤ F5
        (ModuleCat.Bimodule.RingChange.ofActions ℤ F5 F5)).smul z x =
      (ModuleCat.Bimodule.RingChange.leftModule F5 F5
        (ModuleCat.Bimodule.RingChange.ofActions F5 F5 F5)).smul (reduction z) x
    rw [ModuleCat.Bimodule.RingChange.ofActions_leftModule ℤ F5 F5,
      ModuleCat.Bimodule.RingChange.ofActions_leftModule F5 F5 F5]
    exact (Int.cast_smul_eq_zsmul F5 z x).symm
  · intro s x
    change (ModuleCat.Bimodule.RingChange.rightModule ℤ F5
        (ModuleCat.Bimodule.RingChange.ofActions ℤ F5 F5)).smul s x =
      (ModuleCat.Bimodule.RingChange.rightModule F5 F5
        (ModuleCat.Bimodule.RingChange.ofActions F5 F5 F5)).smul ((RingHom.id F5).op s) x
    rw [ModuleCat.Bimodule.RingChange.ofActions_rightModule ℤ F5 F5,
      ModuleCat.Bimodule.RingChange.ofActions_rightModule F5 F5 F5]
    rfl

def coefficientMap : sourceCoefficient ⟶
    (ModuleCat.Bimodule.RingChange.restrictFunctor reduction (RingHom.id F5)).obj
      targetCoefficient :=
  ModuleCat.semilinearMapAddEquiv
    (ModuleCat.Bimodule.RingChange.envelopingRingHom reduction (RingHom.id F5))
    sourceCoefficient targetCoefficient coefficientIdentity

abbrev targetInput : ModuleCat.{0} F5ᵐᵒᵖ := ModuleCat.of F5ᵐᵒᵖ F5ᵐᵒᵖ
local instance sourceInputRestrictedModule : Module ℤᵐᵒᵖ F5ᵐᵒᵖ :=
  Module.compHom F5ᵐᵒᵖ reduction.op
local instance sourceInputRestrictedSMul : SMul ℤᵐᵒᵖ F5ᵐᵒᵖ :=
  sourceInputRestrictedModule.toSMul

abbrev sourceInput : ModuleCat.{0} ℤᵐᵒᵖ :=
  letI := Module.compHom F5ᵐᵒᵖ reduction.op
  ModuleCat.of ℤᵐᵒᵖ F5ᵐᵒᵖ

/-- The target input is the actual free rank-one right module, not a projectivity premise. -/
theorem targetInput_projective : Projective targetInput := by infer_instance

/-- The actual restricted input has nonzero five-torsion, so it is not flat over ℤᵐᵒᵖ. -/
theorem sourceInput_not_flat : ¬ Module.Flat ℤᵐᵒᵖ sourceInput := by
  intro hFlat
  letI : Module.Flat ℤᵐᵒᵖ sourceInput := hFlat
  letI : Module.IsTorsionFree ℤᵐᵒᵖ sourceInput := inferInstance
  have hFive : (5 : ℤᵐᵒᵖ) • (1 : sourceInput) = 0 := by
    change (reduction.op (5 : ℤᵐᵒᵖ)) * (1 : F5ᵐᵒᵖ) = 0
    apply MulOpposite.unop_injective
    change (1 : F5) * (5 : F5) = 0
    decide
  rcases (Module.isTorsionFree_iff_smul_eq_zero.mp
    (inferInstance : Module.IsTorsionFree ℤᵐᵒᵖ sourceInput)) (5 : ℤᵐᵒᵖ)
      (1 : sourceInput) hFive with hScalar | hElement
  · have h := congrArg MulOpposite.unop hScalar
    norm_num at h
  · exact (by decide : (1 : F5ᵐᵒᵖ) ≠ 0) hElement

/-- This genuine free target becomes nonprojective after integer restriction. -/
theorem sourceInput_not_projective : ¬ Projective sourceInput := by
  intro h
  letI : Projective sourceInput := h
  letI : Module ℤᵐᵒᵖ sourceInput := sourceInput.isModule
  letI : Module.Projective ℤᵐᵒᵖ sourceInput :=
    ModuleCat.projective_of_module_projective (P := sourceInput)
  exact sourceInput_not_flat (inferInstance : Module.Flat ℤᵐᵒᵖ sourceInput)

/-- Arbitrary restriction cannot be inserted into the projective-preserving precomp iso. -/
theorem restriction_does_not_preserve_projectives :
    ¬ (ModuleCat.restrictScalars.{0} reduction.op).PreservesProjectiveObjects := by
  intro h
  letI : (ModuleCat.restrictScalars.{0} reduction.op).PreservesProjectiveObjects := h
  letI : Projective targetInput := targetInput_projective
  exact sourceInput_not_projective
    (Functor.PreservesProjectiveObjects.projective_obj
      (F := ModuleCat.restrictScalars reduction.op) targetInput_projective)

/-- The canonical positive-degree ring-change map is nevertheless defined, and its actual
target is zero because the target input is projective over its own ring. -/
theorem canonical_positive_ring_change_zero (n : ℕ) :
    torRingChangeMap ℤ F5 reduction (RingHom.id F5) sourceCoefficient targetCoefficient
      coefficientMap (n + 1) (A := sourceInput) (A' := targetInput) (𝟙 sourceInput) = 0 := by
  letI : Projective targetInput := targetInput_projective
  let G := (coefficientTensorObj F5 F5 targetCoefficient).obj
  have hZero : IsZero (((coefficientTorFunctor F5 F5 (n + 1)).obj targetCoefficient).obj
      targetInput) := Functor.isZero_leftDerived_obj_projective_succ G n targetInput
  have hTarget := (ModuleCat.restrictScalars (RingHom.id F5).op).map_isZero hZero
  exact hTarget.eq_of_tgt _ _

section IndependentWorlds

universe r r' s s' a a' b b' z

variable (R : Type r) (S : Type s) (R' : Type r') (S' : Type s')
  [Ring R] [Ring S] [Ring R'] [Ring S']

-- The exact output annotation admits scalar worlds unrelated to either carrier world.
example (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[ModuleCat.Bimodule.RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (n : ℕ) :
    (((torCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S n).obj B).obj A).carrier
      →ₛₗ[ψ.op]
        (((torCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S' n).obj B').obj A').carrier :=
  torRingChangeSemilinearMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g n

end IndependentWorlds


section ThreeRings

abbrev F25 := ZMod 25
def firstReduction : ℤ →+* F25 := Int.castRingHom F25
def secondReduction : F25 →+* F5 := ZMod.castHom (by norm_num : 5 ∣ 25) F5

theorem reduction_comp : secondReduction.comp firstReduction = reduction :=
  Subsingleton.elim _ _

local instance : Module F25 F5 := Module.compHom F5 secondReduction
local instance : SMulCommClass F25 F5ᵐᵒᵖ F5 := by
  refine ⟨?_⟩
  intro r s x
  change secondReduction r * (x * s.unop) = (secondReduction r * x) * s.unop
  exact (mul_assoc _ _ _).symm

local instance intermediateCoefficientEnveloping : Module (F25 ⊗[ℤ] F5ᵐᵒᵖ) F5 :=
  ModuleCat.Bimodule.RingChange.moduleOfActions F25 F5 F5

abbrev intermediateCoefficient : coefficientCategory.{0, 0, 0} F25 F5 :=
  letI := ModuleCat.Bimodule.RingChange.moduleOfActions F25 F5 F5
  ModuleCat.of (F25 ⊗[ℤ] F5ᵐᵒᵖ) F5

def firstCoefficientIdentity :
    sourceCoefficient →ₛₗ[ModuleCat.Bimodule.RingChange.envelopingRingHom
      firstReduction (RingHom.id F5)] intermediateCoefficient := by
  refine ModuleCat.Bimodule.RingChange.ofSemilinearMap firstReduction (RingHom.id F5)
    sourceCoefficient intermediateCoefficient (AddMonoidHom.id F5) ?_ ?_
  · intro z x
    change (ModuleCat.Bimodule.RingChange.leftModule ℤ F5
        (ModuleCat.Bimodule.RingChange.ofActions ℤ F5 F5)).smul z x =
      (ModuleCat.Bimodule.RingChange.leftModule F25 F5
        (ModuleCat.Bimodule.RingChange.ofActions F25 F5 F5)).smul (firstReduction z) x
    rw [ModuleCat.Bimodule.RingChange.ofActions_leftModule ℤ F5 F5,
      ModuleCat.Bimodule.RingChange.ofActions_leftModule F25 F5 F5]
    change z • x = secondReduction (firstReduction z) • x
    have h := congrArg (fun f : ℤ →+* F5 => f z) reduction_comp
    change secondReduction (firstReduction z) = reduction z at h
    rw [h]
    exact (Int.cast_smul_eq_zsmul F5 z x).symm
  · intro s x
    change (ModuleCat.Bimodule.RingChange.rightModule ℤ F5
        (ModuleCat.Bimodule.RingChange.ofActions ℤ F5 F5)).smul s x =
      (ModuleCat.Bimodule.RingChange.rightModule F25 F5
        (ModuleCat.Bimodule.RingChange.ofActions F25 F5 F5)).smul ((RingHom.id F5).op s) x
    rw [ModuleCat.Bimodule.RingChange.ofActions_rightModule ℤ F5 F5,
      ModuleCat.Bimodule.RingChange.ofActions_rightModule F25 F5 F5]
    rfl

def secondCoefficientIdentity :
    intermediateCoefficient →ₛₗ[ModuleCat.Bimodule.RingChange.envelopingRingHom
      secondReduction (RingHom.id F5)] targetCoefficient := by
  refine ModuleCat.Bimodule.RingChange.ofSemilinearMap secondReduction (RingHom.id F5)
    intermediateCoefficient targetCoefficient (AddMonoidHom.id F5) ?_ ?_
  · intro r x
    change (ModuleCat.Bimodule.RingChange.leftModule F25 F5
        (ModuleCat.Bimodule.RingChange.ofActions F25 F5 F5)).smul r x =
      (ModuleCat.Bimodule.RingChange.leftModule F5 F5
        (ModuleCat.Bimodule.RingChange.ofActions F5 F5 F5)).smul (secondReduction r) x
    rw [ModuleCat.Bimodule.RingChange.ofActions_leftModule F25 F5 F5,
      ModuleCat.Bimodule.RingChange.ofActions_leftModule F5 F5 F5]
    rfl
  · intro s x
    change (ModuleCat.Bimodule.RingChange.rightModule F25 F5
        (ModuleCat.Bimodule.RingChange.ofActions F25 F5 F5)).smul s x =
      (ModuleCat.Bimodule.RingChange.rightModule F5 F5
        (ModuleCat.Bimodule.RingChange.ofActions F5 F5 F5)).smul ((RingHom.id F5).op s) x
    rw [ModuleCat.Bimodule.RingChange.ofActions_rightModule F25 F5 F5,
      ModuleCat.Bimodule.RingChange.ofActions_rightModule F5 F5 F5]
    rfl

local instance intermediateInputRestrictedModule : Module F25ᵐᵒᵖ F5ᵐᵒᵖ :=
  Module.compHom F5ᵐᵒᵖ secondReduction.op
local instance intermediateInputRestrictedSMul : SMul F25ᵐᵒᵖ F5ᵐᵒᵖ :=
  intermediateInputRestrictedModule.toSMul

abbrev intermediateInput : ModuleCat.{0} F25ᵐᵒᵖ :=
  letI := Module.compHom F5ᵐᵒᵖ secondReduction.op
  ModuleCat.of F25ᵐᵒᵖ F5ᵐᵒᵖ

def firstInputIdentity : sourceInput →ₛₗ[firstReduction.op] intermediateInput where
  toFun := id
  map_add' _ _ := rfl
  map_smul' r x := by
    change reduction.op r * x = secondReduction.op (firstReduction.op r) * x
    have h := congrArg (fun f : ℤ →+* F5 => f.op r) reduction_comp
    change secondReduction.op (firstReduction.op r) = reduction.op r at h
    rw [h]

def secondInputIdentity : intermediateInput →ₛₗ[secondReduction.op] targetInput where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def compositeCoefficientIdentity :=
  composeCoefficientSemilinear ℤ F5 firstReduction (RingHom.id F5)
    secondReduction (RingHom.id F5) sourceCoefficient intermediateCoefficient targetCoefficient
    firstCoefficientIdentity secondCoefficientIdentity

def compositeInputIdentity :=
  composeInputSemilinear ℤ firstReduction secondReduction sourceInput intermediateInput
    targetInput firstInputIdentity secondInputIdentity

end ThreeRings

section WorkingWorlds


abbrev sourceTorAt.{h} (n : ℕ) : ModuleCat.{h} F5ᵐᵒᵖ :=
  ((torCoefficientFunctorAt.{h, 0, 0, 0, 0} ℤ F5 n).obj sourceCoefficient).obj sourceInput
abbrev intermediateTorAt.{h} (n : ℕ) : ModuleCat.{h} F5ᵐᵒᵖ :=
  ((torCoefficientFunctorAt.{h, 0, 0, 0, 0} F25 F5 n).obj intermediateCoefficient).obj
    intermediateInput
abbrev targetTorAt.{h} (n : ℕ) : ModuleCat.{h} F5ᵐᵒᵖ :=
  ((torCoefficientFunctorAt.{h, 0, 0, 0, 0} F5 F5 n).obj targetCoefficient).obj targetInput

def firstMapAt.{h} (n : ℕ) :=
  torRingChangeMapAt.{h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ F5
    firstReduction (RingHom.id F5) sourceCoefficient intermediateCoefficient
    firstCoefficientIdentity sourceInput intermediateInput firstInputIdentity n

def secondMapAt.{h} (n : ℕ) :=
  torRingChangeMapAt.{h, 0, 0, 0, 0, 0, 0, 0, 0} F25 F5
    secondReduction (RingHom.id F5) intermediateCoefficient targetCoefficient
    secondCoefficientIdentity intermediateInput targetInput secondInputIdentity n

def compositeMapAt.{h} (n : ℕ) :=
  torRingChangeMapAt.{h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ F5
    (secondReduction.comp firstReduction) ((RingHom.id F5).comp (RingHom.id F5))
    sourceCoefficient targetCoefficient compositeCoefficientIdentity sourceInput targetInput
    compositeInputIdentity n

def twoStepMapAt.{h} (n : ℕ) :
    sourceTorAt.{h} n ⟶
      (ModuleCat.restrictScalars ((RingHom.id F5).comp (RingHom.id F5)).op).obj
        (targetTorAt.{h} n) :=
  firstMapAt.{h} n ≫ (ModuleCat.restrictScalars (RingHom.id F5).op).map
    (secondMapAt.{h} n) ≫
    (ModuleCat.restrictScalarsComp' (RingHom.id F5).op (RingHom.id F5).op
      ((RingHom.id F5).comp (RingHom.id F5)).op (by ext s; rfl)).inv.app (targetTorAt.{h} n)

/-- The actual nonprojective integer input passes through ℤ/25 by canonical Tor composition. -/
theorem two_step_equals_composite.{h} (n : ℕ) :
    twoStepMapAt.{h} n = compositeMapAt.{h} n := by
  exact torRingChangeMapAt_comp.{h, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    ℤ F5 firstReduction (RingHom.id F5) secondReduction (RingHom.id F5)
    sourceCoefficient intermediateCoefficient targetCoefficient firstCoefficientIdentity
    secondCoefficientIdentity sourceInput intermediateInput targetInput firstInputIdentity
    secondInputIdentity n

def sourceHeightIso.{h, q} (n : ℕ) :=
  coefficientTorHeightIsoAt.{q, h, 0, 0, 0, 0} ℤ F5 sourceCoefficient n
def intermediateHeightIso.{h, q} (n : ℕ) :=
  coefficientTorHeightIsoAt.{q, h, 0, 0, 0, 0} F25 F5 intermediateCoefficient n
def targetHeightIso.{h, q} (n : ℕ) :=
  coefficientTorHeightIsoAt.{q, h, 0, 0, 0, 0} F5 F5 targetCoefficient n

/-- Height is tested on the first map into the restricted ℤ/25 input, before projective
target vanishing at the final ℤ/5 step. Neither ring restriction is given
projective preservation. -/
theorem first_map_height.{h, q} (n : ℕ) :
    firstMapAt.{max h q} n ≫
        (ModuleCat.restrictScalars (RingHom.id F5).op).map
          ((intermediateHeightIso.{h, q} n).inv.app intermediateInput) ≫
        (ModuleCat.uliftRestrictionIso.{q, h, 0, 0} (RingHom.id F5).op).inv.app
          (intermediateTorAt.{h} n) =
      (sourceHeightIso.{h, q} n).inv.app sourceInput ≫
        (ModuleCat.uliftFunctor.{max h q, h} F5ᵐᵒᵖ).map (firstMapAt.{h} n) := by
  exact torRingChangeMapAt_height_inverse.{q, h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ F5
    firstReduction (RingHom.id F5) sourceCoefficient intermediateCoefficient
    firstCoefficientIdentity sourceInput intermediateInput firstInputIdentity n

/-- The canonical two-step comparison also obeys the actual original-carrier height cube. -/
theorem two_step_height.{h, q} (n : ℕ) :
    twoStepMapAt.{max h q} n ≫
        (ModuleCat.restrictScalars ((RingHom.id F5).comp (RingHom.id F5)).op).map
          ((targetHeightIso.{h, q} n).inv.app targetInput) ≫
        (ModuleCat.uliftRestrictionIso.{q, h, 0, 0}
          ((RingHom.id F5).comp (RingHom.id F5)).op).inv.app (targetTorAt.{h} n) =
      (sourceHeightIso.{h, q} n).inv.app sourceInput ≫
        (ModuleCat.uliftFunctor.{max h q, h} F5ᵐᵒᵖ).map (twoStepMapAt.{h} n) := by
  rw [two_step_equals_composite, two_step_equals_composite]
  exact torRingChangeMapAt_height_inverse.{q, h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ F5
    (secondReduction.comp firstReduction) ((RingHom.id F5).comp (RingHom.id F5))
    sourceCoefficient targetCoefficient compositeCoefficientIdentity sourceInput targetInput
    compositeInputIdentity n

/-- Positive-degree two-step Tor vanishes at its genuinely free final input, while the
original integer input remains nonflat and nonprojective. Only native input ULift preserves
projectives; neither ring restriction receives that premise. -/
theorem two_step_positive_zero.{h} (n : ℕ) :
    twoStepMapAt.{h} (n + 1) = 0 := by
  letI : Projective targetInput := targetInput_projective
  letI : (ModuleCat.uliftFunctor.{h, 0} F5ᵐᵒᵖ).PreservesProjectiveObjects := inferInstance
  let A := (ModuleCat.uliftFunctor.{h, 0} F5ᵐᵒᵖ).obj targetInput
  let B := (ModuleCat.uliftFunctor.{h, 0} (F5 ⊗[ℤ] F5ᵐᵒᵖ)).obj targetCoefficient
  letI : Projective A :=
    Functor.PreservesProjectiveObjects.projective_obj
      (F := ModuleCat.uliftFunctor.{h, 0} F5ᵐᵒᵖ) targetInput_projective
  let G := (coefficientTensorObj F5 F5 B).obj
  have hZero : IsZero (targetTorAt.{h} (n + 1)) :=
    Functor.isZero_leftDerived_obj_projective_succ G n A
  have hTarget :=
    (ModuleCat.restrictScalars ((RingHom.id F5).comp (RingHom.id F5)).op).map_isZero hZero
  rw [two_step_equals_composite]
  exact hTarget.eq_of_tgt _ _

end WorkingWorlds

end MathlibExtTest.Bimodule.TorScalarChangeRingMapCoherence
