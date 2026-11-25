/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.TorScalarChangeHeight
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Tactic.NormNum

/-!
# Ordered matrix Tor under actual composition and working-height transport

The acting ring changes from ℤ to ℤ/5 and the independent outer ring changes
from M₂(ℤ) to M₂(ℤ/5). The canonical Tor map, not just an underived quotient
map, carries the two ordered outer operations to different target classes.
Its native zero augmentation and an actual balanced scalar-action evaluator
detect the distinction. The reductions through ℤ/25 below directly exercise
canonical ring-map composition and its height comparison on these nonzero
ordered classes.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits MulOpposite
open ModuleCat.BalancedTensorRight ModuleCat.Bimodule.Tensor
open scoped TensorProduct

namespace MathlibExtTest.Bimodule.TorScalarChangeMatrixCoherence

abbrev F5 := ZMod 5
abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ
abbrev M2F := Matrix (Fin 2) (Fin 2) F5

local instance : Module ℤ F5 := AddCommGroup.toIntModule F5
local instance : Module ℤ M2Z := AddCommGroup.toIntModule M2Z
local instance : Module ℤ M2F := AddCommGroup.toIntModule M2F
local instance : SMulCommClass M2Zᵐᵒᵖ ℤ M2Z := Module.intModule_smulCommClass
local instance : SMulCommClass ℤ M2Zᵐᵒᵖ M2Z := SMulCommClass.symm _ _ _
local instance : SMulCommClass F5 M2Fᵐᵒᵖ M2F := by
  refine ⟨?_⟩
  intro r s x
  change r • (x * s.unop) = (r • x) * s.unop
  exact (Matrix.smul_mul r x s.unop).symm

def actingReduction : ℤ →+* F5 := Int.castRingHom F5
def outerReduction : M2Z →+* M2F := actingReduction.mapMatrix
def reductionGround : M2Z →ₗ[ℤ] M2F := outerReduction.toAddMonoidHom.toIntLinearMap

abbrev originalSourceLeft : Module ℤ M2Z := inferInstance
abbrev originalSourceRight : Module M2Zᵐᵒᵖ M2Z := inferInstance

local instance sourceCoefficientEnveloping : Module (ℤ ⊗[ℤ] M2Zᵐᵒᵖ) M2Z :=
  ModuleCat.Bimodule.RingChange.moduleOfActions ℤ M2Z M2Z

abbrev sourceCoefficient : coefficientCategory.{0, 0, 0} ℤ M2Z :=
  letI := ModuleCat.Bimodule.RingChange.moduleOfActions ℤ M2Z M2Z
  ModuleCat.of (ℤ ⊗[ℤ] M2Zᵐᵒᵖ) M2Z
abbrev originalTargetLeft : Module F5 M2F := inferInstance
abbrev originalTargetRight : Module M2Fᵐᵒᵖ M2F := inferInstance

local instance targetCoefficientEnveloping : Module (F5 ⊗[ℤ] M2Fᵐᵒᵖ) M2F :=
  ModuleCat.Bimodule.RingChange.moduleOfActions F5 M2F M2F

abbrev targetCoefficient : coefficientCategory.{0, 0, 0} F5 M2F :=
  letI := ModuleCat.Bimodule.RingChange.moduleOfActions F5 M2F M2F
  ModuleCat.of (F5 ⊗[ℤ] M2Fᵐᵒᵖ) M2F

local instance targetCoefficientLeftModule : Module F5 targetCoefficient :=
  coefficientLeftModule F5 M2F targetCoefficient
local instance targetCoefficientLeftSMul : SMul F5 targetCoefficient :=
  targetCoefficientLeftModule.toSMul
local instance targetCoefficientRightModule : Module M2Fᵐᵒᵖ targetCoefficient :=
  coefficientRightModule F5 M2F targetCoefficient
local instance targetCoefficientRightSMul : SMul M2Fᵐᵒᵖ targetCoefficient :=
  targetCoefficientRightModule.toSMul
local instance targetCoefficientCommuting : SMulCommClass F5 M2Fᵐᵒᵖ targetCoefficient :=
  coefficientActionsCommute F5 M2F targetCoefficient
local instance targetCoefficientIntegerComm : SMulCommClass ℤ F5 targetCoefficient := by
  refine ⟨?_⟩
  intro z r y
  let a : targetCoefficient →+ targetCoefficient :=
    { toFun := targetCoefficientLeftModule.smul r
      map_zero' := targetCoefficientLeftModule.smul_zero r
      map_add' := targetCoefficientLeftModule.smul_add r }
  exact (a.map_zsmul z y).symm
local instance targetCoefficientIntegerTower :
    @IsScalarTower ℤ F5 targetCoefficient (Algebra.toModule : Module ℤ F5).toSMul
      targetCoefficientLeftModule.toSMul (AddCommGroup.toIntModule targetCoefficient).toSMul :=
  Module.intModule_isScalarTower (Algebra.toModule : Module ℤ F5)
    (AddCommGroup.toIntModule targetCoefficient)

/-- The concrete source's stored left action is the original integer action. -/
theorem actualSourceLeft : ModuleCat.Bimodule.RingChange.leftModule ℤ M2Z sourceCoefficient =
    originalSourceLeft := by
  apply Module.ext'
  intro r y
  change originalSourceLeft.smul r (originalSourceRight.smul (1 : M2Zᵐᵒᵖ) y) =
    originalSourceLeft.smul r y
  exact congrArg (originalSourceLeft.smul r) (originalSourceRight.one_smul y)

/-- The concrete source's stored right action is the original right matrix multiplication. -/
theorem actualSourceRight : ModuleCat.Bimodule.RingChange.rightModule ℤ M2Z sourceCoefficient =
    originalSourceRight := by
  apply Module.ext'
  intro t y
  change originalSourceLeft.smul (1 : ℤ) (originalSourceRight.smul t y) =
    originalSourceRight.smul t y
  exact originalSourceLeft.one_smul (originalSourceRight.smul t y)

/-- The actual stored left action of the concrete target is the original matrix scalar action. -/
theorem actualTargetLeft : ModuleCat.Bimodule.RingChange.leftModule F5 M2F targetCoefficient =
    originalTargetLeft := by
  apply Module.ext'
  intro r y
  change originalTargetLeft.smul r (originalTargetRight.smul (1 : M2Fᵐᵒᵖ) y) =
    originalTargetLeft.smul r y
  exact congrArg (originalTargetLeft.smul r) (originalTargetRight.one_smul y)

/-- The actual stored outer action of the concrete target is the original right matrix action. -/
theorem actualTargetRight : ModuleCat.Bimodule.RingChange.rightModule F5 M2F targetCoefficient =
    originalTargetRight := by
  apply Module.ext'
  intro t y
  change originalTargetLeft.smul (1 : F5) (originalTargetRight.smul t y) =
    originalTargetRight.smul t y
  exact originalTargetLeft.one_smul (originalTargetRight.smul t y)

/-- The actual entrywise reduction is semilinear for both original endpoint actions. -/
def coefficientReduction :
    sourceCoefficient →ₛₗ[ModuleCat.Bimodule.RingChange.envelopingRingHom
      actingReduction outerReduction] targetCoefficient := by
  refine ModuleCat.Bimodule.RingChange.ofSemilinearMap actingReduction outerReduction
    sourceCoefficient targetCoefficient outerReduction.toAddMonoidHom ?_ ?_
  · intro z x
    change outerReduction ((ModuleCat.Bimodule.RingChange.leftModule ℤ M2Z sourceCoefficient).smul z x) =
      (ModuleCat.Bimodule.RingChange.leftModule F5 M2F targetCoefficient).smul
        (actingReduction z) (outerReduction x)
    rw [actualTargetLeft, actualSourceLeft]
    have hSource : originalSourceLeft.smul z x = z • x :=
      int_smul_eq_zsmul originalSourceLeft z x
    have hTarget : originalTargetLeft.smul (actingReduction z) (outerReduction x) =
        z • outerReduction x :=
      @Int.cast_smul_eq_zsmul F5 M2F inferInstance inferInstance originalTargetLeft z (outerReduction x)
    exact (congrArg outerReduction hSource).trans
      ((outerReduction.toAddMonoidHom.map_zsmul z x).trans hTarget.symm)
  · intro t x
    change outerReduction ((ModuleCat.Bimodule.RingChange.rightModule ℤ M2Z sourceCoefficient).smul t x) =
      (ModuleCat.Bimodule.RingChange.rightModule F5 M2F targetCoefficient).smul
        (outerReduction.op t) (outerReduction x)
    rw [actualTargetRight, actualSourceRight]
    change outerReduction (x * t.unop) = outerReduction x * outerReduction t.unop
    exact outerReduction.map_mul x t.unop

def coefficientMap : sourceCoefficient ⟶
    (ModuleCat.Bimodule.RingChange.restrictFunctor actingReduction outerReduction).obj
      targetCoefficient :=
  ModuleCat.semilinearMapAddEquiv
    (ModuleCat.Bimodule.RingChange.envelopingRingHom actingReduction outerReduction)
    sourceCoefficient targetCoefficient coefficientReduction

abbrev sourceInput : ModuleCat.{0} ℤᵐᵒᵖ := ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ
abbrev targetInput : ModuleCat.{0} F5ᵐᵒᵖ := ModuleCat.of F5ᵐᵒᵖ F5ᵐᵒᵖ

def inputReduction : sourceInput →ₛₗ[actingReduction.op] targetInput where
  toFun := actingReduction.op
  map_add' := actingReduction.op.map_add
  map_smul' r x := actingReduction.op.map_mul r x

def inputMap : sourceInput ⟶ (ModuleCat.restrictScalars actingReduction.op).obj targetInput :=
  ModuleCat.semilinearMapAddEquiv actingReduction.op sourceInput targetInput inputReduction

abbrev sourceTor := ((coefficientTorFunctor ℤ M2Z 0).obj sourceCoefficient).obj sourceInput
abbrev targetTor := ((coefficientTorFunctor F5 M2F 0).obj targetCoefficient).obj targetInput
abbrev targetTensor := ((coefficientTensorObj F5 M2F targetCoefficient).obj).obj targetInput
abbrev targetTensorOriginal := (ModuleCat.Bimodule.Tensor.functor F5 M2F targetCoefficient).obj targetInput

def canonicalMap : sourceTor →ₛₗ[outerReduction.op] targetTor :=
  torRingChangeSemilinearMap ℤ M2Z actingReduction outerReduction
    sourceCoefficient targetCoefficient coefficientMap 0 inputMap

def seed : sourceTor :=
  ((coefficientTorZeroIso ℤ M2Z sourceCoefficient).inv.app sourceInput).hom
    (pairing ℤ M2Z sourceCoefficient sourceInput (op (1 : ℤ)) (1 : sourceCoefficient))

private theorem seed_zero_image :
    ((coefficientTorZeroIso ℤ M2Z sourceCoefficient).hom.app sourceInput).hom seed =
      pairing ℤ M2Z sourceCoefficient sourceInput (op (1 : ℤ)) (1 : sourceCoefficient) :=
  ConcreteCategory.congr_hom
    ((coefficientTorZeroIso ℤ M2Z sourceCoefficient).app sourceInput).inv_hom_id
      (pairing ℤ M2Z sourceCoefficient sourceInput (op (1 : ℤ)) (1 : sourceCoefficient))

private theorem zero_diagram :
    torRingChangeMap ℤ M2Z actingReduction outerReduction sourceCoefficient targetCoefficient
        coefficientMap 0 inputMap ≫
      (ModuleCat.restrictScalars outerReduction.op).map
        ((coefficientTorZeroIso F5 M2F targetCoefficient).hom.app targetInput) =
    (coefficientTorZeroIso ℤ M2Z sourceCoefficient).hom.app sourceInput ≫
      (coefficientTensorObj ℤ M2Z sourceCoefficient).obj.map inputMap ≫
      (tensorRingChangeTransformation ℤ M2Z actingReduction outerReduction
        sourceCoefficient targetCoefficient coefficientMap).app targetInput := by
  have h := congrArg (fun α => α.app targetInput)
    (torRingChangeTransformation_zero ℤ M2Z actingReduction outerReduction
      sourceCoefficient targetCoefficient coefficientMap)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  let u := ((coefficientTorFunctor ℤ M2Z 0).obj sourceCoefficient).map inputMap
  let c := (torRingChangeTransformation ℤ M2Z actingReduction outerReduction
    sourceCoefficient targetCoefficient coefficientMap 0).app targetInput
  let z := (ModuleCat.restrictScalars outerReduction.op).map
    ((coefficientTorZeroIso F5 M2F targetCoefficient).hom.app targetInput)
  let zA := (coefficientTorZeroIso ℤ M2Z sourceCoefficient).hom.app
    ((ModuleCat.restrictScalars actingReduction.op).obj targetInput)
  let zS := (coefficientTorZeroIso ℤ M2Z sourceCoefficient).hom.app sourceInput
  let m := (coefficientTensorObj ℤ M2Z sourceCoefficient).obj.map inputMap
  let d := (tensorRingChangeTransformation ℤ M2Z actingReduction outerReduction
    sourceCoefficient targetCoefficient coefficientMap).app targetInput
  have hBase : c ≫ z = zA ≫ d := h
  have hNat : u ≫ zA = zS ≫ m :=
    (coefficientTorZeroIso ℤ M2Z sourceCoefficient).hom.naturality inputMap
  change (u ≫ c) ≫ z = zS ≫ m ≫ d
  exact (Category.assoc u c z).trans ((congrArg (fun f => u ≫ f) hBase).trans
    ((Category.assoc u zA d).symm.trans ((congrArg (fun f => f ≫ d) hNat).trans
      (Category.assoc zS m d))))

/-- The actual canonical Tor map has the original pure tensor value through native zero. -/
theorem canonical_seed_image :
    ((coefficientTorZeroIso F5 M2F targetCoefficient).hom.app targetInput).hom
        (canonicalMap seed) =
      pairing F5 M2F targetCoefficient targetInput (op (1 : F5)) (1 : targetCoefficient) := by
  have h := ConcreteCategory.congr_hom zero_diagram seed
  change ((coefficientTorZeroIso F5 M2F targetCoefficient).hom.app targetInput).hom
      (canonicalMap seed) =
    (((coefficientTensorObj ℤ M2Z sourceCoefficient).obj.map inputMap) ≫
      (tensorRingChangeTransformation ℤ M2Z actingReduction outerReduction
        sourceCoefficient targetCoefficient coefficientMap).app targetInput).hom
      (((coefficientTorZeroIso ℤ M2Z sourceCoefficient).hom.app sourceInput).hom seed) at h
  rw [seed_zero_image] at h
  have hTensor : (((coefficientTensorObj ℤ M2Z sourceCoefficient).obj.map inputMap) ≫
      (tensorRingChangeTransformation ℤ M2Z actingReduction outerReduction
        sourceCoefficient targetCoefficient coefficientMap).app targetInput).hom
        (pairing ℤ M2Z sourceCoefficient sourceInput (op (1 : ℤ)) (1 : sourceCoefficient)) =
      pairing F5 M2F targetCoefficient targetInput (actingReduction.op (op (1 : ℤ)))
        (outerReduction (1 : M2Z)) := rfl
  rw [hTensor, outerReduction.map_one] at h
  have hOne : actingReduction.op (op (1 : ℤ)) = op (1 : F5) :=
    congrArg op actingReduction.map_one
  exact h.trans (congrArg (fun x => pairing F5 M2F targetCoefficient targetInput x
    (1 : targetCoefficient)) hOne)

private theorem target_pairing_smul (s : M2Fᵐᵒᵖ) (x : targetInput) (y : targetCoefficient) :
    targetTensorOriginal.isModule.smul s (pairing F5 M2F targetCoefficient targetInput x y) =
      pairing F5 M2F targetCoefficient targetInput x (y * s.unop) := by
  letI := coefficientLeftModule F5 M2F targetCoefficient
  letI := coefficientRightModule F5 M2F targetCoefficient
  letI := coefficientActionsCommute F5 M2F targetCoefficient
  have hy : (coefficientRightModule F5 M2F targetCoefficient).smul s y = y * s.unop := by
    exact congrArg (fun d : Module M2Fᵐᵒᵖ M2F => d.smul s y) actualTargetRight
  have h := TensorProduct.Balanced.rightModule_smul_mk ℤ F5 M2F targetInput targetCoefficient s x y
  exact h.trans (congrArg (pairing F5 M2F targetCoefficient targetInput x) hy)

def inputCoordinate : targetInput →ₗ[ℤ] F5 :=
  (show targetInput →+ F5 from
    { toFun := MulOpposite.unop
      map_zero' := rfl
      map_add' := fun _ _ => rfl }).toIntLinearMap

/-- The native original scalar representation gives this integer-bilinear pairing. -/
def scalarPairing : F5 →ₗ[ℤ] targetCoefficient →ₗ[ℤ] targetCoefficient :=
  (Algebra.lsmul ℤ ℤ targetCoefficient : F5 →ₐ[ℤ] Module.End ℤ targetCoefficient).toLinearMap

/-- The actual original scalar action descends through the target's balanced relations. -/
def evaluateOriginal : targetTensorOriginal →+ targetCoefficient := by
  letI := coefficientLeftModule F5 M2F targetCoefficient
  letI := coefficientRightModule F5 M2F targetCoefficient
  letI := coefficientActionsCommute F5 M2F targetCoefficient
  exact (TensorProduct.Balanced.lift (scalarPairing.comp inputCoordinate) (fun r x y => by
    change (x.unop * r : F5) • y = x.unop • (r • y)
    exact (coefficientLeftModule F5 M2F targetCoefficient).mul_smul x.unop r y)).toAddMonoidHom

private theorem evaluateOriginal_unit_pairing (y : targetCoefficient) :
    evaluateOriginal (pairing F5 M2F targetCoefficient targetInput (op (1 : F5)) y) = y := by
  have h := TensorProduct.Balanced.lift_mk (scalarPairing.comp inputCoordinate)
    (fun r x y => (coefficientLeftModule F5 M2F targetCoefficient).mul_smul x.unop r y)
    (op (1 : F5)) y
  exact h.trans ((coefficientLeftModule F5 M2F targetCoefficient).one_smul y)

/-- Evaluation uses the actual native provider inverse on the original balanced tensor. -/
def evaluate : targetTensor →+ targetCoefficient :=
  evaluateOriginal.comp ((nativeTensorFunctorIso F5 M2F targetCoefficient).inv.app targetInput).hom.toAddMonoidHom

private theorem evaluate_unit_pairing (y : targetCoefficient) :
    evaluate (pairing F5 M2F targetCoefficient targetInput (op (1 : F5)) y) = y := by
  exact evaluateOriginal_unit_pairing y

def upper : M2Z := fun i j => if i = 0 ∧ j = 1 then 1 else 0
def lower : M2Z := fun i j => if i = 1 ∧ j = 0 then 1 else 0

def orderedClass (s t : M2Z) : sourceTor := op s • (op t • seed)

/-- The canonical Tor image detects the true ordered matrix product after ring change. -/
theorem ordered_value (s t : M2Z) :
    evaluate (((coefficientTorZeroIso F5 M2F targetCoefficient).hom.app targetInput).hom
      (canonicalMap (orderedClass s t))) = outerReduction (t * s) := by
  let q := (coefficientTorZeroIso F5 M2F targetCoefficient).hom.app targetInput
  let j := (nativeTensorFunctorIso F5 M2F targetCoefficient).inv.app targetInput
  let rS := outerReduction.op (op s)
  let rT := outerReduction.op (op t)
  let w := pairing F5 M2F targetCoefficient targetInput (op (1 : F5)) (1 : targetCoefficient)
  have hCt := canonicalMap.map_smul' (op t) seed
  have hCs := canonicalMap.map_smul' (op s) (sourceTor.isModule.smul (op t) seed)
  have hC : canonicalMap (orderedClass s t) =
      targetTor.isModule.smul rS (targetTor.isModule.smul rT (canonicalMap seed)) :=
    hCs.trans (congrArg (targetTor.isModule.smul rS) hCt)
  have hZs := q.hom.map_smul' rS (targetTor.isModule.smul rT (canonicalMap seed))
  have hZt := q.hom.map_smul' rT (canonicalMap seed)
  have hSeed : q.hom (canonicalMap seed) = w := canonical_seed_image
  have hZ : q.hom (canonicalMap (orderedClass s t)) =
      targetTensor.isModule.smul rS (targetTensor.isModule.smul rT w) :=
    (congrArg q.hom hC).trans (hZs.trans
      (congrArg (targetTensor.isModule.smul rS) (hZt.trans
        (congrArg (targetTensor.isModule.smul rT) hSeed))))
  have hJ := j.hom.map_smul' rS (targetTensor.isModule.smul rT w)
  have hJt := nativeTensorFunctorIso_inv_smul_pairing F5 M2F targetCoefficient targetInput
    rT (op (1 : F5)) (1 : targetCoefficient)
  have hPairt := target_pairing_smul rT (op (1 : F5)) (1 : targetCoefficient)
  have hPairs := target_pairing_smul rS (op (1 : F5)) ((1 : targetCoefficient) * rT.unop)
  have hResult : j.hom (q.hom (canonicalMap (orderedClass s t))) =
      pairing F5 M2F targetCoefficient targetInput (op (1 : F5))
        (((1 : targetCoefficient) * rT.unop) * rS.unop) :=
    (congrArg j.hom hZ).trans (hJ.trans
      ((congrArg (targetTensorOriginal.isModule.smul rS) hJt).trans
        ((congrArg (targetTensorOriginal.isModule.smul rS) hPairt).trans hPairs)))
  have hValue := congrArg evaluateOriginal hResult
  change evaluateOriginal (j.hom (q.hom (canonicalMap (orderedClass s t)))) = _
  exact hValue.trans ((evaluateOriginal_unit_pairing _).trans (by
    change ((1 : M2F) * outerReduction t) * outerReduction s = outerReduction (t * s)
    rw [one_mul, outerReduction.map_mul]))

private theorem reduced_products_differ :
    outerReduction (upper * lower) ≠ outerReduction (lower * upper) := by
  have h₁ : (upper * lower) 0 0 = 1 := by
    simpa [upper, lower] using (Matrix.two_mul_expl upper lower).1
  have h₂ : (lower * upper) 0 0 = 0 := by
    simpa [upper, lower] using (Matrix.two_mul_expl lower upper).1
  intro h
  have h₀ := congrArg (fun x : M2F => x 0 0) h
  change (((upper * lower) 0 0 : ℤ) : F5) = (((lower * upper) 0 0 : ℤ) : F5) at h₀
  rw [h₁, h₂] at h₀
  exact (by decide : (1 : F5) ≠ 0) (by simpa only [Int.cast_one, Int.cast_zero] using h₀)

/-- Reversing the two actual outer operations changes the target canonical Tor class. -/
theorem canonical_Tor_outer_order_survives :
    canonicalMap (orderedClass upper lower) ≠ canonicalMap (orderedClass lower upper) := by
  intro h
  have h' := congrArg (fun x =>
    evaluate (((coefficientTorZeroIso F5 M2F targetCoefficient).hom.app targetInput).hom x)) h
  rw [ordered_value, ordered_value] at h'
  exact reduced_products_differ h'.symm


section ThreeRings

abbrev F25 := ZMod 25
abbrev M2I := Matrix (Fin 2) (Fin 2) F25

local instance : Module ℤ F25 := AddCommGroup.toIntModule F25
local instance : Module ℤ M2I := AddCommGroup.toIntModule M2I
local instance : SMulCommClass F25 M2Iᵐᵒᵖ M2I := by
  refine ⟨?_⟩
  intro r s x
  change r • (x * s.unop) = (r • x) * s.unop
  exact (Matrix.smul_mul r x s.unop).symm

def firstActingReduction : ℤ →+* F25 := Int.castRingHom F25
def secondActingReduction : F25 →+* F5 := ZMod.castHom (by norm_num : 5 ∣ 25) F5
def firstOuterReduction : M2Z →+* M2I := firstActingReduction.mapMatrix
def secondOuterReduction : M2I →+* M2F := secondActingReduction.mapMatrix

/-- Both acting-ring maps are the actual residue homomorphisms. -/
theorem actingReduction_comp :
    secondActingReduction.comp firstActingReduction = actingReduction :=
  Subsingleton.elim _ _

/-- Entrywise reduction through ℤ/25 is the actual original matrix-ring reduction. -/
theorem outerReduction_comp :
    secondOuterReduction.comp firstOuterReduction = outerReduction := by
  apply RingHom.ext
  intro x
  ext i j
  exact congrArg (fun f : ℤ →+* F5 => f (x i j)) actingReduction_comp

local instance intermediateCoefficientEnveloping : Module (F25 ⊗[ℤ] M2Iᵐᵒᵖ) M2I :=
  ModuleCat.Bimodule.RingChange.moduleOfActions F25 M2I M2I

abbrev intermediateCoefficient : coefficientCategory.{0, 0, 0} F25 M2I :=
  letI := ModuleCat.Bimodule.RingChange.moduleOfActions F25 M2I M2I
  ModuleCat.of (F25 ⊗[ℤ] M2Iᵐᵒᵖ) M2I

def firstCoefficientReduction :
    sourceCoefficient →ₛₗ[ModuleCat.Bimodule.RingChange.envelopingRingHom
      firstActingReduction firstOuterReduction] intermediateCoefficient := by
  refine ModuleCat.Bimodule.RingChange.ofSemilinearMap
    firstActingReduction firstOuterReduction sourceCoefficient intermediateCoefficient
    firstOuterReduction.toAddMonoidHom ?_ ?_
  · intro z x
    change firstOuterReduction ((ModuleCat.Bimodule.RingChange.leftModule ℤ M2Z
        (ModuleCat.Bimodule.RingChange.ofActions ℤ M2Z M2Z)).smul z x) =
      (ModuleCat.Bimodule.RingChange.leftModule F25 M2I
        (ModuleCat.Bimodule.RingChange.ofActions F25 M2I M2I)).smul
          (firstActingReduction z) (firstOuterReduction x)
    rw [ModuleCat.Bimodule.RingChange.ofActions_leftModule,
      ModuleCat.Bimodule.RingChange.ofActions_leftModule]
    have h := firstOuterReduction.toAddMonoidHom.toIntLinearMap.map_smul z x
    exact h.trans (Int.cast_smul_eq_zsmul F25 z (firstOuterReduction x)).symm
  · intro s x
    change firstOuterReduction ((ModuleCat.Bimodule.RingChange.rightModule ℤ M2Z
        (ModuleCat.Bimodule.RingChange.ofActions ℤ M2Z M2Z)).smul s x) =
      (ModuleCat.Bimodule.RingChange.rightModule F25 M2I
        (ModuleCat.Bimodule.RingChange.ofActions F25 M2I M2I)).smul
          (firstOuterReduction.op s) (firstOuterReduction x)
    rw [ModuleCat.Bimodule.RingChange.ofActions_rightModule,
      ModuleCat.Bimodule.RingChange.ofActions_rightModule]
    change firstOuterReduction (x * s.unop) =
      firstOuterReduction x * firstOuterReduction s.unop
    exact firstOuterReduction.map_mul x s.unop

def secondCoefficientReduction :
    intermediateCoefficient →ₛₗ[ModuleCat.Bimodule.RingChange.envelopingRingHom
      secondActingReduction secondOuterReduction] targetCoefficient := by
  refine ModuleCat.Bimodule.RingChange.ofSemilinearMap
    secondActingReduction secondOuterReduction intermediateCoefficient targetCoefficient
    secondOuterReduction.toAddMonoidHom ?_ ?_
  · intro r x
    change secondOuterReduction ((ModuleCat.Bimodule.RingChange.leftModule F25 M2I
        (ModuleCat.Bimodule.RingChange.ofActions F25 M2I M2I)).smul r x) =
      (ModuleCat.Bimodule.RingChange.leftModule F5 M2F
        targetCoefficient).smul
          (secondActingReduction r) (secondOuterReduction x)
    rw [actualTargetLeft, ModuleCat.Bimodule.RingChange.ofActions_leftModule F25 M2I M2I]
    letI : Module F5 M2F := originalTargetLeft
    ext i j
    exact secondActingReduction.map_mul r (x i j)
  · intro s x
    change secondOuterReduction ((ModuleCat.Bimodule.RingChange.rightModule F25 M2I
        (ModuleCat.Bimodule.RingChange.ofActions F25 M2I M2I)).smul s x) =
      (ModuleCat.Bimodule.RingChange.rightModule F5 M2F
        targetCoefficient).smul
          (secondOuterReduction.op s) (secondOuterReduction x)
    rw [actualTargetRight, ModuleCat.Bimodule.RingChange.ofActions_rightModule F25 M2I M2I]
    change secondOuterReduction (x * s.unop) =
      secondOuterReduction x * secondOuterReduction s.unop
    exact secondOuterReduction.map_mul x s.unop

abbrev intermediateInput : ModuleCat.{0} F25ᵐᵒᵖ := ModuleCat.of F25ᵐᵒᵖ F25ᵐᵒᵖ

def firstInputReduction : sourceInput →ₛₗ[firstActingReduction.op] intermediateInput where
  toFun := firstActingReduction.op
  map_add' := firstActingReduction.op.map_add
  map_smul' r x := firstActingReduction.op.map_mul r x

def secondInputReduction : intermediateInput →ₛₗ[secondActingReduction.op] targetInput where
  toFun := secondActingReduction.op
  map_add' := secondActingReduction.op.map_add
  map_smul' r x := secondActingReduction.op.map_mul r x

def compositeCoefficientReduction :=
  composeCoefficientSemilinear ℤ M2Z firstActingReduction firstOuterReduction
    secondActingReduction secondOuterReduction sourceCoefficient intermediateCoefficient
    targetCoefficient firstCoefficientReduction secondCoefficientReduction

def compositeInputReduction :=
  composeInputSemilinear ℤ firstActingReduction secondActingReduction sourceInput
    intermediateInput targetInput firstInputReduction secondInputReduction

end ThreeRings

section WorkingWorlds


abbrev sourceTorAt.{h} (n : ℕ) : ModuleCat.{h} M2Zᵐᵒᵖ :=
  ((torCoefficientFunctorAt.{h, 0, 0, 0, 0} ℤ M2Z n).obj sourceCoefficient).obj sourceInput

abbrev intermediateTorAt.{h} (n : ℕ) : ModuleCat.{h} M2Iᵐᵒᵖ :=
  ((torCoefficientFunctorAt.{h, 0, 0, 0, 0} F25 M2I n).obj intermediateCoefficient).obj
    intermediateInput

abbrev targetTorAt.{h} (n : ℕ) : ModuleCat.{h} M2Fᵐᵒᵖ :=
  ((torCoefficientFunctorAt.{h, 0, 0, 0, 0} F5 M2F n).obj targetCoefficient).obj targetInput

abbrev liftedSourceCoefficient.{h} :=
  (ModuleCat.uliftFunctor.{h, 0} (ℤ ⊗[ℤ] M2Zᵐᵒᵖ)).obj sourceCoefficient
abbrev liftedTargetCoefficient.{h} :=
  (ModuleCat.uliftFunctor.{h, 0} (F5 ⊗[ℤ] M2Fᵐᵒᵖ)).obj targetCoefficient
abbrev liftedSourceInput.{h} := (ModuleCat.uliftFunctor.{h, 0} ℤᵐᵒᵖ).obj sourceInput
abbrev liftedTargetInput.{h} := (ModuleCat.uliftFunctor.{h, 0} F5ᵐᵒᵖ).obj targetInput

abbrev targetTensorAt.{h} : ModuleCat.{h} M2Fᵐᵒᵖ :=
  ((tensorCoefficientFunctorAt.{h, 0, 0, 0, 0} F5 M2F).obj targetCoefficient).obj targetInput

def firstMapAt.{h} (n : ℕ) :=
  torRingChangeMapAt.{h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ M2Z
    firstActingReduction firstOuterReduction sourceCoefficient intermediateCoefficient
    firstCoefficientReduction sourceInput intermediateInput firstInputReduction n

def secondMapAt.{h} (n : ℕ) :=
  torRingChangeMapAt.{h, 0, 0, 0, 0, 0, 0, 0, 0} F25 M2I
    secondActingReduction secondOuterReduction intermediateCoefficient targetCoefficient
    secondCoefficientReduction intermediateInput targetInput secondInputReduction n

def compositeMapAt.{h} (n : ℕ) :=
  torRingChangeMapAt.{h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ M2Z
    (secondActingReduction.comp firstActingReduction)
    (secondOuterReduction.comp firstOuterReduction) sourceCoefficient targetCoefficient
    compositeCoefficientReduction sourceInput targetInput compositeInputReduction n

def twoStepMapAt.{h} (n : ℕ) :
    sourceTorAt.{h} n ⟶
      (ModuleCat.restrictScalars (secondOuterReduction.comp firstOuterReduction).op).obj
        (targetTorAt.{h} n) :=
  firstMapAt.{h} n ≫ (ModuleCat.restrictScalars firstOuterReduction.op).map
    (secondMapAt.{h} n) ≫
    (ModuleCat.restrictScalarsComp' firstOuterReduction.op secondOuterReduction.op
      (secondOuterReduction.comp firstOuterReduction).op (by ext s; rfl)).inv.app
        (targetTorAt.{h} n)

/-- The real ℤ→ℤ/25→ℤ/5 and matrix reductions directly instantiate canonical Tor composition. -/
theorem two_step_equals_composite.{h} (n : ℕ) :
    twoStepMapAt.{h} n = compositeMapAt.{h} n := by
  exact torRingChangeMapAt_comp.{h, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    ℤ M2Z firstActingReduction firstOuterReduction secondActingReduction secondOuterReduction
    sourceCoefficient intermediateCoefficient targetCoefficient firstCoefficientReduction
    secondCoefficientReduction sourceInput intermediateInput targetInput firstInputReduction
    secondInputReduction n

def sourceHeightIso.{h, q} (n : ℕ) :=
  coefficientTorHeightIsoAt.{q, h, 0, 0, 0, 0} ℤ M2Z sourceCoefficient n

def targetHeightIso.{h, q} (n : ℕ) :=
  coefficientTorHeightIsoAt.{q, h, 0, 0, 0, 0} F5 M2F targetCoefficient n

/-- The actual composite ring map directly instantiates the height cube, in every degree.
Both working worlds contain all three acting rings; no outer-ring projectivity is used. -/
theorem two_step_height.{h, q} (n : ℕ) :
    twoStepMapAt.{max h q} n ≫
        (ModuleCat.restrictScalars (secondOuterReduction.comp firstOuterReduction).op).map
          ((targetHeightIso.{h, q} n).inv.app targetInput) ≫
        (ModuleCat.uliftRestrictionIso.{q, h, 0, 0}
          (secondOuterReduction.comp firstOuterReduction).op).inv.app (targetTorAt.{h} n) =
      (sourceHeightIso.{h, q} n).inv.app sourceInput ≫
        (ModuleCat.uliftFunctor.{max h q, h} M2Zᵐᵒᵖ).map (twoStepMapAt.{h} n) := by
  rw [two_step_equals_composite, two_step_equals_composite]
  exact torRingChangeMapAt_height_inverse.{q, h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ M2Z
    (secondActingReduction.comp firstActingReduction)
    (secondOuterReduction.comp firstOuterReduction) sourceCoefficient targetCoefficient
    compositeCoefficientReduction sourceInput targetInput compositeInputReduction n

def seedAt.{h} : sourceTorAt.{h} 0 :=
  ((coefficientTorZeroIsoAt.{h, 0, 0, 0, 0} ℤ M2Z sourceCoefficient).inv.app sourceInput).hom
    (pairing ℤ M2Z liftedSourceCoefficient.{h} liftedSourceInput.{h}
      (ULift.up (op (1 : ℤ))) (ULift.up (1 : sourceCoefficient)))

private theorem seedAt_zero_image.{h} :
    ((coefficientTorZeroIsoAt.{h, 0, 0, 0, 0} ℤ M2Z sourceCoefficient).hom.app sourceInput).hom
        seedAt.{h} =
      pairing ℤ M2Z liftedSourceCoefficient.{h} liftedSourceInput.{h}
        (ULift.up (op (1 : ℤ))) (ULift.up (1 : sourceCoefficient)) :=
  ConcreteCategory.congr_hom
    ((coefficientTorZeroIsoAt.{h, 0, 0, 0, 0} ℤ M2Z sourceCoefficient).app sourceInput).inv_hom_id
      (pairing ℤ M2Z liftedSourceCoefficient.{h} liftedSourceInput.{h}
        (ULift.up (op (1 : ℤ))) (ULift.up (1 : sourceCoefficient)))

private theorem composite_seed_imageAt.{h} :
    ((coefficientTorZeroIsoAt.{h, 0, 0, 0, 0} F5 M2F targetCoefficient).hom.app targetInput).hom
        ((compositeMapAt.{h} 0).hom seedAt.{h}) =
      pairing F5 M2F liftedTargetCoefficient.{h} liftedTargetInput.{h}
        (ULift.up (op (1 : F5))) (ULift.up (1 : targetCoefficient)) := by
  have h := ConcreteCategory.congr_hom
    (torRingChangeMapAt_zero.{h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ M2Z
      (secondActingReduction.comp firstActingReduction)
      (secondOuterReduction.comp firstOuterReduction) sourceCoefficient targetCoefficient
      compositeCoefficientReduction sourceInput targetInput compositeInputReduction) seedAt.{h}
  change _ =
    (tensorRingChangeMapAt.{h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ M2Z
      (secondActingReduction.comp firstActingReduction)
      (secondOuterReduction.comp firstOuterReduction) sourceCoefficient targetCoefficient
      compositeCoefficientReduction sourceInput targetInput compositeInputReduction).hom
      (((coefficientTorZeroIsoAt.{h, 0, 0, 0, 0} ℤ M2Z sourceCoefficient).hom.app sourceInput).hom
        seedAt.{h}) at h
  rw [seedAt_zero_image, tensorRingChangeMapAt_pairing] at h
  have hf : compositeCoefficientReduction (1 : sourceCoefficient) = (1 : targetCoefficient) := by
    change secondOuterReduction (firstOuterReduction (1 : M2Z)) = (1 : M2F)
    rw [firstOuterReduction.map_one, secondOuterReduction.map_one]
  have hg : compositeInputReduction (op (1 : ℤ)) = op (1 : F5) := by
    change secondActingReduction.op (firstActingReduction.op (op (1 : ℤ))) = op (1 : F5)
    exact (congrArg secondActingReduction.op (congrArg op firstActingReduction.map_one)).trans
      (congrArg op secondActingReduction.map_one)
  rw [hf, hg] at h
  exact h

def tensorDownAt.{h} : targetTensorAt.{h} →+ targetTensor := by
  letI := coefficientLeftModule F5 M2F liftedTargetCoefficient.{h}
  letI := coefficientRightModule F5 M2F liftedTargetCoefficient.{h}
  letI := coefficientActionsCommute F5 M2F liftedTargetCoefficient.{h}
  letI := coefficientLeftModule F5 M2F targetCoefficient
  letI := coefficientRightModule F5 M2F targetCoefficient
  letI := coefficientActionsCommute F5 M2F targetCoefficient
  exact (TensorProduct.Balanced.map
    (ULift.moduleEquiv : ULift.{h} targetInput ≃ₗ[ℤ] targetInput).toLinearMap
    (ULift.moduleEquiv : ULift.{h} targetCoefficient ≃ₗ[ℤ] targetCoefficient).toLinearMap
    (fun _ _ => rfl) (fun _ _ => rfl)).toAddMonoidHom

def evaluateAt.{h} : targetTensorAt.{h} →+ targetCoefficient :=
  evaluate.comp tensorDownAt.{h}

private theorem evaluateAt_unit_pairing.{h} (y : liftedTargetCoefficient.{h}) :
    evaluateAt.{h}
      (pairing F5 M2F liftedTargetCoefficient.{h} liftedTargetInput.{h}
        (ULift.up (op (1 : F5))) y) = y.down := by
  change evaluate (pairing F5 M2F targetCoefficient targetInput (op (1 : F5)) y.down) = y.down
  exact evaluate_unit_pairing y.down

private theorem lifted_target_pairing_smul.{h} (s : M2Fᵐᵒᵖ)
    (x : liftedTargetInput.{h}) (y : liftedTargetCoefficient.{h}) :
    ((ModuleCat.Bimodule.Tensor.functor F5 M2F liftedTargetCoefficient.{h}).obj
      liftedTargetInput.{h}).isModule.smul s
      (pairing F5 M2F liftedTargetCoefficient.{h} liftedTargetInput.{h} x y) =
      pairing F5 M2F liftedTargetCoefficient.{h} liftedTargetInput.{h} x
        (ULift.up (y.down * s.unop)) := by
  letI := coefficientLeftModule F5 M2F liftedTargetCoefficient.{h}
  letI := coefficientRightModule F5 M2F liftedTargetCoefficient.{h}
  letI := coefficientActionsCommute F5 M2F liftedTargetCoefficient.{h}
  have hLow : (ModuleCat.Bimodule.RingChange.rightModule F5 M2F targetCoefficient).smul s y.down =
      y.down * s.unop := congrArg (fun d : Module M2Fᵐᵒᵖ M2F => d.smul s y.down) actualTargetRight
  have hLift : (coefficientRightModule F5 M2F liftedTargetCoefficient.{h}).smul s y =
      ULift.up ((ModuleCat.Bimodule.RingChange.rightModule F5 M2F targetCoefficient).smul s y.down) := rfl
  have hy := hLift.trans (congrArg ULift.up hLow)
  have h := TensorProduct.Balanced.rightModule_smul_mk ℤ F5 M2F
    liftedTargetInput.{h} liftedTargetCoefficient.{h} s x y
  exact h.trans (congrArg (pairing F5 M2F liftedTargetCoefficient.{h} liftedTargetInput.{h} x) hy)

def orderedClassAt.{h} (s t : M2Z) : sourceTorAt.{h} 0 :=
  op s • (op t • seedAt.{h})

/-- Canonical comparison through both real residue rings detects the ordered matrix product
in every working universe, rather than relying on vanishing target Tor. -/
theorem composite_ordered_valueAt.{h} (s t : M2Z) :
    evaluateAt.{h}
      (((coefficientTorZeroIsoAt.{h, 0, 0, 0, 0} F5 M2F targetCoefficient).hom.app targetInput).hom
        ((compositeMapAt.{h} 0).hom (orderedClassAt.{h} s t))) =
      outerReduction (t * s) := by
  let c := torRingChangeSemilinearMapAt.{h, 0, 0, 0, 0, 0, 0, 0, 0} ℤ M2Z
    (secondActingReduction.comp firstActingReduction)
    (secondOuterReduction.comp firstOuterReduction) sourceCoefficient targetCoefficient
    compositeCoefficientReduction sourceInput targetInput compositeInputReduction 0
  let q := (coefficientTorZeroIsoAt.{h, 0, 0, 0, 0} F5 M2F targetCoefficient).hom.app targetInput
  let j := (nativeTensorFunctorIso F5 M2F liftedTargetCoefficient.{h}).inv.app liftedTargetInput.{h}
  let O := (ModuleCat.Bimodule.Tensor.functor F5 M2F liftedTargetCoefficient.{h}).obj liftedTargetInput.{h}
  let rS := (secondOuterReduction.comp firstOuterReduction).op (op s)
  let rT := (secondOuterReduction.comp firstOuterReduction).op (op t)
  let w := pairing F5 M2F liftedTargetCoefficient.{h} liftedTargetInput.{h}
    (ULift.up (op (1 : F5))) (ULift.up (1 : targetCoefficient))
  have hCt := c.map_smul' (op t) seedAt.{h}
  have hCs := c.map_smul' (op s) ((sourceTorAt.{h} 0).isModule.smul (op t) seedAt.{h})
  have hC : c (orderedClassAt.{h} s t) =
      (targetTorAt.{h} 0).isModule.smul rS ((targetTorAt.{h} 0).isModule.smul rT (c seedAt.{h})) :=
    hCs.trans (congrArg ((targetTorAt.{h} 0).isModule.smul rS) hCt)
  have hZs := q.hom.map_smul' rS ((targetTorAt.{h} 0).isModule.smul rT (c seedAt.{h}))
  have hZt := q.hom.map_smul' rT (c seedAt.{h})
  have hSeed : q.hom (c seedAt.{h}) = w := composite_seed_imageAt.{h}
  have hZ : q.hom (c (orderedClassAt.{h} s t)) =
      (targetTensorAt.{h}).isModule.smul rS ((targetTensorAt.{h}).isModule.smul rT w) :=
    (congrArg q.hom hC).trans (hZs.trans
      (congrArg ((targetTensorAt.{h}).isModule.smul rS) (hZt.trans
        (congrArg ((targetTensorAt.{h}).isModule.smul rT) hSeed))))
  have hJ := j.hom.map_smul' rS ((targetTensorAt.{h}).isModule.smul rT w)
  have hJt := nativeTensorFunctorIso_inv_smul_pairing F5 M2F liftedTargetCoefficient.{h}
    liftedTargetInput.{h} rT (ULift.up (op (1 : F5))) (ULift.up (1 : targetCoefficient))
  have hPairt := lifted_target_pairing_smul.{h} rT (ULift.up (op (1 : F5)))
    (ULift.up (1 : targetCoefficient))
  have hPairs := lifted_target_pairing_smul.{h} rS (ULift.up (op (1 : F5)))
    (ULift.up ((1 : targetCoefficient) * rT.unop))
  have hResult : j.hom (q.hom (c (orderedClassAt.{h} s t))) =
      pairing F5 M2F liftedTargetCoefficient.{h} liftedTargetInput.{h}
        (ULift.up (op (1 : F5)))
        (ULift.up (((1 : targetCoefficient) * rT.unop) * rS.unop)) :=
    (congrArg j.hom hZ).trans (hJ.trans
      ((congrArg (O.isModule.smul rS) hJt).trans
        ((congrArg (O.isModule.smul rS) hPairt).trans hPairs)))
  have hValue := congrArg evaluateAt.{h} hResult
  change evaluateAt.{h} (j.hom (q.hom (c (orderedClassAt.{h} s t)))) = _
  exact hValue.trans ((evaluateAt_unit_pairing.{h} _).trans (by
    change ((1 : M2F) * (secondOuterReduction.comp firstOuterReduction) t) *
      (secondOuterReduction.comp firstOuterReduction) s = outerReduction (t * s)
    rw [one_mul, ← (secondOuterReduction.comp firstOuterReduction).map_mul, outerReduction_comp]))

/-- This actual two-step Tor composite has nonzero ordered images in every working world. -/
theorem two_step_outer_order_survives.{h} :
    (twoStepMapAt.{h} 0).hom (orderedClassAt.{h} upper lower) ≠
      (twoStepMapAt.{h} 0).hom (orderedClassAt.{h} lower upper) := by
  rw [two_step_equals_composite]
  intro h
  have h' := congrArg (fun x =>
    evaluateAt.{h} (((coefficientTorZeroIsoAt.{h, 0, 0, 0, 0} F5 M2F targetCoefficient).hom.app
      targetInput).hom x)) h
  rw [composite_ordered_valueAt, composite_ordered_valueAt] at h'
  exact reduced_products_differ h'.symm

/-- The height square is exercised on nonzero ordered two-step images. The actual target
height/output-restriction comparison is an iso, so the distinction survives transport. -/
theorem height_then_two_step_outer_order_survives.{h, q} :
    ((sourceHeightIso.{h, q} 0).inv.app sourceInput ≫
        (ModuleCat.uliftFunctor.{max h q, h} M2Zᵐᵒᵖ).map (twoStepMapAt.{h} 0)).hom
      (orderedClassAt.{max h q} upper lower) ≠
    ((sourceHeightIso.{h, q} 0).inv.app sourceInput ≫
        (ModuleCat.uliftFunctor.{max h q, h} M2Zᵐᵒᵖ).map (twoStepMapAt.{h} 0)).hom
      (orderedClassAt.{max h q} lower upper) := by
  rw [← two_step_height]
  let e :=
    (Functor.mapIso (ModuleCat.restrictScalars.{max h q}
        (secondOuterReduction.comp firstOuterReduction).op)
      ((targetHeightIso.{h, q} 0).app targetInput).symm) ≪≫
    ((ModuleCat.uliftRestrictionIso.{q, h, 0, 0}
      (secondOuterReduction.comp firstOuterReduction).op).app (targetTorAt.{h} 0)).symm
  intro hEq
  let x₀ := (twoStepMapAt.{max h q} 0).hom (orderedClassAt.{max h q} upper lower)
  let x₁ := (twoStepMapAt.{max h q} 0).hom (orderedClassAt.{max h q} lower upper)
  change e.hom.hom x₀ = e.hom.hom x₁ at hEq
  have h := congrArg (fun x => e.inv.hom x) hEq
  have hx : e.inv.hom (e.hom.hom x₀) = x₀ :=
    ConcreteCategory.congr_hom e.hom_inv_id x₀
  have hy : e.inv.hom (e.hom.hom x₁) = x₁ :=
    ConcreteCategory.congr_hom e.hom_inv_id x₁
  rw [hx, hy] at h
  exact two_step_outer_order_survives.{max h q} h

end WorkingWorlds

end MathlibExtTest.Bimodule.TorScalarChangeMatrixCoherence
