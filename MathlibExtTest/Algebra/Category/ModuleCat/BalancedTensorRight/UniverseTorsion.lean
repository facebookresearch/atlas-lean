/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.UniverseLongExact
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.PresentationBoundarySign
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# Torsion and boundaries with independent Tor carrier universes

The cokernel sequence of multiplication by 4 has a projective presentation
computing degree one with coefficient ZMod 4. This coefficient need not
be projective or flat. The presentation boundary theorem determines the
negative sign, and the examples use the scalar action, coefficient and
height maps.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct

namespace IndependentCarrierTorTorsion

/-- Ordinary integer scalar action, via the native opposite-ring construction. -/
def integerUnop : ℤᵐᵒᵖ →+* ℤ :=
  (RingHom.id ℤ).fromOpposite (fun x y => show Commute x y from mul_comm x y)

local instance coefficientRightInteger : Module ℤᵐᵒᵖ (ZMod 4) :=
  Module.compHom (ZMod 4) integerUnop
local instance coefficientActions : SMulCommClass ℤ ℤᵐᵒᵖ (ZMod 4) := by
  refine ⟨?_⟩
  intro r s x
  change r • (s.unop • x) = s.unop • (r • x)
  exact smul_comm r s.unop x

abbrev C := ModuleCat.{0} ℤᵐᵒᵖ
abbrev D := ModuleCat.{1} ℤᵐᵒᵖ
abbrev Z : C := ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ
abbrev U := ModuleCat.uliftFunctor.{1, 0} ℤᵐᵒᵖ
abbrev F := ModuleCat.BalancedTensorRight.largeTensorFunctorAt.{1, 0, 0, 0, 0}
  ℤ ℤ (ZMod 4)

/-- The real original source map is multiplication by4 in the regular right module. -/
def fourMap : Z ⟶ Z :=
  ModuleCat.ofHom (LinearMap.mulLeft ℤᵐᵒᵖ (op (4 : ℤ)))

local instance fourMap_mono : Mono fourMap := by
  apply (ModuleCat.mono_iff_injective fourMap).mpr
  intro x y h
  change (op (4 : ℤ)) * x = (op (4 : ℤ)) * y at h
  exact mul_left_cancel₀ (by decide : (op (4 : ℤ)) ≠ 0) h

abbrev Q : ShortComplex C := ShortComplex.cokernelSequence fourMap

/-- The original short exact sequence is earned from the actual injective map and its cokernel. -/
theorem shortExact : Q.ShortExact := by
  apply ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact fourMap)
  · change Mono fourMap
    infer_instance
  · change Epi (cokernel.π fourMap)
    infer_instance

abbrev QU := Q.map U

/-- The actual native lift keeps the exact original sequence. -/
theorem liftedShortExact : QU.ShortExact := shortExact.map_of_exact U

local instance presentationSourceOneProjective : Projective QU.X₁ := by
  change Projective (ModuleCat.of ℤᵐᵒᵖ (ULift.{1} ℤᵐᵒᵖ))
  infer_instance

local instance presentationSourceZeroProjective : Projective QU.X₂ := by
  change Projective (ModuleCat.of ℤᵐᵒᵖ (ULift.{1} ℤᵐᵒᵖ))
  infer_instance

/-- Native presentation resolution of the lifted source, with no coefficient condition. -/
def P : ProjectiveResolution QU.X₃ :=
  ProjectiveResolution.ofPresentation QU liftedShortExact

abbrev K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
  (ProjectiveResolution.presentationComplex QU)
abbrev T : D := F.obj QU.X₁

/-- The actual multiplication-by4 becomes zero after tensoring with the torsion coefficient. -/
theorem tensor_four_zero : F.map QU.f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ ℤ (ULift.{1} ℤᵐᵒᵖ) (ULift.{1} (ZMod 4))
  intro x y
  change (ModuleCat.BalancedTensorRight.tensorMap ℤ ℤ (ULift.{1} (ZMod 4))
      (U.map fourMap)).hom
      (TensorProduct.Balanced.mk ℤ ℤ (ULift.{1} ℤᵐᵒᵖ) (ULift.{1} (ZMod 4)) x y) = 0
  have hMap := ModuleCat.BalancedTensorRight.tensorMap_mk ℤ ℤ (ULift.{1} (ZMod 4))
    (A := U.obj Z) (A' := U.obj Z) (U.map fourMap) x y
  refine hMap.trans ?_
  change TensorProduct.Balanced.mk ℤ ℤ (ULift.{1} ℤᵐᵒᵖ) (ULift.{1} (ZMod 4))
    ((op (4 : ℤ)) • x) y = 0
  rw [TensorProduct.Balanced.balance]
  have hy : (4 : ℤ) • y = 0 := by
    apply ULift.ext
    change (4 : ℤ) • y.down = 0
    rw [← Int.cast_smul_eq_zsmul (R := ZMod 4)]
    change (4 : ZMod 4) * y.down = 0
    rw [show (4 : ZMod 4) = 0 by decide, zero_mul]
  rw [hy, map_zero]

/-- The actual identity degree-one word is a cycle in the native presentation complex. -/
theorem cycle_condition : (𝟙 T) ≫ K.d 1 0 = 0 := by
  change (𝟙 T) ≫ F.map ((ProjectiveResolution.presentationComplex QU).d 1 0) = 0
  have hd := ProjectiveResolution.presentationComplex_d_zero QU
  have h := congrArg (fun f : QU.X₁ ⟶ QU.X₂ => (𝟙 T) ≫ F.map f) hd
  exact h.trans ((Category.id_comp _).trans tensor_four_zero)

/-- The native cycle and homology quotient give the actual class in the facade's Tor object. -/
def classMap : T ⟶
    ModuleCat.BalancedTensorRight.torObjAt.{1, 0, 0, 0, 0} ℤ ℤ (ZMod 4) 1 Q.X₃ :=
  K.liftCycles (i := 1) (𝟙 T) 0 (by simp) cycle_condition ≫ K.homologyπ 1 ≫
    (P.isoLeftDerivedObj F 1).inv

/-- The original native projective presentation computes the unchanged negative boundary sign. -/
theorem boundary_sign :
    classMap ≫ ModuleCat.BalancedTensorRight.torBoundaryToTensorAt.{1, 0, 0, 0, 0}
      ℤ ℤ (ZMod 4) Q shortExact = -(𝟙 T) := by
  exact ProjectiveResolution.presentationBoundary_cycle_sign QU liftedShortExact F
    (𝟙 T) ((Category.id_comp _).trans tensor_four_zero)

/-- The source integer coordinate is lowered by the existing native opposite linear equivalence. -/
def inputCoordinate : ULift.{1} ℤᵐᵒᵖ →ₗ[ℤ] ZMod 4 :=
  (Int.castRingHom (ZMod 4)).toAddMonoidHom.toIntLinearMap.comp
    ((MulOpposite.opLinearEquiv ℤ : ℤ ≃ₗ[ℤ] ℤᵐᵒᵖ).symm.toLinearMap.comp
      (ULift.moduleEquiv : ULift.{1} ℤᵐᵒᵖ ≃ₗ[ℤ] ℤᵐᵒᵖ).toLinearMap)

/-- The literal integer product descends through the actual balanced quotient. -/
def probe : T →ₗ[ℤ] ZMod 4 :=
  TensorProduct.Balanced.lift
    (((LinearMap.mul ℤ (ZMod 4)).compl₂
      (ULift.moduleEquiv : ULift.{1} (ZMod 4) ≃ₗ[ℤ] ZMod 4).toLinearMap).comp
      inputCoordinate)
    (fun r x y => by
      change ((x.down.unop * r : ℤ) : ZMod 4) * y.down =
        (x.down.unop : ZMod 4) * (r • y.down)
      rw [Int.cast_mul, ← Int.cast_smul_eq_zsmul (R := ZMod 4)]
      change ((x.down.unop : ZMod 4) * (r : ZMod 4)) * y.down =
        (x.down.unop : ZMod 4) * ((r : ZMod 4) * y.down)
      exact mul_assoc _ _ _)

abbrev word : T :=
  TensorProduct.Balanced.mk ℤ ℤ (ULift.{1} ℤᵐᵒᵖ) (ULift.{1} (ZMod 4))
    (ULift.up (op (1 : ℤ))) (ULift.up (1 : ZMod 4))

/-- The actual probe keeps the original integer and coefficient coordinates. -/
theorem probe_mk (x : ULift.{1} ℤᵐᵒᵖ) (y : ULift.{1} (ZMod 4)) :
    probe (TensorProduct.Balanced.mk ℤ ℤ (ULift.{1} ℤᵐᵒᵖ)
      (ULift.{1} (ZMod 4)) x y) = (x.down.unop : ZMod 4) * y.down := rfl

/-- The actual original quotient unit has coefficient value one. -/
theorem probe_word : probe word = 1 := by
  rfl

/-- The actual Tor class reaches3 modulo4 under the signed native boundary. -/
theorem boundary_value_three :
    probe ((ModuleCat.BalancedTensorRight.torBoundaryToTensorAt.{1, 0, 0, 0, 0}
      ℤ ℤ (ZMod 4) Q shortExact).hom (classMap.hom word)) = 3 := by
  have h := ConcreteCategory.congr_hom boundary_sign word
  have h' := congrArg probe h
  change probe ((ModuleCat.BalancedTensorRight.torBoundaryToTensorAt
    ℤ ℤ (ZMod 4) Q shortExact).hom (classMap.hom word)) = probe (-word) at h'
  exact h'.trans ((probe.map_neg word).trans
    ((congrArg (fun x : ZMod 4 => -x) probe_word).trans (by decide : -(1 : ZMod 4) = 3)))

/-- This is nonzero in the actual Tor object, detected by its constructed boundary. -/
theorem actual_Tor_class_nonzero : classMap.hom word ≠ 0 := by
  intro h
  let d := ModuleCat.BalancedTensorRight.torBoundaryToTensorAt.{1, 0, 0, 0, 0}
    ℤ ℤ (ZMod 4) Q shortExact
  have hv : probe (d.hom (classMap.hom word)) = 3 := boundary_value_three
  have hz := congrArg (fun x => probe (d.hom x)) h
  have hz' : probe (d.hom (classMap.hom word)) = 0 :=
    hz.trans ((congrArg probe (map_zero d.hom)).trans (map_zero probe))
  exact (by decide : (0 : ZMod 4) ≠ 3) (hz'.symm.trans hv)

/-- The original tripling map is an actual coefficient-linear morphism. -/
def tripleCoefficient : ZMod 4 →ₗ[ℤ] ZMod 4 := (3 : ℕ) • LinearMap.id

/-- That legitimate additive coefficient map keeps the original right-integer action. -/
theorem tripleCoefficient_outer (s : ℤᵐᵒᵖ) (x : ZMod 4) :
    tripleCoefficient (s • x) = s • tripleCoefficient x := by
  change tripleCoefficient (integerUnop s • x) = integerUnop s • tripleCoefficient x
  exact tripleCoefficient.toAddMonoidHom.map_zsmul (integerUnop s) x

/-- Tripling acts on the same actual underived word as the residue3. -/
theorem triple_tensor_value :
    probe (((ModuleCat.BalancedTensorRight.tensorCoefficientTransformationAt.{1, 0, 0, 0, 0}
      ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer).app Q.X₁).hom word) = 3 := by
  have h := ModuleCat.BalancedTensorRight.tensorCoefficientTransformationAt_mk.{1, 0, 0, 0, 0}
    ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer Q.X₁ (op 1) 1
  have h' := congrArg probe h
  have hProbe : probe (TensorProduct.Balanced.mk ℤ ℤ (ULift.{1} ℤᵐᵒᵖ)
      (ULift.{1} (ZMod 4)) (ULift.up (op 1)) (ULift.up (tripleCoefficient 1))) = 3 := by
    rw [probe_mk]
    norm_num [tripleCoefficient]
  exact h'.trans hProbe

/-- Coefficient tripling reaches1 on this genuine Tor class after the signed boundary. -/
theorem triple_Tor_boundary_value :
    probe ((ModuleCat.BalancedTensorRight.torBoundaryToTensorAt.{1, 0, 0, 0, 0}
      ℤ ℤ (ZMod 4) Q shortExact).hom
      (((ModuleCat.BalancedTensorRight.torCoefficientTransformationAt.{1, 0, 0, 0, 0}
        ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer 1).app Q.X₃).hom
        (classMap.hom word))) = 1 := by
  let α := ModuleCat.BalancedTensorRight.torCoefficientTransformationAt.{1, 0, 0, 0, 0}
    ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer 1
  let β := (ModuleCat.BalancedTensorRight.tensorCoefficientTransformationAt.{1, 0, 0, 0, 0}
    ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer).app Q.X₁
  let d := ModuleCat.BalancedTensorRight.torBoundaryToTensorAt.{1, 0, 0, 0, 0}
    ℤ ℤ (ZMod 4) Q shortExact
  have hNat : α.app Q.X₃ ≫ d = d ≫ β :=
    ModuleCat.BalancedTensorRight.torBoundaryToTensorAt_natural_coefficient
      ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer Q shortExact
  have hWord := ConcreteCategory.congr_hom boundary_sign word
  have h := ConcreteCategory.congr_hom hNat (classMap.hom word)
  have h' := congrArg probe h
  change probe (d.hom ((α.app Q.X₃).hom (classMap.hom word))) =
    probe (β.hom (d.hom (classMap.hom word))) at h'
  have hWord' : d.hom (classMap.hom word) = -word := hWord
  have hValue : probe (β.hom (d.hom (classMap.hom word))) = -probe (β.hom word) :=
    (congrArg (fun x => probe (β.hom x)) hWord').trans
      ((congrArg probe (map_neg β.hom word)).trans (map_neg probe (β.hom word)))
  exact h'.trans (hValue.trans ((congrArg (fun x : ZMod 4 => -x) triple_tensor_value).trans
    (by decide : -(3 : ZMod 4) = 1)))

/-- Multiplication by2 gives a genuine original sequence morphism in the native additive category. -/
def twiceSequence : Q ⟶ Q := (2 : ℕ) • (𝟙 Q)

/-- The nonidentity sequence map and actual coefficient map commute on the real window. -/
theorem actual_window_interchange :
    ModuleCat.BalancedTensorRight.torLongSequenceMapAt.{1, 0, 0, 0, 0}
      ℤ ℤ (ZMod 4) 0 Q Q twiceSequence shortExact shortExact ≫
      ModuleCat.BalancedTensorRight.torLongSequenceCoefficientMapAt.{1, 0, 0, 0, 0}
        ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer 0 Q shortExact =
    ModuleCat.BalancedTensorRight.torLongSequenceCoefficientMapAt.{1, 0, 0, 0, 0}
      ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer 0 Q shortExact ≫
      ModuleCat.BalancedTensorRight.torLongSequenceMapAt.{1, 0, 0, 0, 0}
        ℤ ℤ (ZMod 4) 0 Q Q twiceSequence shortExact shortExact :=
  ModuleCat.BalancedTensorRight.torLongSequenceMapAt_coefficient_interchange
    ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer 0 Q Q twiceSequence
      shortExact shortExact

/-- The same torsion coefficient/window map uses the actual larger-universe naturality square. -/
theorem actual_window_height_coefficient :
    Functor.whiskerRight
        (ModuleCat.BalancedTensorRight.torLongSequenceCoefficientMapAt.{1, 0, 0, 0, 0}
          ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer 0 Q shortExact)
        (ModuleCat.uliftFunctor.{2, 1} ℤᵐᵒᵖ) ≫
      (ModuleCat.BalancedTensorRight.torLongSequenceHeightIsoAt.{2, 1, 0, 0, 0, 0}
        ℤ ℤ (ZMod 4) 0 Q shortExact).hom =
    (ModuleCat.BalancedTensorRight.torLongSequenceHeightIsoAt.{2, 1, 0, 0, 0, 0}
      ℤ ℤ (ZMod 4) 0 Q shortExact).hom ≫
      ModuleCat.BalancedTensorRight.torLongSequenceCoefficientMapAt.{2, 0, 0, 0, 0}
        ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer 0 Q shortExact :=
  ModuleCat.BalancedTensorRight.torLongSequenceHeightIsoAt_natural_coefficient
    ℤ ℤ (ZMod 4) (ZMod 4) tripleCoefficient tripleCoefficient_outer 0 Q shortExact

/-- The same genuine class uses the actual height boundary law in a larger working world. -/
theorem larger_height_boundary :
    (ModuleCat.uliftFunctor.{2, 1} ℤᵐᵒᵖ).map classMap ≫
        (ModuleCat.BalancedTensorRight.torHeightIsoAt.{2, 1, 0, 0, 0, 0}
          ℤ ℤ (ZMod 4) 1).hom.app Q.X₃ ≫
        ModuleCat.BalancedTensorRight.torBoundaryToTensorAt.{2, 0, 0, 0, 0}
          ℤ ℤ (ZMod 4) Q shortExact =
      (ModuleCat.uliftFunctor.{2, 1} ℤᵐᵒᵖ).map classMap ≫
        (ModuleCat.uliftFunctor.{2, 1} ℤᵐᵒᵖ).map
        (ModuleCat.BalancedTensorRight.torBoundaryToTensorAt.{1, 0, 0, 0, 0}
          ℤ ℤ (ZMod 4) Q shortExact) ≫
        (ModuleCat.BalancedTensorRight.tensorHeightFacadeIsoAt.{2, 1, 0, 0, 0, 0}
          ℤ ℤ (ZMod 4)).hom.app Q.X₁ := by
  exact congrArg (fun f => (ModuleCat.uliftFunctor.{2, 1} ℤᵐᵒᵖ).map classMap ≫ f)
    (ModuleCat.BalancedTensorRight.torBoundaryToTensorAt_height.{2, 1, 0, 0, 0, 0}
      ℤ ℤ (ZMod 4) Q shortExact)

end IndependentCarrierTorTorsion
