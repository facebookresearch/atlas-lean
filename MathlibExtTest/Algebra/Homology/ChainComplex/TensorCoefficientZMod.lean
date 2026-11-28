/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainComplex.TensorCoefficient.LongExact
public import MathlibExt.CategoryTheory.Abelian.Projective.PresentationComplex
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Tactic.FinCases

/-!
# A nonzero coefficient connecting map over ZMod 4

The nonsplit coefficient sequence is `ZMod 2 → ZMod 4 → ZMod 2`, with doubling
and reduction as maps of `ZMod 4`-modules. The two-term chain complex has
differential multiplication by `2`. The quotient-coefficient cycle `1` lifts
to `1` in the middle coefficient module, whose boundary is `2`, the inclusion
of `1`. The connecting map therefore sends its class to the nonzero class `1`
in `ZMod 2`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ZeroObject

namespace MathlibExtTest.TensorCoefficientZMod

abbrev Ring := ZMod 4

def reduction : Ring →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

instance binaryModule : Module Ring (ZMod 2) := Module.compHom (ZMod 2) reduction

abbrev binary : ModuleCat.{0} Ring := ModuleCat.of Ring (ZMod 2)
abbrev regular : ModuleCat.{0} Ring := ModuleCat.of Ring Ring

def doubledInteger : ℤ →+ Ring where
  toFun z := z • (2 : Ring)
  map_zero' := zero_zsmul _
  map_add' := fun x y => add_zsmul (2 : Ring) x y

def doubledIntegerKilled : {f : ℤ →+ Ring // f 2 = 0} :=
  ⟨doubledInteger, by
    change (2 : ℤ) • (2 : Ring) = 0
    norm_num
    exact (by decide : (4 : Ring) = 0)⟩

/-- The actual doubling injection, with A-linearity earned from native ZMod linearization. -/
abbrev inclusion : binary ⟶ regular :=
  ModuleCat.ofHom ((ZMod.lift 2 doubledIntegerKilled).toZModLinearMap 4)

/-- Reduction modulo two, with the same actual original A-scalar action. -/
abbrev quotient : regular ⟶ binary :=
  ModuleCat.ofHom (reduction.toAddMonoidHom.toZModLinearMap 4)

theorem inclusion_zero : inclusion.hom (0 : ZMod 2) = 0 := map_zero _

theorem inclusion_one : inclusion.hom (1 : ZMod 2) = 2 := by
  change ZMod.lift 2 doubledIntegerKilled ((1 : ℤ) : ZMod 2) = 2
  rw [ZMod.lift_coe]
  change (1 : ℤ) • (2 : Ring) = 2
  exact one_zsmul _

theorem quotient_one : quotient.hom (1 : Ring) = 1 := map_one reduction
theorem quotient_two : quotient.hom (2 : Ring) = 0 := by
  change reduction (2 : Ring) = 0
  rw [map_ofNat]
  decide

theorem inclusion_quotient : inclusion ≫ quotient = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  fin_cases x
  · change quotient.hom (inclusion.hom (0 : ZMod 2)) = 0
    exact (congrArg quotient.hom inclusion_zero).trans quotient.hom.map_zero
  · change quotient.hom (inclusion.hom (1 : ZMod 2)) = 0
    exact (congrArg quotient.hom inclusion_one).trans quotient_two

/-- The genuine original A-module short complex. -/
abbrev sequence : ShortComplex (ModuleCat.{0} Ring) :=
  ShortComplex.mk inclusion quotient inclusion_quotient

theorem inclusion_injective : Function.Injective inclusion.hom := by
  intro x y h
  fin_cases x <;> fin_cases y
  · rfl
  · change inclusion.hom (0 : ZMod 2) = inclusion.hom (1 : ZMod 2) at h
    have h02 : (0 : Ring) = 2 := inclusion_zero.symm.trans (h.trans inclusion_one)
    exact False.elim ((by decide : (0 : Ring) ≠ 2) h02)
  · change inclusion.hom (1 : ZMod 2) = inclusion.hom (0 : ZMod 2) at h
    have h20 : (2 : Ring) = 0 := inclusion_one.symm.trans (h.trans inclusion_zero)
    exact False.elim ((by decide : (2 : Ring) ≠ 0) h20)
  · rfl

theorem quotient_surjective : Function.Surjective quotient.hom :=
  ZMod.castHom_surjective (by decide : 2 ∣ 4)

/-- The sequence is earned from its actual finite kernel, injection and quotient. -/
theorem sequence_shortExact : sequence.ShortExact where
  exact := by
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact sequence).mpr
    change Function.Exact inclusion.hom quotient.hom
    intro y
    constructor
    · intro hy
      fin_cases y
      · exact ⟨0, inclusion_zero⟩
      · have h : (1 : ZMod 2) = 0 := hy
        exact False.elim (one_ne_zero h)
      · exact ⟨1, inclusion_one⟩
      · have h : (1 : ZMod 2) = 0 := by
          change reduction (3 : Ring) = 0 at hy
          have heq : reduction (3 : Ring) = (1 : ZMod 2) := by decide
          exact heq.symm.trans hy
        exact False.elim (one_ne_zero h)
    · rintro ⟨x, rfl⟩
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom inclusion_quotient) x
  mono_f := (ModuleCat.mono_iff_injective inclusion).mpr inclusion_injective
  epi_g := (ModuleCat.epi_iff_surjective quotient).mpr quotient_surjective

/-- The actual A-linear multiplication-by-two map. -/
abbrev twice : regular ⟶ regular := ModuleCat.ofHom (LinearMap.lsmul Ring Ring (2 : Ring))

/-- Reuse the existing two-term complex constructor without claiming it is a resolution. -/
abbrev originalComplex : ChainComplex (ModuleCat.{0} Ring) ℕ :=
  ProjectiveResolution.presentationComplex
    (ShortComplex.mk twice (0 : regular ⟶ (0 : ModuleCat.{0} Ring)) (by exact comp_zero))

theorem originalComplex_d : originalComplex.d 1 0 = twice :=
  ProjectiveResolution.presentationComplex_d_zero _

theorem originalComplex_terms_flat (n : ℕ) : Module.Flat Ring (originalComplex.X n) := by
  cases n with
  | zero => change Module.Flat Ring Ring; infer_instance
  | succ n =>
    cases n with
    | zero => change Module.Flat Ring Ring; infer_instance
    | succ n =>
      change Module.Flat Ring (0 : ModuleCat.{0} Ring)
      letI : Subsingleton (0 : ModuleCat.{0} Ring) :=
        ModuleCat.subsingleton_of_isZero (isZero_zero (C := ModuleCat.{0} Ring))
      letI : Module.Free Ring (0 : ModuleCat.{0} Ring) := Module.Free.of_subsingleton Ring _
      infer_instance

abbrev binaryComplex := (ChainComplex.TensorCoefficient.functor Ring originalComplex).obj binary
abbrev regularComplex := (ChainComplex.TensorCoefficient.functor Ring originalComplex).obj regular

theorem two_smul_binary (m : ZMod 2) : (2 : Ring) • m = 0 := by
  change reduction (2 : Ring) * m = 0
  rw [show reduction (2 : Ring) = 0 from quotient_two, zero_mul]

/-- After tensoring the actual differential with ZMod2 it is zero, without changing the complex. -/
theorem binaryComplex_d : binaryComplex.d 1 0 = 0 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m a
  change Ring at a
  change (binaryComplex.d 1 0).hom (m ⊗ₜ[Ring] a) = 0
  have h := ChainComplex.TensorCoefficient.differential_tmul Ring originalComplex binary 1 0 m a
  have hd : (originalComplex.d 1 0).hom a = (2 : Ring) * a := by
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom originalComplex_d) a
  have hz : (m ⊗ₜ[Ring] ((2 : Ring) * a)) = 0 := by
    apply (TensorProduct.rid Ring (ZMod 2)).injective
    change ((2 : Ring) * a) • m = 0
    rw [mul_smul, two_smul_binary]
  exact h.trans ((congrArg (fun a : Ring => m ⊗ₜ[Ring] a) hd).trans hz)

/-- The original unit tensor is a nonzero element of the degree-zero coefficient term. -/
theorem binaryUnit_ne_zero : ((1 : ZMod 2) ⊗ₜ[Ring] (1 : Ring)) ≠ 0 := by
  intro h
  have h' := congrArg (TensorProduct.rid Ring (ZMod 2)) h
  have hone : (1 : ZMod 2) = 0 := by
    simpa only [TensorProduct.rid_tmul, one_smul, map_zero] using h'
  exact one_ne_zero hone

/-- The actual source coefficient cycle, represented by the original unit tensor. -/
def quotientCycleMap : regular ⟶ binaryComplex.cycles 1 :=
  binaryComplex.liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton Ring _ ((1 : ZMod 2) ⊗ₜ[Ring] (1 : Ring))))
    0 ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
      (by rw [binaryComplex_d]; exact comp_zero)

def quotientClassMap : regular ⟶ binaryComplex.homology 1 :=
  quotientCycleMap ≫ binaryComplex.homologyπ 1

def quotientClass : binaryComplex.homology 1 := quotientClassMap.hom 1

/-- The actual target coefficient class of 1 in degree zero. -/
def targetClassMap : regular ⟶ binaryComplex.homology 0 :=
  ModuleCat.ofHom
      (LinearMap.toSpanSingleton Ring _ ((1 : ZMod 2) ⊗ₜ[Ring] (1 : Ring))) ≫
    ChainComplex.homologyZeroClass binaryComplex

def targetClass : binaryComplex.homology 0 := targetClassMap.hom 1

/-- Native tensor-unit evaluation, typed on the actual original degree-zero term. -/
def unitEvaluation : binaryComplex.X 0 ⟶ binary := by
  let L : binaryComplex.X 0 →ₗ[Ring] binary :=
    { toFun := fun x => TensorProduct.rid Ring (ZMod 2) x
      map_add' := fun x y => (TensorProduct.rid Ring (ZMod 2)).map_add x y
      map_smul' := fun r x => (TensorProduct.rid Ring (ZMod 2)).map_smul r x }
  exact ModuleCat.ofHom L

/-- The detector retains the actual original tensor-unit formula. -/
theorem unitEvaluation_tmul (m : ZMod 2) (a : Ring) :
    unitEvaluation.hom (m ⊗ₜ[Ring] a) = a • m :=
  TensorProduct.rid_tmul (R := Ring) m a

/-- A genuine detector descends through the original differential cokernel. -/
def targetDetector : binaryComplex.homology 0 ⟶ binary :=
  (ChainComplex.homologyZeroIsoCokernel binaryComplex).hom ≫
    cokernel.desc (binaryComplex.d 1 0) unitEvaluation
      (by rw [binaryComplex_d]; exact zero_comp)

theorem targetDetector_class :
    ChainComplex.homologyZeroClass binaryComplex ≫ targetDetector =
      unitEvaluation := by
  rw [targetDetector, ← Category.assoc,
    ChainComplex.homologyZeroIsoCokernel_class, cokernel.π_desc]

/-- Detection retains the literal nonzero boundary value of the connecting map. -/
theorem targetClass_detection : targetDetector.hom targetClass = 1 := by
  let u : binaryComplex.X 0 := (1 : ZMod 2) ⊗ₜ[Ring] (1 : Ring)
  have hclass : targetClass = (ChainComplex.homologyZeroClass binaryComplex).hom u := by
    change (ChainComplex.homologyZeroClass binaryComplex).hom
      ((LinearMap.toSpanSingleton Ring (binaryComplex.X 0) u) (1 : Ring)) = _
    exact congrArg (ChainComplex.homologyZeroClass binaryComplex).hom
      (LinearMap.toSpanSingleton_apply_one _ _ _)
  have h := congrArg (fun f : binaryComplex.X 0 ⟶ binary => f.hom u) targetDetector_class
  have hu : unitEvaluation.hom u = (1 : ZMod 2) :=
    (unitEvaluation_tmul 1 1).trans (one_smul Ring (1 : ZMod 2))
  exact (congrArg targetDetector.hom hclass).trans (h.trans hu)

theorem targetClass_ne_zero : targetClass ≠ 0 := by
  intro h
  have h1 := targetClass_detection
  rw [h, map_zero] at h1
  exact zero_ne_one h1

private theorem zeroCycle_class (x : regular ⟶ binaryComplex.X 0)
    (hx : x ≫ binaryComplex.d 0 ((ComplexShape.down ℕ).next 0) = 0) :
    binaryComplex.liftCycles x ((ComplexShape.down ℕ).next 0) rfl hx ≫
        binaryComplex.homologyπ 0 =
      x ≫ ChainComplex.homologyZeroClass binaryComplex := by
  apply (cancel_mono binaryComplex.isoHomologyι₀.hom).1
  change (binaryComplex.liftCycles x _ rfl hx ≫ binaryComplex.homologyπ 0) ≫
      binaryComplex.homologyι 0 =
    (x ≫ ChainComplex.homologyZeroClass binaryComplex) ≫ binaryComplex.isoHomologyι₀.hom
  simp only [ChainComplex.homologyZeroClass, Category.assoc,
    HomologicalComplex.homology_π_ι, HomologicalComplex.liftCycles_i_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Compute the native δ using the actual middle lift and its original boundary. -/
theorem connecting_classMap :
    quotientClassMap ≫
        ChainComplex.TensorCoefficient.connecting Ring originalComplex
          originalComplex_terms_flat sequence sequence_shortExact 0 =
      targetClassMap := by
  let x₃ : regular ⟶ binaryComplex.X 1 := ModuleCat.ofHom
    (LinearMap.toSpanSingleton Ring _ ((1 : ZMod 2) ⊗ₜ[Ring] (1 : Ring)))
  let x₂ : regular ⟶ regularComplex.X 1 := ModuleCat.ofHom
    (LinearMap.toSpanSingleton Ring _ ((1 : Ring) ⊗ₜ[Ring] (1 : Ring)))
  let x₁ : regular ⟶ binaryComplex.X 0 := ModuleCat.ofHom
    (LinearMap.toSpanSingleton Ring _ ((1 : ZMod 2) ⊗ₜ[Ring] (1 : Ring)))
  have hx₂ : x₂ ≫ ((ChainComplex.TensorCoefficient.functor Ring originalComplex).map
      quotient).f 1 = x₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    let F := ((ChainComplex.TensorCoefficient.functor Ring originalComplex).map quotient).f 1
    let u : regularComplex.X 1 := (1 : Ring) ⊗ₜ[Ring] (1 : Ring)
    let v : binaryComplex.X 1 := (1 : ZMod 2) ⊗ₜ[Ring] (1 : Ring)
    change F.hom (r • u) = r • v
    have hu : F.hom u = v :=
      (ChainComplex.TensorCoefficient.map_tmul Ring originalComplex quotient 1
        (1 : Ring) (show originalComplex.X 1 from (1 : Ring))).trans
        (congrArg (fun a : ZMod 2 => a ⊗ₜ[Ring] (1 : Ring)) quotient_one)
    exact (F.hom.map_smul r u).trans (congrArg (fun z => r • z) hu)
  have hx₁ : x₁ ≫ ((ChainComplex.TensorCoefficient.functor Ring originalComplex).map
      inclusion).f 0 = x₂ ≫ regularComplex.d 1 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    let F := ((ChainComplex.TensorCoefficient.functor Ring originalComplex).map inclusion).f 0
    let d := regularComplex.d 1 0
    let u : binaryComplex.X 0 := (1 : ZMod 2) ⊗ₜ[Ring] (1 : Ring)
    let v : regularComplex.X 1 := (1 : Ring) ⊗ₜ[Ring] (1 : Ring)
    change F.hom (r • u) = d.hom (r • v)
    have hF : F.hom u = (2 : Ring) ⊗ₜ[Ring] (1 : Ring) :=
      (ChainComplex.TensorCoefficient.map_tmul Ring originalComplex inclusion 0
        (1 : ZMod 2) (show originalComplex.X 0 from (1 : Ring))).trans
        (congrArg (fun a : Ring => a ⊗ₜ[Ring] (1 : Ring)) inclusion_one)
    have hD : d.hom v = (1 : Ring) ⊗ₜ[Ring] (2 : Ring) := by
      have h := ChainComplex.TensorCoefficient.differential_tmul Ring originalComplex regular 1 0
        (1 : Ring) (show originalComplex.X 1 from (1 : Ring))
      have hvalue : (originalComplex.d 1 0).hom
        (show originalComplex.X 1 from (1 : Ring)) =
          (show originalComplex.X 0 from (2 : Ring)) := by
        have hd := congrArg (fun f : regular ⟶ regular => f.hom (1 : Ring)) originalComplex_d
        exact hd.trans (mul_one (2 : Ring))
      exact h.trans (congrArg (fun a : Ring => (1 : Ring) ⊗ₜ[Ring] a) hvalue)
    have hTensor : (2 : Ring) ⊗ₜ[Ring] (1 : Ring) = (1 : Ring) ⊗ₜ[Ring] (2 : Ring) := by
      apply (TensorProduct.rid Ring Ring).injective
      simp only [TensorProduct.rid_tmul, smul_eq_mul, mul_one, one_mul]
    have hu : F.hom u = d.hom v := hF.trans (hTensor.trans hD.symm)
    exact (F.hom.map_smul r u).trans
      ((congrArg (fun z => r • z) hu).trans (d.hom.map_smul r v).symm)
  have h := ChainComplex.TensorCoefficient.connecting_eq Ring originalComplex
    originalComplex_terms_flat sequence sequence_shortExact 0
    x₃ (by change x₃ ≫ binaryComplex.d 1 0 = 0; rw [binaryComplex_d]; exact comp_zero) x₂ hx₂ x₁ hx₁
  exact h.trans (zeroCycle_class x₁ _)

/-- The actual source class has the positive nonzero native boundary class as its image. -/
theorem connecting_quotientClass :
    (ChainComplex.TensorCoefficient.connecting Ring originalComplex
      originalComplex_terms_flat sequence sequence_shortExact 0).hom quotientClass =
        targetClass := by
  exact congrArg (fun f : regular ⟶ binaryComplex.homology 0 => f.hom (1 : Ring))
    connecting_classMap

/-- The connecting morphism is genuinely nonzero, detected through the actual H₀ quotient. -/
theorem connecting_ne_zero :
    ChainComplex.TensorCoefficient.connecting Ring originalComplex
      originalComplex_terms_flat sequence sequence_shortExact 0 ≠ 0 := by
  intro h
  let δ := ChainComplex.TensorCoefficient.connecting Ring originalComplex
    originalComplex_terms_flat sequence sequence_shortExact 0
  have hδ : δ = (0 : binaryComplex.homology 1 ⟶ binaryComplex.homology 0) := h
  have hvalue : δ.hom quotientClass =
      (0 : binaryComplex.homology 1 ⟶ binaryComplex.homology 0).hom quotientClass :=
    congrArg (fun f : binaryComplex.homology 1 ⟶ binaryComplex.homology 0 => f.hom quotientClass) hδ
  have hz : δ.hom quotientClass = 0 := hvalue.trans rfl
  exact targetClass_ne_zero (connecting_quotientClass.symm.trans hz)

theorem quotientClass_ne_zero : quotientClass ≠ 0 := by
  intro h
  let δ := ChainComplex.TensorCoefficient.connecting Ring originalComplex
    originalComplex_terms_flat sequence sequence_shortExact 0
  have hz : δ.hom quotientClass = 0 := (congrArg δ.hom h).trans δ.hom.map_zero
  exact targetClass_ne_zero (connecting_quotientClass.symm.trans hz)

end MathlibExtTest.TensorCoefficientZMod

end
