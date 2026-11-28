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

abbrev R4 := ZMod 4

def reduction : R4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

instance binaryModule : Module R4 (ZMod 2) := Module.compHom (ZMod 2) reduction

abbrev binary : ModuleCat.{0} R4 := ModuleCat.of R4 (ZMod 2)
abbrev regular : ModuleCat.{0} R4 := ModuleCat.of R4 R4

def doubledInteger : ℤ →+ R4 where
  toFun z := z • (2 : R4)
  map_zero' := zero_zsmul _
  map_add' := fun x y => add_zsmul (2 : R4) x y

def doubledIntegerKilled : {f : ℤ →+ R4 // f 2 = 0} :=
  ⟨doubledInteger, by
    change (2 : ℤ) • (2 : R4) = 0
    norm_num
    exact (by decide : (4 : R4) = 0)⟩

/-- The ZMod 4-linear injection sends a residue class modulo two to twice its lift modulo four. -/
abbrev inclusion : binary ⟶ regular :=
  ModuleCat.ofHom ((ZMod.lift 2 doubledIntegerKilled).toZModLinearMap 4)

/-- The ZMod 4-linear quotient map is reduction modulo two. -/
abbrev quotient : regular ⟶ binary :=
  ModuleCat.ofHom (reduction.toAddMonoidHom.toZModLinearMap 4)

theorem inclusion_zero : inclusion.hom (0 : ZMod 2) = 0 := map_zero _

theorem inclusion_one : inclusion.hom (1 : ZMod 2) = 2 := by
  change ZMod.lift 2 doubledIntegerKilled ((1 : ℤ) : ZMod 2) = 2
  rw [ZMod.lift_coe]
  change (1 : ℤ) • (2 : R4) = 2
  exact one_zsmul _

theorem quotient_one : quotient.hom (1 : R4) = 1 := map_one reduction
theorem quotient_two : quotient.hom (2 : R4) = 0 := by
  change reduction (2 : R4) = 0
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

/-- The coefficient short complex is ZMod 2 → ZMod 4 → ZMod 2. -/
abbrev sequence : ShortComplex (ModuleCat.{0} R4) :=
  ShortComplex.mk inclusion quotient inclusion_quotient

theorem inclusion_injective : Function.Injective inclusion.hom := by
  intro x y h
  fin_cases x <;> fin_cases y
  · rfl
  · change inclusion.hom (0 : ZMod 2) = inclusion.hom (1 : ZMod 2) at h
    have h02 : (0 : R4) = 2 := inclusion_zero.symm.trans (h.trans inclusion_one)
    exact False.elim ((by decide : (0 : R4) ≠ 2) h02)
  · change inclusion.hom (1 : ZMod 2) = inclusion.hom (0 : ZMod 2) at h
    have h20 : (2 : R4) = 0 := inclusion_one.symm.trans (h.trans inclusion_zero)
    exact False.elim ((by decide : (2 : R4) ≠ 0) h20)
  · rfl

theorem quotient_surjective : Function.Surjective quotient.hom :=
  ZMod.castHom_surjective (by decide : 2 ∣ 4)

/-- The doubling/reduction coefficient sequence is short exact. -/
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
          change reduction (3 : R4) = 0 at hy
          have heq : reduction (3 : R4) = (1 : ZMod 2) := by decide
          exact heq.symm.trans hy
        exact False.elim (one_ne_zero h)
    · rintro ⟨x, rfl⟩
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom inclusion_quotient) x
  mono_f := (ModuleCat.mono_iff_injective inclusion).mpr inclusion_injective
  epi_g := (ModuleCat.epi_iff_surjective quotient).mpr quotient_surjective

/-- The differential on the regular ZMod 4-module is multiplication by two. -/
abbrev twice : regular ⟶ regular := ModuleCat.ofHom (LinearMap.lsmul R4 R4 (2 : R4))

/-- The two-term complex has differential multiplication by two in degrees one and zero. -/
abbrev originalComplex : ChainComplex (ModuleCat.{0} R4) ℕ :=
  ProjectiveResolution.presentationComplex
    (ShortComplex.mk twice (0 : regular ⟶ (0 : ModuleCat.{0} R4)) (by exact comp_zero))

theorem originalComplex_d : originalComplex.d 1 0 = twice :=
  ProjectiveResolution.presentationComplex_d_zero _

theorem originalComplex_terms_flat (n : ℕ) : Module.Flat R4 (originalComplex.X n) := by
  cases n with
  | zero => change Module.Flat R4 R4; infer_instance
  | succ n =>
    cases n with
    | zero => change Module.Flat R4 R4; infer_instance
    | succ n =>
      change Module.Flat R4 (0 : ModuleCat.{0} R4)
      let : Subsingleton (0 : ModuleCat.{0} R4) :=
        ModuleCat.subsingleton_of_isZero (isZero_zero (C := ModuleCat.{0} R4))
      let : Module.Free R4 (0 : ModuleCat.{0} R4) := Module.Free.of_subsingleton R4 _
      infer_instance

abbrev binaryComplex := (ChainComplex.TensorCoefficient.functor R4 originalComplex).obj binary
abbrev regularComplex := (ChainComplex.TensorCoefficient.functor R4 originalComplex).obj regular

theorem two_smul_binary (m : ZMod 2) : (2 : R4) • m = 0 := by
  change reduction (2 : R4) * m = 0
  rw [show reduction (2 : R4) = 0 from quotient_two, zero_mul]

/-- Tensoring the differential with ZMod 2 gives the zero map. -/
theorem binaryComplex_d : binaryComplex.d 1 0 = 0 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m a
  change R4 at a
  change (binaryComplex.d 1 0).hom (m ⊗ₜ[R4] a) = 0
  have h := ChainComplex.TensorCoefficient.differential_tmul R4 originalComplex binary 1 0 m a
  have hd : (originalComplex.d 1 0).hom a = (2 : R4) * a := by
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom originalComplex_d) a
  have hz : (m ⊗ₜ[R4] ((2 : R4) * a)) = 0 := by
    apply (TensorProduct.rid R4 (ZMod 2)).injective
    change ((2 : R4) * a) • m = 0
    rw [mul_smul, two_smul_binary]
  exact h.trans ((congrArg (fun a : R4 => m ⊗ₜ[R4] a) hd).trans hz)

/-- The tensor of one with one in the quotient-coefficient degree-zero term is nonzero. -/
theorem binaryUnit_ne_zero : ((1 : ZMod 2) ⊗ₜ[R4] (1 : R4)) ≠ 0 := by
  intro h
  have h' := congrArg (TensorProduct.rid R4 (ZMod 2)) h
  have hone : (1 : ZMod 2) = 0 := by
    simpa only [TensorProduct.rid_tmul, one_smul, map_zero] using h'
  exact one_ne_zero hone

/-- The tensor of one with one is a degree-one quotient-coefficient cycle. -/
def quotientCycleMap : regular ⟶ binaryComplex.cycles 1 :=
  binaryComplex.liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R4 _ ((1 : ZMod 2) ⊗ₜ[R4] (1 : R4))))
    0 ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
      (by rw [binaryComplex_d]; exact comp_zero)

def quotientClassMap : regular ⟶ binaryComplex.homology 1 :=
  quotientCycleMap ≫ binaryComplex.homologyπ 1

def quotientClass : binaryComplex.homology 1 := quotientClassMap.hom 1

/-- The target class is the degree-zero homology class of the tensor of one with one. -/
def targetClassMap : regular ⟶ binaryComplex.homology 0 :=
  ModuleCat.ofHom
      (LinearMap.toSpanSingleton R4 _ ((1 : ZMod 2) ⊗ₜ[R4] (1 : R4))) ≫
    ChainComplex.homologyZeroClass binaryComplex

def targetClass : binaryComplex.homology 0 := targetClassMap.hom 1

/-- Tensor-unit evaluation identifies the degree-zero coefficient term with ZMod 2. -/
def unitEvaluation : binaryComplex.X 0 ⟶ binary := by
  let L : binaryComplex.X 0 →ₗ[R4] binary :=
    { toFun := fun x => TensorProduct.rid R4 (ZMod 2) x
      map_add' := fun x y => (TensorProduct.rid R4 (ZMod 2)).map_add x y
      map_smul' := fun r x => (TensorProduct.rid R4 (ZMod 2)).map_smul r x }
  exact ModuleCat.ofHom L

/-- On a pure tensor, evaluation multiplies its two residue coefficients. -/
theorem unitEvaluation_tmul (m : ZMod 2) (a : R4) :
    unitEvaluation.hom (m ⊗ₜ[R4] a) = a • m :=
  TensorProduct.rid_tmul (R := R4) m a

/-- Evaluation descends to degree-zero homology since the coefficient differential is zero. -/
def targetDetector : binaryComplex.homology 0 ⟶ binary :=
  (ChainComplex.homologyZeroIsoCokernel binaryComplex).hom ≫
    cokernel.desc (binaryComplex.d 1 0) unitEvaluation
      (by rw [binaryComplex_d]; exact zero_comp)

theorem targetDetector_class :
    ChainComplex.homologyZeroClass binaryComplex ≫ targetDetector =
      unitEvaluation := by
  rw [targetDetector, ← Category.assoc,
    ChainComplex.homologyZeroIsoCokernel_class, cokernel.π_desc]

/-- The homology detector sends the target class to one modulo two. -/
theorem targetClass_detection : targetDetector.hom targetClass = 1 := by
  let u : binaryComplex.X 0 := (1 : ZMod 2) ⊗ₜ[R4] (1 : R4)
  have hclass : targetClass = (ChainComplex.homologyZeroClass binaryComplex).hom u := by
    change (ChainComplex.homologyZeroClass binaryComplex).hom
      ((LinearMap.toSpanSingleton R4 (binaryComplex.X 0) u) (1 : R4)) = _
    exact congrArg (ChainComplex.homologyZeroClass binaryComplex).hom
      (LinearMap.toSpanSingleton_apply_one _ _ _)
  have h := congrArg (fun f : binaryComplex.X 0 ⟶ binary => f.hom u) targetDetector_class
  have hu : unitEvaluation.hom u = (1 : ZMod 2) :=
    (unitEvaluation_tmul 1 1).trans (one_smul R4 (1 : ZMod 2))
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

/-- The connecting map is computed by lifting the quotient cycle to one modulo four. -/
theorem connecting_classMap :
    quotientClassMap ≫
        ChainComplex.TensorCoefficient.connecting R4 originalComplex
          originalComplex_terms_flat sequence sequence_shortExact 0 =
      targetClassMap := by
  let x₃ : regular ⟶ binaryComplex.X 1 := ModuleCat.ofHom
    (LinearMap.toSpanSingleton R4 _ ((1 : ZMod 2) ⊗ₜ[R4] (1 : R4)))
  let x₂ : regular ⟶ regularComplex.X 1 := ModuleCat.ofHom
    (LinearMap.toSpanSingleton R4 _ ((1 : R4) ⊗ₜ[R4] (1 : R4)))
  let x₁ : regular ⟶ binaryComplex.X 0 := ModuleCat.ofHom
    (LinearMap.toSpanSingleton R4 _ ((1 : ZMod 2) ⊗ₜ[R4] (1 : R4)))
  have hx₂ : x₂ ≫ ((ChainComplex.TensorCoefficient.functor R4 originalComplex).map
      quotient).f 1 = x₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    let F := ((ChainComplex.TensorCoefficient.functor R4 originalComplex).map quotient).f 1
    let u : regularComplex.X 1 := (1 : R4) ⊗ₜ[R4] (1 : R4)
    let v : binaryComplex.X 1 := (1 : ZMod 2) ⊗ₜ[R4] (1 : R4)
    change F.hom (r • u) = r • v
    have hu : F.hom u = v :=
      (ChainComplex.TensorCoefficient.map_tmul R4 originalComplex quotient 1
        (1 : R4) (show originalComplex.X 1 from (1 : R4))).trans
        (congrArg (fun a : ZMod 2 => a ⊗ₜ[R4] (1 : R4)) quotient_one)
    exact (F.hom.map_smul r u).trans (congrArg (fun z => r • z) hu)
  have hx₁ : x₁ ≫ ((ChainComplex.TensorCoefficient.functor R4 originalComplex).map
      inclusion).f 0 = x₂ ≫ regularComplex.d 1 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    let F := ((ChainComplex.TensorCoefficient.functor R4 originalComplex).map inclusion).f 0
    let d := regularComplex.d 1 0
    let u : binaryComplex.X 0 := (1 : ZMod 2) ⊗ₜ[R4] (1 : R4)
    let v : regularComplex.X 1 := (1 : R4) ⊗ₜ[R4] (1 : R4)
    change F.hom (r • u) = d.hom (r • v)
    have hF : F.hom u = (2 : R4) ⊗ₜ[R4] (1 : R4) :=
      (ChainComplex.TensorCoefficient.map_tmul R4 originalComplex inclusion 0
        (1 : ZMod 2) (show originalComplex.X 0 from (1 : R4))).trans
        (congrArg (fun a : R4 => a ⊗ₜ[R4] (1 : R4)) inclusion_one)
    have hD : d.hom v = (1 : R4) ⊗ₜ[R4] (2 : R4) := by
      have h := ChainComplex.TensorCoefficient.differential_tmul R4 originalComplex regular 1 0
        (1 : R4) (show originalComplex.X 1 from (1 : R4))
      have hvalue : (originalComplex.d 1 0).hom
        (show originalComplex.X 1 from (1 : R4)) =
          (show originalComplex.X 0 from (2 : R4)) := by
        have hd := congrArg (fun f : regular ⟶ regular => f.hom (1 : R4)) originalComplex_d
        exact hd.trans (mul_one (2 : R4))
      exact h.trans (congrArg (fun a : R4 => (1 : R4) ⊗ₜ[R4] a) hvalue)
    have hTensor : (2 : R4) ⊗ₜ[R4] (1 : R4) = (1 : R4) ⊗ₜ[R4] (2 : R4) := by
      apply (TensorProduct.rid R4 R4).injective
      simp only [TensorProduct.rid_tmul, smul_eq_mul, mul_one, one_mul]
    have hu : F.hom u = d.hom v := hF.trans (hTensor.trans hD.symm)
    exact (F.hom.map_smul r u).trans
      ((congrArg (fun z => r • z) hu).trans (d.hom.map_smul r v).symm)
  have h := ChainComplex.TensorCoefficient.connecting_eq R4 originalComplex
    originalComplex_terms_flat sequence sequence_shortExact 0
    x₃ (by change x₃ ≫ binaryComplex.d 1 0 = 0; rw [binaryComplex_d]; exact comp_zero) x₂ hx₂ x₁ hx₁
  exact h.trans (zeroCycle_class x₁ _)

/-- The connecting map sends the quotient unit class to the target unit class. -/
theorem connecting_quotientClass :
    (ChainComplex.TensorCoefficient.connecting R4 originalComplex
      originalComplex_terms_flat sequence sequence_shortExact 0).hom quotientClass =
        targetClass := by
  exact congrArg (fun f : regular ⟶ binaryComplex.homology 0 => f.hom (1 : R4))
    connecting_classMap

/-- The connecting morphism is nonzero because its unit-class image is detected as one. -/
theorem connecting_ne_zero :
    ChainComplex.TensorCoefficient.connecting R4 originalComplex
      originalComplex_terms_flat sequence sequence_shortExact 0 ≠ 0 := by
  intro h
  let δ := ChainComplex.TensorCoefficient.connecting R4 originalComplex
    originalComplex_terms_flat sequence sequence_shortExact 0
  have hδ : δ = (0 : binaryComplex.homology 1 ⟶ binaryComplex.homology 0) := h
  have hvalue : δ.hom quotientClass =
      (0 : binaryComplex.homology 1 ⟶ binaryComplex.homology 0).hom quotientClass :=
    congrArg (fun f : binaryComplex.homology 1 ⟶ binaryComplex.homology 0 => f.hom quotientClass) hδ
  have hz : δ.hom quotientClass = 0 := hvalue.trans rfl
  exact targetClass_ne_zero (connecting_quotientClass.symm.trans hz)

theorem quotientClass_ne_zero : quotientClass ≠ 0 := by
  intro h
  let δ := ChainComplex.TensorCoefficient.connecting R4 originalComplex
    originalComplex_terms_flat sequence sequence_shortExact 0
  have hz : δ.hom quotientClass = 0 := (congrArg δ.hom h).trans δ.hom.map_zero
  exact targetClass_ne_zero (connecting_quotientClass.symm.trans hz)

end MathlibExtTest.TensorCoefficientZMod

end
