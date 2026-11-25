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

public import MathlibExt.Algebra.Homology.Ext.TensorFiniteFactor
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.NormNum

/-!
# Degree-one coefficient tensoring across `ℤ → ZMod 2`

The exact sequence with multiplication by two on `ℤ` produces a nonzero
class in `Ext¹_ℤ(ZMod 2,ZMod 2)`. The scalar map is not flat, while the
rank-two tensor factor is projective over `ZMod 2`. Tensoring the class with
the first basis vector has coefficient projections equal to the original
nonzero class and zero. Ext over `ZMod 2` itself vanishes in degree one.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace MathlibExtTest.Algebra.Homology.ExtTensorFiniteFactor

private abbrev S := ZMod 2
private abbrev σ : ℤ →+* S := algebraMap ℤ S
private abbrev N := ModuleCat.of S S
private abbrev P := (ModuleCat.restrictScalars σ).obj N
private abbrev U := ModuleCat.of S (Fin 2 → S)
private abbrev T := ModuleCat.of S (N ⊗[S] U)
private abbrev A := ModuleCat.of ℤ ℤ

private abbrev twice : A ⟶ A :=
  ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

private abbrev quotient : A ⟶ P :=
  ModuleCat.ofHom (Module.compHom.toLinearMap σ)

private lemma scalar_two_zero (x : P) : (2 : ℤ) • x = 0 := by
  change σ (2 : ℤ) • (x : S) = 0
  have h : σ (2 : ℤ) = 0 := by decide
  rw [h, zero_smul]

private lemma twice_injective : Function.Injective twice.hom := by
  intro x y h
  change (2 : ℤ) * x = 2 * y at h
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h

private lemma quotient_surjective : Function.Surjective quotient.hom := by
  change Function.Surjective ((↑) : ℤ → S)
  exact ZMod.intCast_surjective

private def twoSequence : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk twice quotient (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change σ ((2 : ℤ) * x) = 0
    have h : σ (2 : ℤ) = 0 := by decide
    rw [map_mul, h, zero_mul])

private theorem twoSequence_exact : twoSequence.Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro x
  constructor
  · intro hx
    change (x : S) = 0 at hx
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    change σ ((2 : ℤ) * k) = 0
    have h : σ (2 : ℤ) = 0 := by decide
    rw [map_mul, h, zero_mul]

private theorem twoSequence_shortExact : twoSequence.ShortExact := by
  haveI : Mono twoSequence.f := (ModuleCat.mono_iff_injective _).mpr twice_injective
  haveI : Epi twoSequence.g := (ModuleCat.epi_iff_surjective _).mpr quotient_surjective
  exact ⟨twoSequence_exact⟩

example : ¬ Module.Flat ℤ P := by
  intro h
  letI : Module.Flat ℤ P := h
  let z : ℤ ⊗[ℤ] P := (1 : ℤ) ⊗ₜ[ℤ] (1 : P)
  have hz : z ≠ 0 := by
    intro hzero
    have hv := congrArg (TensorProduct.lid ℤ P) hzero
    have hunit : (1 : P) = 0 := by
      simpa only [z, TensorProduct.lid_tmul, one_smul, map_zero] using hv
    exact (by decide : (1 : S) ≠ 0) hunit
  have hinj : Function.Injective (twice.hom.rTensor P) :=
    Module.Flat.rTensor_preserves_injective_linearMap twice.hom twice_injective
  have hzero : twice.hom.rTensor P z = 0 := by
    rw [LinearMap.rTensor_tmul]
    change ((2 : ℤ) • (1 : ℤ)) ⊗ₜ[ℤ] (1 : P) = 0
    rw [TensorProduct.smul_tmul, scalar_two_zero, TensorProduct.tmul_zero]
  exact hz (hinj (by simpa only [map_zero] using hzero))

private abbrev E := Abelian.Ext.{0} P P 1

private theorem exists_nonzero_degree_one : ∃ x : E, x ≠ 0 := by
  have hnot : ¬ Subsingleton E := by
    intro hs
    have hp : Projective twoSequence.X₂ := inferInstance
    have hsurj := (Abelian.Ext.one_subsingleton_iff_of_projective P
      twoSequence twoSequence_shortExact hp).mp hs
    obtain ⟨x, hx⟩ := hsurj (Abelian.Ext.mk₀ quotient)
    obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective A P).surjective x
    have hf : twice ≫ f = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change f.hom ((2 : ℤ) • a) = 0
      rw [f.hom.map_smul]
      exact scalar_two_zero (f.hom a)
    have hzero : Abelian.Ext.mk₀ quotient = 0 := by
      change (Abelian.Ext.mk₀ twice).comp (Abelian.Ext.mk₀ f) (add_zero 0) =
        Abelian.Ext.mk₀ quotient at hx
      rw [Abelian.Ext.mk₀_comp_mk₀, hf, Abelian.Ext.mk₀_zero] at hx
      exact hx.symm
    have hquotient : quotient = 0 := (Abelian.Ext.mk₀_bijective A P).injective
      (by simpa only [Abelian.Ext.mk₀_zero] using hzero)
    have hunit := congrArg (fun g : A ⟶ P => g.hom (1 : ℤ)) hquotient
    have hz : (1 : S) = 0 := by
      simpa only [quotient, Module.compHom.toLinearMap, map_one,
        ModuleCat.hom_zero, LinearMap.zero_apply] using hunit
    exact (by decide : (1 : S) ≠ 0) hz
  by_contra! h
  exact hnot ⟨fun x y => (h x).trans (h y).symm⟩

private def degreeOneClass : E := Classical.choose exists_nonzero_degree_one

private theorem degreeOneClass_ne_zero : degreeOneClass ≠ 0 :=
  Classical.choose_spec exists_nonzero_degree_one

example : ¬ Projective P := by
  intro h
  haveI : Projective P := h
  exact degreeOneClass_ne_zero (Abelian.Ext.eq_zero_of_projective degreeOneClass)

local instance sourceScalar (n : ℕ) : Module S (Abelian.Ext.{0} P P n) :=
  ModuleCat.extCoefficientModule σ P N n

local instance targetScalar (n : ℕ) :
    Module S (Abelian.Ext.{0} P ((ModuleCat.restrictScalars σ).obj T) n) :=
  ModuleCat.extCoefficientModule σ P T n

private def firstBasis : U := fun i => if i = 0 then 1 else 0

private def coefficientProjection (i : Fin 2) : T ⟶ N :=
  ModuleCat.ofHom ((LinearMap.proj i).comp
    (TensorProduct.piScalarRight S S N (Fin 2)).toLinearMap)

private theorem inclusion_projection_zero :
    ModuleCat.ofHom ((TensorProduct.mk S N U).flip firstBasis) ≫
      coefficientProjection 0 = 𝟙 N := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (TensorProduct.piScalarRight S S N (Fin 2) (x ⊗ₜ[S] firstBasis)) 0 = x
  simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    firstBasis, if_pos rfl, one_smul]

private theorem inclusion_projection_one :
    ModuleCat.ofHom ((TensorProduct.mk S N U).flip firstBasis) ≫
      coefficientProjection 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (TensorProduct.piScalarRight S S N (Fin 2) (x ⊗ₜ[S] firstBasis)) 1 = 0
  simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    firstBasis, if_neg (by decide : (1 : Fin 2) ≠ 0), zero_smul]

example (x : E) : (2 : ℤ) • x = 0 := by
  rw [← ModuleCat.extCoefficient_algebraMap_smul σ P N 1 (2 : ℤ) x]
  have h : σ (2 : ℤ) = 0 := by decide
  rw [h, zero_smul]

example (x : Abelian.Ext.{0} N N 1) : x = 0 :=
  Abelian.Ext.eq_zero_of_projective x

example : Function.Bijective (ModuleCat.extTensorComparison σ P N U 1) :=
  ModuleCat.extTensorComparison_bijective σ P N U 1

private theorem degreeOneTensor_ne_zero :
    (degreeOneClass ⊗ₜ[S] firstBasis : E ⊗[S] U) ≠ 0 := by
  intro h
  have hv := congrArg (fun z : E ⊗[S] U =>
    (TensorProduct.piScalarRight S S E (Fin 2) z) 0) h
  have hz : degreeOneClass = 0 := by
    simpa only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      firstBasis, if_pos rfl, one_smul, map_zero, Pi.zero_apply] using hv
  exact degreeOneClass_ne_zero hz

example : ModuleCat.extTensorFiniteFactorEquiv σ P N U 1
    (degreeOneClass ⊗ₜ[S] firstBasis) ≠ 0 := by
  intro h
  apply degreeOneTensor_ne_zero
  exact (ModuleCat.extTensorFiniteFactorEquiv σ P N U 1).injective
    (by simpa only [map_zero] using h)

example : ModuleCat.extCoefficientMap σ P (coefficientProjection 0) 1
    (ModuleCat.extTensorFiniteFactorEquiv σ P N U 1
      (degreeOneClass ⊗ₜ[S] firstBasis)) = degreeOneClass := by
  rw [ModuleCat.extTensorFiniteFactorEquiv_tmul, ModuleCat.extCoefficientMap_apply,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    ← (ModuleCat.restrictScalars σ).map_comp, inclusion_projection_zero,
    Functor.map_id, Abelian.Ext.comp_mk₀_id]

example : ModuleCat.extCoefficientMap σ P (coefficientProjection 1) 1
    (ModuleCat.extTensorFiniteFactorEquiv σ P N U 1
      (degreeOneClass ⊗ₜ[S] firstBasis)) = 0 := by
  rw [ModuleCat.extTensorFiniteFactorEquiv_tmul, ModuleCat.extCoefficientMap_apply,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    ← (ModuleCat.restrictScalars σ).map_comp, inclusion_projection_one,
    Functor.map_zero, Abelian.Ext.mk₀_zero]
  simp only [Abelian.Ext.comp_zero]

end MathlibExtTest.Algebra.Homology.ExtTensorFiniteFactor
