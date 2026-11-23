/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Completeness passes to finite local extensions of complete DVRs

This module is a valid supporting prerequisite for ATLAS N218. It generalizes the
completeness argument for integral closures of complete discrete valuation rings to
arbitrary finite faithful local extensions of DVRs.

Frozen source mechanism
(`atlas-lean` at `e8b31c5`, `LocalExtensions.lean`, lines 1163--1259):
`https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean#L1163-L1259`

Source-to-API mapping (source name ↦ name used here):

* source helper `isPrecomplete_of_pow_localExt` ↦ private
  `isPrecomplete_of_pow_localExt`;
* source `integral_closure_isAdicComplete` ↦
  `IsDiscreteValuationRing.isAdicComplete_of_finite_local_extension`;
* `isAdicComplete_iff`, `AdicCompletion.of_surjective_iff`,
  `AdicCompletion.ofTensorProduct_surjective_of_finite`,
  `AdicCompletion.of_bijective_iff`, `AdicCompletion.ofTensorProduct_tmul`,
  `IsPrecomplete.map_algebraMap_iff`, `exists_maximalIdeal_pow_eq_of_principal`
  ↦ same names in Mathlib.

The integral-closure-specific inputs of the source proof (injectivity of the
algebra map, the integral hence local-hom structure, finiteness via
`IsIntegralClosure.finite`, and the DVR structure on the integral closure) are
replaced by the corresponding hypotheses on `B`. This module does not complete N218.
-/

@[expose] public section

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]

/-- Precompleteness descends along powers of the ideal, mirroring source helper
`isPrecomplete_of_pow_localExt`. -/
private theorem isPrecomplete_of_pow_localExt
    {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    (e : ℕ) (he : 1 ≤ e) [hpc : IsPrecomplete (I ^ e) M] :
    IsPrecomplete I M := by
  constructor
  intro f hf
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      f (m * e) ≡ f (n * e) [SMOD (I ^ e) ^ m • (⊤ : Submodule R M)] := by
    intro m n hmn
    rw [show (I ^ e) ^ m = I ^ (m * e) from by rw [← pow_mul, mul_comm]]
    exact hf (Nat.mul_le_mul_right e hmn)
  obtain ⟨L, hL⟩ := hpc.prec' (fun n => f (n * e)) hcauchy
  exact ⟨L, fun n => by
    have h1 : f n ≡ f (n * e) [SMOD I ^ n • (⊤ : Submodule R M)] :=
      hf (Nat.le_mul_of_pos_right n (by omega))
    have h2 : f (n * e) ≡ L [SMOD (I ^ e) ^ n • (⊤ : Submodule R M)] := hL n
    rw [show (I ^ e) ^ n = I ^ (n * e) from by rw [← pow_mul, mul_comm]] at h2
    exact h1.trans (SModEq.mono (Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right n (by omega)))) h2)⟩

/-- **Completeness passes to finite extensions of discrete valuation rings.** Let $A$ and $B$ be
discrete valuation rings, and let $B$ be an $A$-algebra that is finitely generated as an
$A$-module and whose structure map $A \to B$ is injective. If $A$ is complete and Hausdorff for
the adic topology of its maximal ideal, then $B$ is complete and Hausdorff for the adic topology
of its maximal ideal.

Source: generalizes `integral_closure_isAdicComplete` (atlas-lean v1, `LocalExtensions.lean`)
from the integral closure to any finite faithful extension of DVRs. -/
theorem IsDiscreteValuationRing.isAdicComplete_of_finite_local_extension
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  have hinj : Function.Injective (algebraMap A B) :=
    FaithfulSMul.algebraMap_injective A B
  rw [isAdicComplete_iff]
  refine ⟨inferInstance, ?_⟩
  have hpc_A : IsPrecomplete (IsLocalRing.maximalIdeal A) B := by
    rw [← AdicCompletion.of_surjective_iff]
    set I := IsLocalRing.maximalIdeal A
    have hsurj_tp := AdicCompletion.ofTensorProduct_surjective_of_finite I B
    have hsurj_A : Function.Surjective (AdicCompletion.of I A) :=
      (AdicCompletion.of_bijective_iff.mpr inferInstance).2
    suffices h : ∀ t, AdicCompletion.ofTensorProduct I B t ∈
        LinearMap.range (AdicCompletion.of I B) by
      intro y
      obtain ⟨t, ht⟩ := hsurj_tp y
      exact ⟨(h t).choose, by rw [(h t).choose_spec, ht]⟩
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r b =>
      obtain ⟨a, ha⟩ := hsurj_A r
      exact ⟨a • b, by
        rw [AdicCompletion.ofTensorProduct_tmul, ← ha, map_smul]; rfl⟩
    | add x y hx hy =>
      obtain ⟨bx, hbx⟩ := hx
      obtain ⟨by_, hby⟩ := hy
      exact ⟨bx + by_, by simp [map_add, hbx, hby]⟩
  have hpc_map : IsPrecomplete (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) B :=
    IsPrecomplete.map_algebraMap_iff.mpr hpc_A
  set J := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) with hJ_def
  have hle : J ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hJne : J ≠ ⊥ := by
    intro h
    rw [hJ_def, Ideal.map_eq_bot_iff_le_ker] at h
    have hker : RingHom.ker (algebraMap A B) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp hinj
    rw [hker, le_bot_iff] at h
    exact IsDiscreteValuationRing.not_a_field A h
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal _) J hJne
  have he1 : 1 ≤ e := by
    by_contra h
    push Not at h
    interval_cases e
    simp only [pow_zero, Ideal.one_eq_top] at he
    exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top
      (eq_top_iff.mpr (he ▸ hle))
  rw [he] at hpc_map
  exact isPrecomplete_of_pow_localExt e he1 (hpc := hpc_map)
