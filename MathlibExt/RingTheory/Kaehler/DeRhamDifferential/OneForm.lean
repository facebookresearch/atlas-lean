/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The differential of Kähler one-forms

The free Kähler presentation gives a base-linear derivative that descends
to the module of Kähler differentials. It differentiates scalar coefficients
and takes values in the second exterior power.
-/

public section
noncomputable section
universe u v
variable (K : Type u) (A : Type v) [CommRing K] [CommRing A] [Algebra K A]

namespace KaehlerDifferential.DeRham


/-- The original Kähler module for the chosen base algebra. -/
abbrev W := KaehlerDifferential K A
/-- The exterior algebra of the original Kähler module. -/
abbrev E := ExteriorAlgebra A (W K A)

/-- The base-linear coefficient derivative for one fixed universal differential. -/
def coefficient (b : A) : A →ₗ[K] E K A where
  toFun a := ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ι A (D K A b)
  map_add' a c := by simp [add_mul]
  map_smul' r a := by
    simp only [Derivation.map_smul, LinearMap.map_smul_of_tower, smul_mul_assoc, RingHom.id_apply]

/-- The base-linear derivative on the actual free Kähler presentation. -/
def freeDifferential : (A →₀ A) →ₗ[K] E K A :=
  Finsupp.lsum K (coefficient K A : A → A →ₗ[K] E K A)

@[simp] theorem freeDifferential_single (b a : A) :
    freeDifferential K A (Finsupp.single b a) =
      ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ι A (D K A b) := by
  change Finsupp.lsum K (coefficient K A : A → A →ₗ[K] E K A) (Finsupp.single b a) = _
  rw [Finsupp.lsum_single]
  rfl

/-- The original free presentation map onto the Kähler module. -/
def presentationMap : (A →₀ A) →ₗ[A] W K A :=
  Finsupp.linearCombination A (D K A)

@[simp] theorem presentationMap_single (b a : A) :
    presentationMap K A (Finsupp.single b a) = a • D K A b := by
  exact Finsupp.linearCombination_single _ _ _

theorem freeDifferential_smul (a : A) (q : A →₀ A) :
    freeDifferential K A (a • q) =
      ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ι A (presentationMap K A q) +
        a • freeDifferential K A q := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr =>
    simp only [smul_add, map_add, presentationMap, hq, hr,
      mul_add]
    abel
  | single b c =>
    simp only [Finsupp.smul_single, smul_eq_mul, freeDifferential_single,
      presentationMap_single, Derivation.leibniz, map_add, map_smul,
      add_mul, smul_mul_assoc, mul_smul_comm]
    rw [add_comm]


lemma freeDifferential_relation_add (a b : A) :
    freeDifferential K A
      (Finsupp.single a 1 + Finsupp.single b 1 - Finsupp.single (a + b) 1) = 0 := by
  simp

lemma freeDifferential_relation_mul (a b : A) :
    freeDifferential K A
      (Finsupp.single b a + Finsupp.single a b - Finsupp.single (a * b) 1) = 0 := by
  simp only [map_sub, map_add, freeDifferential_single, Derivation.map_one_eq_zero,
    map_zero, zero_mul, sub_zero]
  exact ExteriorAlgebra.ι_add_mul_swap (D K A a) (D K A b)

lemma freeDifferential_relation_base (r : K) :
    freeDifferential K A (Finsupp.single (algebraMap K A r) 1) = 0 := by
  simp

lemma freeDifferential_eq_zero_of_mem_kerTotal {q : A →₀ A}
    (hq : q ∈ KaehlerDifferential.kerTotal K A) : freeDifferential K A q = 0 := by
  have both : presentationMap K A q = 0 ∧ freeDifferential K A q = 0 := by
    rw [KaehlerDifferential.kerTotal] at hq
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
    · rintro q ((⟨⟨a,b⟩, rfl⟩ | ⟨⟨a,b⟩, rfl⟩) | ⟨r, rfl⟩)
      · constructor
        · simp [presentationMap, Finsupp.linearCombination_single]
        · exact freeDifferential_relation_add K A a b
      · constructor
        · simp [presentationMap, Finsupp.linearCombination_single]
        · exact freeDifferential_relation_mul K A a b
      · constructor
        · simp [presentationMap, Finsupp.linearCombination_single]
        · exact freeDifferential_relation_base K A r
    · simp
    · intro q r hq hr iq ir
      constructor
      · rw [map_add, iq.1, ir.1, add_zero]
      · rw [map_add, iq.2, ir.2, add_zero]
    · intro a q hq iq
      constructor
      · rw [map_smul, iq.1, smul_zero]
      · rw [freeDifferential_smul, iq.1, map_zero, mul_zero, iq.2, smul_zero, add_zero]
  exact both.2


lemma kerTotal_restrict_le_freeDifferential_ker :
    (KaehlerDifferential.kerTotal K A).restrictScalars K ≤
      (freeDifferential K A).ker := by
  intro q hq
  exact freeDifferential_eq_zero_of_mem_kerTotal K A hq

/-- The derivative descended to actual Kähler one-forms. -/
def differentialOneToExterior : W K A →ₗ[K] E K A :=
  (((KaehlerDifferential.kerTotal K A).restrictScalars K).liftQ
    (freeDifferential K A) (kerTotal_restrict_le_freeDifferential_ker K A)).comp
    ((Submodule.Quotient.restrictScalarsEquiv K (KaehlerDifferential.kerTotal K A)).symm.toLinearMap.comp
      ((KaehlerDifferential.quotKerTotalEquiv K A).symm.restrictScalars K).toLinearMap)

lemma differentialOneToExterior_presentation (q : A →₀ A) :
    differentialOneToExterior K A (presentationMap K A q) = freeDifferential K A q := by
  unfold differentialOneToExterior
  change ((KaehlerDifferential.kerTotal K A).restrictScalars K).liftQ
    (freeDifferential K A) (kerTotal_restrict_le_freeDifferential_ker K A)
    ((Submodule.Quotient.restrictScalarsEquiv K (KaehlerDifferential.kerTotal K A)).symm
      ((KaehlerDifferential.quotKerTotalEquiv K A).symm (presentationMap K A q))) = _
  have hq : (KaehlerDifferential.quotKerTotalEquiv K A).symm (presentationMap K A q) =
      (KaehlerDifferential.kerTotal K A).mkQ q := by
    have he : KaehlerDifferential.quotKerTotalEquiv K A
        ((KaehlerDifferential.kerTotal K A).mkQ q) = presentationMap K A q := rfl
    rw [← he]
    exact (KaehlerDifferential.quotKerTotalEquiv K A).symm_apply_apply _
  rw [hq]
  change ((KaehlerDifferential.kerTotal K A).restrictScalars K).liftQ
    (freeDifferential K A) (kerTotal_restrict_le_freeDifferential_ker K A)
    (Submodule.Quotient.mk q) = freeDifferential K A q
  rfl

@[simp] lemma differentialOneToExterior_D (a : A) :
    differentialOneToExterior K A (D K A a) = 0 := by
  have h := differentialOneToExterior_presentation K A (Finsupp.single a 1)
  simpa using h

lemma differentialOneToExterior_smul (a : A) (w : W K A) :
    differentialOneToExterior K A (a • w) =
      ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ι A w +
        a • differentialOneToExterior K A w := by
  obtain ⟨q, rfl⟩ := KaehlerDifferential.linearCombination_surjective K A w
  change differentialOneToExterior K A (a • presentationMap K A q) =
    ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ι A (presentationMap K A q) +
      a • differentialOneToExterior K A (presentationMap K A q)
  rw [← (presentationMap K A).map_smul, differentialOneToExterior_presentation,
    freeDifferential_smul, differentialOneToExterior_presentation]


lemma freeDifferential_mem_two (q : A →₀ A) :
    freeDifferential K A q ∈ ExteriorAlgebra.exteriorPower A 2 (W K A) := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr =>
    rw [map_add]
    exact Submodule.add_mem _ hq hr
  | single b a =>
    rw [freeDifferential_single]
    have h := ExteriorAlgebra.ιMulti_range A 2
      ⟨![D K A a, D K A b], rfl⟩
    have he : ExteriorAlgebra.ιMulti A 2 ![D K A a, D K A b] =
        ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ι A (D K A b) := by
      simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
    rw [he] at h
    exact h

lemma differentialOneToExterior_mem_two (w : W K A) :
    differentialOneToExterior K A w ∈ ExteriorAlgebra.exteriorPower A 2 (W K A) := by
  obtain ⟨q, rfl⟩ := KaehlerDifferential.linearCombination_surjective K A w
  rw [← presentationMap, differentialOneToExterior_presentation]
  exact freeDifferential_mem_two K A q

/-- The actual derivative of a one-form, with its earned degree-two codomain. -/
def differentialOne : W K A →ₗ[K] ExteriorAlgebra.exteriorPower A 2 (W K A) where
  toFun w := ⟨differentialOneToExterior K A w, differentialOneToExterior_mem_two K A w⟩
  map_add' a b := by apply Subtype.ext; exact map_add _ a b
  map_smul' r w := by apply Subtype.ext; exact map_smul _ r w

@[simp] lemma differentialOne_D (a : A) : differentialOne K A (D K A a) = 0 := by
  apply Subtype.ext
  exact differentialOneToExterior_D K A a

lemma differentialOne_smul_coe (a : A) (w : W K A) :
    (differentialOne K A (a • w) : E K A) =
      ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ι A w +
        a • (differentialOne K A w : E K A) :=
  differentialOneToExterior_smul K A a w



end KaehlerDifferential.DeRham
