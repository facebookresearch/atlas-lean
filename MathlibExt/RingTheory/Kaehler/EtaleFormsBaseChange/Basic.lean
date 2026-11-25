/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.RingTheory.Kaehler.DeRhamDifferential
public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Relative exterior forms under formally étale scalar extension

For a formally étale algebra extension, the scalar-extension map on relative
Kähler forms is an equivalence in each nonnegative exterior degree. The
base ring and the two algebra carriers may lie in independent universes.
The equivalence preserves scalar coefficients and exterior differential
words.
-/

@[expose] public section
noncomputable section

namespace KaehlerDifferential.DeRham

open scoped TensorProduct

universe u v w
variable (R : Type u) (A : Type v) (B : Type w)
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The original forms map extended through its actual coefficient tensor. -/
def tensorFormsMap (n : ℕ) : B ⊗[A] Forms R A n →ₗ[B] Forms R B n :=
  (formsMap R A B n).liftBaseChange B

/-- The actual scalar extension has the original coefficient and form restriction value. -/
theorem tensorFormsMap_tmul (n : ℕ) (b : B) (x : Forms R A n) :
    tensorFormsMap R A B n (b ⊗ₜ[A] x) = b • formsMap R A B n x :=
  LinearMap.liftBaseChange_tmul _ _ _ _

section FormallyEtale

variable [Algebra.FormallyEtale A B]

/-- Formally étale scalar extension gives the original exterior-form equivalence in every degree. -/
def tensorFormsEquivOfFormallyEtale (n : ℕ) :
    B ⊗[A] Forms R A n ≃ₗ[B] Forms R B n :=
  (exteriorPower.baseChangeEquiv A B Ω[A⁄R] n).trans
    (exteriorPower.mapEquiv B (B ⊗[A] Ω[A⁄R]) n
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B))

/-- The actual formally étale equivalence retains every original scalar exterior word. -/
theorem tensorFormsEquivOfFormallyEtale_tmul_ιMulti (n : ℕ) (b : B) (v : Fin n → Ω[A⁄R]) :
    tensorFormsEquivOfFormallyEtale R A B n (b ⊗ₜ[A] exteriorPower.ιMulti A n v) =
      b • formsMap R A B n (exteriorPower.ιMulti A n v) := by
  rw [tensorFormsEquivOfFormallyEtale, LinearEquiv.trans_apply,
    exteriorPower.baseChangeEquiv_apply_tmul_ιMulti, map_smul,
    exteriorPower.mapEquiv_apply_ιMulti, formsMap_ιMulti]
  congr 2
  funext i
  rw [Function.comp_apply, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul]

/-- Every actual tensor representative has the original formally étale form restriction value. -/
theorem tensorFormsEquivOfFormallyEtale_tmul (n : ℕ) (b : B) (x : Forms R A n) :
    tensorFormsEquivOfFormallyEtale R A B n (b ⊗ₜ[A] x) = b • formsMap R A B n x := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n (M := Ω[A⁄R]))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  have hall : ∀ c : B, tensorFormsEquivOfFormallyEtale R A B n (c ⊗ₜ[A] x) =
      c • formsMap R A B n x := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨v, rfl⟩ c
      exact tensorFormsEquivOfFormallyEtale_tmul_ιMulti R A B n c v
    · intro c
      rw [TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]
    · intro x y _ _ hx hy c
      rw [TensorProduct.tmul_add, map_add, map_add, smul_add, hx c, hy c]
    · intro a x _ hx c
      rw [← TensorProduct.smul_tmul, hx (a • c), map_smul, smul_assoc, smul_comm a c]
  exact hall b

/-- The formally étale equivalence is the actual coefficient-tensor forms map. -/
theorem tensorFormsEquivOfFormallyEtale_toLinearMap (n : ℕ) :
    (tensorFormsEquivOfFormallyEtale R A B n).toLinearMap = tensorFormsMap R A B n := by
  apply LinearMap.restrictScalars_injective A
  apply TensorProduct.ext'
  intro b x
  exact (tensorFormsEquivOfFormallyEtale_tmul R A B n b x).trans
    (tensorFormsMap_tmul R A B n b x).symm

/-- The original forms map is a base-change map under formal étaleness in every degree. -/
theorem isBaseChange_formsMap_of_formallyEtale (n : ℕ) : IsBaseChange B (formsMap R A B n) := by
  change Function.Bijective (tensorFormsMap R A B n)
  rw [← tensorFormsEquivOfFormallyEtale_toLinearMap]
  exact (tensorFormsEquivOfFormallyEtale R A B n).bijective

end FormallyEtale

end KaehlerDifferential.DeRham
