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

public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
public import MathlibExt.Analysis.CStarAlgebra.Multiplier.Strict

/-!
# Coefficient ideals and outer multiplier algebras

This file identifies a nonunital C-star algebra with its canonical closed
essential ideal in its multiplier algebra, proves the universal extension
from an essential closed ideal, and forms the corresponding unital outer
quotient.  It also transports multiplier and outer-multiplier algebras along
coefficient star-algebra equivalences.

All quotient C-star structures are explicit values.  Importing this file
installs no quotient instance and supplies no multiplier map for an arbitrary
homomorphism.
-/

@[expose] public section

noncomputable section

open scoped CStarAlgebra MultiplierAlgebra NonUnitalStarSubalgebra.Quotient

universe uA uB uC

namespace DoubleCentralizer

/-- The inherited C-star structure on the actual subtype carrier of a closed star ideal,
used only locally for multiplier extension. -/
noncomputable local instance closedStarIdealNonUnitalCStarAlgebra
    {D : Type*} [NonUnitalCStarAlgebra D] (I : ClosedStarIdeal D) :
    NonUnitalCStarAlgebra I := by
  let _ : IsClosed (I.carrier : Set D) := I.isClosed
  exact NonUnitalStarSubalgebra.nonUnitalCStarAlgebra I.carrier

variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-! ## The coefficient ideal -/

/-- **Coefficient multiplied by a multiplier.** Let `A` be a nonunital complex C*-algebra, let `M(A)` be
its double-centralizer multiplier algebra, and let `ι : A → M(A)` be the coefficient embedding. For
`a ∈ A` and `T ∈ M(A)`, `ι(a) T = ι(T.snd(a))`, where `T.snd` is the right-centralizer action. -/
theorem coe_mul (a : A) (T : 𝓜(ℂ, A)) :
    DoubleCentralizer.coeHom (𝕜 := ℂ) a * T =
      DoubleCentralizer.coeHom (𝕜 := ℂ) (T.snd a) := by
  calc
    DoubleCentralizer.coeHom (𝕜 := ℂ) a * T =
        star (star (DoubleCentralizer.coeHom (𝕜 := ℂ) a * T)) :=
      (star_star _).symm
    _ = star (star T * star (DoubleCentralizer.coeHom (𝕜 := ℂ) a)) := by
      rw [star_mul]
    _ = star (star T * DoubleCentralizer.coeHom (𝕜 := ℂ) (star a)) := by
      rw [map_star]
    _ = star (DoubleCentralizer.coeHom (𝕜 := ℂ) ((star T).fst (star a))) := by
      rw [mul_coe]
    _ = DoubleCentralizer.coeHom (𝕜 := ℂ) (star ((star T).fst (star a))) := by
      exact (map_star (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A)) _).symm
    _ = DoubleCentralizer.coeHom (𝕜 := ℂ) (T.snd a) := by
      simp

/-- **Right-centralizer formula for coefficient multiplication.** Let `A` be a nonunital complex
C*-algebra, let `M(A)` be its double-centralizer multiplier algebra, and let `ι : A → M(A)` be the
coefficient embedding. For `a ∈ A` and `T ∈ M(A)`, multiplication `ι(a) T` is the embedded
coefficient `ι(T.snd(a))`. -/
@[simp]
theorem coe_mul_normalized (a : A) (T : 𝓜(ℂ, A)) :
    DoubleCentralizer.coe ℂ a * T = DoubleCentralizer.coe ℂ (T.snd a) :=
  coe_mul a T

/-- **Coefficient ideal in a multiplier algebra.** Let `A` be a nonunital complex C*-algebra, let `M(A)`
be its double-centralizer multiplier algebra, and let `ι : A → M(A)` be the coefficient embedding.
The range `ι(A)` is a closed two-sided star ideal of `M(A)`. -/
noncomputable def coefficientIdeal (A : Type uA) [NonUnitalCStarAlgebra A] :
    ClosedStarIdeal 𝓜(ℂ, A) where
  carrier := NonUnitalStarAlgHom.range
    (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A))
  isTwoSided := by
    constructor
    · intro T x hx
      obtain ⟨a, rfl⟩ :=
        (NonUnitalStarAlgHom.mem_range
          (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A))).1 hx
      rw [mul_coe]
      exact NonUnitalStarAlgHom.mem_range_self _ _
    · intro x hx T
      obtain ⟨a, rfl⟩ :=
        (NonUnitalStarAlgHom.mem_range
          (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A))).1 hx
      rw [coe_mul]
      exact NonUnitalStarAlgHom.mem_range_self _ _
  isClosed :=
    NonUnitalStarAlgHom.isClosed_range
      (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A))

@[simp]
theorem mem_coefficientIdeal_iff (T : 𝓜(ℂ, A)) :
    T ∈ coefficientIdeal A ↔
      ∃ a : A, DoubleCentralizer.coeHom (𝕜 := ℂ) a = T :=
  NonUnitalStarAlgHom.mem_range
    (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A))

theorem coeHom_mem_coefficientIdeal (a : A) :
    DoubleCentralizer.coeHom (𝕜 := ℂ) a ∈ coefficientIdeal A :=
  (mem_coefficientIdeal_iff _).2 ⟨a, rfl⟩

/-- **Coefficient algebra and its multiplier ideal.** Let `A` be a nonunital complex C*-algebra, let
`M(A)` be its double-centralizer multiplier algebra, and let `ι : A → M(A)` be the coefficient
embedding. The embedding identifies `A` by a complex star-algebra equivalence with the closed ideal
`ι(A) ⊆ M(A)`. -/
noncomputable def coeEquivCoefficientIdeal :
    A ≃⋆ₐ[ℂ] coefficientIdeal A := by
  let f : A →⋆ₙₐ[ℂ] coefficientIdeal A :=
    NonUnitalStarAlgHom.codRestrict
      (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A))
      (coefficientIdeal A).carrier fun a ↦ coeHom_mem_coefficientIdeal a
  exact StarAlgEquiv.ofBijective f ⟨
    (fun a b h ↦ coeHom_injective (congrArg Subtype.val h)),
    (fun T ↦ by
      obtain ⟨a, ha⟩ := (mem_coefficientIdeal_iff (T : 𝓜(ℂ, A))).1 T.property
      exact ⟨a, Subtype.ext ha⟩)⟩

@[simp]
theorem coeEquivCoefficientIdeal_apply (a : A) :
    ((coeEquivCoefficientIdeal a : coefficientIdeal A) : 𝓜(ℂ, A)) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) a :=
  rfl

/-- **Essentiality of the multiplier coefficient ideal.** Let `A` be a nonunital complex C*-algebra, let
`M(A)` be its double-centralizer multiplier algebra, and let `ι : A → M(A)` be the coefficient
embedding. The closed ideal `ι(A)` is essential in `M(A)`: a multiplier annihilating every embedded
coefficient is zero. -/
theorem coefficientIdeal_isEssential :
    (coefficientIdeal A).IsEssential := by
  intro T hT
  have hfst : T.fst = 0 := by
    apply ContinuousLinearMap.ext
    intro a
    apply coeHom_injective
    have hzero := hT
      (⟨DoubleCentralizer.coeHom (𝕜 := ℂ) a,
        coeHom_mem_coefficientIdeal a⟩ : coefficientIdeal A)
    simpa only [mul_coe, zero_apply, map_zero] using hzero
  apply norm_eq_zero.mp
  rw [← T.norm_fst, hfst, norm_zero]

/-! ## Universal extension from a closed ideal -/

variable {B : Type uB} [NonUnitalCStarAlgebra B]

/-- **Multiplier action of an ambient algebra.** Let `A,B` be nonunital complex C*-algebras, let `I ⊆ B`
be a closed two-sided star ideal, and let `e : A ≃ I` be a complex star-algebra equivalence.
Multiplication in `B`, transported through `e`, gives a nonunital complex star homomorphism `B →
M(A)`, with left action `e⁻¹(b e(a))` and right action `e⁻¹(e(a) b)`. -/
noncomputable def multiplierExtension
    (I : ClosedStarIdeal B) (e : A ≃⋆ₐ[ℂ] I) :
    B →⋆ₙₐ[ℂ] 𝓜(ℂ, A) := by
  let left : B → A →L[ℂ] A := fun b ↦ LinearMap.mkContinuous
    { toFun := fun a ↦ e.symm
        (⟨b * (e a : B), I.isTwoSided.mul_mem_left b (e a).property⟩ : I)
      map_add' := fun a₁ a₂ ↦ by
        rw [← map_add e.symm]
        apply congrArg e.symm
        apply Subtype.ext
        rw [map_add e]
        change b * ((e a₁ : B) + (e a₂ : B)) =
          b * (e a₁ : B) + b * (e a₂ : B)
        exact mul_add _ _ _
      map_smul' := fun c a ↦ by
        rw [← map_smul e.symm]
        apply congrArg e.symm
        apply Subtype.ext
        rw [map_smul e]
        change b * (c • (e a : B)) = c • (b * (e a : B))
        exact mul_smul_comm _ _ _ }
    ‖b‖ fun a ↦ by
      calc
        ‖e.symm
            (⟨b * (e a : B), I.isTwoSided.mul_mem_left b (e a).property⟩ : I)‖ =
            ‖(⟨b * (e a : B), I.isTwoSided.mul_mem_left b (e a).property⟩ : I)‖ :=
          StarAlgEquiv.norm_map e.symm _
        _ = ‖b * (e a : B)‖ := rfl
        _ ≤ ‖b‖ * ‖(e a : B)‖ := norm_mul_le _ _
        _ = ‖b‖ * ‖a‖ := by
          have he : ‖(e a : B)‖ = ‖a‖ := StarAlgEquiv.norm_map e a
          rw [he]
  let right : B → A →L[ℂ] A := fun b ↦ LinearMap.mkContinuous
    { toFun := fun a ↦ e.symm
        (⟨(e a : B) * b, I.isTwoSided.mul_mem_right (e a).property b⟩ : I)
      map_add' := fun a₁ a₂ ↦ by
        rw [← map_add e.symm]
        apply congrArg e.symm
        apply Subtype.ext
        rw [map_add e]
        change ((e a₁ : B) + (e a₂ : B)) * b =
          (e a₁ : B) * b + (e a₂ : B) * b
        exact add_mul _ _ _
      map_smul' := fun c a ↦ by
        rw [← map_smul e.symm]
        apply congrArg e.symm
        apply Subtype.ext
        rw [map_smul e]
        change (c • (e a : B)) * b = c • ((e a : B) * b)
        exact smul_mul_assoc _ _ _ }
    ‖b‖ fun a ↦ by
      calc
        ‖e.symm
            (⟨(e a : B) * b, I.isTwoSided.mul_mem_right (e a).property b⟩ : I)‖ =
            ‖(⟨(e a : B) * b, I.isTwoSided.mul_mem_right (e a).property b⟩ : I)‖ :=
          StarAlgEquiv.norm_map e.symm _
        _ = ‖(e a : B) * b‖ := rfl
        _ ≤ ‖(e a : B)‖ * ‖b‖ := norm_mul_le _ _
        _ = ‖a‖ * ‖b‖ := by
          have he : ‖(e a : B)‖ = ‖a‖ := StarAlgEquiv.norm_map e a
          rw [he]
        _ = ‖b‖ * ‖a‖ := mul_comm _ _
  have coe_left (b : B) (a : A) : (e (left b a) : B) = b * (e a : B) := by
    dsimp only [left]
    change ((e (e.symm (⟨b * (e a : B), _⟩ : I)) : I) : B) = _
    rw [e.apply_symm_apply]
  have coe_right (b : B) (a : A) : (e (right b a) : B) = (e a : B) * b := by
    dsimp only [right]
    change ((e (e.symm (⟨(e a : B) * b, _⟩ : I)) : I) : B) = _
    rw [e.apply_symm_apply]
  have e_coe_injective : Function.Injective (fun a : A ↦ (e a : B)) := by
    intro a₁ a₂ h
    apply e.injective
    exact Subtype.ext h
  have e_coe_zero : (e (0 : A) : B) = 0 :=
    congrArg Subtype.val (map_zero e)
  have e_coe_add (a₁ a₂ : A) :
      (e (a₁ + a₂) : B) = (e a₁ : B) + (e a₂ : B) :=
    congrArg Subtype.val (map_add e a₁ a₂)
  have e_coe_smul (c : ℂ) (a : A) : (e (c • a) : B) = c • (e a : B) :=
    congrArg Subtype.val (map_smul e c a)
  have e_coe_mul (a₁ a₂ : A) :
      (e (a₁ * a₂) : B) = (e a₁ : B) * (e a₂ : B) :=
    congrArg Subtype.val (map_mul e a₁ a₂)
  have e_coe_star (a : A) : (e (star a) : B) = star (e a : B) :=
    congrArg Subtype.val (map_star e a)
  exact
    { toFun := fun b ↦
        { fst := left b
          snd := right b
          central := fun a₁ a₂ ↦ by
            apply e_coe_injective
            change (e (right b a₁ * a₂) : B) =
              (e (a₁ * left b a₂) : B)
            rw [e_coe_mul, e_coe_mul]
            rw [coe_left, coe_right]
            exact mul_assoc (e a₁ : B) b (e a₂ : B) }
      map_zero' := by
        apply DoubleCentralizer.ext ℂ A
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a
        · change left 0 a = 0
          apply e_coe_injective
          change (e (left 0 a) : B) = (e (0 : A) : B)
          rw [e_coe_zero]
          rw [coe_left, zero_mul]
        · change right 0 a = 0
          apply e_coe_injective
          change (e (right 0 a) : B) = (e (0 : A) : B)
          rw [e_coe_zero]
          rw [coe_right, mul_zero]
      map_add' := fun b₁ b₂ ↦ by
        apply DoubleCentralizer.ext ℂ A
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a
        · change left (b₁ + b₂) a = left b₁ a + left b₂ a
          apply e_coe_injective
          change (e (left (b₁ + b₂) a) : B) =
            (e (left b₁ a + left b₂ a) : B)
          rw [e_coe_add]
          rw [coe_left, add_mul, coe_left, coe_left]
        · change right (b₁ + b₂) a = right b₁ a + right b₂ a
          apply e_coe_injective
          change (e (right (b₁ + b₂) a) : B) =
            (e (right b₁ a + right b₂ a) : B)
          rw [e_coe_add]
          rw [coe_right, mul_add, coe_right, coe_right]
      map_smul' := fun c b ↦ by
        apply DoubleCentralizer.ext ℂ A
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a
        · change left (c • b) a = c • left b a
          apply e_coe_injective
          change (e (left (c • b) a) : B) = (e (c • left b a) : B)
          rw [e_coe_smul]
          rw [coe_left, smul_mul_assoc, coe_left]
        · change right (c • b) a = c • right b a
          apply e_coe_injective
          change (e (right (c • b) a) : B) = (e (c • right b a) : B)
          rw [e_coe_smul]
          rw [coe_right, mul_smul_comm, coe_right]
      map_mul' := fun b₁ b₂ ↦ by
        apply DoubleCentralizer.ext ℂ A
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a
        · change left (b₁ * b₂) a = left b₁ (left b₂ a)
          apply e_coe_injective
          change (e (left (b₁ * b₂) a) : B) =
            (e (left b₁ (left b₂ a)) : B)
          rw [coe_left, coe_left, coe_left]
          exact mul_assoc b₁ b₂ (e a : B)
        · change right (b₁ * b₂) a = right b₂ (right b₁ a)
          apply e_coe_injective
          change (e (right (b₁ * b₂) a) : B) =
            (e (right b₂ (right b₁ a)) : B)
          rw [coe_right, coe_right, coe_right]
          exact (mul_assoc (e a : B) b₁ b₂).symm
      map_star' := fun b ↦ by
        apply DoubleCentralizer.ext ℂ A
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a
        · rw [DoubleCentralizer.star_fst]
          change left (star b) a = star (right b (star a))
          apply e_coe_injective
          change (e (left (star b) a) : B) =
            (e (star (right b (star a))) : B)
          rw [e_coe_star]
          rw [coe_left, coe_right, star_mul, e_coe_star, star_star]
        · rw [DoubleCentralizer.star_snd]
          change right (star b) a = star (left b (star a))
          apply e_coe_injective
          change (e (right (star b) a) : B) =
            (e (star (left b (star a))) : B)
          rw [e_coe_star]
          rw [coe_right, coe_left, star_mul, e_coe_star, star_star] }

@[simp]
theorem multiplierExtension_fst
    (I : ClosedStarIdeal B) (e : A ≃⋆ₐ[ℂ] I) (b : B) (a : A) :
    (e ((multiplierExtension I e b).fst a) : B) = b * (e a : B) := by
  simp only [multiplierExtension]
  change ((e (e.symm (⟨b * (e a : B), _⟩ : I)) : I) : B) = _
  rw [e.apply_symm_apply]

@[simp]
theorem multiplierExtension_snd
    (I : ClosedStarIdeal B) (e : A ≃⋆ₐ[ℂ] I) (b : B) (a : A) :
    (e ((multiplierExtension I e b).snd a) : B) = (e a : B) * b := by
  simp only [multiplierExtension]
  change ((e (e.symm (⟨(e a : B) * b, _⟩ : I)) : I) : B) = _
  rw [e.apply_symm_apply]

/-- **Multiplier extension on the distinguished ideal.** Let `A,B` be nonunital complex C*-algebras, let
`I ⊆ B` be a closed two-sided star ideal, and let `e : A ≃ I` be a complex star-algebra equivalence.
For `a ∈ A`, the multiplier assigned to `e(a) ∈ B` is the coefficient embedding `ι(a)`. -/
@[simp]
theorem multiplierExtension_idealEquiv
    (I : ClosedStarIdeal B) (e : A ≃⋆ₐ[ℂ] I) (a : A) :
    multiplierExtension I e (e a : B) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) a := by
  apply DoubleCentralizer.ext ℂ A
  apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x
  · apply e.injective
    apply Subtype.ext
    change (e ((multiplierExtension I e (e a : B)).fst x) : B) =
      (e ((DoubleCentralizer.coeHom (𝕜 := ℂ) a).fst x) : B)
    rw [multiplierExtension_fst]
    simp only [DoubleCentralizer.coeHom_apply, DoubleCentralizer.coe_fst]
    exact congrArg Subtype.val (map_mul e a x).symm
  · apply e.injective
    apply Subtype.ext
    change (e ((multiplierExtension I e (e a : B)).snd x) : B) =
      (e ((DoubleCentralizer.coeHom (𝕜 := ℂ) a).snd x) : B)
    rw [multiplierExtension_snd]
    simp only [DoubleCentralizer.coeHom_apply, DoubleCentralizer.coe_snd]
    exact congrArg Subtype.val (map_mul e x a).symm

/-- **Faithful multiplier extension of an essential ideal.** Let `A,B` be nonunital complex C*-algebras,
let `I ⊆ B` be a closed two-sided star ideal, and let `e : A ≃ I` be a complex star-algebra
equivalence. If `I` is essential in `B`, the induced homomorphism `B → M(A)` is injective. -/
theorem multiplierExtension_injective
    (I : ClosedStarIdeal B) (e : A ≃⋆ₐ[ℂ] I) (hI : I.IsEssential) :
    Function.Injective (multiplierExtension I e) := by
  intro b₁ b₂ h
  rw [← sub_eq_zero]
  apply hI (b₁ - b₂)
  intro x
  obtain ⟨a, rfl⟩ := e.surjective x
  have hzero : multiplierExtension I e (b₁ - b₂) = 0 := by
    rw [map_sub, h, sub_self]
  have hcomponent := congrArg (fun T : 𝓜(ℂ, A) ↦ T.fst a) hzero
  rw [DoubleCentralizer.zero_toProd] at hcomponent
  have hcomponent' : (multiplierExtension I e (b₁ - b₂)).fst a = 0 := by
    change (multiplierExtension I e (b₁ - b₂)).fst a =
      (0 : A →L[ℂ] A) a at hcomponent
    simpa only [zero_apply] using hcomponent
  have hambient := congrArg (fun z : A ↦ (e z : B)) hcomponent'
  have ezero : (e (0 : A) : B) = 0 := congrArg Subtype.val (map_zero e)
  rw [multiplierExtension_fst, ezero] at hambient
  change (b₁ - b₂) * (e a : B) = 0
  exact hambient

/-- **Uniqueness of the ambient multiplier extension.** Let `A,B` be nonunital complex C*-algebras, let
`I ⊆ B` be a closed two-sided star ideal, and let `e : A ≃ I` be a complex star-algebra equivalence.
A nonunital complex star homomorphism `f : B → M(A)` equals the ambient extension if, for every `b ∈
B` and `a ∈ A`, its left and right actions satisfy `e((f b).fst(a)) = b e(a)` and `e((f b).snd(a)) =
e(a) b`. -/
theorem multiplierExtension_unique
    (I : ClosedStarIdeal B) (e : A ≃⋆ₐ[ℂ] I)
    (f : B →⋆ₙₐ[ℂ] 𝓜(ℂ, A))
    (hfst : ∀ b a, (e ((f b).fst a) : B) = b * (e a : B))
    (hsnd : ∀ b a, (e ((f b).snd a) : B) = (e a : B) * b) :
    f = multiplierExtension I e := by
  have e_coe_injective : Function.Injective (fun a : A ↦ (e a : B)) := by
    intro a₁ a₂ h
    apply e.injective
    exact Subtype.ext h
  apply NonUnitalStarAlgHom.ext
  intro b
  apply DoubleCentralizer.ext ℂ A
  apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a
  · apply e_coe_injective
    exact (hfst b a).trans (multiplierExtension_fst I e b a).symm
  · apply e_coe_injective
    exact (hsnd b a).trans (multiplierExtension_snd I e b a).symm

/-- **Unital ambient multiplier extension.** Let `A` be a nonunital complex C*-algebra, `U` a unital
complex C*-algebra, `I ⊆ U` a closed two-sided star ideal, and `e : A ≃ I` a complex star-algebra
equivalence. The ambient action of `U` on `I`, transported by `e`, defines a unital complex star
homomorphism `U → M(A)`. -/
noncomputable def multiplierExtensionUnital
    {U : Type uB} [CStarAlgebra U]
    (I : ClosedStarIdeal U) (e : A ≃⋆ₐ[ℂ] I) :
    U →⋆ₐ[ℂ] 𝓜(ℂ, A) := by
  have e_coe_injective : Function.Injective (fun a : A ↦ (e a : U)) := by
    intro a₁ a₂ h
    apply e.injective
    exact Subtype.ext h
  have hone : multiplierExtension I e 1 = 1 := by
    apply DoubleCentralizer.ext ℂ A
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a
    · change (multiplierExtension I e 1).fst a = a
      apply e_coe_injective
      change (e ((multiplierExtension I e 1).fst a) : U) = (e a : U)
      rw [multiplierExtension_fst]
      exact one_mul (e a : U)
    · change (multiplierExtension I e 1).snd a = a
      apply e_coe_injective
      change (e ((multiplierExtension I e 1).snd a) : U) = (e a : U)
      rw [multiplierExtension_snd]
      exact mul_one (e a : U)
  exact
    { toFun := multiplierExtension I e
      map_one' := hone
      map_mul' := map_mul (multiplierExtension I e)
      map_zero' := map_zero (multiplierExtension I e)
      map_add' := map_add (multiplierExtension I e)
      commutes' := fun c ↦ by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          map_smul, hone]
      map_star' := map_star (multiplierExtension I e) }

@[simp]
theorem multiplierExtensionUnital_one
    {U : Type uB} [CStarAlgebra U]
    (I : ClosedStarIdeal U) (e : A ≃⋆ₐ[ℂ] I) :
    multiplierExtensionUnital I e 1 = 1 :=
  map_one (multiplierExtensionUnital I e)

/-! ## Identity and unital boundary cases -/

theorem multiplierExtension_coefficientIdeal :
    multiplierExtension (coefficientIdeal A) coeEquivCoefficientIdeal =
      NonUnitalStarAlgHom.id ℂ 𝓜(ℂ, A) := by
  symm
  apply multiplierExtension_unique (coefficientIdeal A) coeEquivCoefficientIdeal
  · intro T a
    simpa only [NonUnitalStarAlgHom.coe_id, id_eq,
      coeEquivCoefficientIdeal_apply] using (mul_coe T a).symm
  · intro T a
    simpa only [NonUnitalStarAlgHom.coe_id, id_eq,
      coeEquivCoefficientIdeal_apply] using (coe_mul a T).symm

variable (U : Type uA) [CStarAlgebra U] in
/-- **Multiplier algebra of a unital C*-algebra.** For a unital complex C*-algebra `U`, the coefficient
embedding `U → M(U)` is a complex star-algebra equivalence onto the entire multiplier algebra. -/
noncomputable def coeEquivOfUnital :
    U ≃⋆ₐ[ℂ] 𝓜(ℂ, U) := by
  apply StarAlgEquiv.ofBijective
    (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := U))
  refine ⟨coeHom_injective, ?_⟩
  intro T
  refine ⟨T.fst 1, ?_⟩
  have hone : DoubleCentralizer.coeHom (𝕜 := ℂ) (1 : U) = 1 := by
    apply DoubleCentralizer.ext ℂ U
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a <;> simp
  rw [← mul_coe T 1, hone, mul_one]

theorem coefficientIdeal_eq_top_of_unital
    {U : Type uA} [CStarAlgebra U] : coefficientIdeal U = ⊤ := by
  ext T
  constructor
  · intro _
    exact ClosedStarIdeal.mem_top T
  · intro _
    obtain ⟨a, rfl⟩ := (coeEquivOfUnital U).surjective T
    exact coeHom_mem_coefficientIdeal a

/-! ## The outer multiplier quotient -/

end DoubleCentralizer

/-- **Outer multiplier algebra.** Let `A` be a nonunital complex C*-algebra, let `M(A)` be its
double-centralizer multiplier algebra, and let `ι : A → M(A)` be the coefficient embedding. The
outer multiplier algebra is `M(A)/ι(A)`, the quotient by the closed coefficient ideal. -/
abbrev OuterMultiplier (A : Type uA) [NonUnitalCStarAlgebra A] :=
  (DoubleCentralizer.coefficientIdeal A).Quotient

/-- **C*-structure of the outer multiplier algebra.** Let `A` be a nonunital complex C*-algebra, let
`M(A)` be its double-centralizer multiplier algebra, and let `ι : A → M(A)` be the coefficient
embedding. The quotient `M(A)/ι(A)` is a unital complex C*-algebra with its quotient norm and
induced star operations. -/
@[instance_reducible]
noncomputable def outerMultiplierCStarAlgebra
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    CStarAlgebra (OuterMultiplier A) :=
  (DoubleCentralizer.coefficientIdeal A).unitalQuotientCStarAlgebra

/-- **Projection onto the outer multiplier algebra.** Let `A` be a nonunital complex C*-algebra, let
`M(A)` be its double-centralizer multiplier algebra, and let `ι : A → M(A)` be the coefficient
embedding. The projection `M(A) → M(A)/ι(A)` is a unital complex star-algebra homomorphism. -/
noncomputable def outerQuotientMap
    {A : Type uA} [NonUnitalCStarAlgebra A] :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    𝓜(ℂ, A) →⋆ₐ[ℂ] OuterMultiplier A :=
  (DoubleCentralizer.coefficientIdeal A).unitalQuotientMap

@[simp]
theorem outerQuotientMap_apply
    {A : Type uA} [NonUnitalCStarAlgebra A] (T : 𝓜(ℂ, A)) :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    outerQuotientMap T =
      (DoubleCentralizer.coefficientIdeal A).quotientMap T := by
  rfl

theorem outerQuotientMap_surjective
    {A : Type uA} [NonUnitalCStarAlgebra A] :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    Function.Surjective (outerQuotientMap (A := A)) := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  exact (DoubleCentralizer.coefficientIdeal A).unitalQuotientMap_surjective

theorem outerQuotientMap_eq_zero_iff
    {A : Type uA} [NonUnitalCStarAlgebra A] (T : 𝓜(ℂ, A)) :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    outerQuotientMap T = 0 ↔ T ∈ DoubleCentralizer.coefficientIdeal A := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  exact (DoubleCentralizer.coefficientIdeal A).unitalQuotientMap_eq_zero_iff T

theorem outerQuotientMap_coe
    {A : Type uA} [NonUnitalCStarAlgebra A] (a : A) :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    outerQuotientMap (DoubleCentralizer.coeHom (𝕜 := ℂ) a) = 0 := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  exact (outerQuotientMap_eq_zero_iff _).2
    (DoubleCentralizer.coeHom_mem_coefficientIdeal a)

/-- **Coefficient classes vanish in the outer algebra.** Let `A` be a nonunital complex C*-algebra, let
`M(A)` be its double-centralizer multiplier algebra, and let `ι : A → M(A)` be the coefficient
embedding. For every `a ∈ A`, the class of `ι(a)` in the outer multiplier algebra is zero. -/
@[simp]
theorem outerQuotient_mk_coe
    {A : Type uA} [NonUnitalCStarAlgebra A] (a : A) :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    (Submodule.Quotient.mk (DoubleCentralizer.coe ℂ a) : OuterMultiplier A) = 0 := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  simpa only [outerQuotientMap_apply, ClosedStarIdeal.quotientMap_apply,
    DoubleCentralizer.coeHom_apply] using outerQuotientMap_coe a

theorem outerQuotientMap_one
    {A : Type uA} [NonUnitalCStarAlgebra A] :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    outerQuotientMap (A := A) 1 = 1 := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  exact map_one (outerQuotientMap (A := A))

theorem outerMultiplier_eq_zero_of_unital
    {A : Type uA} [CStarAlgebra A] (q : OuterMultiplier A) : q = 0 := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  obtain ⟨T, rfl⟩ := outerQuotientMap_surjective q
  exact (outerQuotientMap_eq_zero_iff T).2 (by
    rw [DoubleCentralizer.coefficientIdeal_eq_top_of_unital]
    exact ClosedStarIdeal.mem_top T)

theorem outerMultiplier_subsingleton_of_unital
    {A : Type uA} [CStarAlgebra A] : Subsingleton (OuterMultiplier A) :=
  ⟨fun x y ↦ (outerMultiplier_eq_zero_of_unital x).trans
    (outerMultiplier_eq_zero_of_unital y).symm⟩

/-! ## Transport along coefficient equivalences -/

namespace DoubleCentralizer

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem mem_coefficientIdeal_congr_iff
    (e : A ≃⋆ₐ[ℂ] B) (T : 𝓜(ℂ, A)) :
    DoubleCentralizer.congr e T ∈ coefficientIdeal B ↔
      T ∈ coefficientIdeal A := by
  constructor
  · rw [mem_coefficientIdeal_iff]
    rintro ⟨b, hb⟩
    rw [mem_coefficientIdeal_iff]
    refine ⟨e.symm b, ?_⟩
    calc
      DoubleCentralizer.coeHom (𝕜 := ℂ) (e.symm b) =
          DoubleCentralizer.congr e.symm
            (DoubleCentralizer.coeHom (𝕜 := ℂ) b) :=
        (congr_coeHom e.symm b).symm
      _ = DoubleCentralizer.congr e.symm (DoubleCentralizer.congr e T) :=
        congrArg (DoubleCentralizer.congr e.symm) hb
      _ = T := by
        simpa only [congr_symm] using
          (DoubleCentralizer.congr e).symm_apply_apply T
  · rw [mem_coefficientIdeal_iff]
    rintro ⟨a, rfl⟩
    rw [mem_coefficientIdeal_iff]
    exact ⟨e a, (congr_coeHom e a).symm⟩

/-- **Coefficient range under multiplier transport.** Let `A,B` be nonunital complex C*-algebras and `e
: A ≃ B` a complex star-algebra equivalence. For `T ∈ M(A)`, its transported multiplier belongs to
the coefficient image of `B` exactly when `T` belongs to the coefficient image of `A`. -/
@[simp]
theorem exists_coe_eq_congr_iff
    (e : A ≃⋆ₐ[ℂ] B) (T : 𝓜(ℂ, A)) :
    (∃ b : B, DoubleCentralizer.coe ℂ b = DoubleCentralizer.congr e T) ↔
      ∃ a : A, DoubleCentralizer.coe ℂ a = T := by
  simpa only [mem_coefficientIdeal_iff, DoubleCentralizer.coeHom_apply] using
    mem_coefficientIdeal_congr_iff e T

/-- **Transport of outer multiplier algebras.** Let `A,B` be nonunital complex C*-algebras and `e : A ≃
B` a complex star-algebra equivalence. The equivalence induces a complex star-algebra equivalence
`M(A)/A ≃ M(B)/B`. -/
noncomputable def outerCongr (e : A ≃⋆ₐ[ℂ] B) :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    OuterMultiplier A ≃⋆ₐ[ℂ] OuterMultiplier B := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  let _ : (coefficientIdeal A).carrier.IsTwoSided := (coefficientIdeal A).isTwoSided
  let _ : (coefficientIdeal B).carrier.IsTwoSided := (coefficientIdeal B).isTwoSided
  let forward : OuterMultiplier A →⋆ₙₐ[ℂ] OuterMultiplier B :=
    NonUnitalStarSubalgebra.Quotient.map
      (coefficientIdeal A).carrier (coefficientIdeal B).carrier
      (DoubleCentralizer.congr e).toNonUnitalStarAlgHom fun T hT ↦
        (mem_coefficientIdeal_congr_iff e T).2 hT
  let backward : OuterMultiplier B →⋆ₙₐ[ℂ] OuterMultiplier A :=
    NonUnitalStarSubalgebra.Quotient.map
      (coefficientIdeal B).carrier (coefficientIdeal A).carrier
      (DoubleCentralizer.congr e.symm).toNonUnitalStarAlgHom fun T hT ↦
        (mem_coefficientIdeal_congr_iff e.symm T).2 hT
  have forward_apply (T : 𝓜(ℂ, A)) :
      forward (outerQuotientMap T) =
        outerQuotientMap (DoubleCentralizer.congr e T) := by
    rfl
  have backward_apply (T : 𝓜(ℂ, B)) :
      backward (outerQuotientMap T) =
        outerQuotientMap (DoubleCentralizer.congr e.symm T) := by
    rfl
  apply StarAlgEquiv.ofNonUnitalStarAlgHom forward backward
  · apply NonUnitalStarAlgHom.ext
    intro q
    obtain ⟨T, rfl⟩ := outerQuotientMap_surjective q
    rw [NonUnitalStarAlgHom.comp_apply, forward_apply, backward_apply,
      NonUnitalStarAlgHom.coe_id, id_eq]
    apply congrArg (fun U : 𝓜(ℂ, A) ↦ outerQuotientMap U)
    simpa only [congr_symm] using
      (DoubleCentralizer.congr e).symm_apply_apply T
  · apply NonUnitalStarAlgHom.ext
    intro q
    obtain ⟨T, rfl⟩ := outerQuotientMap_surjective q
    rw [NonUnitalStarAlgHom.comp_apply, backward_apply, forward_apply,
      NonUnitalStarAlgHom.coe_id, id_eq]
    apply congrArg (fun U : 𝓜(ℂ, B) ↦ outerQuotientMap U)
    simpa only [congr_symm] using
      (DoubleCentralizer.congr e).apply_symm_apply T

theorem outerCongr_outerQuotientMap
    (e : A ≃⋆ₐ[ℂ] B) (T : 𝓜(ℂ, A)) :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    outerCongr e (outerQuotientMap T) =
      outerQuotientMap (DoubleCentralizer.congr e T) := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  let _ : (coefficientIdeal A).carrier.IsTwoSided := (coefficientIdeal A).isTwoSided
  let _ : (coefficientIdeal B).carrier.IsTwoSided := (coefficientIdeal B).isTwoSided
  let forward : OuterMultiplier A →⋆ₙₐ[ℂ] OuterMultiplier B :=
    NonUnitalStarSubalgebra.Quotient.map
      (coefficientIdeal A).carrier (coefficientIdeal B).carrier
      (DoubleCentralizer.congr e).toNonUnitalStarAlgHom fun S hS ↦
        (mem_coefficientIdeal_congr_iff e S).2 hS
  change forward ((coefficientIdeal A).quotientMap T) =
    (coefficientIdeal B).quotientMap (DoubleCentralizer.congr e T)
  exact NonUnitalStarSubalgebra.Quotient.map_mk
    (coefficientIdeal A).carrier (coefficientIdeal B).carrier
    (DoubleCentralizer.congr e).toNonUnitalStarAlgHom _ T

/-- **Classes under outer multiplier transport.** Let `A,B` be nonunital complex C*-algebras and `e : A
≃ B` a complex star-algebra equivalence. The induced outer equivalence sends the class of `T ∈ M(A)`
to the class of its transported multiplier in `M(B)`. -/
@[simp]
theorem outerCongr_mkQ
    (e : A ≃⋆ₐ[ℂ] B) (T : 𝓜(ℂ, A)) :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    outerCongr e (Submodule.Quotient.mk T : OuterMultiplier A) =
      (Submodule.Quotient.mk (DoubleCentralizer.congr e T) : OuterMultiplier B) := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  simpa only [outerQuotientMap_apply, ClosedStarIdeal.quotientMap_apply] using
    outerCongr_outerQuotientMap e T

@[simp]
theorem outerCongr_refl :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    outerCongr (StarAlgEquiv.refl ℂ A) =
      StarAlgEquiv.refl ℂ (OuterMultiplier A) := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  apply StarAlgEquiv.ext
  intro q
  obtain ⟨T, rfl⟩ := outerQuotientMap_surjective q
  rw [outerCongr_outerQuotientMap]
  exact congrArg (fun U : 𝓜(ℂ, A) ↦ outerQuotientMap U)
    (DFunLike.congr_fun DoubleCentralizer.congr_refl T)

@[simp]
theorem outerCongr_trans
    [NonUnitalCStarAlgebra C]
    (e : A ≃⋆ₐ[ℂ] B) (f : B ≃⋆ₐ[ℂ] C) :
    let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    let _ : CStarAlgebra (OuterMultiplier C) := outerMultiplierCStarAlgebra C
    outerCongr (e.trans f) = (outerCongr e).trans (outerCongr f) := by
  let _ : CStarAlgebra (OuterMultiplier A) := outerMultiplierCStarAlgebra A
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  let _ : CStarAlgebra (OuterMultiplier C) := outerMultiplierCStarAlgebra C
  apply StarAlgEquiv.ext
  intro q
  obtain ⟨T, rfl⟩ := outerQuotientMap_surjective q
  change outerCongr (e.trans f) (outerQuotientMap T) =
    outerCongr f (outerCongr e (outerQuotientMap T))
  rw [outerCongr_outerQuotientMap, outerCongr_outerQuotientMap,
    outerCongr_outerQuotientMap]
  exact congrArg (fun U : 𝓜(ℂ, C) ↦ outerQuotientMap U)
    (DFunLike.congr_fun (DoubleCentralizer.congr_trans e f) T)

end DoubleCentralizer

end
