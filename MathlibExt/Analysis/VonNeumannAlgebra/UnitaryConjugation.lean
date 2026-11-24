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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalEquiv
public import MathlibExt.Analysis.VonNeumannAlgebra.Generated
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Spatial normal conjugation on the original concrete algebra

An actual unitary which normalizes a concrete von Neumann algebra restricts
the stock conjugation automorphism to that same operator subtype. Its vector
functionals pull back to the original functionals on the adjoint-transformed
vectors. Bounded functional pullback preserves their actual norm-closed span,
so both original conjugation maps are ultraweak continuous.

This supplies the spatial normal-equivalence constructor needed by normal
dual actions. The carrier conditions express the actual unitary normalization;
normality and predual preservation are proved from the original unitary.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Restricted

variable (M : VonNeumannAlgebra H) (U : unitary (H →L[ℂ] H))
variable (hU : ∀ T : H →L[ℂ] H, T ∈ M → (U : H →L[ℂ] H) * T * (star U : H →L[ℂ] H) ∈ M)
variable (hUstar : ∀ T : H →L[ℂ] H, T ∈ M →
  (star U : H →L[ℂ] H) * T * (U : H →L[ℂ] H) ∈ M)

/-- Restrict the stock unitary conjugation and its actual inverse to the original algebra. -/
def unitaryConjugationStarAlgEquiv : M ≃⋆ₐ[ℂ] M := by
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) U
  exact
    { toRingEquiv :=
        { toFun := fun x => ⟨(U : H →L[ℂ] H) * (x : H →L[ℂ] H) * (star U : H →L[ℂ] H),
            hU x.val x.property⟩
          invFun := fun x => ⟨(star U : H →L[ℂ] H) * (x : H →L[ℂ] H) * (U : H →L[ℂ] H),
            hUstar x.val x.property⟩
          left_inv := by
            intro x
            apply Subtype.ext
            change e.symm (e (x : H →L[ℂ] H)) = (x : H →L[ℂ] H)
            exact e.symm_apply_apply _
          right_inv := by
            intro x
            apply Subtype.ext
            change e (e.symm (x : H →L[ℂ] H)) = (x : H →L[ℂ] H)
            exact e.apply_symm_apply _
          map_mul' := by
            intro x y
            apply Subtype.ext
            change e ((x : H →L[ℂ] H) * (y : H →L[ℂ] H)) =
              e (x : H →L[ℂ] H) * e (y : H →L[ℂ] H)
            exact map_mul e _ _
          map_add' := by
            intro x y
            apply Subtype.ext
            change e ((x : H →L[ℂ] H) + (y : H →L[ℂ] H)) =
              e (x : H →L[ℂ] H) + e (y : H →L[ℂ] H)
            exact map_add e _ _ }
      map_smul' := by
        intro c x
        apply Subtype.ext
        change e (c • (x : H →L[ℂ] H)) = c • e (x : H →L[ℂ] H)
        exact map_smul e _ _
      map_star' := by
        intro x
        apply Subtype.ext
        change e (star (x : H →L[ℂ] H)) = star (e (x : H →L[ℂ] H))
        exact map_star e _ }

/-- The restricted automorphism keeps the original spatial operator value. -/
@[simp]
theorem unitaryConjugationStarAlgEquiv_apply (x : M) :
    (unitaryConjugationStarAlgEquiv M U hU hUstar x : H →L[ℂ] H) =
      (U : H →L[ℂ] H) * (x : H →L[ℂ] H) * (star U : H →L[ℂ] H) :=
  rfl

/-- The restricted inverse is the original adjoint-unitary conjugation. -/
theorem unitaryConjugationStarAlgEquiv_symm_apply (x : M) :
    ((unitaryConjugationStarAlgEquiv M U hU hUstar).symm x : H →L[ℂ] H) =
      (star U : H →L[ℂ] H) * (x : H →L[ℂ] H) * (U : H →L[ℂ] H) :=
  rfl

/-- Spatial pullback is the actual vector functional on the adjoint-transformed vectors. -/
theorem unitaryConjugation_vectorFunctional (ξ η : H) (x : M) :
    vectorFunctional M ξ η (unitaryConjugationStarAlgEquiv M U hU hUstar x) =
      vectorFunctional M ((star U : H →L[ℂ] H) ξ) ((star U : H →L[ℂ] H) η) x := by
  simp only [vectorFunctional_apply, unitaryConjugationStarAlgEquiv_apply]
  change ⟪ξ, (U : H →L[ℂ] H) ((x : H →L[ℂ] H) ((star U : H →L[ℂ] H) η))⟫_ℂ =
    ⟪(star U : H →L[ℂ] H) ξ, (x : H →L[ℂ] H) ((star U : H →L[ℂ] H) η)⟫_ℂ
  exact (ContinuousLinearMap.adjoint_inner_left (U : H →L[ℂ] H)
    ((x : H →L[ℂ] H) ((star U : H →L[ℂ] H) η)) ξ).symm

/-- Actual spatial normalization gives the original normal automorphism in both directions. -/
def unitaryConjugationNormalEquiv : NormalStarAlgEquiv M M := by
  let e := unitaryConjugationStarAlgEquiv M U hU hUstar
  have hnormal (f : M ≃⋆ₐ[ℂ] M) (V : unitary (H →L[ℂ] H))
      (hf : ∀ x : M, (f x : H →L[ℂ] H) =
        Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) V (x : H →L[ℂ] H)) :
      Continuous fun x : Ultraweak M =>
        (ultraweakLinearEquiv M).symm (f (ultraweakLinearEquiv M x)) := by
    let T : M →L[ℂ] M := ⟨LinearMap.ofClass f.toStarAlgHom, map_continuous f.toStarAlgHom⟩
    let B : StrongDual ℂ M →L[ℂ] StrongDual ℂ M := (ContinuousLinearMap.compL ℂ M M ℂ).flip T
    let P := (normalFunctionalSpace M).comap B.toLinearMap
    have hPclosed : IsClosed (P : Set (StrongDual ℂ M)) := by
      change IsClosed (B ⁻¹' (normalFunctionalSpace M : Set (StrongDual ℂ M)))
      exact (normalFunctionalSpace_isClosed M).preimage B.continuous
    have hvec (ξ η : H) : vectorFunctional M ξ η ∈ P := by
      change B (vectorFunctional M ξ η) ∈ normalFunctionalSpace M
      have hB : B (vectorFunctional M ξ η) =
          vectorFunctional M ((star V : H →L[ℂ] H) ξ) ((star V : H →L[ℂ] H) η) := by
        apply ContinuousLinearMap.ext
        intro x
        change vectorFunctional M ξ η (f x) =
          vectorFunctional M ((star V : H →L[ℂ] H) ξ) ((star V : H →L[ℂ] H) η) x
        simp only [vectorFunctional_apply]
        rw [hf]
        change ⟪ξ, (V : H →L[ℂ] H) ((x : H →L[ℂ] H) ((star V : H →L[ℂ] H) η))⟫_ℂ =
          ⟪(star V : H →L[ℂ] H) ξ, (x : H →L[ℂ] H) ((star V : H →L[ℂ] H) η)⟫_ℂ
        exact (ContinuousLinearMap.adjoint_inner_left (V : H →L[ℂ] H)
          ((x : H →L[ℂ] H) ((star V : H →L[ℂ] H) η)) ξ).symm
      rw [hB]
      exact vectorFunctional_mem_normalFunctionalSpace M _ _
    have hPall := normalFunctionalSpace_le M hPclosed hvec
    apply (ultraweak_continuous_iff M).2
    intro φ
    have hmem := hPall φ.property
    change B (φ : StrongDual ℂ M) ∈ normalFunctionalSpace M at hmem
    change Continuous fun x : Ultraweak M => (φ : StrongDual ℂ M) (f (ultraweakLinearEquiv M x))
    have hfun : (fun x : Ultraweak M => (φ : StrongDual ℂ M) (f (ultraweakLinearEquiv M x))) =
        (fun x : Ultraweak M => (B (φ : StrongDual ℂ M)) (ultraweakLinearEquiv M x)) := by
      funext x
      rfl
    rw [hfun]
    exact ultraweak_eval_continuous M ⟨B (φ : StrongDual ℂ M), hmem⟩
  exact
    { toStarAlgEquiv := e
      continuous_ultraweak := hnormal e U (by intro x; rfl)
      continuous_ultraweak_symm := hnormal e.symm (star U) (by
        intro x
        change ((unitaryConjugationStarAlgEquiv M U hU hUstar).symm x : H →L[ℂ] H) = _
        simp only [unitaryConjugationStarAlgEquiv_symm_apply, Unitary.conjStarAlgAut_apply,
          Unitary.coe_star, star_star]) }

/-- The normal bundle retains the original unitary-conjugation value. -/
@[simp]
theorem unitaryConjugationNormalEquiv_apply (x : M) :
    (unitaryConjugationNormalEquiv M U hU hUstar x : H →L[ℂ] H) =
      (U : H →L[ℂ] H) * (x : H →L[ℂ] H) * (star U : H →L[ℂ] H) :=
  rfl

/-- The actual normal inverse retains the original adjoint-conjugation value. -/
theorem unitaryConjugationNormalEquiv_symm_apply (x : M) :
    ((unitaryConjugationNormalEquiv M U hU hUstar).symm x : H →L[ℂ] H) =
      (star U : H →L[ℂ] H) * (x : H →L[ℂ] H) * (U : H →L[ℂ] H) :=
  rfl

include hU hUstar in
/-- The two original carrier inclusions give the printed spatial normalization equality. -/
theorem unitaryConjugationStarAlgEquiv_image :
    (fun T : H →L[ℂ] H => (U : H →L[ℂ] H) * T * (star U : H →L[ℂ] H)) ''
      (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H)) := by
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) U
  apply Set.ext
  intro T
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact hU S hS
  · intro hT
    refine ⟨(star U : H →L[ℂ] H) * T * (U : H →L[ℂ] H), hUstar T hT, ?_⟩
    change e (e.symm T) = T
    exact e.apply_symm_apply T

/-- The exact source equality U M U* = M constructs the same original normal spatial automorphism. -/
def unitaryConjugationNormalEquivOfEq
    (hEq : (fun T : H →L[ℂ] H => (U : H →L[ℂ] H) * T * (star U : H →L[ℂ] H)) ''
      (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H))) : NormalStarAlgEquiv M M := by
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) U
  have heq : e '' (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H)) := hEq
  have hfwd (T : H →L[ℂ] H) (hT : T ∈ M) :
      (U : H →L[ℂ] H) * T * (star U : H →L[ℂ] H) ∈ M := by
    change e T ∈ (M : Set (H →L[ℂ] H))
    rw [← heq]
    exact Set.mem_image_of_mem e hT
  have hbwd (T : H →L[ℂ] H) (hT : T ∈ M) :
      (star U : H →L[ℂ] H) * T * (U : H →L[ℂ] H) ∈ M := by
    have hmem : T ∈ e '' (M : Set (H →L[ℂ] H)) := by
      rw [heq]
      exact hT
    rcases hmem with ⟨S, hS, hST⟩
    change e.symm T ∈ (M : Set (H →L[ℂ] H))
    rw [← hST, StarAlgEquiv.symm_apply_apply]
    exact hS
  exact unitaryConjugationNormalEquiv M U hfwd hbwd

/-- The exact-equality constructor retains the original unitary conjugation formula. -/
@[simp]
theorem unitaryConjugationNormalEquivOfEq_apply
    (hEq : (fun T : H →L[ℂ] H => (U : H →L[ℂ] H) * T * (star U : H →L[ℂ] H)) ''
      (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H))) (x : M) :
    (unitaryConjugationNormalEquivOfEq M U hEq x : H →L[ℂ] H) =
      (U : H →L[ℂ] H) * (x : H →L[ℂ] H) * (star U : H →L[ℂ] H) :=
  rfl

end Restricted

/-- Preserving the original star adjoin preserves its actual generated double commutant. -/
theorem unitaryConjugation_generatedBy_mem (s : Set (H →L[ℂ] H)) (U : unitary (H →L[ℂ] H))
    (hs : ∀ a : H →L[ℂ] H, a ∈ s →
      (U : H →L[ℂ] H) * a * (star U : H →L[ℂ] H) ∈ StarAlgebra.adjoin ℂ s)
    (x : H →L[ℂ] H) (hx : x ∈ generatedBy s) :
    (U : H →L[ℂ] H) * x * (star U : H →L[ℂ] H) ∈ generatedBy s := by
  let A := StarAlgebra.adjoin ℂ s
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) U
  have hA : A ≤ A.comap e.toStarAlgHom := by
    apply StarAlgebra.adjoin_le
    intro a ha
    change e a ∈ A
    exact hs a ha
  have hx' : x ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    change x ∈ (generatedBy s : Set (H →L[ℂ] H)) at hx
    rw [coe_generatedBy] at hx
    exact hx
  change e x ∈ (generatedBy s : Set (H →L[ℂ] H))
  rw [coe_generatedBy]
  change ∀ b : H →L[ℂ] H, b ∈ Set.centralizer (A : Set (H →L[ℂ] H)) → b * e x = e x * b
  intro b hb
  have hpre : e.symm b ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
    intro a ha
    apply e.injective
    calc
      e (a * e.symm b) = e a * e (e.symm b) := map_mul e _ _
      _ = e a * b := congrArg (fun z : H →L[ℂ] H => e a * z) (e.apply_symm_apply b)
      _ = b * e a := hb (e a) (hA ha)
      _ = e (e.symm b) * e a :=
        congrArg (fun z : H →L[ℂ] H => z * e a) (e.apply_symm_apply b).symm
      _ = e (e.symm b * a) := (map_mul e _ _).symm
  calc
    b * e x = e (e.symm b) * e x :=
      congrArg (fun z : H →L[ℂ] H => z * e x) (e.apply_symm_apply b).symm
    _ = e (e.symm b * x) := (map_mul e _ _).symm
    _ = e (x * e.symm b) := congrArg e (hx' (e.symm b) hpre)
    _ = e x * e (e.symm b) := map_mul e _ _
    _ = e x * b := congrArg (fun z : H →L[ℂ] H => e x * z) (e.apply_symm_apply b)

end

end VonNeumannAlgebra
