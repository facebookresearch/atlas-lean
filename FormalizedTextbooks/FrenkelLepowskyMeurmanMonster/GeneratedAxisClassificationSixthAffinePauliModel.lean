/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSpinSupportPhases

/-! A finite affine phase formula follows from actual Pauli fixation and a matrix certificate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Literal binary products of an arbitrary twelve-element family of original Q operators. -/
def generatedSixthAffinePauliProduct (q : Fin 12 → Q) (a : SpinIndex) : Q :=
  (List.ofFn (fun j : Fin 12 => (q j) ^ (a j).val)).prod

/-- The literal original translations as matrix columns. -/
def generatedSixthAffineTranslationMatrix (q : Fin 12 → Q) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) := fun i j => spinTranslation (q j) i

/-- The literal original modulations as matrix rows. -/
def generatedSixthAffineModulationMatrix (p : Fin 12 → Q) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) := fun j i => spinModulation (p j) i

private theorem translation_prod (l : List Q) :
    spinTranslation l.prod = (l.map spinTranslation).sum := by
  induction l with
  | nil => rfl
  | cons q l ih => simp only [List.prod_cons, spinTranslation_mul, ih, List.map_cons,
      List.sum_cons]

private theorem translation_pow (q : Q) (n : ℕ) :
    spinTranslation (q ^ n) = n • spinTranslation q := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, spinTranslation_mul, ih, succ_nsmul]

/-- The actual product translation is precisely the matrix of the original family columns. -/
theorem generatedSixth_affine_product_translation (q : Fin 12 → Q) (a : SpinIndex) :
    spinTranslation (generatedSixthAffinePauliProduct q a) =
      generatedSixthAffineTranslationMatrix q *ᵥ a := by
  unfold generatedSixthAffinePauliProduct
  rw [translation_prod, List.map_ofFn, List.sum_ofFn]
  funext i
  simp only [Finset.sum_apply, Function.comp_apply, translation_pow,
    ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_val, ZMod.cast_id,
    Pi.smul_apply, smul_eq_mul, generatedSixthAffineTranslationMatrix, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Products of actual fixing Pauli operators fix the original state. -/
theorem generatedSixth_affine_product_fixed (q : Fin 12 → Q) (f : SpinSpace)
    (hq : ∀ j, spinRepresentation (q j) f = f) (a : SpinIndex) :
    spinRepresentation (generatedSixthAffinePauliProduct q a) f = f := by
  let K : Subgroup Q := (MulAction.stabilizer
    (SpinSpace ≃ₗ[ℝ] SpinSpace) f).comap spinRepresentation
  change generatedSixthAffinePauliProduct q a ∈ K
  apply K.list_prod_mem
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  exact K.pow_mem (hq j) _

private theorem phase_difference (q : Q) (t a : SpinIndex)
    (ht : spinPhase q t = 0) (ha : spinPhase q a = 0) :
    spinDot (spinModulation q) (t + a) = 0 := by
  rw [spinPhase] at ht ha
  rw [spinDot_add_right]
  calc
    spinDot (spinModulation q) t + spinDot (spinModulation q) a =
        (Multiplicative.toAdd q.coeff + spinDot (spinModulation q) t) +
          (Multiplicative.toAdd q.coeff + spinDot (spinModulation q) a) := by
      rw [add_add_add_comm, ZModModule.add_self, zero_add]
    _ = 0 := by rw [ht, ha, zero_add]

/-- Fixed pure modulations force every nonzero coordinate into their anchored affine kernel. -/
theorem generatedSixth_affine_support (p : Fin 12 → Q) (f : SpinSpace) (a t : SpinIndex)
    (hp : ∀ j, spinRepresentation (p j) f = f)
    (hz : ∀ j, spinTranslation (p j) = 0)
    (ha : ∀ j, spinPhase (p j) a = 0) (ht : f t ≠ 0) :
    generatedSixthAffineModulationMatrix p *ᵥ
      (t + a) = 0 := by
  funext j
  have hf := generatedSpinSupport_fixed_phase (p j) f 0 (hp j)
    (fun u => by rw [hz j, add_zero, qSign_zero, one_mul]) t ht
  rw [add_zero] at hf
  exact phase_difference (p j) t a hf (ha j)

/-- The complete original state is the anchored finite phase model
with explicit matrix hypotheses. -/
theorem generatedSixth_affine_phase_model
    (q p : Fin 12 → Q) (f : SpinSpace) (a t : SpinIndex)
    (B C : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hq : ∀ j, spinRepresentation (q j) f = f)
    (hp : ∀ j, spinRepresentation (p j) f = f)
    (hz : ∀ j, spinTranslation (p j) = 0)
    (ha : ∀ j, spinPhase (p j) a = 0)
    (hcert : generatedSixthAffineTranslationMatrix q * B +
      C * generatedSixthAffineModulationMatrix p = 1) :
    f t =
      (if generatedSixthAffineModulationMatrix p *ᵥ
        (t + a) = 0 then
          qSign (spinPhase (generatedSixthAffinePauliProduct q (B *ᵥ (t + a))) a)
        else 0) * f a := by
  by_cases ht :
      generatedSixthAffineModulationMatrix p *ᵥ
        (t + a) = 0
  · have he : spinTranslation (generatedSixthAffinePauliProduct q (B *ᵥ (t + a))) =
        t + a := by
      rw [generatedSixth_affine_product_translation]
      have hc := congrArg (fun M : Matrix (Fin 12) (Fin 12) (ZMod 2) => M *ᵥ (t + a)) hcert
      rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ht, Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at hc
      exact hc
    have hf := (generatedSpinSupport_fixed_iff _ f).mp
      (generatedSixth_affine_product_fixed q f hq (B *ᵥ (t + a))) a
    rw [he, add_left_comm a t a, ZModModule.add_self, add_zero] at hf
    rw [ite_eq_left ht, ← hf, ← mul_assoc, qSign_sq, one_mul]
  · have hf : f t = 0 := by
      by_contra hf
      exact ht (generatedSixth_affine_support p f a t hp hz ha hf)
    rw [hf, ite_eq_right ht, zero_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
