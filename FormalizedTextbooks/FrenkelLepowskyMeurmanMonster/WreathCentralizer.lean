/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The elementary wreath-product centralizer argument needed for the independent
Monster reference. No bimonster recognition theorem is assumed here.
-/
module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

abbrev WreathParity := Multiplicative (ZMod 2)

def wreathFlip : WreathParity := Multiplicative.ofAdd 1

theorem wreathParity_cases (x : WreathParity) : x = 1 ∨ x = wreathFlip := by
  have h : Multiplicative.toAdd x = 0 ∨ Multiplicative.toAdd x = 1 := by
    generalize Multiplicative.toAdd x = z
    fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases h with h | h
  · exact Or.inl (Multiplicative.toAdd.injective h)
  · exact Or.inr (Multiplicative.toAdd.injective h)

@[simp] theorem wreathFlip_sq : wreathFlip * wreathFlip = 1 := by decide

@[simp] theorem wreathFlip_inv : wreathFlip⁻¹ = wreathFlip := by decide

variable (M : Type*) [Group M]

/-- The factor swap in the regular two-factor wreath product. -/
def wreathSwap : M ≀ᵣ WreathParity := RegularWreathProduct.inl wreathFlip

/-- A base-group element used to conjugate an outer involution to the swap. -/
def wreathOuterConjugator (g : M ≀ᵣ WreathParity) : M ≀ᵣ WreathParity :=
  ⟨fun x => if x = 1 then g.left 1 else 1, 1⟩

/-- Every involution outside the base group is conjugate to the factor swap. -/
theorem wreathOuterInvolution_conjugate (g : M ≀ᵣ WreathParity)
    (hg : g * g = 1) (hr : g.right = wreathFlip) :
    wreathOuterConjugator M g * wreathSwap M * (wreathOuterConjugator M g)⁻¹ = g := by
  have hl : g.left 1 * g.left wreathFlip = 1 := by
    have h := congrArg (fun w : M ≀ᵣ WreathParity => w.left 1) hg
    simpa only [RegularWreathProduct.mul_left, Pi.mul_apply, hr,
      wreathFlip_inv, mul_one, RegularWreathProduct.one_left, Pi.one_apply] using h
  have hi : g.left wreathFlip = (g.left 1)⁻¹ := eq_inv_of_mul_eq_one_right hl
  apply RegularWreathProduct.ext
  · funext x
    rcases wreathParity_cases x with rfl | rfl
    · simp [wreathOuterConjugator, wreathSwap, RegularWreathProduct.mul_left,
        RegularWreathProduct.inv_left, wreathFlip,
        show (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 by decide]
    · simp only [wreathOuterConjugator, wreathSwap, RegularWreathProduct.mul_left,
        RegularWreathProduct.inv_left, RegularWreathProduct.left_inl,
        RegularWreathProduct.right_inl, RegularWreathProduct.mul_right,
        Pi.mul_apply, Pi.inv_apply, Pi.one_apply, one_mul, mul_one, inv_one,
        wreathFlip_inv, wreathFlip_sq]
      simp only [↓reduceIte, ite_mul, mul_inv_cancel, one_mul]
      exact hi.symm
  · simp [wreathOuterConjugator, wreathSwap, hr]

def wreathSwapCentralizer : Subgroup (M ≀ᵣ WreathParity) :=
  Subgroup.centralizer {wreathSwap M}

/-- Commuting with the factor swap means having equal entries in the two factors. -/
theorem mem_wreathSwapCentralizer_iff (g : M ≀ᵣ WreathParity) :
    g ∈ wreathSwapCentralizer M ↔ ∀ x, g.left x = g.left 1 := by
  rw [wreathSwapCentralizer, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h x
    have hl := congrArg (fun w : M ≀ᵣ WreathParity => w.left 1) h
    simp only [wreathSwap, RegularWreathProduct.mul_left,
      RegularWreathProduct.left_inl, RegularWreathProduct.right_inl,
      Pi.mul_apply, Pi.one_apply, mul_one, one_mul, wreathFlip_inv] at hl
    rcases wreathParity_cases x with rfl | rfl
    · rfl
    · exact hl.symm
  · intro h
    apply RegularWreathProduct.ext
    · funext x
      simp only [wreathSwap, RegularWreathProduct.mul_left,
        RegularWreathProduct.left_inl, RegularWreathProduct.right_inl,
        Pi.mul_apply, Pi.one_apply, mul_one, one_mul]
      exact (h _).trans (h _).symm
    · simp only [wreathSwap, RegularWreathProduct.mul_right,
        RegularWreathProduct.right_inl]
      exact mul_comm _ _

/-- Evaluation on either factor gives a homomorphism on the swap centralizer. -/
def wreathCentralizerEvaluation : wreathSwapCentralizer M →* M where
  toFun g := g.val.left 1
  map_one' := rfl
  map_mul' g h := by
    change g.val.left 1 * h.val.left (g.val.right⁻¹ * 1) =
      g.val.left 1 * h.val.left 1
    rw [(mem_wreathSwapCentralizer_iff M h.val).mp h.property]

/-- The diagonal copy gives a section of the evaluation homomorphism. -/
def wreathDiagonal (m : M) : wreathSwapCentralizer M :=
  ⟨⟨fun _ => m, 1⟩, (mem_wreathSwapCentralizer_iff M _).mpr (fun _ => rfl)⟩

theorem wreathCentralizerEvaluation_surjective :
    Function.Surjective (wreathCentralizerEvaluation M) :=
  fun m => ⟨wreathDiagonal M m, rfl⟩

/-- The swap, regarded as an element of its own centralizer. -/
def wreathSwapInCentralizer : wreathSwapCentralizer M :=
  ⟨wreathSwap M, (mem_wreathSwapCentralizer_iff M _).mpr (fun _ => rfl)⟩

/-- The kernel consists exactly of the powers of the factor swap. -/
theorem wreathCentralizerEvaluation_ker :
    (wreathCentralizerEvaluation M).ker =
      Subgroup.zpowers (wreathSwapInCentralizer M) := by
  apply le_antisymm
  · intro g hg
    have he : g.val.left 1 = 1 := hg
    have hl : g.val.left = 1 := by
      funext x
      rw [(mem_wreathSwapCentralizer_iff M g.val).mp g.property x, he]
      rfl
    rcases wreathParity_cases g.val.right with hr | hr
    · have h : g = 1 := by
        apply Subtype.ext
        exact RegularWreathProduct.ext hl hr
      rw [h]
      exact Subgroup.one_mem _
    · have h : g = wreathSwapInCentralizer M := by
        apply Subtype.ext
        exact RegularWreathProduct.ext hl hr
      rw [h]
      exact Subgroup.mem_zpowers _
  · apply Subgroup.zpowers_le.mpr
    rfl

instance wreathSwapPowers_normal :
    (Subgroup.zpowers (wreathSwapInCentralizer M)).Normal := by
  rw [← wreathCentralizerEvaluation_ker]
  infer_instance

/-- Quotienting the swap centralizer by the swap recovers the original group. -/
noncomputable def wreathSwapCentralizerQuotientEquiv :
    (wreathSwapCentralizer M ⧸ Subgroup.zpowers (wreathSwapInCentralizer M)) ≃* M := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (wreathCentralizerEvaluation M) (wreathCentralizerEvaluation_surjective M)
  exact (QuotientGroup.congr (Subgroup.zpowers (wreathSwapInCentralizer M))
    (wreathCentralizerEvaluation M).ker (MulEquiv.refl _)
    (by
      change Subgroup.map (MonoidHom.id _) _ = _
      rw [Subgroup.map_id]
      exact (wreathCentralizerEvaluation_ker M).symm)).trans e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
