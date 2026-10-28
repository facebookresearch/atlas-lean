/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightFrameTransport

/-! The actual coordinate E8 section contains precisely 135 norm-eight lattice classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual classes represented by norm-eight vectors in the specified section. -/
def generatedOctadNormEightFrameClasses (c : Fin 24 → ZMod 2) : Set LeechModTwo :=
  Set.range (fun x : GeneratedOctadNormEight c => leechReduction x.val)

/-- There are exactly 135 genuine norm-eight classes in the standard coordinate section. -/
theorem generatedStandardOctad_frameClasses_card :
    Nat.card (generatedOctadNormEightFrameClasses golayStandardOctad) = 135 := by
  classical
  let X := GeneratedOctadNormEight golayStandardOctad
  let B := generatedOctadNormEightFrameClasses golayStandardOctad
  let f : X → B := fun x => ⟨leechReduction x.val, ⟨x, rfl⟩⟩
  let : Finite X := Finite.of_equiv _ generatedOctadNormEightEnumerationEquiv
  have hf : Function.Surjective f := by
    rintro ⟨b, u, hu⟩
    exact ⟨u, Subtype.ext hu⟩
  let : Finite B := Finite.of_surjective f hf
  let : Fintype B := Fintype.ofFinite B
  have hcard (b : B) : Nat.card {x : X // f x = b} = 16 := by
    obtain ⟨u, hu⟩ := b.property
    change leechReduction u.val = b.val at hu
    have E : {x : X // f x = b} ≃
        GeneratedOctadNormEightReductionFiber golayStandardOctad (leechReduction u.val) :=
      Equiv.subtypeEquivRight (fun x => by
        change f x = b ↔ leechReduction x.val = leechReduction u.val
        rw [Subtype.ext_iff]
        change leechReduction x.val = b.val ↔ leechReduction x.val = leechReduction u.val
        rw [hu])
    rw [Nat.card_congr E]
    exact generatedStandardOctad_reductionFiber_card u
  have h : 2160 = Nat.card B * 16 := by
    calc
      2160 = Nat.card X := generatedStandardOctad_normEight_card.symm
      _ = Nat.card (Σ b : B, {x : X // f x = b}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
      _ = ∑ b : B, Nat.card {x : X // f x = b} := Nat.card_sigma
      _ = ∑ _b : B, 16 := Finset.sum_congr rfl (fun b _ => hcard b)
      _ = Nat.card B * 16 := by simp [Nat.card_eq_fintype_card]
  change Nat.card B = 135
  omega

/-- Actual Golay transport induces a bijection of the represented lattice classes. -/
def generatedOctadFrameClassesPermutationEquiv (c d : Fin 24 → ZMod 2)
    (p : golayAutomorphismSubgroup) (hp : golayPermute p.val c = d) :
    generatedOctadNormEightFrameClasses c ≃ generatedOctadNormEightFrameClasses d := by
  let E := generatedOctadNormEightPermutationEquiv c d p hp
  let A := leechQuotientAut (leechIntegralAction (golayPermutationIsometry p))
  have hE (x : GeneratedOctadNormEight c) :
      leechReduction (E x).val = A (leechReduction x.val) := rfl
  exact {
    toFun := fun b => ⟨A b.val, by
      obtain ⟨x, hx⟩ := b.property
      exact ⟨E x, (hE x).trans (congrArg A hx)⟩⟩
    invFun := fun b => ⟨A.symm b.val, by
      obtain ⟨y, hy⟩ := b.property
      refine ⟨E.symm y, ?_⟩
      apply A.injective
      rw [A.apply_symm_apply]
      have h := hE (E.symm y)
      rw [E.apply_symm_apply] at h
      exact h.symm.trans hy⟩
    left_inv := fun b => Subtype.ext (A.symm_apply_apply b.val)
    right_inv := fun b => Subtype.ext (A.apply_symm_apply b.val)
  }

/-- Every actual coordinate Golay octad contains exactly 135 norm-eight lattice classes. -/
theorem generatedOctad_frameClasses_card (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8) :
    Nat.card (generatedOctadNormEightFrameClasses c) = 135 := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard c hc hw
  rw [Nat.card_congr (generatedOctadFrameClassesPermutationEquiv c golayStandardOctad p hp)]
  exact generatedStandardOctad_frameClasses_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
