/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionFirstRow

/-! Genuine feasible transition cosets are actual signed Ω conjugates, with the
central phase retained. This description does not identify a signed Ω element
with its binary quotient class. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Ω conjugates reached by elements fixing the first actual axis. -/
def generatedFeasibleOmegaConjugacyOrbit (p : Fin 276) : Set H :=
  Set.range (fun h : localAxisStabilizer p => h.val⁻¹ * inclQ sourceOmegaQ * h.val)

/-- Equality of the full Ω conjugates is precisely the genuine right coset relation. -/
theorem generatedFeasibleOmegaConjugate_eq_iff (p : Fin 276)
    (a b : localAxisStabilizer p) :
    a.val⁻¹ * inclQ sourceOmegaQ * a.val = b.val⁻¹ * inclQ sourceOmegaQ * b.val ↔
      QuotientGroup.rightRel (localFeasibleTransitionSubgroup p) a b := by
  rw [QuotientGroup.rightRel_apply]
  change _ ↔ b.val * a.val⁻¹ ∈ Subgroup.centralizer {inclQ sourceOmegaQ}
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have he := congrArg (fun z : H => b.val * z * a.val⁻¹) h
    change b.val * a.val⁻¹ * inclQ sourceOmegaQ = inclQ sourceOmegaQ * (b.val * a.val⁻¹)
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel_left, inv_mul_cancel_right, mul_inv_cancel, inv_mul_cancel, mul_one] using he
  · intro h
    have he := congrArg (fun z : H => b.val⁻¹ * z * a.val) h
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel_left, inv_mul_cancel_right, mul_inv_cancel, inv_mul_cancel, mul_one] using he

/-- The original transition coset sends Ω to its actual full conjugate. -/
def generatedFeasibleOmegaConjugateMap (p : Fin 276) :
    generatedFeasibleTransitionCosetSpace p → generatedFeasibleOmegaConjugacyOrbit p :=
  Quotient.lift (fun h => ⟨h.val⁻¹ * inclQ sourceOmegaQ * h.val, ⟨h, rfl⟩⟩)
    (fun a b hab => Subtype.ext ((generatedFeasibleOmegaConjugate_eq_iff p a b).mpr hab))

/-- Every actual signed Ω conjugate has a genuine transition coset. -/
theorem generatedFeasibleOmegaConjugateMap_surjective (p : Fin 276) :
    Function.Surjective (generatedFeasibleOmegaConjugateMap p) := by
  rintro ⟨x, h, rfl⟩
  exact ⟨Quotient.mk _ h, rfl⟩

/-- Retaining the full Ω element separates all genuine transition cosets. -/
theorem generatedFeasibleOmegaConjugateMap_injective (p : Fin 276) :
    Function.Injective (generatedFeasibleOmegaConjugateMap p) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      intro he
      exact Quotient.sound' ((generatedFeasibleOmegaConjugate_eq_iff p a b).mp
        (congrArg Subtype.val he))

/-- The actual feasible transition domain is exactly the full signed Ω conjugacy orbit. -/
def generatedFeasibleOmegaConjugacyEquiv (p : Fin 276) :
    generatedFeasibleTransitionCosetSpace p ≃ generatedFeasibleOmegaConjugacyOrbit p :=
  Equiv.ofBijective (generatedFeasibleOmegaConjugateMap p)
    ⟨generatedFeasibleOmegaConjugateMap_injective p,
      generatedFeasibleOmegaConjugateMap_surjective p⟩

/-- There are 93,150 actual full Ω elements in the feasible transition domain. -/
theorem generatedFeasibleOmegaConjugacyOrbit_card (p : Fin 276) :
    Nat.card (generatedFeasibleOmegaConjugacyOrbit p) = 93150 := by
  rw [← Nat.card_congr (generatedFeasibleOmegaConjugacyEquiv p)]
  exact generatedFeasibleTransitionCosetSpace_card p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
