/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The original source central coefficient is an exact binary group equivalence. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoCenterExact

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Nontriviality makes the faithful canonical source commutator character surjective. -/
theorem co1UniversalCommutatorCharacter_surjective
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    Function.Surjective (co1UniversalCommutatorCharacter hfinite hcard) := by
  classical
  obtain ⟨z, hz, _⟩ := co1Universal_commutator_unique_involution hfinite hcard hne
  intro a
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases h a.toAdd with ha | ha
  · refine ⟨1, ?_⟩
    change Multiplicative.ofAdd (co1UniversalCommutatorCoefficient 1) = a
    simp only [co1UniversalCommutatorCoefficient, ite_true]
    exact (congrArg Multiplicative.ofAdd ha).symm
  · refine ⟨z, ?_⟩
    change Multiplicative.ofAdd (co1UniversalCommutatorCoefficient z) = a
    simp only [co1UniversalCommutatorCoefficient, hz.1, ite_false]
    exact (congrArg Multiplicative.ofAdd ha).symm

/-- The original source commutator is canonically the actual two-element coefficient group. -/
def co1UniversalCommutatorEquiv
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    commutator Co1UniversalPresentation ≃* Multiplicative (ZMod 2) :=
  MulEquiv.ofBijective (co1UniversalCommutatorCharacter hfinite hcard)
    ⟨co1UniversalCommutatorCharacter_injective hfinite hcard,
      co1UniversalCommutatorCharacter_surjective hfinite hcard hne⟩

/-- The exact central coefficient embedding into the original source presentation. -/
def co1UniversalCentralEmbedding
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    Multiplicative (ZMod 2) →* Co1UniversalPresentation :=
  (commutator Co1UniversalPresentation).subtype.comp
    (co1UniversalCommutatorEquiv hfinite hcard hne).symm.toMonoidHom

/-- The source central embedding exactly inverts every source commutator coefficient. -/
theorem co1UniversalCentralEmbedding_coefficient
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥)
    (c : commutator Co1UniversalPresentation) :
    co1UniversalCentralEmbedding hfinite hcard hne
      (Multiplicative.ofAdd (co1UniversalCommutatorCoefficient c)) = c.val := by
  exact congrArg Subtype.val
    ((co1UniversalCommutatorEquiv hfinite hcard hne).symm_apply_apply c)

/-- The literal coefficient embedding has central image in the original source group. -/
theorem co1UniversalCentralEmbedding_mem_center
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (a : Multiplicative (ZMod 2)) :
    co1UniversalCentralEmbedding hfinite hcard hne a ∈ Subgroup.center Co1UniversalPresentation :=
  co1Universal_commutator_le_center_of_card_le_two hfinite hcard
    ((co1UniversalCommutatorEquiv hfinite hcard hne).symm a).property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
