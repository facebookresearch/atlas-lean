/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerBlocks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralInvolution
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFiniteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityFullProduct
public import Mathlib.GroupTheory.GroupAction.Quotient

/-! Exact counting for the actual generated group and its central involution.

These identities do not enumerate the conjugacy class. In particular they do not
assume, or prove, the Monster order. The orbit is the actual conjugation orbit,
not a separately prescribed set of the desired cardinality. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The distinguished involution as an element of the actual generated group. -/
noncomputable def generatedCentralInvolution : G := qIntoGenerated qCentralInvolution

/-- Its actual conjugacy orbit, without an assumed enumeration. -/
noncomputable def generatedCentralOrbit : Set G :=
  MulAction.orbit (ConjAct G) generatedCentralInvolution

/-- The actual local image inside G. -/
noncomputable def generatedLocalSubgroup : Subgroup G := localIntoGenerated.range

theorem generatedLocalSubgroup_card : Nat.card generatedLocalSubgroup = Nat.card H :=
  (Nat.card_congr (MonoidHom.ofInjective localIntoGenerated_injective).toEquiv).symm

theorem generatedLocalSubgroup_le_centralizer :
    generatedLocalSubgroup ≤ generatedCentralizer :=
  localIntoGenerated_range_le_centralizer

/-- Conjugacy orbit size is the index of the actual centralizer. -/
theorem generatedCentralizer_index :
    generatedCentralizer.index = Nat.card generatedCentralOrbit := by
  rw [generatedCentralizer, Subgroup.centralizer_eq_comap_stabilizer,
    Subgroup.index_comap_of_surjective _ (f := ConjAct.toConjAct.toMonoidHom)
      ConjAct.toConjAct.surjective,
    MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  rfl

/-- Exact orbit--centralizer counting, valid without a finiteness assumption. -/
theorem generated_card_eq_orbit_mul_centralizer :
    Nat.card G = Nat.card generatedCentralOrbit * Nat.card generatedCentralizer := by
  rw [← generatedCentralizer.index_mul_card, generatedCentralizer_index]

/-- Exact local index counting, with the proved concrete local kernel. -/
theorem generated_card_eq_local_index_mul_local_card :
    Nat.card G = generatedLocalSubgroup.index * (2 ^ 25 * Nat.card Co1) := by
  rw [← generatedLocalSubgroup.index_mul_card, generatedLocalSubgroup_card, h_card]

/-- A proved centralizer identification would reduce the global count to the
actual orbit cardinality and the already proved local exact-sequence count. -/
theorem generated_card_eq_orbit_mul_local_card
    (hcentralizer : generatedCentralizer = generatedLocalSubgroup) :
    Nat.card G = Nat.card generatedCentralOrbit * (2 ^ 25 * Nat.card Co1) := by
  rw [generated_card_eq_orbit_mul_centralizer, hcentralizer,
    generatedLocalSubgroup_card, h_card]

/-- Each of the three genuine triality signs, as an element of G. -/
noncomputable def generatedCentralSign (k : Fin 3) : G :=
  ⟨trialityCentralSign k, trialityCentralSign_mem_G k⟩

theorem generatedCentralSign_injective : Function.Injective generatedCentralSign := by
  intro k l h
  exact trialityCentralSign_injective (congrArg Subtype.val h)

/-- The three distinct dictionary signs are in the actual conjugacy orbit. -/
theorem generatedCentralSign_mem_orbit (k : Fin 3) :
    generatedCentralSign k ∈ generatedCentralOrbit := by
  let t : G := ⟨sExtra, sExtra_mem_generated_G⟩
  change generatedCentralSign k ∈ MulAction.orbit (ConjAct G) generatedCentralInvolution
  apply MulAction.mem_orbit_iff.mpr
  fin_cases k
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    exact localCentralGriess_eq_trialityCentralSign
  · refine ⟨ConjAct.toConjAct t, ?_⟩
    apply Subtype.ext
    exact localCentralGriess_conjugate
  · refine ⟨ConjAct.toConjAct (t ^ 2), ?_⟩
    apply Subtype.ext
    exact localCentralGriess_conjugate_square

/-- Triality supplies three distinct elements of the genuine central-involution
conjugacy class. Finiteness follows from the proved coordinate product laws. -/
theorem generatedCentralOrbit_card_ge_three : 3 ≤ Nat.card generatedCentralOrbit := by
  have : Finite G := generated_group_finite_of_triality_product sExtra_preserves_griessProd
  let f : Fin 3 → generatedCentralOrbit :=
    fun k => ⟨generatedCentralSign k, generatedCentralSign_mem_orbit k⟩
  have hf : Function.Injective f := by
    intro k l h
    exact generatedCentralSign_injective (congrArg Subtype.val h)
  simpa using Nat.card_le_card_of_injective f hf

theorem generatedCentralizer_index_ge_three : 3 ≤ generatedCentralizer.index := by
  rw [generatedCentralizer_index]
  exact generatedCentralOrbit_card_ge_three

theorem generatedLocalSubgroup_index_ge_three : 3 ≤ generatedLocalSubgroup.index := by
  have : Finite G := generated_group_finite_of_triality_product sExtra_preserves_griessProd
  exact generatedCentralizer_index_ge_three.trans
    (Subgroup.index_antitone generatedLocalSubgroup_le_centralizer)

/-- Triality proves that the genuine local subgroup is proper in G. -/
theorem generatedLocalSubgroup_ne_top : generatedLocalSubgroup ≠ ⊤ := by
  intro h
  have hindex := generatedLocalSubgroup_index_ge_three
  rw [h, Subgroup.index_top] at hindex
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
