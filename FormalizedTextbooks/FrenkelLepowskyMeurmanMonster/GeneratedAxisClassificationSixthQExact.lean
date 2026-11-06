/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQModulation

/-! The original full sixth-axis extraspecial stabilizer has exactly four elements. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exact membership in the genuine full-axis Q stabilizer, with no tensor-only weakening. -/
theorem generatedSixthAxisQStabilizer_mem_iff (q : Q) :
    q ∈ generatedSixthAxisQStabilizer ↔
      ∃ j : Fin 4, q = cocodeQ (generatedSixthRootQModulation j) := by
  constructor
  · intro hq
    exact generatedSixth_Q_fixed_mem q hq
  · rintro ⟨j, rfl⟩
    exact generatedSixth_root_Q_mem j

/-- The literal four original cocodes enumerate the entire actual full-axis Q stabilizer. -/
def generatedSixthAxisQStabilizerEquiv : Fin 4 ≃ generatedSixthAxisQStabilizer :=
  Equiv.ofBijective
    (fun j => ⟨cocodeQ (generatedSixthRootQModulation j), generatedSixth_root_Q_mem j⟩)
    ⟨by
      intro a b h
      apply generatedSixth_root_Q_modulation_injective
      have he := congrArg (fun q : generatedSixthAxisQStabilizer => spinModulation q.val) h
      simpa only [cocodeQ_modulation] using he,
    by
      intro q
      obtain ⟨j, hj⟩ := (generatedSixthAxisQStabilizer_mem_iff q.val).mp q.property
      refine ⟨j, ?_⟩
      apply Subtype.ext
      exact hj.symm⟩

/-- The actual full-coordinate sixth-axis Q stabilizer has cardinality exactly four. -/
theorem generatedSixthAxisQStabilizer_card : Nat.card generatedSixthAxisQStabilizer = 4 := by
  have h := Nat.card_congr generatedSixthAxisQStabilizerEquiv
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
