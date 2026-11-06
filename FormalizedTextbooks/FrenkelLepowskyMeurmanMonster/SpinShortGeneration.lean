/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortSpan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit

/-! The actual preferred short lifts, together with the central involution, generate Q.
The input is the proved integer short span of the genuine lattice; reduction is modulo
twice the lattice, not modulo ambient integer coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The short lattice vectors span the actual integral lattice as an integer module. -/
theorem spinShort_lattice_span :
    Submodule.span ℤ (Set.range griessShortLatticeVector) = ⊤ := by
  apply Submodule.map_injective_of_injective leechIntegral.injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top]
  have hs : leechIntegral.subtype '' Set.range griessShortLatticeVector =
      Set.range griessShortIntegral := by
    ext x
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨griessShortLatticeVector r, ⟨r, rfl⟩, rfl⟩
  rw [hs]
  exact leechShortIntegralSpan_eq

/-- The genuine lattice reduction followed by the fixed hyperbolic coordinate dictionary. -/
noncomputable def spinShortReductionCoordinates :
    leechIntegral →ₗ[ℤ] (Fin 24 → ZMod 2) :=
  (leechHyperbolicCoordinates.toLinearMap.toAddMonoidHom.comp leechReduction).toIntLinearMap

theorem spinShortReductionCoordinates_surjective :
    Function.Surjective spinShortReductionCoordinates :=
  leechHyperbolicCoordinates.surjective.comp
    (QuotientAddGroup.mk'_surjective twiceLeechIntegral)

/-- Any Q subgroup containing every actual preferred short lift has full binary image. -/
theorem spinShort_binaryImage_eq_top (K : Subgroup Q)
    (hshort : ∀ r : GriessShortIndex, griessShortQ r ∈ K) :
    qSubgroupBinaryImage K = ⊤ := by
  let P : Submodule ℤ leechIntegral :=
    ((qSubgroupBinaryImage K).restrictScalars ℤ).comap spinShortReductionCoordinates
  have hP : P = ⊤ := by
    apply top_unique
    rw [← spinShort_lattice_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    change ofAdd (leechHyperbolicCoordinates (griessShortClass r)) ∈ K.map qQuotHom
    exact ⟨griessShortQ r, hshort r, rfl⟩
  apply top_unique
  intro v _
  obtain ⟨u, rfl⟩ := spinShortReductionCoordinates_surjective v
  have hu : u ∈ P := by rw [hP]; exact Submodule.mem_top
  exact hu

/-- Containing the actual short lifts and central involution is sufficient for all of Q. -/
theorem spinShort_subgroup_eq_top (K : Subgroup Q)
    (hshort : ∀ r : GriessShortIndex, griessShortQ r ∈ K)
    (hz : qCentralInvolution ∈ K) : K = ⊤ :=
  qSubgroup_eq_top_of_binaryImage_eq_top K (centerQ_le_of_central_mem K hz)
    (spinShort_binaryImage_eq_top K hshort)

/-- The actual preferred short lifts, together with the central sign, generate all of Q. -/
theorem spinShort_closure_eq_top :
    Subgroup.closure (Set.range griessShortQ ∪ {qCentralInvolution}) = ⊤ := by
  apply spinShort_subgroup_eq_top
  · intro r
    exact Subgroup.subset_closure (Or.inl ⟨r, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr rfl)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
