/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2FlagAction

/-! Actual pairs of Leech roots with pairing16 yield the counted rooted flags. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Normalizing both integer roots does not change their actual real plane. -/
theorem leechRootedA2_embedding_span (u v : Fin 24 → ℤ) :
    Submodule.span ℝ ({leechCoordinateEmbedding u, leechCoordinateEmbedding v} :
      Set (Fin 24 → ℝ)) =
    Submodule.span ℝ ({leechRootedA2RealVector u, leechRootedA2RealVector v} :
      Set (Fin 24 → ℝ)) := by
  have hs : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hf (w : Fin 24 → ℤ) : leechCoordinateEmbedding w =
      (Real.sqrt 8)⁻¹ • leechRootedA2RealVector w := by
    funext i
    change (w i : ℝ) / Real.sqrt 8 = (Real.sqrt 8)⁻¹ * (w i : ℝ)
    ring
  have hb (w : Fin 24 → ℤ) : leechRootedA2RealVector w =
      Real.sqrt 8 • leechCoordinateEmbedding w := by
    funext i
    change (w i : ℝ) = Real.sqrt 8 * ((w i : ℝ) / Real.sqrt 8)
    field_simp
  apply le_antisymm <;> apply Submodule.span_le.mpr <;> intro x hx <;>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
  · rw [hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
  · have he := Set.mem_singleton_iff.mp hx
    subst x
    rw [hf]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
  · have he := Set.mem_singleton_iff.mp hx
    subst x
    rw [hb]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- Every original short-root pair with pairing16 transports to a genuine standard-root flag. -/
theorem leechRootedA2TwoRootFlag_transported (r s : GriessShortIndex)
    (hrs : leechIntegralPairing (griessShortLatticeVector r).val
      (griessShortLatticeVector s).val = 16) :
    ∃ e : leechIsomSubgroup, ∃ p : leechRootedA2Plane,
      e • (Submodule.span ℝ ({griessShortVector r, griessShortVector s} :
        Set (Fin 24 → ℝ)), r) = (p.val, leechRootedA2RootAddress) := by
  obtain ⟨e, _, he⟩ := leechShort_concrete_vector_transitive r leechRootedA2RootAddress
  have hei : leechIntegralAction e (griessShortLatticeVector r) = leechRootedA2Root := by
    apply Subtype.ext
    apply leechCoordinateEmbedding_injective
    rw [leechIntegralAction_embedding]
    change e.val (griessShortVector r) = leechCoordinateEmbedding leechRootedA2Root.val
    rw [he, ← leechRootedA2RootAddress_integral]
    rfl
  have hp := leechRootedA2_integral_pairing_action e
    (griessShortLatticeVector r) (griessShortLatticeVector s)
  rw [hei, hrs] at hp
  have hcoord : (leechIntegralAction e (griessShortLatticeVector s)).val 0 +
      (leechIntegralAction e (griessShortLatticeVector s)).val 1 = 4 := by
    change leechIntegralPairing leechRootedA2RootIntegral
      (leechIntegralAction e (griessShortLatticeVector s)).val = 16 at hp
    rw [leechRootedA2RootIntegral_pairing] at hp
    omega
  let v : leechRootedA2OrientedNeighbor :=
    ⟨leechIntegralAction e (griessShortLatticeVector s),
      by rw [leechIntegralAction_squareSum]; exact griessShortIntegral_squareSum s, hcoord⟩
  refine ⟨e, leechRootedA2PlaneOfNeighbor v, ?_⟩
  apply Prod.ext
  · change (Submodule.span ℝ ({griessShortVector r, griessShortVector s} :
      Set (Fin 24 → ℝ))).map e.val.toLinearMap = leechRootedA2NeighborPlane v
    rw [Submodule.map_span, Set.image_pair]
    change Submodule.span ℝ ({e.val (leechCoordinateEmbedding (griessShortLatticeVector r).val),
        e.val (leechCoordinateEmbedding (griessShortLatticeVector s).val)} :
      Set (Fin 24 → ℝ)) = leechRootedA2NeighborPlane v
    rw [← leechIntegralAction_embedding, ← leechIntegralAction_embedding, hei]
    exact leechRootedA2_embedding_span leechRootedA2Root.val v.val.val
  · change griessShortPermutation e r = leechRootedA2RootAddress
    apply (leechRootedA2_short_perm_eq_iff e r leechRootedA2RootAddress).mpr
    exact Or.inl (hei.trans leechRootedA2RootAddress_integral.symm)

/-- The actual stabilizer of two original roots with pairing16 has the exact rooted-flag order. -/
theorem leechRootedA2TwoRootFlag_stabilizer_card (r s : GriessShortIndex)
    (hrs : leechIntegralPairing (griessShortLatticeVector r).val
      (griessShortLatticeVector s).val = 16) :
    Nat.card (MulAction.stabilizer leechIsomSubgroup
      (Submodule.span ℝ ({griessShortVector r, griessShortVector s} :
        Set (Fin 24 → ℝ)), r)) = 36787322880 := by
  obtain ⟨e, p, he⟩ := leechRootedA2TwoRootFlag_transported r s hrs
  exact leechRootedA2Flag_stabilizer_card_of_transport _ r p e he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
