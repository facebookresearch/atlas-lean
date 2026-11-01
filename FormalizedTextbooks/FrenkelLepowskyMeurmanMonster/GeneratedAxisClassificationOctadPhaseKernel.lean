/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadBinaryRank

/-! Eight simultaneous actual extraspecial phase constraints. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Binary commutator phases against the eight checked actual roots. -/
def generatedOctadBasisBinaryPhases :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun v j := qBeta v (generatedOctadBasisBinaryMatrix.col j) +
    qBeta (generatedOctadBasisBinaryMatrix.col j) v
  map_add' u v := by
    funext j
    simp only [qBeta_add_left, qBeta_add_right, Pi.add_apply]
    abel
  map_smul' a v := by
    funext j
    simp only [qBeta_smul_left, qBeta_smul_right, RingHom.id_apply, Pi.smul_apply,
      smul_add]

/-- The supplied commutator duals give a right inverse to all eight phases. -/
theorem generatedOctadBasis_binary_phases_right_inverse :
    generatedOctadBasisBinaryPhases.comp generatedOctadBasisDual.mulVecLin =
      LinearMap.id := by
  apply LinearMap.pi_ext
  intro i a
  have hs : Pi.single i a = a • Pi.single i (1 : ZMod 2) := by
    funext j
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hroot : generatedOctadBasisBinaryPhases
      (generatedOctadBasisDual.mulVecLin (Pi.single i 1)) = Pi.single i 1 := by
    ext j
    change qBeta (generatedOctadBasisDual *ᵥ Pi.single i 1)
        (generatedOctadBasisBinaryMatrix.col j) +
      qBeta (generatedOctadBasisBinaryMatrix.col j)
        (generatedOctadBasisDual *ᵥ Pi.single i 1) = (Pi.single i (1 : ZMod 2) : Fin 8 → ZMod 2) j
    rw [Matrix.mulVec_single_one, generatedOctadBasis_dual_certificate]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, Pi.single_eq_same]
    · simp only [hij, ite_false, Pi.single_eq_of_ne (Ne.symm hij)]
  change generatedOctadBasisBinaryPhases
    (generatedOctadBasisDual.mulVecLin (Pi.single i a)) = Pi.single i a
  rw [hs, map_smul, map_smul, hroot]

set_option maxHeartbeats 800000 in
-- Applying the explicit right-inverse certificate elaborates two finite matrix maps.
/-- Every assignment of the eight actual binary phases is attained. -/
theorem generatedOctadBasis_binary_phases_surjective :
    Function.Surjective generatedOctadBasisBinaryPhases := by
  intro a
  refine ⟨generatedOctadBasisDual.mulVecLin a, ?_⟩
  exact LinearMap.congr_fun generatedOctadBasis_binary_phases_right_inverse a

/-- The eight genuine preferred-short conjugation phases on Q. -/
noncomputable def generatedOctadBasisQPhases : Q →* Multiplicative (Fin 8 → ZMod 2) where
  toFun q := ofAdd (fun j => toAdd (localAxisQPhase (generatedOctadBasisLabel j) q))
  map_one' := by simp only [map_one]; rfl
  map_mul' q k := by
    apply toAdd.injective
    funext j
    simp only [map_mul, toAdd_mul, toAdd_ofAdd, Pi.add_apply]

/-- The actual preferred lifts agree with the checked binary phase map. -/
theorem generatedOctadBasis_Q_phases_apply (q : Q) :
    toAdd (generatedOctadBasisQPhases q) =
      generatedOctadBasisBinaryPhases (toAdd q.base) := by
  funext j
  change qBeta (toAdd q.base) (toAdd (griessShortQ (generatedOctadBasisLabel j)).base) +
    qBeta (toAdd (griessShortQ (generatedOctadBasisLabel j)).base) (toAdd q.base) = _
  rw [generatedOctadBasis_actual_base]
  rfl

/-- All 256 sign assignments on these actual short roots are realized by Q. -/
theorem generatedOctadBasis_Q_phases_surjective :
    Function.Surjective generatedOctadBasisQPhases := by
  intro a
  obtain ⟨v, hv⟩ := generatedOctadBasis_binary_phases_surjective (toAdd a)
  refine ⟨⟨ofAdd v, 1⟩, toAdd.injective ?_⟩
  rw [generatedOctadBasis_Q_phases_apply]
  exact hv

set_option maxRecDepth 4000 in
/-- Exactly 2^17 elements of the actual extraspecial group have zero phase
on all eight independent preferred-short lifts. -/
theorem generatedOctadBasis_Q_phases_kernel_card :
    Nat.card generatedOctadBasisQPhases.ker = 2 ^ 17 := by
  have h := generatedOctadBasisQPhases.ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr generatedOctadBasis_Q_phases_surjective,
    Subgroup.card_top, q_card] at h
  have hc : Nat.card (Multiplicative (Fin 8 → ZMod 2)) = 256 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [hc] at h
  norm_num only [Nat.reducePow] at h ⊢
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
