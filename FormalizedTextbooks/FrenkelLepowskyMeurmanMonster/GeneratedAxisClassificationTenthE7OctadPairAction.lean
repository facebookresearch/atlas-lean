/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OctadPairData

/-! The actual standard-octad permutation group acts transitively on all twenty-eight pairs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine octad stabilizer preserves all twenty-four support memberships. -/
theorem generatedTenth_e7_octad_point_membership
    (g : generatedTenthE7OctadPermutationGroup) (i : Fin 24) :
    (g.val.val i).val < 8 ↔ i.val < 8 := by
  have h := congrFun ((generatedTenth_e7_octad_permutation_mem g.val).mp g.property)
    (g.val.val i)
  change golayStandardOctad (g.val.val.symm (g.val.val i)) = golayStandardOctad (g.val.val i) at h
  rw [g.val.val.symm_apply_apply] at h
  by_cases hi : i.val < 8 <;> by_cases hj : (g.val.val i).val < 8 <;>
    simp_all [golayStandardOctad]
  omega

/-- The actual restriction of the whole octad stabilizer to its eight coordinates. -/
def generatedTenthE7OctadPointPermutation (g : generatedTenthE7OctadPermutationGroup) :
    Equiv.Perm (Fin 8) where
  toFun i := ⟨(g.val.val (Fin.castAdd 16 i)).val,
    (generatedTenth_e7_octad_point_membership g (Fin.castAdd 16 i)).mpr i.isLt⟩
  invFun i := ⟨(g.val.val.symm (Fin.castAdd 16 i)).val,
    (generatedTenth_e7_octad_point_membership g⁻¹ (Fin.castAdd 16 i)).mpr i.isLt⟩
  left_inv i := by
    apply Fin.ext
    change (g.val.val.symm (g.val.val (Fin.castAdd 16 i))).val = i.val
    rw [g.val.val.symm_apply_apply]
    rfl
  right_inv i := by
    apply Fin.ext
    change (g.val.val (g.val.val.symm (Fin.castAdd 16 i))).val = i.val
    rw [g.val.val.apply_symm_apply]
    rfl

/-- Restriction is a genuine group homomorphism on the entire actual stabilizer. -/
def generatedTenthE7OctadPointPermutationHom : generatedTenthE7OctadPermutationGroup →*
    Equiv.Perm (Fin 8) where
  toFun := generatedTenthE7OctadPointPermutation
  map_one' := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rfl

/-- The actual induced action on the entire unordered-pair universe. -/
def generatedTenthE7OctadPairPermutationHom : generatedTenthE7OctadPermutationGroup →*
    Equiv.Perm generatedTenthE7OctadPairs where
  toFun g := (Equiv.finsetCongr (generatedTenthE7OctadPointPermutationHom g)).subtypeEquiv
    (fun s => by
      change s.card = 2 ↔ (s.map (generatedTenthE7OctadPointPermutationHom g).toEmbedding).card = 2
      rw [Finset.card_map])
  map_one' := by
    apply Equiv.ext
    intro s
    apply Subtype.ext
    change s.val.map (generatedTenthE7OctadPointPermutationHom 1).toEmbedding = s.val
    rw [map_one]
    exact Finset.map_refl
  map_mul' g h := by
    apply Equiv.ext
    intro s
    apply Subtype.ext
    change s.val.map (generatedTenthE7OctadPointPermutationHom (g * h)).toEmbedding =
      (s.val.map (generatedTenthE7OctadPointPermutationHom h).toEmbedding).map
        (generatedTenthE7OctadPointPermutationHom g).toEmbedding
    rw [map_mul, Finset.map_map]
    rfl

instance : MulAction generatedTenthE7OctadPermutationGroup generatedTenthE7OctadPairs :=
  MulAction.compHom generatedTenthE7OctadPairs generatedTenthE7OctadPairPermutationHom

/-- Every original pair word genuinely preserves the whole actual standard octad. -/
theorem generatedTenth_e7_octad_pair_word_mem (i : Fin 28) :
    generatedTenthE7OctadPairWord i ∈ generatedTenthE7OctadPermutationGroup := by
  apply (generatedTenth_e7_octad_permutation_mem _).mpr
  funext j
  change golayStandardOctad ((generatedTenthE7OctadPairWord i).val.symm j) = golayStandardOctad j
  have h := (generatedTenth_e7_octad_pair_word_actual i).1
    ((generatedTenthE7OctadPairWord i).val.symm j)
  rw [(generatedTenthE7OctadPairWord i).val.apply_symm_apply] at h
  unfold golayStandardOctad
  by_cases hj : j.val < 8
  · simp only [ite_eq_left hj, ite_eq_left (h.mp hj)]
  · simp only [ite_eq_right hj, ite_eq_right (fun hi => hj (h.mpr hi))]

/-- Each original certified word as a genuine member of the entire actual octad group. -/
def generatedTenthE7OctadPairWordElement (i : Fin 28) : generatedTenthE7OctadPermutationGroup :=
  ⟨generatedTenthE7OctadPairWord i, generatedTenth_e7_octad_pair_word_mem i⟩

/-- The original unordered first pair in the standard octad. -/
def generatedTenthE7OctadFirstPair : generatedTenthE7OctadPairs := ⟨{0, 1}, by decide⟩

/-- Every original pair source is an actual member of the complete unordered-pair universe. -/
def generatedTenthE7OctadPairDataElement (i : Fin 28) : generatedTenthE7OctadPairs :=
  ⟨generatedTenthE7OctadPairData i, generatedTenth_e7_octad_pair_data_card i⟩

/-- Original source words attain their full actual unordered pair exactly. -/
theorem generatedTenth_e7_octad_pair_word_image (i : Fin 28) :
    generatedTenthE7OctadPairWordElement i • generatedTenthE7OctadFirstPair =
      generatedTenthE7OctadPairDataElement i := by
  have h0 : generatedTenthE7OctadPointPermutationHom (generatedTenthE7OctadPairWordElement i) 0 =
      generatedTenthE7OctadPairLeft i := by
    apply Fin.ext
    change ((generatedTenthE7OctadPairWord i).val 0).val =
      (generatedTenthE7OctadPairLeft i).val
    exact congrArg Fin.val (generatedTenth_e7_octad_pair_word_actual i).2.1
  have h1 : generatedTenthE7OctadPointPermutationHom (generatedTenthE7OctadPairWordElement i) 1 =
      generatedTenthE7OctadPairRight i := by
    apply Fin.ext
    change ((generatedTenthE7OctadPairWord i).val 1).val =
      (generatedTenthE7OctadPairRight i).val
    exact congrArg Fin.val (generatedTenth_e7_octad_pair_word_actual i).2.2
  apply Subtype.ext
  change ({0, 1} : Finset (Fin 8)).map
    (generatedTenthE7OctadPointPermutationHom
      (generatedTenthE7OctadPairWordElement i)).toEmbedding =
      generatedTenthE7OctadPairData i
  simp [generatedTenthE7OctadPairData, h0, h1]

/-- All actual unordered pairs biject with the complete original twenty-eight source addresses. -/
def generatedTenthE7OctadPairDataEquiv : Fin 28 ≃ generatedTenthE7OctadPairs :=
  Equiv.ofBijective generatedTenthE7OctadPairDataElement
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j h
      exact generatedTenth_e7_octad_pair_data_injective (congrArg Subtype.val h), by
      rw [Nat.card_fin, generatedTenth_e7_octad_pairs_card]⟩)

/-- The entire actual octad stabilizer is transitive on the whole actual unordered-pair set. -/
theorem generatedTenth_e7_octad_pair_transitive (r s : generatedTenthE7OctadPairs) :
    ∃ g : generatedTenthE7OctadPermutationGroup, g • r = s := by
  obtain ⟨i, rfl⟩ := generatedTenthE7OctadPairDataEquiv.surjective r
  obtain ⟨j, rfl⟩ := generatedTenthE7OctadPairDataEquiv.surjective s
  refine ⟨generatedTenthE7OctadPairWordElement j *
    (generatedTenthE7OctadPairWordElement i)⁻¹, ?_⟩
  change (generatedTenthE7OctadPairWordElement j *
    (generatedTenthE7OctadPairWordElement i)⁻¹) • generatedTenthE7OctadPairDataElement i =
      generatedTenthE7OctadPairDataElement j
  rw [← generatedTenth_e7_octad_pair_word_image i, mul_smul, inv_smul_smul,
    generatedTenth_e7_octad_pair_word_image j]

/-- Every actual octad coordinate pair has the entire twenty-eight-pair orbit. -/
theorem generatedTenth_e7_octad_pair_orbit (r : generatedTenthE7OctadPairs) :
    MulAction.orbit generatedTenthE7OctadPermutationGroup r = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro s
  exact generatedTenth_e7_octad_pair_transitive r s

/-- The actual pair orbit has cardinality twenty-eight, without a transitivity premise. -/
theorem generatedTenth_e7_octad_pair_orbit_card (r : generatedTenthE7OctadPairs) :
    Nat.card (MulAction.orbit generatedTenthE7OctadPermutationGroup r) = 28 := by
  rw [generatedTenth_e7_octad_pair_orbit, Nat.card_univ, generatedTenth_e7_octad_pairs_card]

/-- The entire actual octad and unordered-pair permutation stabilizer has order11520. -/
theorem generatedTenth_e7_octad_pair_stabilizer_card (r : generatedTenthE7OctadPairs) :
    Nat.card (MulAction.stabilizer generatedTenthE7OctadPermutationGroup r) = 11520 := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup generatedTenthE7OctadPermutationGroup r)
  rw [Nat.card_prod, generatedTenth_e7_octad_pair_orbit_card,
    generatedTenth_e7_octad_permutation_group_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
