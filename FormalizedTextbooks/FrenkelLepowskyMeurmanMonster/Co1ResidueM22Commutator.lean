/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22LocalConnected
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryCommutatorBound

/-! The original Golay auxiliary M22 geometry meets the explicit hypotheses of
Ivanov II Lemma2.3.7. Every generated representation has central commutator of order≤2. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original auxiliary hexad line consists of three distinct pair points. -/
theorem co1ResidueM22_line_distinct (p q : Fin 24) (hpq : p ≠ q)
    (s t u : Co1ResidueM22Point p q) (h : co1ResidueM22Line p q s t u) :
    s ≠ t ∧ t ≠ u ∧ u ≠ s := by
  obtain ⟨o, hp, hq, he⟩ := h
  have hc := co1ResidueM22Hexad_card p q hpq o hp hq
  refine ⟨?_, ?_, ?_⟩
  · intro hst
    rw [hst, Finset.union_self] at he
    have hb := Finset.card_union_le t.val u.val
    rw [he, hc, t.property.1, u.property.1] at hb
    omega
  · intro htu
    rw [htu, Finset.union_assoc, Finset.union_self] at he
    have hb := Finset.card_union_le s.val u.val
    rw [he, hc, s.property.1, u.property.1] at hb
    omega
  · intro hus
    rw [hus, Finset.union_eq_left.mpr (Finset.subset_union_left)] at he
    have hb := Finset.card_union_le s.val t.val
    rw [he, hc, s.property.1, t.property.1] at hb
    omega

/-- The actual rooted auxiliary geometry has a genuine hexad line. -/
theorem co1ResidueM22_line_exists : ∃ s t u : Co1ResidueM22Point 0 1,
    co1ResidueM22Line 0 1 s t u := by
  let o := (co1ResidueM22FiniteOctad 0).val
  have h0 : (0 : Fin 24) ∈ golayOctadSupport o := by
    simpa only [o, golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_zero] using (co1ResidueM22FiniteOctad 0).property.1
  have h1 : (1 : Fin 24) ∈ golayOctadSupport o := by
    simpa only [o, golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_one] using (co1ResidueM22FiniteOctad 0).property.2
  let e := co1ResidueM22HexadCoordinates 0 1 (by decide +kernel) o h0 h1
  exact ⟨_, _, _, co1ResidueM22HexadPair_line 0 1 o h0 h1 e id Function.bijective_id⟩

/-- The original rooted Golay hexad geometry satisfies both genuine-line connectivity contracts. -/
def co1ResidueM22CommutatorGeometry : Co1GeometryCommutatorGeometry (Co1ResidueM22Point 0 1) where
  distant := co1ResidueM22Distant 0 1
  line := co1ResidueM22Line 0 1
  distant_symm := co1ResidueM22Distant_symm 0 1
  connected := co1ResidueM22Finite_global_connected
  line_distinct := co1ResidueM22_line_distinct 0 1 (by decide +kernel)
  line_exists := co1ResidueM22_line_exists
  local_connected := co1ResidueM22_local_connected

/-- Every generated group representation of the actual auxiliary M22 hexad lines
has a finite central commutator subgroup of order at most two. -/
theorem co1ResidueM22_representation_commutator_bound {G : Type*} [Group G]
    (phi : Co1ResidueM22Point 0 1 → G) (hsquare : ∀ s, phi s * phi s = 1)
    (hline : ∀ s t u, co1ResidueM22Line 0 1 s t u → phi s * phi t * phi u = 1)
    (hgen : Subgroup.closure (Set.range phi) = ⊤) :
    commutator G ≤ Subgroup.center G ∧
      Finite (commutator G) ∧ Nat.card (commutator G) ≤ 2 := by
  let representation : Co1GeometryCommutatorRepresentation co1ResidueM22CommutatorGeometry G :=
    { point := phi
      square := hsquare
      line_product := hline
      close_commute := co1ResidueM22_nearby_commute 0 1 (by decide +kernel) phi hsquare hline
      generates := hgen }
  exact ⟨co1GeometryCommutator_le_center _ representation,
    co1GeometryCommutator_finite_card_le_two _ representation⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
