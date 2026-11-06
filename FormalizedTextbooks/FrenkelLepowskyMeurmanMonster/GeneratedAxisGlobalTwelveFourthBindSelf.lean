/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthReverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestColumns

/-! Wrappers reducing Fourth forest roots two, thirteen and fifteen to self-identifications at
explicit one-xi coset representatives.

For a source word `h` whose actual binary root lies in the stabilizer orbit of a forest root (an
explicit word in the five Fourth generators carries the forest root to it), a whole-vector
identification `τ⁻¹ (h v₄) = g v₄` with `g ∈ H` binds the root: both signs at the phase-merged
roots two and thirteen, and the Fourth-class sign at root fifteen given the Odd class of its other
sign. The identifications themselves are hypotheses here; no identification is asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The product of a list of Fourth forest generators. -/
def generatedAxisGlobalTwelveFourthGeneratorWord (ws : List (Fin 5)) : H :=
  (ws.map fun k => (generatedAxisGlobalTwelveFourthGenerator k).val).prod

/-- Every generator word fixes the complete Fourth axis. -/
theorem generatedAxisGlobalTwelveFourthGeneratorWord_mem (ws : List (Fin 5)) :
    generatedAxisGlobalTwelveFourthGeneratorWord ws ∈ generatedFourthLocalAxisStabilizer := by
  induction ws with
  | nil => exact Subgroup.one_mem _
  | cons k ws ih =>
    simp only [generatedAxisGlobalTwelveFourthGeneratorWord, List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (generatedAxisGlobalTwelveFourthGenerator k).property ih

/-- The binary action of a generator word is the iterated column-mask action. -/
theorem generatedAxisGlobalTwelveFourthGeneratorWord_binary (ws : List (Fin 5))
    (x : generatedAxisGlobalBinaryOrbit) (b : ℕ)
    (hx : x.val = monsterCo1GeometryBinaryMaskDecode b) :
    (generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveFourthGeneratorWord ws) x).val =
      monsterCo1GeometryBinaryMaskDecode (ws.foldr (fun k m =>
        generatedAxisGlobalMaskColumnAction
          (generatedAxisGlobalTwelveFourthBinaryColumns k) m) b) := by
  induction ws with
  | nil =>
    change co1BinaryAction (projH 1) x.val = _
    rw [map_one, map_one, hx]
    rfl
  | cons k ws ih =>
    simp only [generatedAxisGlobalTwelveFourthGeneratorWord, List.map_cons, List.prod_cons,
      List.foldr_cons]
    rw [generatedAxisGlobalBinaryAct_mul, generatedAxisGlobalTwelveFourthGenerator_binary]
    change generatedAxisGlobalTwelveFourthBinaryMatrix k *ᵥ
      (generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveFourthGeneratorWord ws) x).val = _
    rw [ih, generatedAxisGlobalTwelveFourthBinaryColumns_action]

private theorem selfSourceProduct_binary (ls : List (Fin 10)) (b : ℕ) :
    co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode
        (ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalOddSourceRows l) x) b) := by
  induction ls generalizing b with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, LinearEquiv.mul_apply]
    rw [ih, generatedAxisGlobalOddSourceLocalLetter_binary]

/-- The binary root of a source word, from a finite mask evaluation. -/
theorem generatedAxisGlobalTwelveFourth_sourceWord_root (ls : List (Fin 10)) (m : ℕ)
    (hm : ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) m = 2048) :
    (generatedAxisGlobalBinaryRoot ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod)).val =
      monsterCo1GeometryBinaryMaskDecode m := by
  have hb : co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod))
      (monsterCo1GeometryBinaryMaskDecode m) = toAdd (qQuotHom sourceOmegaQ) := by
    rw [selfSourceProduct_binary, hm, generatedAxisGlobalTwelveFourth_omega_mask]
  change co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [map_inv, ← hb, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- One-xi coset representative words in the orbits of roots two, thirteen and fifteen. -/
def generatedAxisGlobalTwelveFourthSelfWord : Fin 3 → List (Fin 10) :=
  ![[1, 9, 6, 9], [1, 7, 7, 9, 7, 9, 6], [1, 9, 6, 6, 3, 6]]

/-- The corresponding actual local elements. -/
def generatedAxisGlobalTwelveFourthSelfLocal (i : Fin 3) : H :=
  ((generatedAxisGlobalTwelveFourthSelfWord i).map generatedAxisGlobalOddSourceLocalLetter).prod

/-- The forest roots of the three representatives. -/
def generatedAxisGlobalTwelveFourthSelfRoot : Fin 3 → Fin 16 := ![2, 13, 15]

/-- Binary root masks of the three representatives. -/
def generatedAxisGlobalTwelveFourthSelfMask : Fin 3 → ℕ := ![7401472, 7749632, 5494784]

/-- Generator words carrying each forest root to the binary root of its representative. -/
def generatedAxisGlobalTwelveFourthSelfPath : Fin 3 → List (Fin 5) :=
  ![[4, 0, 4, 0, 1, 4, 0], [4, 1, 4, 2, 0, 2, 3, 0], [2, 3, 2, 1]]

set_option maxHeartbeats 20000000 in
-- Evaluate three source words and three generator words on their masks.
/-- The finite mask identities for the three representatives. -/
theorem generatedAxisGlobalTwelveFourthSelf_certificate : ∀ i : Fin 3,
    (generatedAxisGlobalTwelveFourthSelfWord i).foldr (fun l x =>
        generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
      (generatedAxisGlobalTwelveFourthSelfMask i) = 2048 ∧
    (generatedAxisGlobalTwelveFourthSelfPath i).foldr (fun k m =>
        generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveFourthBinaryColumns k) m)
      (generatedAxisGlobalTwelveFourthRootMask (generatedAxisGlobalTwelveFourthSelfRoot i)) =
      generatedAxisGlobalTwelveFourthSelfMask i := by
  decide +kernel

/-- Each representative is related to its forest root by an actual Fourth stabilizer word. -/
theorem generatedAxisGlobalTwelveFourthSelf_relation (i : Fin 3) :
    generatedAxisGlobalBinaryAct
        (generatedAxisGlobalTwelveFourthGeneratorWord (generatedAxisGlobalTwelveFourthSelfPath i))
        (generatedAxisGlobalTwelveFourthRoot (generatedAxisGlobalTwelveFourthSelfRoot i)) =
      generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveFourthSelfLocal i) := by
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFourthGeneratorWord_binary _ _ _
      (generatedAxisGlobalTwelveFourthRoot_val _),
    (generatedAxisGlobalTwelveFourthSelf_certificate i).2,
    generatedAxisGlobalTwelveFourthSelfLocal,
    generatedAxisGlobalTwelveFourth_sourceWord_root _ _
      (generatedAxisGlobalTwelveFourthSelf_certificate i).1]

/-- A self-identification at the root-two representative binds the forward image at root two. -/
theorem generatedAxisGlobalTwelveFourth_root2_of_self
    (hid : ∃ g : H, sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthSelfLocal 0)
      generatedFourthAxis) = rhoLocal g generatedFourthAxis) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 2) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨g, hg⟩ := hid
  exact generatedAxisGlobalTwelveFourth_reverse_merged _ 1 _ _
    (generatedAxisGlobalTwelveFourthGeneratorWord_mem _)
    (generatedAxisGlobalTwelveFourthSelf_relation 0)
    (Or.inr (generatedAxisGlobalTwelve_mem_of_transport 3 g hg))

/-- A self-identification at the root-thirteen representative binds the forward image there. -/
theorem generatedAxisGlobalTwelveFourth_root13_of_self
    (hid : ∃ g : H, sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthSelfLocal 1)
      generatedFourthAxis) = rhoLocal g generatedFourthAxis) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 13) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨g, hg⟩ := hid
  exact generatedAxisGlobalTwelveFourth_reverse_merged _ 10 _ _
    (generatedAxisGlobalTwelveFourthGeneratorWord_mem _)
    (generatedAxisGlobalTwelveFourthSelf_relation 1)
    (Or.inr (generatedAxisGlobalTwelve_mem_of_transport 3 g hg))

/-- The actual local orbits of the Fourth and Odd representatives are disjoint. -/
theorem generatedAxisGlobalTwelveFourth_odd_disjoint :
    Disjoint (MulAction.orbit H generatedFourthAxis) (MulAction.orbit H generatedOddAxis) := by
  refine (MulAction.orbit.eq_or_disjoint generatedFourthAxis generatedOddAxis).resolve_left ?_
  intro he
  have h4 := generatedCountedAxisOrbit_card 3
  have h2 := generatedCountedAxisOrbit_card 2
  change Nat.card (MulAction.orbit H generatedFourthAxis) = _ at h4
  change Nat.card (MulAction.orbit H generatedOddAxis) = _ at h2
  rw [he, h2] at h4
  exact absurd h4 (by decide)

/-- A self-identification at the root-fifteen representative, with the Odd class of the inverse
image at root fifteen, binds the forward image at root fifteen. -/
theorem generatedAxisGlobalTwelveFourth_root15_of_self
    (hid : ∃ g : H, sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthSelfLocal 2)
      generatedFourthAxis) = rhoLocal g generatedFourthAxis)
    (hodd : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨g, hg⟩ := hid
  have hfix : rhoLocal (generatedAxisGlobalTwelveFourthGeneratorWord
      (generatedAxisGlobalTwelveFourthSelfPath 2)) generatedFourthAxis = generatedFourthAxis :=
    generatedAxisGlobalTwelveFourthGeneratorWord_mem _
  have hmem : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthSelfLocal 2)
      generatedFourthAxis) ∈ MulAction.orbit H generatedFourthAxis := ⟨g, hg.symm⟩
  rcases generatedAxisGlobalTwelve_root_relation_pair generatedFourthAxis
      (generatedAxisGlobalTwelveFourthSelfLocal 2) (generatedAxisGlobalTwelveFourthRootLocal 15)
      _ hfix (generatedAxisGlobalTwelveFourthSelf_relation 2) with
    ⟨_, ⟨k2, h2⟩⟩ | ⟨_, ⟨k2, h2⟩⟩
  · exfalso
    have h4 := MulAction.mem_orbit_of_mem_orbit k2⁻¹ hmem
    rw [h2] at h4
    change rhoLocal k2⁻¹ (rhoLocal k2 _) ∈ _ at h4
    rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h4
    exact Set.disjoint_left.mp generatedAxisGlobalTwelveFourth_odd_disjoint h4 hodd
  · have h4 := MulAction.mem_orbit_of_mem_orbit k2⁻¹ hmem
    rw [h2] at h4
    change rhoLocal k2⁻¹ (rhoLocal k2 _) ∈ _ at h4
    rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h4
    obtain ⟨t, ht⟩ := h4
    exact generatedAxisGlobalTwelve_mem_of_transport 3 t (by exact ht.symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
