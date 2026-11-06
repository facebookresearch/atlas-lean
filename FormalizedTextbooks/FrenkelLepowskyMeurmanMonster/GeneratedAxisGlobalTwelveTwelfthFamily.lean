/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthDecompose
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelvePrototypeCosets

/-! Reduction of the Twelfth-family triality coverage to explicit root vectors.

The checked Twelfth forest and the thirty-eight root words decompose every actual Twelfth
transition into a root word and a triality sign. The identity root word is bound by the existing
identity-coset pair (forward to Twelfth, inverse to Fifth). The remaining seventy-four signed
vectors at the thirty-seven non-identity root words are the explicit hypotheses of
`generatedAxisGlobalTwelve_twelfth_covered_of`; no destination of them is asserted here.

Binary matching (`generatedAxisGlobalTwelveTwelfth_root_pair_of_word`) transfers a binding at any
local element whose binary root lies in the same Twelfth stabilizer orbit to the root word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The thirty-seven root words other than the identity coset. -/
def generatedAxisGlobalTwelveTwelfthOpenRoots : Finset (Fin 38) :=
  Finset.univ.erase 0

/-- The Twelfth catalogue representative is the literal Twelfth axis. -/
theorem generatedAxisGlobalTwelveTwelfth_representative :
    generatedAxisGlobalTwelveRepresentative 10 = generatedTwelfthAxis := rfl

/-- The seventy-four non-identity root vectors suffice for complete Twelfth-family coverage. -/
theorem generatedAxisGlobalTwelve_twelfth_covered_of
    (hpos : ∀ k ∈ generatedAxisGlobalTwelveTwelfthOpenRoots,
      sExtra (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ k ∈ generatedAxisGlobalTwelveTwelfthOpenRoots,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 10 := by
  have h0 := generatedAxisGlobalTwelve_twelfth_identity_pair
  rw [generatedAxisGlobalTwelveTwelfth_representative] at h0
  have hp : ∀ k : Fin 38,
      sExtra (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [generatedAxisGlobalTwelveTwelfthRootWord_zero]
      exact h0.1
    · exact hpos k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
  have hn : ∀ k : Fin 38,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [generatedAxisGlobalTwelveTwelfthRootWord_zero]
      exact h0.2
    · exact hneg k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
  intro h
  rw [generatedAxisGlobalTwelveTwelfth_representative]
  exact generatedAxisGlobalTwelveTwelfth_triality_of_actual_destinations _ hp hn h

/-- An actual stabilizer element given as a word in the six forest generators. -/
def generatedAxisGlobalTwelveTwelfthWordElement (ws : List (Fin 6)) : H :=
  (ws.map fun e => (generatedAxisGlobalTwelveTwelfthGenerator e).val).prod

/-- Forest-generator words fix the whole Twelfth axis. -/
theorem generatedAxisGlobalTwelveTwelfthWordElement_mem (ws : List (Fin 6)) :
    generatedAxisGlobalTwelveTwelfthWordElement ws ∈ generatedTwelfthLocalAxisStabilizer := by
  unfold generatedAxisGlobalTwelveTwelfthWordElement
  induction ws with
  | nil => exact Subgroup.one_mem _
  | cons e ws ih =>
    rw [List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (generatedAxisGlobalTwelveTwelfthGenerator e).property ih

/-- Forest-generator words act on masks by their checked child columns. -/
theorem generatedAxisGlobalTwelveTwelfthWordElement_binary (ws : List (Fin 6)) (b : ℕ) :
    co1BinaryAction (projH (generatedAxisGlobalTwelveTwelfthWordElement ws))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode (ws.foldr (fun e x =>
        generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveTwelfthChildColumns e) x)
          b) := by
  unfold generatedAxisGlobalTwelveTwelfthWordElement
  induction ws generalizing b with
  | nil => simp
  | cons e ws ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, LinearEquiv.mul_apply]
    rw [ih, generatedAxisGlobalTwelveTwelfthGenerator_child,
      generatedAxisGlobalMaskColumnAction_decode]

/-- Binary matching: a binding of both signs at a local element whose binary root is a checked
forest-word image of a root mask binds both signs at that root word. -/
theorem generatedAxisGlobalTwelveTwelfth_root_pair_of_word {ι : Type*} (u : ι → GriessSpace)
    (k : Fin 38) (h : H) (mh : ℕ)
    (hh : (generatedAxisGlobalBinaryRoot h).val = monsterCo1GeometryBinaryMaskDecode mh)
    (ws : List (Fin 6))
    (hm : ws.foldr (fun e x =>
      generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveTwelfthChildColumns e) x)
        (generatedAxisGlobalTwelveTwelfthOmegaRootMask k) = mh)
    (hpos : sExtra (rhoLocal h generatedTwelfthAxis) ∈ generatedLocalOrbitUnion u)
    (hneg : sExtra⁻¹ (rhoLocal h generatedTwelfthAxis) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion u ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion u := by
  apply generatedAxisGlobalTwelve_root_pair_mem u generatedTwelfthAxis h
    (generatedAxisGlobalTwelveTwelfthRootWord k) (generatedAxisGlobalTwelveTwelfthWordElement ws)
    (generatedAxisGlobalTwelveTwelfthWordElement_mem ws) _ hpos hneg
  apply Subtype.ext
  change co1BinaryAction (projH (generatedAxisGlobalTwelveTwelfthWordElement ws))
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveTwelfthRootWord k)).val =
      (generatedAxisGlobalBinaryRoot h).val
  rw [generatedAxisGlobalTwelveTwelfthRootWord_root,
    generatedAxisGlobalTwelveTwelfthWordElement_binary, hm, hh]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
