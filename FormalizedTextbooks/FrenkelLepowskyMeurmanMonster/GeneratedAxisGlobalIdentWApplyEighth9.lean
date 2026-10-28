/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Eighth root 9 from the factory identifications (gident2)

The source words of the factory identifications `wGoctadE9p_ident` (Eighth[13]+ <-> Seventh[14]+)
and `wGoctadE9n_ident`
(Eighth[13]- <-> Eighth[13]-) are the representative coset of Eighth root 9, so they are the two
wrapper
hypotheses of `generatedAxisGlobalTwelveEighthBind_root9` (goctad). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The representative coset of Eighth root 9 is the source word of `wGoctadE9p_ident`. -/
theorem wApplyEighth9_cosetP :
    generatedAxisGlobalTwelveEighthBindCoset9 = identWordLocal wGoctadE9pH := by
  unfold generatedAxisGlobalTwelveEighthBindCoset9 eighthBindRep
  rfl

/-- The representative coset of Eighth root 9 is the source word of `wGoctadE9n_ident`. -/
theorem wApplyEighth9_cosetN :
    generatedAxisGlobalTwelveEighthBindCoset9 = identWordLocal wGoctadE9nH := by
  unfold generatedAxisGlobalTwelveEighthBindCoset9 eighthBindRep
  rfl

/-- The listed representative `7` is the Eighth axis. -/
theorem wApplyEighth9_rep : generatedAxisGlobalTwelveRepresentative 7 = generatedEighthAxis := rfl

/-- The hypothesis `hpos` of `generatedAxisGlobalTwelveEighthBind_root9`. -/
theorem wApplyEighth9_hpos : ∃ i : Fin 12, ∃ g : H,
    sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset9 generatedEighthAxis) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
  refine ⟨6, identWordLocal wGoctadE9pG, ?_⟩
  rw [wApplyEighth9_cosetP, ← wApplyEighth9_rep]
  exact wGoctadE9p_ident

/-- The hypothesis `hneg` of `generatedAxisGlobalTwelveEighthBind_root9`. -/
theorem wApplyEighth9_hneg : ∃ i : Fin 12, ∃ g : H,
    sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset9 generatedEighthAxis) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
  refine ⟨7, identWordLocal wGoctadE9nG, ?_⟩
  rw [wApplyEighth9_cosetN, ← wApplyEighth9_rep]
  exact wGoctadE9n_ident

/-- Eighth root 9 is bound (goctad's wrapper with both factory identifications). -/
theorem wApplyEighth9_root : GeneratedAxisGlobalTwelveEighthRootBound 9 :=
  generatedAxisGlobalTwelveEighthBind_root9 wApplyEighth9_hpos wApplyEighth9_hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
