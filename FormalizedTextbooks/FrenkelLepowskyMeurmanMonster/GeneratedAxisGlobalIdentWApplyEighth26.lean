/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Eighth root 26 from the factory identifications (gident2)

The source words of the factory identifications `wGoctadE26p_ident` (Eighth[37]+ <-> Seventh[32]+)
and `wGoctadE26n_ident`
(Eighth[37]- <-> Seventh[1]+) are the representative coset of Eighth root 26, so they are the two
wrapper
hypotheses of `generatedAxisGlobalTwelveEighthBind_root26` (goctad). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The representative coset of Eighth root 26 is the source word of `wGoctadE26p_ident`. -/
theorem wApplyEighth26_cosetP :
    generatedAxisGlobalTwelveEighthBindCoset26 = identWordLocal wGoctadE26pH := by
  unfold generatedAxisGlobalTwelveEighthBindCoset26 eighthBindRep
  rfl

/-- The representative coset of Eighth root 26 is the source word of `wGoctadE26n_ident`. -/
theorem wApplyEighth26_cosetN :
    generatedAxisGlobalTwelveEighthBindCoset26 = identWordLocal wGoctadE26nH := by
  unfold generatedAxisGlobalTwelveEighthBindCoset26 eighthBindRep
  rfl

/-- The listed representative `7` is the Eighth axis. -/
theorem wApplyEighth26_rep : generatedAxisGlobalTwelveRepresentative 7 = generatedEighthAxis := rfl

/-- The hypothesis `hpos` of `generatedAxisGlobalTwelveEighthBind_root26`. -/
theorem wApplyEighth26_hpos : ∃ i : Fin 12, ∃ g : H,
    sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset26 generatedEighthAxis) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
  refine ⟨6, identWordLocal wGoctadE26pG, ?_⟩
  rw [wApplyEighth26_cosetP, ← wApplyEighth26_rep]
  exact wGoctadE26p_ident

/-- The hypothesis `hneg` of `generatedAxisGlobalTwelveEighthBind_root26`. -/
theorem wApplyEighth26_hneg : ∃ i : Fin 12, ∃ g : H,
    sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset26 generatedEighthAxis) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
  refine ⟨6, identWordLocal wGoctadE26nG, ?_⟩
  rw [wApplyEighth26_cosetN, ← wApplyEighth26_rep]
  exact wGoctadE26n_ident

/-- Eighth root 26 is bound (goctad's wrapper with both factory identifications). -/
theorem wApplyEighth26_root : GeneratedAxisGlobalTwelveEighthRootBound 26 :=
  generatedAxisGlobalTwelveEighthBind_root26 wApplyEighth26_hpos wApplyEighth26_hneg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
