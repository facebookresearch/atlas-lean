/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFeasibleIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionCosets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialVector

/-! Genuine triality normalization of the feasible-axis transition subgroup. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Triality conjugates every genuine feasible transition element to another one. -/
theorem localFeasibleTransition_triality_conjugate (p : Fin 276)
    (n : localFeasibleTransitionSubgroup p) :
    ∃ k : localFeasibleTransitionSubgroup p,
      extraIntoGenerated * localIntoGenerated n.val.val * extraIntoGenerated⁻¹ =
        localIntoGenerated k.val.val := by
  let h : localOmegaStabilizer := ⟨n.val.val, n.property⟩
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_conjugate h
  have hw : extraIntoGenerated * localIntoGenerated h.val =
      localIntoGenerated k.val * extraIntoGenerated := by
    calc
      _ = (extraIntoGenerated * localIntoGenerated h.val * extraIntoGenerated⁻¹) *
          extraIntoGenerated := by group
      _ = _ := by rw [hk]
  have hfix : rhoLocal h.val (conwayAxis p) = conwayAxis p := n.val.property
  have he := congrArg (fun g : G => g.val (conwayAxis p)) hw
  change sExtra (rhoLocal h.val (conwayAxis p)) =
    rhoLocal k.val (sExtra (conwayAxis p)) at he
  rw [hfix, conwayAxis_triality] at he
  have hkaxis : k.val ∈ localAxisStabilizer p := he.symm
  exact ⟨⟨⟨k.val, hkaxis⟩, k.property⟩, hk⟩

/-- Feasible transition inputs differing by the actual transition subgroup
have triality images in the same actual first-axis-stabilizer orbit. -/
theorem localFeasibleTransition_triality_orbit (p : Fin 276)
    (n : localFeasibleTransitionSubgroup p) (x : GriessSpace) :
    ∃ h : localAxisStabilizer p,
      rhoLocal h.val (sExtra x) = sExtra (rhoLocal n.val.val x) := by
  obtain ⟨k, hk⟩ := localFeasibleTransition_triality_conjugate p n
  have hw : extraIntoGenerated * localIntoGenerated n.val.val =
      localIntoGenerated k.val.val * extraIntoGenerated := by
    calc
      _ = (extraIntoGenerated * localIntoGenerated n.val.val * extraIntoGenerated⁻¹) *
          extraIntoGenerated := by group
      _ = _ := by rw [hk]
  refine ⟨k.val, ?_⟩
  have he := congrArg (fun g : G => g.val x) hw
  change sExtra (rhoLocal n.val.val x) = rhoLocal k.val.val (sExtra x) at he
  exact he.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
