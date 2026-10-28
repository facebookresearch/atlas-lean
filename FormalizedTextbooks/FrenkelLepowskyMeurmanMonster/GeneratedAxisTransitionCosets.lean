/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationLocal

/-! Genuine local-orbit invariance of the source triality transition inputs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Triality conjugates each genuine local Ω-centralizer element to another one. -/
theorem localOmegaStabilizer_triality_conjugate (n : localOmegaStabilizer) :
    ∃ k : localOmegaStabilizer,
      extraIntoGenerated * localIntoGenerated n.val * extraIntoGenerated⁻¹ =
        localIntoGenerated k.val := by
  have hn : localIntoGenerated n.val ∈ generatedAxisTransitionNormalizer := by
    rw [generatedAxisTransitionNormalizer_eq_map_local]
    exact ⟨n.val, n.property, rfl⟩
  have hc := generatedAxisTransitionNormalizer_triality (localIntoGenerated n.val) hn
  rw [generatedAxisTransitionNormalizer_eq_map_local] at hc
  obtain ⟨k, hk, he⟩ := hc
  exact ⟨⟨k, hk⟩, he.symm⟩

/-- Changing a transition input by a genuine local Ω-centralizer element
does not change the local orbit of its triality image. -/
theorem localOmegaStabilizer_triality_orbit (n : localOmegaStabilizer) (x : GriessSpace) :
    ∃ h : H, rhoLocal h (sExtra x) = sExtra (rhoLocal n.val x) := by
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_conjugate n
  have hw : extraIntoGenerated * localIntoGenerated n.val =
      localIntoGenerated k.val * extraIntoGenerated := by
    calc
      _ = (extraIntoGenerated * localIntoGenerated n.val * extraIntoGenerated⁻¹) *
          extraIntoGenerated := by group
      _ = _ := by rw [hk]
  refine ⟨k.val, ?_⟩
  have he := congrArg (fun g : G => g.val x) hw
  change sExtra (rhoLocal n.val x) = rhoLocal k.val (sExtra x) at he
  exact he.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
