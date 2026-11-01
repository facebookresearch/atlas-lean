/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Transport the classical reference quotient after an independent recognition
of the Y₅₅₅ presentation. The recognition is an explicit unproved input to
this helper, not an assumption of any of the six milestone statements.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Presentation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.WreathCentralizer

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

variable {M : Type*} [Group M]

/-- Restrict a recognition isomorphism to the distinguished centralizers. -/
def bimonsterCentralizerComparison
    (e : BimonsterPresentation ≃* M ≀ᵣ WreathParity)
    (he : e bimonsterSwap = wreathSwap M) :
    bimonsterSwapCentralizer ≃* wreathSwapCentralizer M where
  toFun g := ⟨e g.val, by
    change e g.val ∈ Subgroup.centralizer {wreathSwap M}
    rw [Subgroup.mem_centralizer_singleton_iff, ← he, ← map_mul, ← map_mul]
    exact congrArg e (Subgroup.mem_centralizer_singleton_iff.mp g.property)⟩
  invFun g := ⟨e.symm g.val, by
    change e.symm g.val ∈ Subgroup.centralizer {bimonsterSwap}
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simp only [map_mul, e.apply_symm_apply, he]
    exact Subgroup.mem_centralizer_singleton_iff.mp g.property⟩
  left_inv g := by apply Subtype.ext; exact e.symm_apply_apply g.val
  right_inv g := by apply Subtype.ext; exact e.apply_symm_apply g.val
  map_mul' g h := by apply Subtype.ext; exact e.map_mul g.val h.val

theorem bimonsterCentralizerComparison_swap
    (e : BimonsterPresentation ≃* M ≀ᵣ WreathParity)
    (he : e bimonsterSwap = wreathSwap M) :
    bimonsterCentralizerComparison e he bimonsterSwapInCentralizer =
      wreathSwapInCentralizer M := by
  apply Subtype.ext
  exact he

/-- The independent reference quotient recovers a recognized wreath factor.
This leaves the recognition theorem as an explicit prerequisite. -/
noncomputable def classicalMonsterComparison
    (e : BimonsterPresentation ≃* M ≀ᵣ WreathParity)
    (he : e bimonsterSwap = wreathSwap M) : classicalMonster ≃* M :=
  (QuotientGroup.congr bimonsterSwapPowers
    (Subgroup.zpowers (wreathSwapInCentralizer M))
    (bimonsterCentralizerComparison e he) (by
      change Subgroup.map (bimonsterCentralizerComparison e he).toMonoidHom
        (Subgroup.zpowers bimonsterSwapInCentralizer) = _
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers (bimonsterCentralizerComparison_swap e he))).trans
    (wreathSwapCentralizerQuotientEquiv M)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
