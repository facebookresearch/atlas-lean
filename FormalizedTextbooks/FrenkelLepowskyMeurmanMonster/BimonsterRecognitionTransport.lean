/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Remove the distinguished-generator side condition from recognition transport.
This proves consequences of a recognition isomorphism; it does not provide
or assume an unconditional recognition theorem.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555Parity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PresentationComparison

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

variable {M : Type*} [Group M]

/-- Normalize any recognition isomorphism by an explicitly defined base-group
conjugation so that the source central generator is the pure factor swap. -/
def bimonsterRecognitionNormalized
    (e : BimonsterPresentation ≃* M ≀ᵣ WreathParity) :
    BimonsterPresentation ≃* M ≀ᵣ WreathParity :=
  e.trans (MulAut.conj (wreathOuterConjugator M (e bimonsterSwap))⁻¹)

/-- Surjectivity and the source Coxeter relations provide the required parity;
no side assumption on the image of the central generator is needed. -/
theorem bimonsterRecognitionNormalized_swap
    (e : BimonsterPresentation ≃* M ≀ᵣ WreathParity) :
    bimonsterRecognitionNormalized e bimonsterSwap = wreathSwap M := by
  have hp := y555_surjective_wreath_swap e.toMonoidHom e.surjective
  have hs : e bimonsterSwap * e bimonsterSwap = 1 := by
    have h := congrArg e bimonsterSwap_sq
    simpa only [map_pow, pow_two, map_mul, map_one] using h
  have hc := wreathOuterInvolution_conjugate M (e bimonsterSwap) hs hp
  change (MulAut.conj (wreathOuterConjugator M (e bimonsterSwap))⁻¹)
    (e bimonsterSwap) = wreathSwap M
  let k := wreathOuterConjugator M (e bimonsterSwap)
  rw [MulAut.conj_apply, inv_inv]
  change k⁻¹ * e bimonsterSwap * k = wreathSwap M
  calc
    k⁻¹ * e bimonsterSwap * k = k⁻¹ * (k * wreathSwap M * k⁻¹) * k :=
      congrArg (fun g => k⁻¹ * g * k) hc.symm
    _ = wreathSwap M := by group

/-- Any genuine recognition of the independent source presentation identifies
its centralizer quotient with the actual recognized factor. The only input is
an isomorphism; the distinguished-generator condition is proved above. -/
noncomputable def classicalMonsterComparisonOfRecognition
    (e : BimonsterPresentation ≃* M ≀ᵣ WreathParity) : classicalMonster ≃* M :=
  classicalMonsterComparison (bimonsterRecognitionNormalized e)
    (bimonsterRecognitionNormalized_swap e)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
