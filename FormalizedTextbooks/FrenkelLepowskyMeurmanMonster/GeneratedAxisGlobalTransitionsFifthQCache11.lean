/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCacheData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadReturns

/-! The genuine all-one-root word is identity, with its complete preferred-coordinate phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine Omega-root source word has identity Q image, before any cache comparison. -/
theorem generatedAxisGlobalFifthQCache11_identity (q : Q) :
    generatedAxisGlobalFifthChainQImage 11 7 q = q := by
  apply inclQ_injective
  rw [← generatedAxisGlobalFifthShortWord_QImage, inclQ_spinConjugation,
    generatedAxisGlobalFifthShortWordFiber_local, generatedAxisGlobalFifthShort_omega_word,
    one_mul, inv_one, mul_one]

/-- Every candidate coordinate image is the actual complete positive lift of that coordinate. -/
theorem generatedAxisGlobalFifthQCache11_actual (i : Fin 24) :
    generatedAxisGlobalFifthChainQImage 11 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache 11 i := by
  rw [generatedAxisGlobalFifthQCache11_identity]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24, toAdd (qCoordinateGenerator i).base j =
        toAdd (generatedAxisGlobalFifthQCache 11 i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24, toAdd (qCoordinateGenerator i).coeff =
        toAdd (generatedAxisGlobalFifthQCache 11 i).coeff := by decide +kernel
    exact h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
