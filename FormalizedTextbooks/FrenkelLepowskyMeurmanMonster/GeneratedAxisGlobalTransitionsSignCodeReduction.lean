/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

/-! Exact code phases and all-one factors for the displayed fifth normalization signs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The displayed low grey-code labels used by the actual fifth normalization stages. -/
def generatedAxisGlobalGreySignLow (k : Fin 8) : Fin 4096 := ⟨256 * k.val, by omega⟩

/-- Their actual all-one translates in the original source code labels. -/
def generatedAxisGlobalGreySignHigh (k : Fin 8) : Fin 4096 :=
  ⟨256 * k.val + 2048, by omega⟩

/-- The all-one source lift is exactly the genuine noncentral extraspecial Omega. -/
theorem generatedAxisGlobalSourceCode_omega : sourceQCode 2048 0 = sourceOmegaQ := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    ext i
    have h : ∀ i : Fin 24, toAdd (sourceQCode 2048 0).base i =
        toAdd sourceOmegaQ.base i := by decide +kernel
    exact h i
  · apply toAdd.injective
    have h : toAdd (sourceQCode 2048 0).coeff = toAdd sourceOmegaQ.coeff := by decide +kernel
    exact h

set_option maxHeartbeats 10000000 in
-- Check the actual 192 coordinate entries of the eight displayed all-one factorizations.
/-- The high source lift has exactly its genuine Omega factor, including its central phase. -/
theorem generatedAxisGlobalGreySignHigh_factor (k : Fin 8) :
    sourceQCode (generatedAxisGlobalGreySignHigh k) 0 =
      sourceOmegaQ * sourceQCode (generatedAxisGlobalGreySignLow k) 0 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    ext i
    have h : ∀ k : Fin 8, ∀ i : Fin 24,
        toAdd (sourceQCode (generatedAxisGlobalGreySignHigh k) 0).base i =
          toAdd (sourceOmegaQ * sourceQCode (generatedAxisGlobalGreySignLow k) 0).base i := by
      decide +kernel
    exact h k i
  · apply toAdd.injective
    have h : ∀ k : Fin 8, toAdd (sourceQCode (generatedAxisGlobalGreySignHigh k) 0).coeff =
        toAdd (sourceOmegaQ * sourceQCode (generatedAxisGlobalGreySignLow k) 0).coeff := by
      decide +kernel
    exact h k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
