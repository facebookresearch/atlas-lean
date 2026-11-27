/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.Ultraweak
public import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Ultraweak continuity characterizes normal functionals

For a concrete von Neumann algebra `M`, let `M_*` be the norm-closed span of its vector
functionals. Equip `M` with the ultraweak topology `σ(M,M_*)`, given by evaluation against these
functionals.

A norm-continuous complex-linear functional `ψ ∈ M*` that is also continuous for this ultraweak
topology belongs to `M_*`. The Hilbert space is complete, and no separability or nonzero-space
hypothesis is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Ultraweak continuous functional belongs to the predual space.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. if `ψ ∈ M*` is continuous on `M` with its ultraweak
topology, then `ψ∈M_* = normalFunctionalSpace M`. -/
theorem mem_normalFunctionalSpace_of_ultraweak_continuous (M : VonNeumannAlgebra H)
    (ψ : StrongDual ℂ M)
    (hψ : Continuous fun x : Ultraweak M => ψ (ultraweakLinearEquiv M x)) :
    ψ ∈ normalFunctionalSpace M := by
  let F : StrongDual ℂ (Ultraweak M) :=
    { toLinearMap := ψ.toLinearMap.comp (ultraweakLinearEquiv M).toLinearMap
      cont := hψ }
  obtain ⟨φ, hφ⟩ := LinearMap.dualEmbedding_surjective (normalFunctionalPairing M) F
  have hval : (φ : StrongDual ℂ M) = ψ := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg
      (fun f : StrongDual ℂ (Ultraweak M) => f ((ultraweakLinearEquiv M).symm x)) hφ
    change (φ : StrongDual ℂ M)
        (ultraweakLinearEquiv M ((ultraweakLinearEquiv M).symm x)) =
      ψ (ultraweakLinearEquiv M ((ultraweakLinearEquiv M).symm x)) at hx
    simpa only [LinearEquiv.apply_symm_apply] using hx
  exact hval ▸ φ.property

end VonNeumannAlgebra
