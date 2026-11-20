/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicConvergence











open Filter Set Topology

namespace StatMech.Universality



noncomputable def isingFermionicNormalizedInterpolant
    (delta : Nat → Real) (raw : Nat → ℂ → ℂ) : Nat → ℂ → ℂ :=
  fun n z ↦ raw n z / (Real.sqrt (2 * delta n) : ℂ)

@[simp] theorem isingFermionicNormalizedInterpolant_apply
    (delta : Nat → Real) (raw : Nat → ℂ → ℂ) (n : Nat) (z : ℂ) :
    isingFermionicNormalizedInterpolant delta raw n z =
      raw n z / (Real.sqrt (2 * delta n) : ℂ) :=
  rfl






theorem isingFermionic_scalingLimit_of_compactBounds_and_primitiveIm
    (delta : Nat → Real) (raw : Nat → ℂ → ℂ)
    (target Phi : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hF : ∀ n, DifferentiableOn ℂ
      (isingFermionicNormalizedInterpolant delta raw n) U)
    (htarget : DifferentiableOn ℂ target U) (htarget_ne : target z₀ ≠ 0)
    (hPhi : DifferentiableOn ℂ Phi U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) U)
    (E : StatMech.FrontierA.CompactExhaustion U)
    (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : Real, ∀ n z, z ∈ K →
        ‖isingFermionicNormalizedInterpolant delta raw n z‖ ≤ C)
    (hidentifyPrimitive : ∀ (phi psi : Nat → Nat) (f : ℂ → ℂ),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
          (fun n ↦ isingFermionicNormalizedInterpolant delta raw
            (phi (psi n)))
          f atTop U →
      ∃ (P : ℂ → ℂ) (C : Real),
        DifferentiableOn ℂ P U ∧
        Set.EqOn (deriv P) (fun z ↦ f z ^ 2) U ∧
        (∀ z ∈ U, (P z).im = (Phi z).im + C) ∧
        f z₀ = target z₀) :
    TendstoLocallyUniformlyOn
        (isingFermionicNormalizedInterpolant delta raw) target atTop U ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ isingFermionicNormalizedInterpolant delta raw)
        (deriv target) atTop U := by
  exact isingFermionic_fullConvergence_of_compactBounds_and_primitiveIm
    (isingFermionicNormalizedInterpolant delta raw) target Phi U z₀
    hUopen hUconnected hz₀ hF htarget htarget_ne hPhi hPhideriv E
    hbounded hidentifyPrimitive

end StatMech.Universality
