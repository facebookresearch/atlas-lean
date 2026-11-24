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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulPredualQuotient
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Topology.Homeomorph.Defs

/-!
# A faithful normal map is a homeomorphism onto its actual ultraweak range

The original normal map is injective between the actual ultraweak views.
Its literal range equivalence is constructed by the stock injective-range
factory. Every original source normal evaluation has a genuine target
predual preimage under the constructed pullback. Those original target
evaluations prove continuity of the actual inverse. No range, quotient,
normal inverse or model certificate is supplied as an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- Construct the original ultraweak homeomorphism onto the literal operator-map range. -/
def ultraweakRangeHomeomorph (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    Ultraweak M ≃ₜ Set.range f.ultraweakMap := by
  have hinjective : Function.Injective f.ultraweakMap := by
    intro x y hxy
    apply (ultraweakLinearEquiv M).injective
    apply hf
    have hvalue := congrArg (ultraweakLinearEquiv N) hxy
    simpa only [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply] using hvalue
  let e : Ultraweak M ≃ Set.range f.ultraweakMap := Equiv.ofInjective f.ultraweakMap hinjective
  have hforward : Continuous e := by
    change Continuous (fun x : Ultraweak M =>
      (⟨f.ultraweakMap x, Set.mem_range_self x⟩ : Set.range f.ultraweakMap))
    exact f.ultraweakMap.continuous.subtype_mk (fun x => Set.mem_range_self x)
  have hinverse : Continuous e.symm := by
    apply (ultraweak_continuous_iff M).mpr
    intro ψ
    obtain ⟨φ, hφ⟩ := f.predualPullback_surjective_of_injective hf ψ
    have hfunction :
        (fun y : Set.range f.ultraweakMap => (ψ : StrongDual ℂ M) (ultraweakLinearEquiv M (e.symm y))) =
        (fun y : Set.range f.ultraweakMap => (φ : StrongDual ℂ N) (ultraweakLinearEquiv N y.val)) := by
      funext y
      have hmap := Equiv.apply_ofInjective_symm hinjective y
      have hvalue := congrArg (ultraweakLinearEquiv N) hmap
      rw [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply] at hvalue
      calc
        (ψ : StrongDual ℂ M) (ultraweakLinearEquiv M (e.symm y)) =
            (f.predualPullback φ : StrongDual ℂ M) (ultraweakLinearEquiv M (e.symm y)) := by rw [hφ]
        _ = (φ : StrongDual ℂ N) (f (ultraweakLinearEquiv M (e.symm y))) :=
          f.predualPullback_apply φ _
        _ = (φ : StrongDual ℂ N) (ultraweakLinearEquiv N y.val) := congrArg (φ : StrongDual ℂ N) hvalue
    rw [hfunction]
    exact (ultraweak_eval_continuous N φ).comp continuous_subtype_val
  exact ⟨e, hforward, hinverse⟩

/-- The actual range homeomorphism retains exactly the original ultraweak-map value. -/
@[simp]
theorem ultraweakRangeHomeomorph_apply (f : NormalStarAlgHom M N) (hf : Function.Injective f)
    (x : Ultraweak M) : (f.ultraweakRangeHomeomorph hf x).val = f.ultraweakMap x :=
  rfl

end

end VonNeumannAlgebra.NormalStarAlgHom
