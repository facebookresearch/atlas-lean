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
# Ultraweak homeomorphism onto an injective normal range

For an injective normal unital complex star homomorphism `f : M → N`, the bijection from `M` to
its range is a homeomorphism for the ultraweak topology on `M` and the subspace ultraweak
topology of `N`.

Its forward value is the normal map `f`; the inverse is continuous because normal functionals on
`M` lift through predual pullback from `N`. Surjectivity onto all of `N` is not assumed.
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

/-- **Ultraweak homeomorphism onto a normal map's range.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. `ultraweakRangeHomeomorph f : Ultraweak M
≃ₜ range(f.ultraweakMap)` is `x ↦ f(x)`, with the range carrying the subspace topology of
ultraweak `N`. -/
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

/-- **Forward value of the ultraweak range homeomorphism.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. for `x ∈ Ultraweak M`, the element of
`Ultraweak N` underlying `ultraweakRangeHomeomorph f x` is `f.ultraweakMap x`. -/
@[simp]
theorem ultraweakRangeHomeomorph_apply (f : NormalStarAlgHom M N) (hf : Function.Injective f)
    (x : Ultraweak M) : (f.ultraweakRangeHomeomorph hf x).val = f.ultraweakMap x :=
  rfl

end

end VonNeumannAlgebra.NormalStarAlgHom
