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

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# Fredholm transport through continuous linear equivalences

Let `𝕜` be a nontrivially normed field and `D,E,C,F` additive groups with topologies and
algebraic `𝕜`-module structures. For a continuous Fredholm map `V : E → F` and continuous linear
equivalences `d : D ≃ E`, `c : C ≃ F`, the rectangular transport `c⁻¹ V d` is Fredholm from `D`
to `C`.

Strictness, closed finite-codimension range and finite-dimensional complemented kernel are all
retained. No stage norms, completeness, separation or continuity of the module operations is
assumed.
-/

@[expose] public section

open Topology

namespace ContinuousLinearMap

universe u𝕜 uD uE uC uF

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {D : Type uD} {E : Type uE} {C : Type uC} {F : Type uF}
variable [AddCommGroup D] [Module 𝕜 D] [TopologicalSpace D]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup C] [Module 𝕜 C] [TopologicalSpace C]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- **Fredholm transport through source and target equivalences.** Let `𝕜` be a nontrivially
normed field and `D,E,C,F` have additive-group, algebraic `𝕜`-module and topological-space
structures in independent universes. If `V : E →L[𝕜] F` is Fredholm and `d : D ≃L[𝕜] E`,
`c : C ≃L[𝕜] F`, then `c⁻¹∘V∘d : D → C` is Fredholm. No stage norm, completeness or
Hausdorff condition is imposed. -/
theorem IsFredholm.transport {V : E →L[𝕜] F} (hV : V.IsFredholm)
    (d : D ≃L[𝕜] E) (c : C ≃L[𝕜] F) :
    (c.symm.toContinuousLinearMap.comp (V.comp d.toContinuousLinearMap)).IsFredholm := by
  let U := c.symm.toContinuousLinearMap.comp (V.comp d.toContinuousLinearMap)
  have hKerComap : U.ker = V.ker.comap d.toLinearMap := by
    ext x
    change c.symm (V (d x)) = 0 ↔ V (d x) = 0
    exact c.symm.map_eq_zero_iff
  have hKerMap : U.ker = V.ker.map d.symm.toLinearMap := by
    rw [hKerComap]
    exact Submodule.comap_equiv_eq_map_symm d.toLinearEquiv V.ker
  have hRangeComap : U.range = V.range.comap c.toLinearMap := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change c (c.symm (V (d x))) ∈ V.range
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact ⟨d x, rfl⟩
    · intro hy
      change c y ∈ V.range at hy
      obtain ⟨x, hx⟩ := hy
      change V x = c y at hx
      refine ⟨d.symm x, ?_⟩
      change c.symm (V (d (d.symm x))) = y
      rw [ContinuousLinearEquiv.apply_symm_apply, hx,
        ContinuousLinearEquiv.symm_apply_apply]
  have hRangeMap : U.range = V.range.map c.symm.toLinearMap := by
    rw [hRangeComap]
    exact Submodule.comap_equiv_eq_map_symm c.toLinearEquiv V.range
  change U.IsFredholm
  refine
    { isStrictMap := ?_
      isClosed_range := ?_
      finite_ker := ?_
      finite_coker := ?_
      closedComplemented_ker := ?_ }
  · change IsStrictMap (c.symm ∘ V ∘ d)
    apply c.symm.toHomeomorph.comp_isStrictMap_iff.mpr
    exact d.toHomeomorph.isStrictMap_comp_iff.mpr hV.isStrictMap
  · rw [hRangeMap]
    change IsClosed (c.symm '' (V.range : Set F))
    exact c.symm.toHomeomorph.isClosed_image.mpr hV.isClosed_range
  · rw [hKerMap]
    apply (Submodule.fg_iff_finiteDimensional _).mp
    exact ((Submodule.fg_iff_finiteDimensional V.ker).mpr hV.finite_ker).map
      d.symm.toLinearMap
  · let : Module.Finite 𝕜 (F ⧸ V.range) := hV.finite_coker
    let q : C →ₗ[𝕜] F ⧸ V.range := V.range.mkQ.comp c.toLinearMap
    have hq : q.ker = U.range := by
      calc
        q.ker = V.range.comap c.toLinearMap := by
          change (V.range.mkQ.comp c.toLinearMap).ker = V.range.comap c.toLinearMap
          rw [LinearMap.ker_comp, Submodule.ker_mkQ]
        _ = U.range := hRangeComap.symm
    have hCoFG : q.ker.CoFG := Submodule.CoFG.ker q
    rw [hq] at hCoFG
    exact hCoFG
  · obtain ⟨p, hp⟩ := hV.closedComplemented_ker
    let r : D →L[𝕜] D :=
      d.symm.toContinuousLinearMap.comp
        ((V.ker.subtypeL.comp p).comp d.toContinuousLinearMap)
    have hr (x : D) : r x ∈ U.ker := by
      rw [hKerComap]
      change d (d.symm (p (d x) : E)) ∈ V.ker
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using (p (d x)).2
    refine ⟨r.codRestrict U.ker hr, ?_⟩
    intro x
    have hx : d x.1 ∈ V.ker := by
      have hmem : x.1 ∈ V.ker.comap d.toLinearMap :=
        Eq.mp (congrArg (fun K : Submodule 𝕜 D => x.1 ∈ K) hKerComap) x.2
      exact hmem
    have hfix : (p (d x.1) : E) = d x.1 :=
      congrArg (fun y : V.ker => (y : E)) (hp ⟨d x.1, hx⟩)
    apply Subtype.ext
    change d.symm (p (d x.1) : E) = x.1
    rw [hfix]
    exact d.symm_apply_apply x.1

end ContinuousLinearMap
