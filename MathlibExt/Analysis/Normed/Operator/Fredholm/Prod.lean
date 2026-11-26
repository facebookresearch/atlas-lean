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
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Maps.Strict.Module

/-!
# Fredholm Cartesian products of continuous linear maps

Let `𝕜` be a nontrivially normed field and four additive groups carry topologies and algebraic
`𝕜`-module structures. Assume addition and negation are continuous on the two source groups. The
Cartesian product of two continuous Fredholm maps is Fredholm for the product topologies.

This preserves strictness, closed finite-codimension range and finite-dimensional complemented
kernel. Stage norms, scalar or stage completeness, and continuity of target addition are not
premises.
-/

@[expose] public section

open Topology

namespace ContinuousLinearMap

universe u𝕜 uE₀ uE₁ uF₀ uF₁

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E₀ : Type uE₀} {E₁ : Type uE₁} {F₀ : Type uF₀} {F₁ : Type uF₁}
variable [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
variable [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
variable [AddCommGroup F₀] [Module 𝕜 F₀] [TopologicalSpace F₀]
variable [AddCommGroup F₁] [Module 𝕜 F₁] [TopologicalSpace F₁]
variable [IsTopologicalAddGroup E₀] [IsTopologicalAddGroup E₁]

/-- **Cartesian product of two Fredholm maps.** Let `𝕜` be a nontrivially normed field. Let
`E₀,E₁,F₀,F₁` have additive-group, algebraic `𝕜`-module and topological-space structures,
with continuous addition and negation on `E₀,E₁`. If continuous linear `S : E₀ → F₀` and
`T : E₁ → F₁` are Fredholm, then `(x,y) ↦ (Sx,Ty)` is Fredholm for product topologies,
retaining all five conditions. No stage norms or completeness are assumed. -/
theorem IsFredholm.prodMap {S : E₀ →L[𝕜] F₀} {T : E₁ →L[𝕜] F₁}
    (hS : S.IsFredholm) (hT : T.IsFredholm) : (S.prodMap T).IsFredholm := by
  let U := S.prodMap T
  have hKer : U.ker = S.ker.prod T.ker := by
    change (S.toLinearMap.prodMap T.toLinearMap).ker =
      S.toLinearMap.ker.prod T.toLinearMap.ker
    exact LinearMap.ker_prodMap _ _
  have hRange : U.range = S.range.prod T.range := by
    change (S.toLinearMap.prodMap T.toLinearMap).range =
      S.toLinearMap.range.prod T.toLinearMap.range
    exact LinearMap.range_prodMap _ _
  change U.IsFredholm
  refine
    { isStrictMap := ?_
      isClosed_range := ?_
      finite_ker := ?_
      finite_coker := ?_
      closedComplemented_ker := ?_ }
  · change IsStrictMap (S.toLinearMap.prodMap T.toLinearMap)
    exact LinearMap.isStrictMap_prodMap hS.isStrictMap hT.isStrictMap
  · rw [hRange]
    change IsClosed (Set.prod (S.range : Set F₀) (T.range : Set F₁))
    exact hS.isClosed_range.prod hT.isClosed_range
  · rw [hKer]
    apply (Submodule.fg_iff_finiteDimensional _).mp
    exact ((Submodule.fg_iff_finiteDimensional S.ker).mpr hS.finite_ker).prod
      ((Submodule.fg_iff_finiteDimensional T.ker).mpr hT.finite_ker)
  · let : Module.Finite 𝕜 (F₀ ⧸ S.range) := hS.finite_coker
    let : Module.Finite 𝕜 (F₁ ⧸ T.range) := hT.finite_coker
    let q : F₀ × F₁ →ₗ[𝕜] (F₀ ⧸ S.range) × (F₁ ⧸ T.range) :=
      S.range.mkQ.prodMap T.range.mkQ
    have hq : q.ker = U.range := by
      calc
        q.ker = S.range.prod T.range := by
          change (S.range.mkQ.prodMap T.range.mkQ).ker = S.range.prod T.range
          simp only [LinearMap.ker_prodMap, Submodule.ker_mkQ]
        _ = U.range := hRange.symm
    have hCoFG : q.ker.CoFG := Submodule.CoFG.ker q
    rw [hq] at hCoFG
    exact hCoFG
  · obtain ⟨P₀, hP₀⟩ := hS.closedComplemented_ker
    obtain ⟨P₁, hP₁⟩ := hT.closedComplemented_ker
    let r : E₀ × E₁ →L[𝕜] E₀ × E₁ :=
      (S.ker.subtypeL.comp P₀).prodMap (T.ker.subtypeL.comp P₁)
    have hr (x : E₀ × E₁) : r x ∈ U.ker := by
      rw [hKer]
      change (P₀ x.1 : E₀) ∈ S.ker ∧ (P₁ x.2 : E₁) ∈ T.ker
      exact ⟨(P₀ x.1).2, (P₁ x.2).2⟩
    refine ⟨r.codRestrict U.ker hr, ?_⟩
    intro x
    apply Subtype.ext
    change r x.1 = x.1
    have hx : x.1.1 ∈ S.ker ∧ x.1.2 ∈ T.ker := by
      have hmem : x.1 ∈ S.ker.prod T.ker :=
        Eq.mp (congrArg (fun K : Submodule 𝕜 (E₀ × E₁) => x.1 ∈ K) hKer) x.2
      exact hmem
    apply Prod.ext
    · change (P₀ x.1.1 : E₀) = x.1.1
      exact congrArg (fun y : S.ker => (y : E₀)) (hP₀ ⟨x.1.1, hx.1⟩)
    · change (P₁ x.1.2 : E₁) = x.1.2
      exact congrArg (fun y : T.ker => (y : E₁)) (hP₁ ⟨x.1.2, hx.2⟩)

end ContinuousLinearMap
