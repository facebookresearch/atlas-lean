/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/RepresentationTheory/CompactGroupSemisimple.lean` (leanprover/lean-eval),
at commit 38361be884302c7edce1908c4aef8296eb2cb27e, for the statement and docstring of
`compact_group_semisimple`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License");
you may not use these portions except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Modification notice: ATLAS placed the statement in its current namespace and
deferred its proof in the former wanted module. This module supplies the proof.
lean-eval ships no `NOTICE` file.
-/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.Projection
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Complete reducibility for compact groups

For a continuous representation of a compact group on a finite-dimensional real vector space,
`compact_group_semisimple` gives every subrepresentation an invariant complement. Averaging
the conjugates of a projection onto the subrepresentation over normalized Haar measure gives
an equivariant projection. Its kernel is the complement.
-/

namespace MathlibExt.GroupTheory.CompactGroupSemisimpleWanted
namespace RepresentationTheory.CompactGroupSemisimple

open Representation MeasureTheory

/-- Averaging the conjugates of a projection gives an equivariant retraction onto `W`. -/
private theorem exists_equivariant_projection
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : Representation ℝ G V) (hρ : Continuous fun p : G × V => ρ p.1 p.2)
    (W : Subrepresentation ρ) :
    ∃ P : V →ₗ[ℝ] W.toSubmodule, (∀ w : W.toSubmodule, P w = w) ∧
      ∀ g v, P (ρ g v) = W.toRepresentation g (P v) := by
  borelize G
  let K : TopologicalSpace.PositiveCompacts G := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let μ := Measure.haarMeasure K
  have : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  have : CompleteSpace W.toSubmodule := FiniteDimensional.completeSpace ℝ _
  obtain ⟨U, hU⟩ := exists_isCompl W.toSubmodule
  let p := W.toSubmodule.projectionOnto U hU
  let F (g : G) : V →ₗ[ℝ] W.toSubmodule := W.toRepresentation g ∘ₗ p ∘ₗ ρ g⁻¹
  have hF (v : V) : Integrable (fun g => F g v) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply Continuous.subtype_mk
    have horbit : Continuous fun g : G => ρ g⁻¹ v :=
      hρ.comp (continuous_inv.prodMk continuous_const)
    have hp := p.continuous_of_finiteDimensional.comp horbit
    exact hρ.comp (continuous_id.prodMk (continuous_subtype_val.comp hp))
  let P : V →ₗ[ℝ] W.toSubmodule :=
    { toFun := fun v => ∫ g, F g v ∂μ
      map_add' := fun v w => by simp only [map_add, integral_add (hF v) (hF w)]
      map_smul' := fun c v => by simp only [map_smul, integral_smul, RingHom.id_apply] }
  refine ⟨P, ?_, ?_⟩
  · intro w
    have hfix (g : G) : F g w = w := by
      change W.toRepresentation g (W.toSubmodule.projectionOnto U hU (ρ g⁻¹ w)) = w
      rw [Submodule.projectionOnto_apply_of_mem_left hU (W.apply_mem_toSubmodule g⁻¹ w.property)]
      exact Subtype.ext (ρ.self_inv_apply g w)
    change (∫ g, F g w ∂μ) = w
    simp_rw [hfix]
    simp
  · intro g v
    have hconj (x : G) : F (g * x) (ρ g v) = W.toRepresentation g (F x v) := by
      simp [F, mul_inv_rev, map_mul]
    calc
      P (ρ g v) = ∫ x, F (g * x) (ρ g v) ∂μ :=
        (integral_mul_left_eq_self (fun x => F x (ρ g v)) g).symm
      _ = ∫ x, W.toRepresentation g (F x v) ∂μ := by simp_rw [hconj]
      _ = W.toRepresentation g (P v) :=
        (W.toRepresentation g).toContinuousLinearMap.integral_comp_comm (hF v)

/-- **Representations of compact groups are semisimple.** Let $G$ be a compact topological group
and let $\rho$ be a representation of $G$ on a finite-dimensional real normed space $V$ such that
the action map $G \times V \to V$, $(g, v) \mapsto \rho(g)(v)$, is continuous. Then $\rho$ is
semisimple: every subrepresentation of $\rho$ has a complementary subrepresentation.

Source: H. Weyl, *Theorie der Darstellung kontinuierlicher halb-einfacher Gruppen durch lineare
Transformationen* (1925–26); Peter–Weyl (1927). Knill, *Some fundamental theorems in
mathematics*, §21. Via leanprover/lean-eval@38361be, problem `compact_group_semisimple`. -/
public theorem compact_group_semisimple
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : Representation ℝ G V)
    (hρ : Continuous fun p : G × V => ρ p.1 p.2) :
    ρ.IsSemisimpleRepresentation := by
  constructor
  intro W
  obtain ⟨P, hfix, hequiv⟩ := exists_equivariant_projection ρ hρ W
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker P
      apply_mem_toSubmodule g v hv := by
        change P (ρ g v) = 0
        rw [hequiv, LinearMap.mem_ker.mp hv, map_zero] }
  have h := LinearMap.isCompl_of_proj hfix
  exact ⟨K, disjoint_iff_inf_le.mpr h.disjoint.le_bot,
    codisjoint_iff_le_sup.mpr h.codisjoint.top_le⟩

end RepresentationTheory.CompactGroupSemisimple

end MathlibExt.GroupTheory.CompactGroupSemisimpleWanted
