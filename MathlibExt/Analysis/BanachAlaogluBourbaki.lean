/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/BanachAlaoglu.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval),
problem `banach_alaoglu_bourbaki`, at commit 38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/banach_alaoglu_bourbaki.toml`, rev 1, submitter Kim Morrison, status archived):
the definition of `weakStarPolar` and the statement of `banach_alaoglu_bourbaki`, with their
docstrings from `WantedExt/Analysis/BanachAlaogluWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations
under the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS converted the benchmark statement to
a Batteries wanted declaration and placed it in the namespace below. ATLAS subsequently proved
the theorem and moved the definition and statement to this module with their names, types,
and docstrings intact.
-/
module

public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Banach–Alaoglu–Bourbaki theorem

The weak-star polar `weakStarPolar` of a zero-neighbourhood in a real locally convex space is
compact in the weak-star topology (`banach_alaoglu_bourbaki`).
-/

@[expose] public section

namespace MathlibExt.Analysis.BanachAlaogluWanted
namespace Analysis

open Set Topology
open scoped Pointwise

set_option linter.dupNamespace false in
/-- **Weak-star polar.** For a real topological vector space $E$ and a subset $s \subseteq E$,
the weak-star polar of $s$ is the set of continuous linear functionals $\varphi$ on $E$, viewed
as elements of the weak dual of $E$, such that $|\varphi(x)| \le 1$ for every $x \in s$. -/
def weakStarPolar (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] (s : Set E) : Set (WeakDual ℝ E) :=
  {φ | ∀ x ∈ s, ‖φ x‖ ≤ 1}

set_option linter.dupNamespace false in
/-- **Banach–Alaoglu–Bourbaki theorem.** Let $E$ be a real locally convex topological vector
space and let $U$ be a neighbourhood of $0$ in $E$. Then the weak-star polar of $U$ is compact
in the weak dual of $E$, that is, in the space of continuous linear functionals on $E$ with the
weak-star topology.

Source: N. Bourbaki, Espaces vectoriels topologiques; the normed case is L. Alaoglu, Ann. of Math.
41 (1940). Listed as §137 in O. Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `banach_alaoglu_bourbaki`. -/
theorem banach_alaoglu_bourbaki (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (U : Set E) (hU : U ∈ 𝓝 (0 : E)) :
    IsCompact (weakStarPolar E U) := by
  let : IsTopologicalAddGroup E :=
    { ‹ContinuousAdd E›, ContinuousNeg.of_continuousConstSMul ℝ E with }
  let ev : WeakDual ℝ E → E → ℝ := fun φ x ↦ φ x
  have he : IsEmbedding ev := WeakBilin.isEmbedding ContinuousLinearMap.coe_injective
  rw [he.isCompact_iff]
  -- Within the algebraic dual, the polar constraints ensure continuity.
  let L : Set (E → ℝ) := range ((↑) : (E →ₗ[ℝ] ℝ) → E → ℝ)
  let B : Set (E → ℝ) := {f | ∀ x ∈ U, ‖f x‖ ≤ 1}
  have himage : ev '' weakStarPolar E U = L ∩ B := by
    ext f
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨⟨φ.toStrongDual.toLinearMap, rfl⟩, hφ⟩
    · rintro ⟨⟨g, rfl⟩, hg⟩
      have hbounded : Bornology.IsVonNBounded ℝ (g '' U) :=
        (NormedSpace.image_isVonNBounded_iff ℝ).2 ⟨1, hg⟩
      exact ⟨g.clmOfExistsBoundedImage ⟨U, hU, hbounded⟩, hg, rfl⟩
  have hclosed : IsClosed (ev '' weakStarPolar E U) := by
    rw [himage]
    refine (LinearMap.isClosed_range_coe E ℝ (RingHom.id ℝ)).inter ?_
    dsimp only [B]
    simp only [ofPred_forall]
    exact isClosed_biInter fun x hx ↦ isClosed_Iic.preimage (continuous_apply x).norm
  -- Absorbency gives a compact interval containing the values at each point.
  have hbound (x : E) : ∃ r : ℝ, ∀ φ ∈ weakStarPolar E U, ‖φ x‖ ≤ r := by
    obtain ⟨r, hr, hsub⟩ := (absorbent_nhds_zero (𝕜 := ℝ) hU x).exists_pos
    have hx : x ∈ r • U := hsub r (by simp [Real.norm_of_nonneg hr.le]) (mem_singleton x)
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨‖r‖, fun φ hφ ↦ ?_⟩
    rw [map_smul, norm_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hφ y hy) (norm_nonneg r)
  choose r hr using hbound
  refine (isCompact_univ_pi fun x ↦ isCompact_closedBall (0 : ℝ) (r x)).of_isClosed_subset
    hclosed ?_
  rintro _ ⟨φ, hφ, rfl⟩
  exact fun x _ ↦ mem_closedBall_zero_iff.mpr (hr x φ hφ)

end Analysis

end MathlibExt.Analysis.BanachAlaogluWanted
