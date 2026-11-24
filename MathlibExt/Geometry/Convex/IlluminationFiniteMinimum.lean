/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Convex.Illumination
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Finiteness of the illumination number
-/

public section

namespace ConvexCovering

open NormedSpace Set

/-- **Every convex body has a finite illumination number.** For every $n \ge 1$ and every convex
body $K \subseteq \mathbb{R}^n$ there is a least natural number $q$ such that some $q$ unit vectors
$v_1, \dots, v_q$ illuminate $K$: every boundary point $x$ of $K$ has an $i$ and a $t > 0$ with
$x + t v_i$ in the interior of $K$.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction's illumination-number
definition; finite existence is the standard compact-convex-body qualification. -/
theorem illuminationFiniteMinimum :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∃ q : ℕ, IsLeast {q : ℕ | IlluminatedByDirections K q} q := by
  classical
  intro n _ K hK
  obtain ⟨c, hc⟩ := hK.2.2
  have hfront : IsCompact (frontier K) := hK.1.closure.diff isOpen_interior
  -- Translating a boundary point to c also takes a neighborhood of it into the interior.
  let shift (x : frontier K) := c - x.val
  have hne (x : frontier K) : shift x ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ x.property.2 (h ▸ hc)
  obtain ⟨s, hs⟩ := hfront.elim_nhds_subcover'
    (fun x hx ↦ (· + shift ⟨x, hx⟩) ⁻¹' interior K) fun x hx ↦ by
      apply (isOpen_interior.preimage (continuous_id.add_const _)).mem_nhds
      simpa [shift] using hc
  -- Normalize the finitely many translations and take the least feasible count.
  refine ⟨_, Nat.isLeast_find (p := IlluminatedByDirections K) ?_⟩
  let point (i : Fin s.card) : frontier K := (s.equivFin.symm i).val
  refine ⟨s.card, fun i ↦ normalize (shift (point i)), fun i ↦ norm_normalize (hne _), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
  refine ⟨s.equivFin ⟨y, hy⟩, hx, norm_normalize (hne _), ‖shift y‖, norm_pos_iff.mpr (hne y), ?_⟩
  simpa [point] using hxy

end ConvexCovering
