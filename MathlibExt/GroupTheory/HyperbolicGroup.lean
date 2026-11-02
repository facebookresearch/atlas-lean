/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Group.WordMetric
public import Mathlib.GroupTheory.Finiteness
public import MathlibExt.Topology.MetricSpace.GromovHyperbolic

/-!
# Hyperbolic groups

This file defines word-hyperbolic finitely generated groups: a group is word-hyperbolic
when some finite generating family's word metric is Gromov-hyperbolic
(`MathlibExt.Topology.MetricSpace.GromovHyperbolic`).

## Main definitions

* `Group.IsHyperbolic G`: a group `G` is word-hyperbolic, i.e. it admits a finite generating
  family whose word metric (`Group.Generators.normedGroup`) makes `G` a Gromov-hyperbolic space.

## Main results

* `Group.IsHyperbolic.fg`: a word-hyperbolic group is finitely generated.
* `Group.IsHyperbolic.of_subsingleton`: a trivial (subsingleton) group is word-hyperbolic.

## References

* M. Gromov, *Hyperbolic groups*, in Essays in Group Theory, Math. Sci. Res. Inst. Publ. 8,
  Springer (1987), 75-263. Word-hyperbolic groups are defined via the word metric on the
  Cayley graph in §1.2.

## Tags

hyperbolic group, word metric, geometric group theory
-/

@[expose] public section

namespace Group

variable {G : Type*} [Group G]

/-- **Word-hyperbolic groups.** A group $G$ is word-hyperbolic if there are a finite index set
$\iota$ and a family $(s_i)_{i \in \iota}$ of elements generating $G$ such that $G$, equipped with
the word metric of this generating family, is $\delta$-hyperbolic for some real number $\delta$. -/
def IsHyperbolic (G : Type*) [Group G] : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (P : Group.Generators G ι) (δ : ℝ),
    @Metric.IsDeltaHyperbolic G P.normedGroup.toMetricSpace.toPseudoMetricSpace δ

/-- **Word-hyperbolic groups are finitely generated.** Every word-hyperbolic group is finitely
generated. -/
theorem IsHyperbolic.fg (h : IsHyperbolic G) : Group.FG G := by
  obtain ⟨ι, hι, P, _, _⟩ := h
  letI := hι
  rw [Group.fg_iff]
  exact ⟨Set.range P.val, P.closure_eq_top, Set.finite_range P.val⟩

/-- **The trivial group is word-hyperbolic.** Every trivial group is word-hyperbolic: the empty
family generates it, and its word metric is $0$-hyperbolic. -/
theorem IsHyperbolic.of_subsingleton (G : Type*) [Group G] [Subsingleton G] : IsHyperbolic G := by
  refine ⟨Empty, inferInstance, ⟨Empty.elim, Subsingleton.elim _ _⟩, 0, le_refl 0, fun w x y z => ?_⟩
  rw [Subsingleton.elim x w, Subsingleton.elim y w, Subsingleton.elim z w, min_self, sub_zero]

end Group

/-! ### Examples -/

-- The trivial group is word-hyperbolic.
example {G : Type*} [Group G] [Subsingleton G] : Group.IsHyperbolic G :=
  Group.IsHyperbolic.of_subsingleton G
