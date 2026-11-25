/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Affine

/-!
# Affine subdivision-cell consumers

Persistent clients for all six affine-cell declarations, the S4 coordinate
formula, low-dimensional and repeated chains, and the noninjective ambient
naturality counterexample.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial Opposite Topology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SubdivisionAffineTests

universe u

section PublicSurface

variable {n : SimplexCategory} {d e : ℕ}
  (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))

example :
    C(Convexity.StdSimplex ℝ (Fin (d + 1)),
      Convexity.StdSimplex ℝ (Fin (n.len + 1))) :=
  SimplexCategory.sdCellMap σ

example (x : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (i : Fin (n.len + 1)) :
    (SimplexCategory.sdCellMap σ x).weights i =
      ∑ j, x.weights j *
        (Convexity.StdSimplex.subBarycenter
          ((σ.obj j).finset.image
            (fun a => (a.down : Fin (n.len + 1))))
          (by exact (σ.obj j).nonempty.image _)).weights i :=
  SimplexCategory.sdCellMap_weights_apply σ x i

example (f : SimplexCategory.mk e ⟶ SimplexCategory.mk d) :
    (SimplexCategory.sdCellMap σ).comp
        (SSet.stdSimplex.toTopMap f).hom =
      SimplexCategory.sdCellMap
        ((SimplexCategory.sd.{u}.obj n).map f.op σ) :=
  SimplexCategory.sdCellMap_face σ f

example {m n : SimplexCategory} (f : m ⟶ n) [Mono f] {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj m).obj (op (SimplexCategory.mk d))) :
    SimplexCategory.sdCellMap ((SimplexCategory.sd.{u}.map f).app _ σ) =
      (SSet.stdSimplex.toTopMap f).hom.comp
        (SimplexCategory.sdCellMap σ) :=
  SimplexCategory.sdCellMap_natural_mono f σ

example (x : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    ((SimplexCategory.sdCellMap σ x).weights :
        Fin (n.len + 1) → ℝ) ∈
      convexHull ℝ
        (Set.range fun j : Fin (d + 1) =>
          ((SimplexCategory.sdCellMap σ
              (Convexity.StdSimplex.single (R := ℝ) j)).weights :
            Fin (n.len + 1) → ℝ)) :=
  SimplexCategory.sdCellMap_weights_mem_convexHull σ x

example :
    Metric.diam (Set.range (SimplexCategory.sdCellMap σ)) ≤
      (n.len : ℝ) / ((n.len : ℝ) + 1) *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin (n.len + 1)))) :=
  SimplexCategory.diam_range_sdCellMap_le σ

end PublicSurface

section LowDimensional

example {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj ⦋0⦌).obj
      (op (SimplexCategory.mk d))) :
    Metric.diam (Set.range (SimplexCategory.sdCellMap σ)) ≤ 0 := by
  simpa using SimplexCategory.diam_range_sdCellMap_le σ

example {n : SimplexCategory}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk 0))) :
    C(Convexity.StdSimplex ℝ (Fin 1),
      Convexity.StdSimplex ℝ (Fin (n.len + 1))) :=
  SimplexCategory.sdCellMap σ

/-- Degenerating a vertex cell produces a repeated-face edge cell, and the
all-domain face theorem still applies. -/
example {n : SimplexCategory}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk 0))) :
    (SimplexCategory.sdCellMap σ).comp
        (SSet.stdSimplex.toTopMap
          (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)).hom =
      SimplexCategory.sdCellMap
        ((SimplexCategory.sd.{u}.obj n).map
          (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op σ) :=
  SimplexCategory.sdCellMap_face σ
    (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)

end LowDimensional

section NoninjectiveAmbientMap

/-- The monotone ambient degeneracy `0,1 ↦ 0`, `2 ↦ 1`. -/
private def collapseOrderHom : Fin 3 →o Fin 2 where
  toFun i := if i = 2 then 1 else 0
  monotone' := by decide

private def collapse : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 1 :=
  SimplexCategory.Hom.mk collapseOrderHom

private theorem collapse_not_injective :
    ¬ Function.Injective collapse := by
  intro h
  have h01 : collapse (0 : Fin 3) = collapse (1 : Fin 3) := rfl
  exact Fin.zero_ne_one (h h01)

private theorem collapse_fullBarycenter_weight_zero :
    ((Convexity.StdSimplex.barycenter :
      Convexity.StdSimplex ℝ (Fin 3)).map collapse).weights 0 = 2 / 3 := by
  rw [Convexity.StdSimplex.weights_map_apply]
  have hfilter :
      Finset.univ.filter (fun i : Fin 3 => collapse i = 0) = {0, 1} := by
    decide
  rw [hfilter]
  norm_num [Convexity.StdSimplex.weights_barycenter_apply]

private theorem image_fullBarycenter_weight_zero :
    (Convexity.StdSimplex.barycenter :
      Convexity.StdSimplex ℝ (Fin 2)).weights 0 = 1 / 2 := by
  rw [Convexity.StdSimplex.weights_barycenter_apply, Fintype.card_fin]
  norm_num

/-- Uniform face barycenters do not commute with a noninjective ambient map;
this is why `sdCellMap_natural_mono` requires `[Mono f]`. -/
example :
    (Convexity.StdSimplex.barycenter :
      Convexity.StdSimplex ℝ (Fin 3)).map collapse ≠
        (Convexity.StdSimplex.barycenter :
          Convexity.StdSimplex ℝ (Fin 2)) := by
  intro h
  have h0 := congrArg (fun q => q.weights 0) h
  rw [collapse_fullBarycenter_weight_zero,
    image_fullBarycenter_weight_zero] at h0
  norm_num at h0

end NoninjectiveAmbientMap

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SubdivisionAffineTests
