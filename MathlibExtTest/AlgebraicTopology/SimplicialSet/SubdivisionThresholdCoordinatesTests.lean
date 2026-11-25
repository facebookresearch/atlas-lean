/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.ThresholdCoordinates

/-!
# Tests for all-universe subdivision threshold coordinates

Public-only clients exercise the coordinate equivalence at symbolic, one, and
zero universes, the representable subdivision cells for `Delta[0]` through
`Delta[2]`, repeated positive thresholds, a zero coordinate, support faces,
and singleton restrictions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace SubdivisionThresholdCoordinatesTests

/-- Symbolic-universe `Delta[0]` coordinate client. -/
noncomputable example (x : Convexity.StdSimplex ℝ (Fin 1)) :
    SSet.ThresholdCoordinates.{u} 0 :=
  SSet.thresholdCoordinates x

/-- Universe-one `Delta[1]` coordinate client. -/
noncomputable example (x : Convexity.StdSimplex ℝ (Fin 2)) :
    SSet.ThresholdCoordinates.{1} 1 :=
  SSet.thresholdCoordinates x

/-- Universe-zero `Delta[2]` coordinate client. -/
noncomputable example (x : Convexity.StdSimplex ℝ (Fin 3)) :
    SSet.ThresholdCoordinates.{0} 2 :=
  SSet.thresholdCoordinates x

/-- The representable affine chart reconstructs every point. -/
example {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SimplexCategory.sdCellMap (SSet.thresholdSimplex.{u} x)
        (SSet.thresholdWeights x) = x :=
  SSet.sdCellMap_threshold (x := x)

/-- Threshold cell evaluation is compatible with every ambient face map. -/
example {m n : SimplexCategory} (f : m ⟶ n) [Mono f]
    (x : Convexity.StdSimplex ℝ (Fin (m.len + 1))) :
    SimplexCategory.sdCellMap
        ((SimplexCategory.sd.{u}.map f).app _
          (SSet.thresholdSimplex.{u} x))
        (SSet.thresholdWeights x) =
      Convexity.StdSimplex.map f x :=
  SSet.sdCellMap_threshold_natural_mono f x

/-- The forward coordinate map followed by evaluation is the identity. -/
example {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SSet.thresholdCoordinatesToPoint (SSet.thresholdCoordinates.{u} x) = x :=
  SSet.thresholdCoordinatesToPoint_thresholdCoordinates x

/-- Evaluation followed by coordinate extraction is the identity. -/
example {n : ℕ} (c : SSet.ThresholdCoordinates.{u} n) :
    SSet.thresholdCoordinates.{u} (SSet.thresholdCoordinatesToPoint c) = c :=
  SSet.thresholdCoordinates_thresholdCoordinatesToPoint c

/-- The bundled coordinate equivalence has the intended inverse. -/
example {n : ℕ} (c : SSet.ThresholdCoordinates.{u} n) :
    SSet.thresholdCoordinatesEquiv.{u} n
        ((SSet.thresholdCoordinatesEquiv.{u} n).symm c) = c := by
  simp

/-- Threshold levels decrease while threshold faces increase. -/
example {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    StrictAnti (SSet.thresholdLevel x) ∧
      Monotone (SSet.thresholdFace.{u} x) :=
  ⟨SSet.thresholdLevel_strictAnti x,
    SSet.thresholdFace_monotone x⟩

/-- Face membership is exactly the coordinate threshold inequality. -/
example {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (SSet.thresholdDim x + 1)) (i : Fin (n + 1)) :
    ULift.up i ∈ ((SSet.thresholdSimplex.{u} x).obj j).finset ↔
      SSet.thresholdLevel x j ≤ x.weights i :=
  SSet.mem_thresholdSimplex_face_iff x j i

/-- The maximal threshold face is the coordinate support. -/
example {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) :
    ULift.up i ∈ ((SSet.thresholdSimplex.{u} x).obj
        (Fin.last (SSet.thresholdDim x))).finset ↔
      0 < x.weights i :=
  SSet.mem_thresholdSimplex_last_iff x i

/-- Zero coordinates are exactly absent from the maximal support face. -/
example {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) :
    x.weights i = 0 ↔
      ULift.up i ∉ ((SSet.thresholdSimplex.{u} x).obj
        (Fin.last (SSet.thresholdDim x))).finset :=
  SSet.weight_eq_zero_iff_not_mem_thresholdSimplex_last x i

/-- Singleton input has dimension zero and its face has only that vertex. -/
example {n : ℕ} (i k : Fin (n + 1))
    (j : Fin (SSet.thresholdDim
      (Convexity.StdSimplex.single (R := ℝ) i) + 1)) :
    SSet.thresholdDim (Convexity.StdSimplex.single (R := ℝ) i) = 0 ∧
      (ULift.up k ∈ ((SSet.thresholdSimplex.{u}
          (Convexity.StdSimplex.single (R := ℝ) i)).obj j).finset ↔
        k = i) :=
  ⟨SSet.thresholdDim_single i,
    SSet.mem_thresholdSimplex_single_face_iff i k j⟩

/-- A `Delta[2]` point with two equal positive coordinates and one zero
coordinate. -/
private noncomputable def repeatedThresholdPoint :
    Convexity.StdSimplex ℝ (Fin 3) :=
  Convexity.StdSimplex.duple (0 : Fin 3) (1 : Fin 3)
    (s := 1 / 2) (t := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)

private theorem repeatedThresholdPoint_levels :
    SSet.thresholdPositiveLevels repeatedThresholdPoint = {1 / 2} := by
  ext r
  constructor
  · intro hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    have hpos := (Finset.mem_filter.mp ha).2
    fin_cases a <;>
      norm_num [repeatedThresholdPoint, Convexity.StdSimplex.duple,
        Finsupp.single_apply] at *
  · intro hr
    have hr' : r = 1 / 2 := by simpa using hr
    subst r
    apply Finset.mem_image.mpr
    refine ⟨(0 : Fin 3), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      norm_num [repeatedThresholdPoint, Convexity.StdSimplex.duple,
        Finsupp.single_apply]
    · norm_num [repeatedThresholdPoint, Convexity.StdSimplex.duple,
        Finsupp.single_apply]

/-- Repeated positive values produce one threshold rather than duplicate
faces. -/
private theorem repeatedThresholdPoint_dim :
    SSet.thresholdDim repeatedThresholdPoint = 0 := by
  rw [SSet.thresholdDim, repeatedThresholdPoint_levels]
  simp

/-- Both positive coordinates lie in the support face. -/
private theorem repeatedThresholdPoint_zero_mem :
    ULift.up (0 : Fin 3) ∈
      ((SSet.thresholdSimplex.{u} repeatedThresholdPoint).obj
        (Fin.last (SSet.thresholdDim repeatedThresholdPoint))).finset := by
  rw [SSet.mem_thresholdSimplex_last_iff]
  norm_num [repeatedThresholdPoint, Convexity.StdSimplex.duple]

private theorem repeatedThresholdPoint_one_mem :
    ULift.up (1 : Fin 3) ∈
      ((SSet.thresholdSimplex.{u} repeatedThresholdPoint).obj
        (Fin.last (SSet.thresholdDim repeatedThresholdPoint))).finset := by
  rw [SSet.mem_thresholdSimplex_last_iff]
  norm_num [repeatedThresholdPoint, Convexity.StdSimplex.duple]

/-- The zero coordinate is absent from the support face. -/
private theorem repeatedThresholdPoint_two_not_mem :
    ULift.up (2 : Fin 3) ∉
      ((SSet.thresholdSimplex.{u} repeatedThresholdPoint).obj
        (Fin.last (SSet.thresholdDim repeatedThresholdPoint))).finset := by
  rw [← SSet.weight_eq_zero_iff_not_mem_thresholdSimplex_last]
  norm_num [repeatedThresholdPoint, Convexity.StdSimplex.duple]

#print axioms SSet.sdCellMap_threshold
#print axioms SSet.thresholdCoordinates_thresholdCoordinatesToPoint
#print axioms SSet.thresholdCoordinatesEquiv
#print axioms SSet.mem_thresholdSimplex_last_iff
#print axioms SSet.weight_eq_zero_iff_not_mem_thresholdSimplex_last

end SubdivisionThresholdCoordinatesTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
