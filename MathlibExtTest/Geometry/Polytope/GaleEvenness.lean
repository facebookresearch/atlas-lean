/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Polytope.GaleEvenness

@[expose] public section

open MathlibExt.Geometry.Polytope

namespace MathlibExtTest.Geometry.Polytope.GaleEvenness

/-- Parameters `0 < 1 < 2 < 3` on the moment curve. -/
noncomputable abbrev t4 : Fin 4 → ℝ := fun i => (i : ℝ)

theorem t4_strictMono : StrictMono t4 := fun a b h => by
  simp only [t4, Nat.cast_lt]
  exact h

/-- Non-vacuity of Gale's criterion: in the cyclic quadrilateral `C_2(4)`, the segment
`[γ(0), γ(1)]` is an edge. -/
example : IsExposed ℝ (cyclicPolytope 2 t4)
    (convexHull ℝ ((fun i => momentCurve 2 (t4 i)) '' (({0, 1} : Finset (Fin 4)) : Set (Fin 4)))) :=
  (isExposed_cyclicPolytope_iff_galeEvenness t4_strictMono _ (by decide)).2 (by decide)

/-- ... while the diagonal `[γ(0), γ(2)]` is not a face. -/
example : ¬ IsExposed ℝ (cyclicPolytope 2 t4)
    (convexHull ℝ ((fun i => momentCurve 2 (t4 i)) '' (({0, 2} : Finset (Fin 4)) : Set (Fin 4)))) :=
  fun h => absurd ((isExposed_cyclicPolytope_iff_galeEvenness t4_strictMono _ (by decide)).1 h)
    (by decide)

/-- Neighborliness: in `C_4(4)`, any two vertices span an edge. -/
example : IsExposed ℝ (cyclicPolytope 4 t4)
    (convexHull ℝ ((fun i => momentCurve 4 (t4 i)) '' (({1, 3} : Finset (Fin 4)) : Set (Fin 4)))) :=
  isExposed_cyclicPolytope_of_two_mul_card_le t4_strictMono.injective _ (by decide)

/-- Parameters `0 < 1 < 2`: the cyclic simplex `C_2(3)` is a triangle in `ℝ^2`. -/
noncomputable abbrev t3 : Fin 3 → ℝ := fun i => (i : ℝ)

theorem t3_injective : Function.Injective t3 := fun a b h => by
  simp only [t3, Nat.cast_inj] at h
  exact Fin.ext h

/-- The triangle `C_2(3)` has f-vector `(f_0, f_1) = (3, 3)` and `f_2 = 1`. -/
example : faceNumber (cyclicVertices 2 t3) 0 = 3 ∧ faceNumber (cyclicVertices 2 t3) 1 = 3 ∧
    faceNumber (cyclicVertices 2 t3) 2 = 1 := by
  simp only [faceNumber_cyclicSimplex t3_injective]
  decide

/-- It has dimension `2` and is simplicial. -/
example : dim (cyclicVertices 2 t3) = 2 ∧ IsSimplicial (cyclicVertices 2 t3) :=
  ⟨dim_cyclicSimplex t3_injective, isSimplicial_cyclicSimplex t3_injective⟩

/-- The Euler–Poincaré relation `f_0 - f_1 + f_2 = 1` holds for the triangle, computed from the
definitions (a consistency check for the wanted statement). -/
example : ∑ k ∈ Finset.range (dim (cyclicVertices 2 t3) + 1),
    (-1 : ℤ) ^ k * (faceNumber (cyclicVertices 2 t3) k : ℤ) = 1 := by
  rw [dim_cyclicSimplex t3_injective]
  simp only [faceNumber_cyclicSimplex t3_injective, Finset.sum_range_succ, Finset.sum_range_zero]
  decide

/-- A cyclic `4`-simplex `C_4(5)` has f-vector `(5, 10, 10, 5)`. -/
example {t : Fin 5 → ℝ} (ht : Function.Injective t) :
    (List.range 4).map (faceNumber (cyclicVertices 4 t)) = [5, 10, 10, 5] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, faceNumber_cyclicSimplex ht]
  decide

/-- The points `γ(0)` and `γ(1)` are vertices of the triangle, and adjacent in its graph. -/
example (h0 : momentCurve 2 (t3 0) ∈ (cyclicPolytope 2 t3).extremePoints ℝ)
    (h1 : momentCurve 2 (t3 1) ∈ (cyclicPolytope 2 t3).extremePoints ℝ) :
    (graph (cyclicVertices 2 t3)).Adj ⟨_, h0⟩ ⟨_, h1⟩ := by
  refine ⟨fun h => ?_, ?_⟩
  · have h' := (momentCurve_injective (by norm_num)) (congrArg Subtype.val h)
    simp [t3] at h'
  · have h := (isExposed_cyclicSimplex t3_injective {0, 1}).1
    rw [← convexHull_pair]
    convert h using 2
    · rfl
    · ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.coe_insert,
        Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]

/-- Every point `γ(t_i)` is a vertex of the triangle, so the hypotheses above are satisfiable. -/
example (i : Fin 3) : momentCurve 2 (t3 i) ∈ (cyclicPolytope 2 t3).extremePoints ℝ := by
  rw [extremePoints_cyclicSimplex t3_injective]
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩

end MathlibExtTest.Geometry.Polytope.GaleEvenness
