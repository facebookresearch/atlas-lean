/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialComplex.SphereTriangulation

/-!
# Ordinary finite sphere consumers

These clients retain the actual weak coordinates, realized boundary inclusion
and chosen classical disk gauge. The zero-dimensional boundary has no actual
vertices or points; the one-dimensional disk has its two-vertex boundary.
-/

open CategoryTheory Topology
open scoped Simplicial
open PreAbstractSimplicialComplex
open PreAbstractSimplicialComplex.SphereTriangulation

noncomputable section

universe u

example (n : ℕ) : Finite (Face (complex n)) := finite_faces n

example (n : ℕ)
    (x : Realization (⊤ : PreAbstractSimplicialComplex (Fin (n + 1)))) :
    fullSimplexHomeomorph n x = x.point := rfl

example (n : ℕ) (x : Realization (complex n)) :
    (coordinatesHomeomorph n x).val = x.point := coordinatesHomeomorph_coe n x

example (n : ℕ) :
    Realization (complex n) ≃ₜ SSet.toTop.obj (SSet.boundary.{u} n) :=
  realizedBoundaryHomeomorph n

example (n : ℕ) (x : Realization (complex n)) :
    (SSet.toTop.map (SSet.boundary.{u} n).ι).hom (realizedBoundaryHomeomorph.{u} n x) =
      (SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm x.point :=
  realizedBoundaryHomeomorph_map n x

example (n : ℕ) (x : Realization (complex n)) :
    (sphereHomeomorph n).symm (sphereHomeomorph n x) = x :=
  (sphereHomeomorph n).symm_apply_apply x

example (n : ℕ) (x : Realization (complex n)) :
    (SSet.stdSimplex.toClassicalDiskHomeomorph.{0} n
      ((SSet.toTop.map (SSet.boundary.{0} n).ι).hom
        (realizedBoundaryHomeomorph.{0} n x))).val = (sphereHomeomorph n x).val := by
  rw [realizedBoundaryHomeomorph_map, sphereHomeomorph_coe]

example : complex 0 = ⊥ := zero_geometry.1
example : IsEmpty (Face (complex 0)) := zero_geometry.2.1
example : IsEmpty (Vertex (complex 0)) := zero_geometry.2.2.1
example : IsEmpty (Realization (complex 0)) := zero_geometry.2.2.2.1
example : IsEmpty (Metric.sphere (0 : Fin 0 → ℝ) 1) := zero_geometry.2.2.2.2

example : ({0} : Finset (Fin 2)) ∈ complex 1 ∧
    ({1} : Finset (Fin 2)) ∈ complex 1 ∧ ({0, 1} : Finset (Fin 2)) ∉ complex 1 := by
  have h0 : ({0} : Finset (Fin 2)) ≠ Finset.univ := by
    intro h
    have hm : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := h ▸ Finset.mem_univ _
    simp at hm
  have h1 : ({1} : Finset (Fin 2)) ≠ Finset.univ := by
    intro h
    have hm : (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) := h ▸ Finset.mem_univ _
    simp at hm
  have h01 : ({0, 1} : Finset (Fin 2)) = Finset.univ := by
    ext i
    fin_cases i <;> simp
  change (_ ∧ _) ∧ (_ ∧ _) ∧ ¬(_ ∧ _)
  exact ⟨⟨Finset.singleton_nonempty _, h0⟩,
    ⟨Finset.singleton_nonempty _, h1⟩, fun h => h.2 h01⟩

end
