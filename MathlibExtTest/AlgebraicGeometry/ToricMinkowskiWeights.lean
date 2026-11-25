/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ToricMinkowskiWeights

/-!
# Tests for Minkowski weights and the displacement product

No cone of an `n`-dimensional fan has codimension `n + 1`, so the only weight of
that codimension is zero, and the displacement product of weights whose
codimensions add up to more than `n` vanishes. The lattice coefficient is the
actual index: for the rays `(1, 0)` and `(1, 2)` it is `2`. Quotient normals
point into the larger cone, so their sign is fixed.
-/

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.ToricMinkowskiWeights

/-- The only weight of codimension `n + 1` is zero. -/
example {n : ℕ} (F : FiniteFan n) (N : NormalData F) (w : weights F N (n + 1)) : w.val = 0 := by
  funext σ
  exact w.property.1 σ (by omega)

/-- The displacement product vanishes beyond the dimension. -/
example {n : ℕ} (F : FiniteFan n) (k l : ℕ) (h : n < k + l) (w v : F.Face → ℤ)
    (a : RealSpace n) : displacementProduct F k l w v a = 0 := by
  funext γ
  simp only [displacementProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun σ _ ↦ Finset.sum_eq_zero fun τ _ ↦ ?_
  split_ifs with h'
  · exact absurd h'.2.2.2.2.1 (by omega)
  · rfl

theorem coneSpan_ray {n : ℕ} (u : Lattice n) :
    coneSpan (PointedCone.hull ℝ {latticeCast n u}) = ℝ ∙ latticeCast n u := by
  simp [coneSpan, PointedCone.hull]

theorem mem_coneLattice_ray {n : ℕ} (u v : Lattice n) :
    v ∈ coneLattice (PointedCone.hull ℝ {latticeCast n u}) ↔
      ∃ c : ℝ, c • latticeCast n u = latticeCast n v := by
  change latticeCast n v ∈ coneSpan _ ↔ _
  rw [coneSpan_ray, Submodule.mem_span_singleton]

theorem mem_ray_one_zero (v : Lattice 2) :
    v ∈ coneLattice (PointedCone.hull ℝ {latticeCast 2 ![1, 0]}) ↔ v 1 = 0 := by
  rw [mem_coneLattice_ray]
  constructor
  · rintro ⟨c, hc⟩
    have h := congrFun hc 1
    simp [latticeCast] at h
    exact_mod_cast h.symm
  · intro h
    refine ⟨v 0, funext fun i ↦ ?_⟩
    fin_cases i <;> simp [latticeCast, h]

theorem mem_ray_one_two (v : Lattice 2) :
    v ∈ coneLattice (PointedCone.hull ℝ {latticeCast 2 ![1, 2]}) ↔ v 1 = 2 * v 0 := by
  rw [mem_coneLattice_ray]
  constructor
  · rintro ⟨c, hc⟩
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [latticeCast] at h0 h1
    have : (v 1 : ℝ) = 2 * v 0 := by rw [← h1, ← h0]; ring
    exact_mod_cast this
  · intro h
    refine ⟨v 0, funext fun i ↦ ?_⟩
    fin_cases i
    · simp [latticeCast]
    · simp [latticeCast, h]
      ring

theorem mem_sup_rays (v : Lattice 2) :
    v ∈ coneLattice (PointedCone.hull ℝ {latticeCast 2 ![1, 0]}) ⊔
        coneLattice (PointedCone.hull ℝ {latticeCast 2 ![1, 2]}) ↔ Even (v 1) := by
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [mem_ray_one_zero] at ha
    rw [mem_ray_one_two] at hb
    exact ⟨b 0, by simp [ha, hb]; ring⟩
  · rintro ⟨m, hm⟩
    refine ⟨![v 0 - m, 0], (mem_ray_one_zero _).mpr (by simp), ![m, 2 * m],
      (mem_ray_one_two _).mpr (by simp), funext fun i ↦ ?_⟩
    fin_cases i
    · simp
    · simp [hm]
      ring

/-- The rays `(1, 0)` and `(1, 2)` span a sublattice of index two. -/
theorem index_rays : (coneLattice (PointedCone.hull ℝ {latticeCast 2 ![1, 0]}) ⊔
    coneLattice (PointedCone.hull ℝ {latticeCast 2 ![1, 2]})).index = 2 := by
  rw [AddSubgroup.index_eq_two_iff]
  refine ⟨![0, 1], fun b ↦ ?_⟩
  rw [mem_sup_rays, mem_sup_rays]
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Int.even_add_one]
  by_cases h : Even (b 1) <;> simp [h]

/-- In any fan containing the rays `(1, 0)` and `(1, 2)`, their lattice coefficient is `2`. -/
example (F : FiniteFan 2) (σ τ : F.Face)
    (hσ : σ.val = PointedCone.hull ℝ {latticeCast 2 ![1, 0]})
    (hτ : τ.val = PointedCone.hull ℝ {latticeCast 2 ![1, 2]}) :
    latticeCoefficient F σ τ = 2 := by
  rw [latticeCoefficient, hσ, hτ, index_rays]
  rfl

/-- The normal of the ray `(1, 0)` over its vertex points into the ray: it is
never `(-1, 0)`. -/
example (F : FiniteFan 2) (σ τ : F.Face)
    (hσ : σ.val = PointedCone.hull ℝ {latticeCast 2 ![1, 0]}) (hτ : τ.val = ⊥)
    (N : FaceNormal F σ τ) : N.vector ≠ ![-1, 0] := by
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ := N.positive
  have hy0 : y = 0 := by
    rw [hτ, coneSpan] at hy
    simpa using hy
  rw [hσ, PointedCone.mem_hull_singleton] at hx
  obtain ⟨c, hc0, hc⟩ := hx
  have h0 := congrFun hxy 0
  rw [h, hy0, add_zero, ← hc] at h0
  simp [latticeCast] at h0
  linarith
