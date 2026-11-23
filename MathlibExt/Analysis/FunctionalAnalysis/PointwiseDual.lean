/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Continuous linear functionals for the topology of pointwise convergence -/

@[expose] public section

open Filter Topology

/-- **Continuous linear functionals on the space of all real functions.** A linear
functional on `H → ℝ` that is continuous for the product topology is a finite linear
combination of coordinate evaluations.

This is Banach and Mazur's theorem from Problem 10 of the *Scottish Book*, with continuity
made explicit. -/
theorem LinearMap.exists_fin_sum_mul_apply_of_continuous {H : Type*}
    (f : (H → ℝ) →ₗ[ℝ] ℝ) (hf : Continuous f) :
    ∃ (n : ℕ) (t : Fin n → H) (a : Fin n → ℝ), ∀ x : H → ℝ,
      f x = ∑ i, a i * x (t i) := by
  classical
  have hpre : f ⁻¹' Set.Iio (1 : ℝ) ∈ 𝓝 (0 : H → ℝ) :=
    (hf.continuousAt (x := 0)).preimage_mem_nhds (Iio_mem_nhds (by simp))
  rw [nhds_pi, Filter.mem_pi'] at hpre
  obtain ⟨s, U, hU, hs⟩ := hpre
  -- A vector vanishing on the constrained coordinates stays in this neighborhood when scaled.
  have hzero (z : H → ℝ) (hz : ∀ j ∈ s, z j = 0) : f z = 0 := by
    by_contra hne
    have hmem : (f z)⁻¹ • z ∈ (s : Set H).pi U := by
      intro j hj
      simpa [Pi.smul_apply, hz j hj] using mem_of_mem_nhds (hU j)
    have hlt : f ((f z)⁻¹ • z) < 1 := hs hmem
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne] at hlt
    exact (lt_irrefl _ hlt)
  let t : Fin s.card → H := fun i => (s.equivFin.symm i).val
  have ht : Function.Injective t := Subtype.val_injective.comp s.equivFin.symm.injective
  refine ⟨s.card, t, fun i => f (Pi.single (t i) (1 : ℝ)), ?_⟩
  intro x
  let y : H → ℝ := ∑ i : Fin s.card, x (t i) • Pi.single (t i) (1 : ℝ)
  have hy (j : H) (hj : j ∈ s) : y j = x j := by
    let i := s.equivFin ⟨j, hj⟩
    have hti : t i = j := by simp [t, i]
    change ((∑ k : Fin s.card, x (t k) • Pi.single (t k) (1 : ℝ)) : H → ℝ) j = x j
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [hti]
    · intro k _ hk
      have htk : t k ≠ j := fun h => hk (ht (h.trans hti.symm))
      simp [Pi.smul_apply, Pi.single_eq_of_ne htk.symm]
    · simp
  have hxy : f (x - y) = 0 := hzero (x - y) (fun j hj => by simp [Pi.sub_apply, hy j hj])
  rw [map_sub, sub_eq_zero] at hxy
  calc
    f x = f y := hxy
    _ = ∑ i, f (Pi.single (t i) (1 : ℝ)) * x (t i) := by
      simp [y, map_sum, map_smul, smul_eq_mul, mul_comm]
