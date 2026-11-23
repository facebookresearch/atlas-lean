/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Module.WeakTopologyInfiniteDimensional
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Lp.lpSpace

@[expose] public section

namespace MathlibExtTest.Analysis.Normed.Module.WeakTopologyInfiniteDimensional

open Metric
open MathlibExt.Analysis.Normed.Module.WeakTopologyInfiniteDimensional

/-- `Fact` instance for `1 ≤ 2` in `ENNReal`, needed by the `lp _ 2` normed-group
instances. -/
instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-- The standard basis vectors of `ℓ²(ℕ, ℝ)` are linearly independent. -/
private theorem l2_linearIndependent_single :
    LinearIndependent ℝ (fun n : ℕ => lp.single 2 n (1 : ℝ)) := by
  rw [linearIndependent_iff']
  intro s a ha j hj
  have h := congrArg (lp.evalₗ (𝕜 := ℝ) (fun _ : ℕ => ℝ) 2 j) ha
  simp only [map_sum, map_smul, map_zero, lp.evalₗ_apply] at h
  rw [Finset.sum_eq_single j _ _] at h
  · simpa [lp.single_apply_self] using h
  · intro i _ hne
    rw [lp.single_apply_ne _ _ _ hne.symm]
    simp
  · intro hns
    exact absurd hj hns

/-- The sequence space `ℓ²(ℕ, ℝ)` is infinite-dimensional. -/
private theorem l2_not_finiteDimensional :
    ¬ FiniteDimensional ℝ (lp (fun _ : ℕ => ℝ) 2) := by
  intro hfin
  have : Module.Finite ℝ (lp (fun _ : ℕ => ℝ) 2) := hfin
  exact Module.Finite.not_linearIndependent_of_infinite
    (fun n : ℕ => lp.single 2 n (1 : ℝ)) l2_linearIndependent_single

-- The coordinate functionals at `0` and `1` on `ℓ²` have a common nonzero
-- kernel vector. (The two-element Finset is built with `Finset.cons`: the
-- `{a, b}` literal would need a `DecidableEq` instance on continuous linear
-- maps, which does not exist.)
example : ∃ v : lp (fun _ : ℕ => ℝ) 2,
    v ≠ 0 ∧ lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0 v = 0 ∧
      lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 1 v = 0 := by
  have hne : lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0 ≠ lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 1 := by
    intro h
    have h1 : (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0)
        (lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ))
        = (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 1)
          (lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ)) := by rw [h]
    have e0 : (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0)
        (lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ)) = (1 : ℝ) := by
      show (lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ)) 0 = 1
      exact lp.single_apply_self _ _ _
    have e1 : (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 1)
        (lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ)) = (0 : ℝ) := by
      show (lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ)) 1 = 0
      exact lp.single_apply_ne _ _ _ (by norm_num : (1 : ℕ) ≠ 0)
    rw [e0, e1] at h1
    exact one_ne_zero h1
  have hmem : lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0 ∉
      ({lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 1} :
        Finset (↥(lp (fun _ : ℕ => ℝ) 2) →L[ℝ] ℝ)) := by
    rw [Finset.mem_singleton]
    exact hne
  let S : Finset (↥(lp (fun _ : ℕ => ℝ) 2) →L[ℝ] ℝ) :=
    Finset.cons (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0)
      {lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 1} hmem
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_forall_dual_apply_eq_zero
    l2_not_finiteDimensional S
  refine ⟨v, hv0, ?_, ?_⟩
  · exact hv _ (Finset.mem_cons_self _ _)
  · exact hv _ (Finset.mem_cons_of_mem (Finset.mem_singleton_self _))

-- `0` lies in the weak closure of the unit sphere of `ℓ²`, since the weak
-- closure of the sphere is the closed unit ball.
example : toWeakSpace ℝ (lp (fun _ : ℕ => ℝ) 2) (0 : lp (fun _ : ℕ => ℝ) 2) ∈
    closure (toWeakSpace ℝ (lp (fun _ : ℕ => ℝ) 2) ''
      Metric.sphere (0 : lp (fun _ : ℕ => ℝ) 2) 1) := by
  rw [closure_image_sphere_eq_image_closedBall l2_not_finiteDimensional]
  exact ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩

-- The open unit ball of `ℓ²` is not weakly open.
example : ¬ IsOpen (toWeakSpace ℝ (lp (fun _ : ℕ => ℝ) 2) ''
    Metric.ball (0 : lp (fun _ : ℕ => ℝ) 2) 1) :=
  not_isOpen_image_ball l2_not_finiteDimensional

-- The unit sphere of `ℓ²` is not weakly closed.
example : ¬ IsClosed (toWeakSpace ℝ (lp (fun _ : ℕ => ℝ) 2) ''
    Metric.sphere (0 : lp (fun _ : ℕ => ℝ) 2) 1) :=
  not_isClosed_image_sphere l2_not_finiteDimensional

-- The unit sphere of `ℓ²` is not weakly compact.
example : ¬ IsCompact (toWeakSpace ℝ (lp (fun _ : ℕ => ℝ) 2) ''
    Metric.sphere (0 : lp (fun _ : ℕ => ℝ) 2) 1) :=
  not_isCompact_image_sphere l2_not_finiteDimensional

-- In finite dimensions, the identity map to the weak topology is an open map.
example : IsOpenMap (toWeakSpaceCLM ℝ (EuclideanSpace ℝ (Fin 2))) :=
  isOpenMap_toWeakSpaceCLM_of_finiteDimensional

end MathlibExtTest.Analysis.Normed.Module.WeakTopologyInfiniteDimensional
