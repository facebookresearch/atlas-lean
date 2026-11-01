/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.SturmLiouvilleUniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Tests for Sturm–Liouville uniqueness

* The zero function is a solution of the homogeneous problem `-u'' + V u = 0`
  with Dirichlet boundary conditions, for every continuous `V`.
* Any `C²` solution of that homogeneous problem agrees with the zero
  function on `[0, 1]`, by `sturm_liouville_uniqueness`: this exercises the
  theorem with a genuinely different second solution, not just `u₁ = u₂`.
* Two syntactically different presentations of the zero solution agree on
  `[0, 1]`, by `sturm_liouville_uniqueness`.
-/

namespace MathlibExtTest.Analysis.ODE.SturmLiouvilleUniquenessTests

open MathlibExt.Analysis.ODE.SturmLiouvilleUniqueness

/-- The zero function solves the homogeneous Sturm–Liouville problem. -/
private theorem zero_solution
    (V : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    ContDiffOn ℝ 2 (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 1) ∧
      (∀ x : ℝ, ∀ hx : x ∈ Set.Icc (0 : ℝ) 1,
        -(iteratedDerivWithin 2 (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 1) x) +
          V ⟨x, hx⟩ * (fun _ : ℝ => (0 : ℝ)) x =
          (ContinuousMap.const (Set.Icc (0 : ℝ) 1) (0 : ℝ)) ⟨x, hx⟩) ∧
      (fun _ : ℝ => (0 : ℝ)) 0 = 0 ∧ (fun _ : ℝ => (0 : ℝ)) 1 = 0 := by
  refine ⟨contDiffOn_const, fun x hx => ?_, rfl, rfl⟩
  simp

/-- Any `C²` solution of the homogeneous problem with Dirichlet boundary
conditions vanishes on `[0, 1]`. -/
example (V : C(Set.Icc (0 : ℝ) 1, ℝ)) (hV : ∀ x : Set.Icc (0 : ℝ) 1, 0 ≤ V x)
    (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Icc 0 1) ∧
      (∀ x : ℝ, ∀ hx : x ∈ Set.Icc (0 : ℝ) 1, -(iteratedDerivWithin 2 u (Set.Icc 0 1) x) +
        V ⟨x, hx⟩ * u x = (ContinuousMap.const (Set.Icc (0 : ℝ) 1) (0 : ℝ)) ⟨x, hx⟩) ∧
      u 0 = 0 ∧ u 1 = 0) :
    Set.EqOn u (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 1) :=
  sturm_liouville_uniqueness V hV (ContinuousMap.const (Set.Icc (0 : ℝ) 1) (0 : ℝ)) u
    (fun _ : ℝ => (0 : ℝ)) hu (zero_solution V)

/-- Two presentations of the zero solution agree on `[0, 1]`. -/
example (V : C(Set.Icc (0 : ℝ) 1, ℝ)) (hV : ∀ x : Set.Icc (0 : ℝ) 1, 0 ≤ V x) :
    Set.EqOn (fun _ : ℝ => (0 : ℝ)) (fun x => (0 : ℝ) * x) (Set.Icc 0 1) := by
  have h₂ : ContDiffOn ℝ 2 (fun x => (0 : ℝ) * x) (Set.Icc 0 1) ∧
      (∀ x : ℝ, ∀ hx : x ∈ Set.Icc (0 : ℝ) 1,
        -(iteratedDerivWithin 2 (fun x => (0 : ℝ) * x) (Set.Icc 0 1) x) +
          V ⟨x, hx⟩ * (fun x => (0 : ℝ) * x) x =
          (ContinuousMap.const (Set.Icc (0 : ℝ) 1) (0 : ℝ)) ⟨x, hx⟩) ∧
      (fun x => (0 : ℝ) * x) 0 = 0 ∧ (fun x => (0 : ℝ) * x) 1 = 0 := by
    have hfun : (fun x => (0 : ℝ) * x) = fun _ : ℝ => (0 : ℝ) := by
      funext x; simp
    rw [hfun]
    exact zero_solution V
  exact sturm_liouville_uniqueness V hV (ContinuousMap.const (Set.Icc (0 : ℝ) 1) (0 : ℝ))
    (fun _ : ℝ => (0 : ℝ)) (fun x => (0 : ℝ) * x) (zero_solution V) h₂

#print axioms sturm_liouville_uniqueness

end MathlibExtTest.Analysis.ODE.SturmLiouvilleUniquenessTests
