/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainContraction

open MathlibExt.Probability.MarkovChainContraction

/-- Diagonal distance is zero. -/
example {α : Type*} [Fintype α] (p : PMF α) : tvDist p p = 0 :=
  MathlibExt.Probability.MarkovMixing.tvDist_self _

/-- Boundary check: starting both chains at the same state keeps
the distance at `0` (both sides are the same law). -/
example {α : Type*} [Fintype α] (K : α → PMF α) (x : α) (t : ℕ) :
    tvDist (chainDist K x (t + 1)) (chainDist K x (t + 1)) ≤
      tvDist (chainDist K x t) (chainDist K x t) :=
  tvDist_chainDist_mono K x x t

/-- The zero-step chain is the point mass at the start. -/
example {α : Type*} (K : α → PMF α) (x : α) : chainDist K x 0 = PMF.pure x := rfl

/-- On `Fin 2`, the identity kernel keeps the two point masses at
distance `1` after one step: this pins the bind orientation, the
step indexing, and the `1 / 2` factor in `tvDist`. -/
example :
    tvDist (chainDist (fun x : Fin 2 => PMF.pure x) 0 1)
        (chainDist (fun x : Fin 2 => PMF.pure x) 1 1) = 1 := by
  have hstep : ∀ x : Fin 2,
      chainDist (fun y : Fin 2 => PMF.pure y) x 1 = PMF.pure x := by
    intro x
    show (PMF.pure x).bind (fun y : Fin 2 => PMF.pure y) = PMF.pure x
    rw [PMF.bind_pure]
  rw [hstep 0, hstep 1]
  simp [tvDist, MathlibExt.Probability.MarkovMixing.tvDist, Fin.sum_univ_two,
    PMF.pure_apply]
  norm_num

/-- On `Fin 2`, the collapsing kernel (every row the point mass at
`0`) brings the two chains together after one step. -/
example :
    tvDist (chainDist (fun _ : Fin 2 => PMF.pure 0) 0 1)
        (chainDist (fun _ : Fin 2 => PMF.pure 0) 1 1) = 0 := by
  have hstep : ∀ x : Fin 2,
      chainDist (fun _ : Fin 2 => PMF.pure 0) x 1 = PMF.pure 0 := by
    intro x
    show (PMF.pure x).bind (fun _ : Fin 2 => PMF.pure 0) = PMF.pure 0
    rw [PMF.pure_bind]
  rw [hstep 0, hstep 1]
  exact MathlibExt.Probability.MarkovMixing.tvDist_self _
