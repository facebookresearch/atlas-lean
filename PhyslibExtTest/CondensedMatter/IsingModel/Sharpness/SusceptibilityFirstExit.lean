/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.SusceptibilityFirstExit

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SusceptibilityFirstExit`

* `susceptibility_self_consistent` on an explicit instance: one site, `Λ = S = {0}`, no boundary
  pairs, `q = 1`, giving `χ = 1 ≤ |S| + 0 · χ`;
* `firstExit_target_bound` applied under the first-exit inclusion `hincl` (the BK step of
  `susceptibility_self_consistent_bk`).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.SusceptibilityFirstExit

open _root_.StatMech _root_.StatMech.Sharpness

-- The algebraic step on a one-site instance.
example : (1 : ℝ) ≤ ({0} : Finset (Fin 1)).card + 0 * 1 :=
  susceptibility_self_consistent {0} {0} subset_rfl (∅ : Finset (Fin 1)) id 0 le_rfl
    (fun _ => 0) (fun _ => 1) (fun _ _ => 0) (fun _ _ => le_rfl) (fun _ => le_rfl)
    (fun _ _ => le_rfl) (fun x hx hxS => absurd hx hxS) 1 (by simp)
    (fun _ => by simp) 0 (by simp)

-- The BK bound from a first-exit decomposition.
example {V ι : Type*} [Fintype V] [DecidableEq V] (p : NNReal) (hp : p ≤ 1) (G : SimpleGraph V)
    (Lam S : Set V) (u x : V) (s : Finset ι) (bp : ι → V × V)
    (hincl : connEvent G Lam u {x} ⊆ ⋃ i ∈ s, connEvent G S u {(bp i).1} □
      edgeOpenEvent (bp i).1 (bp i).2 □ connEvent G Lam (bp i).2 {x})
    (hedge : ∀ i ∈ s, (bernoulliProductMeasure p hp).real (edgeOpenEvent (bp i).1 (bp i).2) ≤ p) :
    (bernoulliProductMeasure p hp).real (connEvent G Lam u {x}) ≤
      ∑ i ∈ s, p * (bernoulliProductMeasure p hp).real (connEvent G S u {(bp i).1}) *
        (bernoulliProductMeasure p hp).real (connEvent G Lam (bp i).2 {x}) :=
  firstExit_target_bound hp G Lam S u x s bp hincl hedge

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.SusceptibilityFirstExit
