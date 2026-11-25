/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.SingleLinkage

@[expose] public section

open MathlibExt.Topology.TDA Relation

/-- `0` and `2` are `1`-equivalent on the line through the chain `0, 1, 2`, although
`dist 0 2 = 2`: single linkage chains through intermediate points. -/
example : SLEquiv (dist : ℝ → ℝ → ℝ) 1 0 2 :=
  EqvGen.trans _ 1 _ (EqvGen.rel _ _ (by norm_num [Real.dist_eq]))
    (EqvGen.rel _ _ (by norm_num [Real.dist_eq]))

example : slDist (dist : ℝ → ℝ → ℝ) 0 2 ≤ 1 :=
  slDist_le_of_slEquiv zero_le_one
    (EqvGen.trans _ 1 _ (EqvGen.rel _ _ (by norm_num [Real.dist_eq]))
      (EqvGen.rel _ _ (by norm_num [Real.dist_eq])))

/-- The hypotheses of the maximality statement are satisfiable (by the zero function). -/
example (d : Fin 3 → Fin 3 → ℝ) (hd : ∀ x y, 0 ≤ d x y) (x y : Fin 3) :
    (0 : ℝ) ≤ slDist d x y :=
  le_slDist (u := fun _ _ => 0) hd (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => by simp) x y

/-- Stability: perturbing a dissimilarity by at most `η` moves `u*` by at most `η`. -/
example (d : Fin 3 → Fin 3 → ℝ) (η : ℝ) (hη : 0 ≤ η) (x y : Fin 3) :
    |slDist d x y - slDist (fun a b => d a b + η) x y| ≤ η :=
  abs_slDist_sub_le (fun a b => by simp [abs_of_nonneg hη]) x y

/-- On a finite set the dendrogram is read off `u*`. -/
example (d : Fin 3 → Fin 3 → ℝ) (x y : Fin 3) :
    SLEquiv d (slDist d x y) x y :=
  (slEquiv_iff_slDist_le (slDist_nonneg d x y)).2 le_rfl

example {M : Type} [PseudoMetricSpace M] (x y : M) (r : ℝ) :
    SLEquiv dist r x y ↔ (ripsGraph r).Reachable x y :=
  slEquiv_dist_iff_reachable
