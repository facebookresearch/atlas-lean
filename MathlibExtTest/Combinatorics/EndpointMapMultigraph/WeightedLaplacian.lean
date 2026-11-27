/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian

@[expose] public section

namespace EndpointMapMultigraphWeightedLaplacianTest

open EndpointMapMultigraph Matrix

/-! ### One edge `0 → 1` of weight `3` -/

/-- The quadratic form of one weighted edge is `3 (x₀ - x₁)²`. -/
example (x : Fin 2 → ℝ) :
    x ⬝ᵥ (laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) *ᵥ x) =
      3 * (x 0 - x 1) ^ 2 := by
  rw [dotProduct_mulVec_laplacian]
  simp

/-- Its Laplacian is positive semidefinite. -/
example : (laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => (3 : ℝ))).PosSemidef :=
  posSemidef_laplacian _ _ fun _ => by norm_num

/-- The cut of `{0}` carries the whole weight `3`. -/
example :
    indicator ({0} : Finset (Fin 2)) ⬝ᵥ
        (laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) *ᵥ
          indicator ({0} : Finset (Fin 2))) = 3 := by
  rw [dotProduct_mulVec_laplacian]
  simp [indicator]

/-- Doubling the weight raises the Laplacian in the Loewner order. -/
example : (laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => (6 : ℝ)) -
    laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3)).PosSemidef :=
  posSemidef_laplacian_sub_of_le _ _ fun _ => by norm_num

/-- The kernel test: a vector is killed iff it is constant on components. -/
example (x : Fin 2 → ℝ)
    (h : laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) *ᵥ x = 0) :
    x 0 = x 1 :=
  (laplacian_mulVec_eq_zero_iff _ _ (fun _ => by norm_num) (fun _ => by decide) x).1 h 0 1
    (underlyingGraph_adj_of_ne (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (e := ())
      (by decide)).reachable

/-- The easy Cheeger bound with `λ = 0` holds for every set. -/
example (S : Finset (Fin 2)) :
    (0 : ℝ) * S.card * (Finset.univ \ S).card ≤
      Fintype.card (Fin 2) *
        ∑ e ∈ cut (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) S, (fun _ => (3 : ℝ)) e :=
  mul_card_mul_card_compl_le_of_forall _ _ _ (fun x _ => by
    rw [zero_mul, dotProduct_mulVec_laplacian]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (by norm_num) (sq_nonneg _)) S

end EndpointMapMultigraphWeightedLaplacianTest
