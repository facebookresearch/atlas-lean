/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaStrongPower

@[expose] public section

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
open scoped RealInnerProductSpace

/-! The hypothesis on `H` holds for the strong power, so the bounds apply to it. -/

/-- The strong power of `G` on words of length `k` (as in the repository's Shannon capacity
pages): distinct words are adjacent when each coordinate is equal or adjacent. -/
private def strongPowerTest {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm.symm x y := by
    rintro ⟨hxy, hcoord⟩
    exact ⟨hxy.symm, fun i => (hcoord i).imp Eq.symm SimpleGraph.Adj.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem strongPowerTest_hyp {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    ∀ x y, x ≠ y → ¬ (strongPowerTest G k).Adj x y → ∃ i, x i ≠ y i ∧ ¬ G.Adj (x i) (y i) := by
  intro x y hxy hadj
  by_contra h
  exact hadj ⟨hxy, fun i => by
    by_cases hi : x i = y i
    · exact Or.inl hi
    · by_cases ha : G.Adj (x i) (y i)
      · exact Or.inr ha
      · exact (h ⟨i, hi, ha⟩).elim⟩

example (G : SimpleGraph (Fin 5)) (k : ℕ) :
    ((strongPowerTest G k).indepNum : ℝ) ≤ lovaszTheta G ^ k :=
  indepNum_le_lovaszTheta_pow G (strongPowerTest_hyp G k)

example (G : SimpleGraph (Fin 5)) {θ : ℝ}
    (hθ : Filter.Tendsto
      (fun k : ℕ => ((strongPowerTest G (k + 1)).indepNum : ℝ) ^ (((k : ℝ) + 1)⁻¹))
      Filter.atTop (nhds θ)) :
    θ ≤ lovaszTheta G :=
  le_lovaszTheta_of_tendsto G (fun k => strongPowerTest G (k + 1))
    (fun k => strongPowerTest_hyp G (k + 1)) hθ

/-- Tensor products of the all-ones vector of `ℝ²` have squared norm `2^k`. -/
example (k : ℕ) :
    let v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1
    ⟪tensorVec (fun _ : Fin k => v), tensorVec (fun _ : Fin k => v)⟫ = 2 ^ k := by
  intro v
  have hv : ⟪v, v⟫ = 2 := by
    simp only [v, inner_add_left, inner_add_right, EuclideanSpace.inner_single_left,
      PiLp.single_apply]
    norm_num
  rw [inner_tensorVec, hv, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
