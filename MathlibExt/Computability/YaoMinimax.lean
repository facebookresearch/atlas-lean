/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ZeroSumMinimax

/-!
# Yao's minimax principle

Let a computational problem have finitely many inputs and finitely many deterministic
algorithms, with `C a x` the cost of algorithm `a` on input `x`. A randomized algorithm is a
probability distribution `R` on algorithms, and its cost on input `x` is the expected cost
`∑ a, R a * C a x`. For a distribution `D` on inputs, the cost of a deterministic algorithm `a`
is `∑ x, D x * C a x`.

Yao's minimax principle (A. C. Yao, "Probabilistic computations: toward a unified measure of
complexity", FOCS 1977; in the form of S. Arora and B. Barak, *Computational Complexity: A
Modern Approach*, web draft of 2007-01-08, Section 11.6, "Yao's MinMax Lemma") says that the
randomized complexity `min_R max_x cost(R, x)` equals the distributional complexity
`max_D min_a cost(a, D)`.

* `exists_le_expectedCost`: the elementary half, used for lower bounds: if every deterministic
  algorithm has expected cost at least `c` on inputs drawn from `D`, then every randomized
  algorithm has expected cost at least `c` on some input;
* `yao_minimax`: the equality, from von Neumann's minimax theorem for matrix games
  (`MathlibExt.GameTheory.ZeroSumMinimax`'s `matrixGame_minimax`).

## Relation to `MathlibExt.GameTheory.Yao`

That module proves the two averaging steps of the easy direction, over `ℚ`
(`MathlibExt.GameTheory.Yao.yao_exists_det`, `MathlibExt.GameTheory.Yao.yao_exists_input`; the
latter is the averaging step behind `exists_le_expectedCost`). It has no counterpart of
`yao_minimax`.
-/

@[expose] public section

open Matrix Convexity

namespace MathlibExt.Computability.YaoMinimax

/-- **Yao's principle, lower-bound form.** Let `C a x` be the cost of deterministic algorithm
`a` on input `x`, over finitely many algorithms and inputs. If a distribution `D` on inputs makes
every deterministic algorithm cost at least `c` in expectation, then every randomized algorithm
`R` (a distribution on algorithms) has expected cost at least `c` on some input (S. Arora and
B. Barak, *Computational Complexity*, web draft of 2007-01-08, Section 11.6: "one proves that
every deterministic algorithm incurs high cost, say `C`, on this distribution. By Yao's Lemma, it
follows that the randomized complexity then is at least `C`"). -/
theorem exists_le_expectedCost {A I : Type*} [Fintype A] [Fintype I] (C : A → I → ℝ)
    (D : StdSimplex ℝ I) (R : StdSimplex ℝ A) {c : ℝ}
    (hD : ∀ a, c ≤ ∑ x, D.weights x * C a x) :
    ∃ x, c ≤ ∑ a, R.weights a * C a x := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hswap : ∑ x, D.weights x * ∑ a, R.weights a * C a x =
      ∑ a, R.weights a * ∑ x, D.weights x * C a x := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  have hge : c ≤ ∑ a, R.weights a * ∑ x, D.weights x * C a x := by
    calc c = ∑ a, R.weights a * c := by rw [← Finset.sum_mul, R.total_of_fintype, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hD a) (R.weights_nonneg a)
  obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < D.weights x := by
    by_contra hpos
    simp only [not_exists, not_lt] at hpos
    have : ∑ x, D.weights x ≤ 0 := Finset.sum_nonpos fun x _ => hpos x
    rw [D.total_of_fintype] at this
    norm_num at this
  have hlt : ∑ x, D.weights x * ∑ a, R.weights a * C a x < ∑ x, D.weights x * c :=
    Finset.sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_left (h x).le (D.weights_nonneg x))
      ⟨x₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (h x₀) hx₀⟩
  rw [← Finset.sum_mul, D.total_of_fintype, one_mul, hswap] at hlt
  linarith

private theorem single_dotProduct_eq {k : ℕ} (j : Fin k) (v : Fin k → ℝ) :
    ((StdSimplex.single j : StdSimplex ℝ (Fin k)).weights : Fin k → ℝ) ⬝ᵥ v = v j := by
  simp [StdSimplex.weights_single, Finsupp.single_eq_pi_single, single_dotProduct]

private theorem iInf_le_dotProduct {k : ℕ} [Nonempty (Fin k)] (v : Fin k → ℝ)
    (q : StdSimplex ℝ (Fin k)) : ⨅ j, v j ≤ (q.weights : Fin k → ℝ) ⬝ᵥ v := by
  calc ⨅ j, v j = ∑ j, q.weights j * ⨅ j, v j := by
        rw [← Finset.sum_mul, q.total_of_fintype, one_mul]
    _ ≤ ∑ j, q.weights j * v j := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (ciInf_le (Set.finite_range v).bddBelow j) (q.weights_nonneg j)
    _ = (q.weights : Fin k → ℝ) ⬝ᵥ v := rfl

private theorem dotProduct_le_iSup {k : ℕ} [Nonempty (Fin k)] (v : Fin k → ℝ)
    (q : StdSimplex ℝ (Fin k)) : (q.weights : Fin k → ℝ) ⬝ᵥ v ≤ ⨆ j, v j := by
  calc (q.weights : Fin k → ℝ) ⬝ᵥ v = ∑ j, q.weights j * v j := rfl
    _ ≤ ∑ j, q.weights j * ⨆ j, v j := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (le_ciSup (Set.finite_range v).bddAbove j) (q.weights_nonneg j)
    _ = ⨆ j, v j := by rw [← Finset.sum_mul, q.total_of_fintype, one_mul]

/-- Minimizing a linear function over the standard simplex is minimizing over its vertices. -/
private theorem iInf_stdSimplex_dotProduct {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) :
    ⨅ q : StdSimplex ℝ (Fin k), (q.weights : Fin k → ℝ) ⬝ᵥ v = ⨅ j, v j := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nonempty (StdSimplex ℝ (Fin k)) := ⟨StdSimplex.single ⟨0, hk⟩⟩
  refine le_antisymm (le_ciInf fun j => ?_) (le_ciInf (iInf_le_dotProduct v))
  refine (ciInf_le ⟨⨅ j, v j, ?_⟩ (StdSimplex.single j)).trans (single_dotProduct_eq j v).le
  rintro _ ⟨q, rfl⟩
  exact iInf_le_dotProduct v q

/-- Maximizing a linear function over the standard simplex is maximizing over its vertices. -/
private theorem iSup_stdSimplex_dotProduct {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) :
    ⨆ q : StdSimplex ℝ (Fin k), (q.weights : Fin k → ℝ) ⬝ᵥ v = ⨆ j, v j := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nonempty (StdSimplex ℝ (Fin k)) := ⟨StdSimplex.single ⟨0, hk⟩⟩
  refine le_antisymm (ciSup_le (dotProduct_le_iSup v)) (ciSup_le fun j => ?_)
  refine (single_dotProduct_eq j v).ge.trans
    (le_ciSup (f := fun q : StdSimplex ℝ (Fin k) => (q.weights : Fin k → ℝ) ⬝ᵥ v)
      ⟨⨆ j, v j, ?_⟩ (StdSimplex.single j))
  rintro _ ⟨q, rfl⟩
  exact dotProduct_le_iSup v q

/-- **Yao's minimax principle.** Let `C : Matrix (Fin m) (Fin n) ℝ` give the cost `C a x` of
each of `m ≥ 1` deterministic algorithms on each of `n ≥ 1` inputs. The randomized complexity,
the least over distributions `R` on algorithms of the worst-case expected cost
`max_x (R ᵥ* C) x = max_x ∑ a, R a * C a x`, equals the distributional complexity, the
greatest over distributions `D` on inputs of the cost `min_a (C *ᵥ D) a = min_a ∑ x, C a x * D x`
of the best deterministic algorithm against `D` (S. Arora and B. Barak, *Computational
Complexity*, web draft of 2007-01-08, Section 11.6, equations (10) and (11); A. Rao and
A. Yehudayoff, *Communication Complexity*, early draft, Theorem 3.3 for the communication
version). The proof is von Neumann's minimax theorem for the matrix game in which the input
player maximizes and the algorithm player minimizes. -/
theorem yao_minimax {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (C : Matrix (Fin m) (Fin n) ℝ) :
    (⨅ R : StdSimplex ℝ (Fin m), ⨆ x : Fin n, ((R.weights : Fin m → ℝ) ᵥ* C) x) =
      ⨆ D : StdSimplex ℝ (Fin n), ⨅ a : Fin m, (C *ᵥ (D.weights : Fin n → ℝ)) a := by
  have key := matrixGame_minimax hn hm Cᵀ
  have h₁ (D : StdSimplex ℝ (Fin n)) :
      ⨅ R : StdSimplex ℝ (Fin m), (D.weights : Fin n → ℝ) ⬝ᵥ (Cᵀ *ᵥ (R.weights : Fin m → ℝ)) =
        ⨅ a, (C *ᵥ (D.weights : Fin n → ℝ)) a := by
    have hR (R : StdSimplex ℝ (Fin m)) :
        (D.weights : Fin n → ℝ) ⬝ᵥ (Cᵀ *ᵥ (R.weights : Fin m → ℝ)) =
          (R.weights : Fin m → ℝ) ⬝ᵥ (C *ᵥ (D.weights : Fin n → ℝ)) := by
      rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
    simp_rw [hR]
    exact iInf_stdSimplex_dotProduct hm _
  have h₂ (R : StdSimplex ℝ (Fin m)) :
      ⨆ D : StdSimplex ℝ (Fin n), (D.weights : Fin n → ℝ) ⬝ᵥ (Cᵀ *ᵥ (R.weights : Fin m → ℝ)) =
        ⨆ x, ((R.weights : Fin m → ℝ) ᵥ* C) x := by
    simp_rw [mulVec_transpose]
    exact iSup_stdSimplex_dotProduct hn _
  simp_rw [← h₁, ← h₂]
  exact key.symm

end MathlibExt.Computability.YaoMinimax
