/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Sion

@[expose] public section

open Matrix Convexity

/-! # Von Neumann's minimax theorem for finite matrix games

For a payoff matrix `A : Matrix (Fin m) (Fin n) ℝ`, a mixed strategy of the
row player is a point `p` of `Convexity.StdSimplex ℝ (Fin m)` and a mixed
strategy of the column player is a point `q` of `Convexity.StdSimplex ℝ (Fin n)`.
The expected payoff is `p.weights ⬝ᵥ (A *ᵥ q.weights)`; the row player maximizes
and the column player minimizes. `matrixGame_minimax` states that the value of
the game exists:
maximizing first or minimizing first gives the same value, attained at a
saddle point (`matrixGame_exists_isSaddlePointOn`).

Both results specialize Mathlib's `Sion.exists_isSaddlePointOn`, whose
module docstring leaves this finite matrix-game case as a TODO. This file
covers roadmap package ML-16 of the Atlas TCS canon roadmap.

Source: J. von Neumann, "Zur Theorie der Gesellschaftsspiele",
Math. Annalen 100 (1928), 295--320; M. Sion, "On general minimax theorems",
Pacific J. Math. 8 (1958), 171--176.
-/

private theorem stdSimplex_nonempty_of_pos {k : ℕ} (hk : 0 < k) :
    (stdSimplex ℝ (Fin k)).Nonempty := by
  refine ⟨Pi.single ⟨0, hk⟩ 1, fun i => ?_, ?_⟩
  · by_cases h : i = ⟨0, hk⟩
    · subst h; simp
    · simp [h]
  · simp

/-- The payoff as a linear function of the column strategy. -/
private noncomputable def matrixGameRight {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun q := p ⬝ᵥ (A *ᵥ q)
  map_add' x y := by simp [mulVec_add, dotProduct_add]
  map_smul' c x := by simp [mulVec_smul, dotProduct_smul]

/-- The payoff as a linear function of the row strategy. -/
private noncomputable def matrixGameLeft {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun p := p ⬝ᵥ (A *ᵥ q)
  map_add' x y := by simp [add_dotProduct]
  map_smul' c x := by simp [smul_dotProduct]

private theorem matrixGame_continuous_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) : Continuous fun p : Fin m → ℝ => p ⬝ᵥ (A *ᵥ q) := by
  unfold dotProduct; fun_prop

private theorem matrixGame_continuous_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) : Continuous fun q : Fin n → ℝ => p ⬝ᵥ (A *ᵥ q) := by
  simp only [dotProduct, mulVec]; fun_prop

/-- A finite matrix game has a saddle point: mixed strategies `p` and `q`
such that `p` is a best response to `q` and `q` is a best response to `p`. -/
theorem matrixGame_exists_isSaddlePointOn {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (p : StdSimplex ℝ (Fin m)) (q : StdSimplex ℝ (Fin n)),
      (∀ p' : StdSimplex ℝ (Fin m),
        p'.weights ⬝ᵥ (A *ᵥ q.weights) ≤ p.weights ⬝ᵥ (A *ᵥ q.weights)) ∧
      ∀ q' : StdSimplex ℝ (Fin n),
        p.weights ⬝ᵥ (A *ᵥ q.weights) ≤ p.weights ⬝ᵥ (A *ᵥ q'.weights) := by
  obtain ⟨q, hq, p, hp, h⟩ := Sion.exists_isSaddlePointOn (X := stdSimplex ℝ (Fin n))
    (Y := stdSimplex ℝ (Fin m)) (f := fun q p => p ⬝ᵥ (A *ᵥ q))
    (stdSimplex_nonempty_of_pos hn) (convex_stdSimplex ℝ _) (isCompact_stdSimplex _ _)
    (fun p _ => (matrixGame_continuous_right A p).continuousOn.lowerSemicontinuousOn)
    (fun p _ => ((matrixGameRight A p).convexOn (convex_stdSimplex ℝ _)).quasiconvexOn)
    (convex_stdSimplex ℝ _) (stdSimplex_nonempty_of_pos hm) (isCompact_stdSimplex _ _)
    (fun q _ => (matrixGame_continuous_left A q).continuousOn.upperSemicontinuousOn)
    (fun q _ => ((matrixGameLeft A q).concaveOn (convex_stdSimplex ℝ _)).quasiconcaveOn)
  have hp_range : p ∈ Set.range (fun t : StdSimplex ℝ (Fin m) =>
      (t.weights : Fin m → ℝ)) := by
    rw [StdSimplex.range_toFun_comp_weights]
    exact ⟨Set.mem_iInter.mpr hp.1, hp.2⟩
  have hq_range : q ∈ Set.range (fun t : StdSimplex ℝ (Fin n) =>
      (t.weights : Fin n → ℝ)) := by
    rw [StdSimplex.range_toFun_comp_weights]
    exact ⟨Set.mem_iInter.mpr hq.1, hq.2⟩
  obtain ⟨p, rfl⟩ := hp_range
  obtain ⟨q, rfl⟩ := hq_range
  exact ⟨p, q,
    fun p' => h q.weights hq p'.weights
      ⟨p'.weights_nonneg, p'.total_of_fintype⟩,
    fun q' => h q'.weights ⟨q'.weights_nonneg, q'.total_of_fintype⟩ p.weights hp⟩

private theorem matrixGame_bddBelow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) :
    BddBelow (Set.range fun q : StdSimplex ℝ (Fin n) =>
      p ⬝ᵥ (A *ᵥ q.weights)) := by
  apply (isCompact_range ?_).bddBelow
  exact (matrixGame_continuous_right A p).comp
    (continuous_pi fun i => StdSimplex.continuous_weights_apply ℝ i)

private theorem matrixGame_bddAbove {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) :
    BddAbove (Set.range fun p : StdSimplex ℝ (Fin m) =>
      p.weights ⬝ᵥ (A *ᵥ q)) := by
  apply (isCompact_range ?_).bddAbove
  exact (matrixGame_continuous_left A q).comp
    (continuous_pi fun i => StdSimplex.continuous_weights_apply ℝ i)

/-- **Von Neumann's minimax theorem.** For a finite matrix game with at
least one row and one column, the row player's maximin value equals the
column player's minimax value. -/
theorem matrixGame_minimax {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (⨆ p : StdSimplex ℝ (Fin m), ⨅ q : StdSimplex ℝ (Fin n),
      p.weights ⬝ᵥ (A *ᵥ q.weights)) =
      ⨅ q : StdSimplex ℝ (Fin n), ⨆ p : StdSimplex ℝ (Fin m),
        p.weights ⬝ᵥ (A *ᵥ q.weights) := by
  obtain ⟨p₀, q₀, hp, hq⟩ := matrixGame_exists_isSaddlePointOn hm hn A
  have : Nonempty (StdSimplex ℝ (Fin m)) := ⟨p₀⟩
  have : Nonempty (StdSimplex ℝ (Fin n)) := ⟨q₀⟩
  have hinf (p : StdSimplex ℝ (Fin m)) :
      ⨅ q : StdSimplex ℝ (Fin n), p.weights ⬝ᵥ (A *ᵥ q.weights) ≤
        p₀.weights ⬝ᵥ (A *ᵥ q₀.weights) :=
    (ciInf_le (matrixGame_bddBelow A p.weights) q₀).trans (hp p)
  have hsup (q : StdSimplex ℝ (Fin n)) :
      p₀.weights ⬝ᵥ (A *ᵥ q₀.weights) ≤
        ⨆ p : StdSimplex ℝ (Fin m), p.weights ⬝ᵥ (A *ᵥ q.weights) :=
    (hq q).trans (le_ciSup (matrixGame_bddAbove A q.weights) p₀)
  refine le_antisymm ((ciSup_le hinf).trans (le_ciInf hsup)) ?_
  calc (⨅ q : StdSimplex ℝ (Fin n), ⨆ p : StdSimplex ℝ (Fin m),
          p.weights ⬝ᵥ (A *ᵥ q.weights))
      ≤ ⨆ p : StdSimplex ℝ (Fin m), p.weights ⬝ᵥ (A *ᵥ q₀.weights) :=
        ciInf_le ⟨_, Set.forall_mem_range.2 hsup⟩ q₀
    _ ≤ p₀.weights ⬝ᵥ (A *ᵥ q₀.weights) := ciSup_le hp
    _ ≤ ⨅ q : StdSimplex ℝ (Fin n), p₀.weights ⬝ᵥ (A *ᵥ q.weights) :=
        le_ciInf hq
    _ ≤ ⨆ p : StdSimplex ℝ (Fin m), ⨅ q : StdSimplex ℝ (Fin n),
          p.weights ⬝ᵥ (A *ᵥ q.weights) :=
        le_ciSup ⟨_, Set.forall_mem_range.2 hinf⟩ p₀
