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

open Matrix

/-! # Von Neumann's minimax theorem for finite matrix games

For a payoff matrix `A : Matrix (Fin m) (Fin n) ℝ`, a mixed strategy of the
row player is a point `p` of `stdSimplex ℝ (Fin m)` and a mixed strategy of
the column player is a point `q` of `stdSimplex ℝ (Fin n)`. The expected
payoff is `p ⬝ᵥ (A *ᵥ q)`; the row player maximizes and the column player
minimizes. `matrixGame_minimax` states that the value of the game exists:
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
    ∃ p ∈ stdSimplex ℝ (Fin m), ∃ q ∈ stdSimplex ℝ (Fin n),
      (∀ p' ∈ stdSimplex ℝ (Fin m), p' ⬝ᵥ (A *ᵥ q) ≤ p ⬝ᵥ (A *ᵥ q)) ∧
        ∀ q' ∈ stdSimplex ℝ (Fin n), p ⬝ᵥ (A *ᵥ q) ≤ p ⬝ᵥ (A *ᵥ q') := by
  obtain ⟨q, hq, p, hp, h⟩ := Sion.exists_isSaddlePointOn (X := stdSimplex ℝ (Fin n))
    (Y := stdSimplex ℝ (Fin m)) (f := fun q p => p ⬝ᵥ (A *ᵥ q))
    (stdSimplex_nonempty_of_pos hn) (convex_stdSimplex ℝ _) (isCompact_stdSimplex _ _)
    (fun p _ => (matrixGame_continuous_right A p).continuousOn.lowerSemicontinuousOn)
    (fun p _ => ((matrixGameRight A p).convexOn (convex_stdSimplex ℝ _)).quasiconvexOn)
    (convex_stdSimplex ℝ _) (stdSimplex_nonempty_of_pos hm) (isCompact_stdSimplex _ _)
    (fun q _ => (matrixGame_continuous_left A q).continuousOn.upperSemicontinuousOn)
    (fun q _ => ((matrixGameLeft A q).concaveOn (convex_stdSimplex ℝ _)).quasiconcaveOn)
  exact ⟨p, hp, q, hq, fun p' hp' => h q hq p' hp', fun q' hq' => h q' hq' p hp⟩

private theorem matrixGame_bddBelow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) :
    BddBelow (Set.range fun q : stdSimplex ℝ (Fin n) => p ⬝ᵥ (A *ᵥ (q : Fin n → ℝ))) := by
  have : CompactSpace (stdSimplex ℝ (Fin n)) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex _ _)
  exact (isCompact_range ((matrixGame_continuous_right A p).comp continuous_subtype_val)).bddBelow

private theorem matrixGame_bddAbove {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) :
    BddAbove (Set.range fun p : stdSimplex ℝ (Fin m) => (p : Fin m → ℝ) ⬝ᵥ (A *ᵥ q)) := by
  have : CompactSpace (stdSimplex ℝ (Fin m)) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex _ _)
  exact (isCompact_range ((matrixGame_continuous_left A q).comp continuous_subtype_val)).bddAbove

/-- **Von Neumann's minimax theorem.** For a finite matrix game with at
least one row and one column, the row player's maximin value equals the
column player's minimax value. -/
theorem matrixGame_minimax {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (⨆ p : stdSimplex ℝ (Fin m), ⨅ q : stdSimplex ℝ (Fin n),
      (p : Fin m → ℝ) ⬝ᵥ (A *ᵥ (q : Fin n → ℝ))) =
      ⨅ q : stdSimplex ℝ (Fin n), ⨆ p : stdSimplex ℝ (Fin m),
        (p : Fin m → ℝ) ⬝ᵥ (A *ᵥ (q : Fin n → ℝ)) := by
  obtain ⟨p₀, hp₀, q₀, hq₀, hp, hq⟩ := matrixGame_exists_isSaddlePointOn hm hn A
  have : Nonempty (stdSimplex ℝ (Fin m)) := (stdSimplex_nonempty_of_pos hm).to_subtype
  have : Nonempty (stdSimplex ℝ (Fin n)) := (stdSimplex_nonempty_of_pos hn).to_subtype
  have hinf (p : stdSimplex ℝ (Fin m)) :
      ⨅ q : stdSimplex ℝ (Fin n), (p : Fin m → ℝ) ⬝ᵥ (A *ᵥ (q : Fin n → ℝ)) ≤
        p₀ ⬝ᵥ (A *ᵥ q₀) :=
    (ciInf_le (matrixGame_bddBelow A p) ⟨q₀, hq₀⟩).trans (hp p p.2)
  have hsup (q : stdSimplex ℝ (Fin n)) :
      p₀ ⬝ᵥ (A *ᵥ q₀) ≤
        ⨆ p : stdSimplex ℝ (Fin m), (p : Fin m → ℝ) ⬝ᵥ (A *ᵥ (q : Fin n → ℝ)) :=
    (hq q q.2).trans (le_ciSup (matrixGame_bddAbove A q) ⟨p₀, hp₀⟩)
  refine le_antisymm ((ciSup_le hinf).trans (le_ciInf hsup)) ?_
  calc (⨅ q : stdSimplex ℝ (Fin n), ⨆ p : stdSimplex ℝ (Fin m),
          (p : Fin m → ℝ) ⬝ᵥ (A *ᵥ (q : Fin n → ℝ)))
      ≤ ⨆ p : stdSimplex ℝ (Fin m), (p : Fin m → ℝ) ⬝ᵥ (A *ᵥ q₀) :=
        ciInf_le ⟨_, Set.forall_mem_range.2 hsup⟩ ⟨q₀, hq₀⟩
    _ ≤ p₀ ⬝ᵥ (A *ᵥ q₀) := ciSup_le fun p => hp p p.2
    _ ≤ ⨅ q : stdSimplex ℝ (Fin n), p₀ ⬝ᵥ (A *ᵥ (q : Fin n → ℝ)) :=
        le_ciInf fun q => hq q q.2
    _ ≤ ⨆ p : stdSimplex ℝ (Fin m), ⨅ q : stdSimplex ℝ (Fin n),
          (p : Fin m → ℝ) ⬝ᵥ (A *ᵥ (q : Fin n → ℝ)) :=
        le_ciSup ⟨_, Set.forall_mem_range.2 hinf⟩ ⟨p₀, hp₀⟩
