/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.LinearProgrammingCertificate
public import Mathlib.Data.Rat.Cast.Order

/-!
# Rational LP gap checker

A computable exact-rational checker for primal/dual epsilon-gap linear
programming certificates, with transfer to the same LP over the reals.
Acceptance implies cast primal feasibility, cast dual feasibility, a real
objective gap in `[0, ε]`, and a one-sided primal bound for every real
feasible competitor; acceptance at zero gap gives primal and dual
optimality. This is an executable representation bridge reusing real weak
duality and the real equal-objective certificate corollary; it is not a
solver, a new duality proof, or a complexity claim.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.RationalLPCertificate

/-- Computable exact-rational LP epsilon-gap checker.

Given dimensions `m` and `n`, rational matrix `A`, right-hand side `b`,
objective `c`, primal candidate `x`, dual candidate `y`, and gap budget
`ε`, returns `true` exactly when all finite rational checks hold:
`x ≥ 0`, `A *ᵥ x ≤ b`, `y ≥ 0`, `c ≤ Aᵀ *ᵥ y`, and
`0 ≤ b ⬝ᵥ y - c ⬝ᵥ x ≤ ε`. Uses only finite rational comparisons and
sums. -/
def checksLPGap (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) (x : Fin n → ℚ) (y : Fin m → ℚ) (ε : ℚ) : Bool :=
  decide (∀ (i : Fin n), 0 ≤ x i) &&
  decide (∀ (j : Fin m), (Matrix.mulVec A x) j ≤ b j) &&
  decide (∀ (j : Fin m), 0 ≤ y j) &&
  decide (∀ (i : Fin n), c i ≤ (Matrix.mulVec (Matrix.transpose A) y) i) &&
  decide (0 ≤ dotProduct b y - dotProduct c x) &&
  decide (dotProduct b y - dotProduct c x ≤ ε)

/-- Entrywise cast commutes with matrix-vector products. -/
private theorem cast_mulVec_apply (p q : ℕ) (M : Matrix (Fin p) (Fin q) ℚ)
    (v : Fin q → ℚ) (k : Fin p) :
    (Matrix.mulVec (Matrix.map M (fun (r : ℚ) => (r : ℝ)))
        (fun (i : Fin q) => (v i : ℝ))) k
      = ((Matrix.mulVec M v) k : ℝ) :=
  (RingHom.map_mulVec (Rat.castHom ℝ) M v k).symm

/-- Entrywise cast commutes with dot products. -/
private theorem cast_dotProduct (p : ℕ) (u v : Fin p → ℚ) :
    dotProduct (fun (i : Fin p) => (u i : ℝ))
        (fun (i : Fin p) => (v i : ℝ))
      = ((dotProduct u v : ℚ) : ℝ) :=
  (RingHom.map_dotProduct (Rat.castHom ℝ) u v).symm

/-- Characterization of `checksLPGap`: acceptance is equivalent to the
conjunction of the exact rational checks. -/
theorem checksLPGap_eq_true_iff (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) (x : Fin n → ℚ) (y : Fin m → ℚ)
    (ε : ℚ) :
    checksLPGap m n A b c x y ε = true ↔
      (∀ i, 0 ≤ x i) ∧
      (∀ j, (Matrix.mulVec A x) j ≤ b j) ∧
      (∀ j, 0 ≤ y j) ∧
      (∀ i, c i ≤ (Matrix.mulVec (Matrix.transpose A) y) i) ∧
      0 ≤ dotProduct b y - dotProduct c x ∧
      dotProduct b y - dotProduct c x ≤ ε := by
  simp only [checksLPGap, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Soundness over the reals: acceptance transfers the rational certificate
entrywise to the same LP over `ℝ`, giving cast primal feasibility, cast
dual feasibility, a nonnegative real gap bounded by `ε`, and the one-sided
primal objective bound for every real feasible competitor. -/
theorem real_feasible_and_gap_le_of_checks (m n : ℕ)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℚ)
    (x : Fin n → ℚ) (y : Fin m → ℚ) (ε : ℚ)
    (h : checksLPGap m n A b c x y ε = true) :
    ((∀ i, 0 ≤ (x i : ℝ)) ∧
      (∀ j,
        (Matrix.mulVec (Matrix.map A (fun (q : ℚ) => (q : ℝ)))
            (fun (i : Fin n) => (x i : ℝ))) j ≤
          (b j : ℝ))) ∧
    ((∀ j, 0 ≤ (y j : ℝ)) ∧
      (∀ i,
        (c i : ℝ) ≤
          (Matrix.mulVec
              (Matrix.transpose (Matrix.map A (fun (q : ℚ) => (q : ℝ))))
              (fun (j : Fin m) => (y j : ℝ))) i)) ∧
    (0 ≤
        dotProduct (fun (j : Fin m) => (b j : ℝ))
            (fun (j : Fin m) => (y j : ℝ)) -
          dotProduct (fun (i : Fin n) => (c i : ℝ))
            (fun (i : Fin n) => (x i : ℝ)) ∧
      dotProduct (fun (j : Fin m) => (b j : ℝ))
          (fun (j : Fin m) => (y j : ℝ)) -
          dotProduct (fun (i : Fin n) => (c i : ℝ))
            (fun (i : Fin n) => (x i : ℝ)) ≤
        (ε : ℝ)) ∧
    (∀ (z : Fin n → ℝ),
      (∀ i, 0 ≤ z i) →
        (∀ j,
          (Matrix.mulVec (Matrix.map A (fun (q : ℚ) => (q : ℝ))) z) j ≤
            (b j : ℝ)) →
          dotProduct (fun (i : Fin n) => (c i : ℝ)) z ≤
            dotProduct (fun (i : Fin n) => (c i : ℝ))
                (fun (i : Fin n) => (x i : ℝ)) +
              (ε : ℝ)) := by
  rw [checksLPGap_eq_true_iff] at h
  obtain ⟨hx0, hAx, hy0, hAty, hgap0, hgapε⟩ := h
  have hx0R : ∀ i, 0 ≤ (x i : ℝ) := fun i => Rat.cast_nonneg.mpr (hx0 i)
  have hy0R : ∀ j, 0 ≤ (y j : ℝ) := fun j => Rat.cast_nonneg.mpr (hy0 j)
  have hAxR : ∀ j,
      (Matrix.mulVec (Matrix.map A (fun (q : ℚ) => (q : ℝ)))
          (fun (i : Fin n) => (x i : ℝ))) j ≤ (b j : ℝ) := by
    intro j
    rw [cast_mulVec_apply]
    exact Rat.cast_le.mpr (hAx j)
  have hAtyR : ∀ i,
      (c i : ℝ) ≤
        (Matrix.mulVec
            (Matrix.transpose (Matrix.map A (fun (q : ℚ) => (q : ℝ))))
            (fun (j : Fin m) => (y j : ℝ))) i := by
    intro i
    have htrans : Matrix.transpose (Matrix.map A (fun (q : ℚ) => (q : ℝ)))
        = Matrix.map (Matrix.transpose A) (fun (q : ℚ) => (q : ℝ)) :=
      Matrix.transpose_map.symm
    rw [htrans, cast_mulVec_apply]
    exact Rat.cast_le.mpr (hAty i)
  have hdotB : dotProduct (fun (j : Fin m) => (b j : ℝ))
      (fun (j : Fin m) => (y j : ℝ)) = ((dotProduct b y : ℚ) : ℝ) :=
    cast_dotProduct m b y
  have hdotC : dotProduct (fun (i : Fin n) => (c i : ℝ))
      (fun (i : Fin n) => (x i : ℝ)) = ((dotProduct c x : ℚ) : ℝ) :=
    cast_dotProduct n c x
  have hgap0R : 0 ≤
      dotProduct (fun (j : Fin m) => (b j : ℝ))
          (fun (j : Fin m) => (y j : ℝ)) -
        dotProduct (fun (i : Fin n) => (c i : ℝ))
          (fun (i : Fin n) => (x i : ℝ)) := by
    rw [hdotB, hdotC, ← Rat.cast_sub]
    exact Rat.cast_nonneg.mpr hgap0
  have hgapεR :
      dotProduct (fun (j : Fin m) => (b j : ℝ))
          (fun (j : Fin m) => (y j : ℝ)) -
        dotProduct (fun (i : Fin n) => (c i : ℝ))
          (fun (i : Fin n) => (x i : ℝ)) ≤ (ε : ℝ) := by
    rw [hdotB, hdotC, ← Rat.cast_sub]
    exact Rat.cast_le.mpr hgapε
  have hbound : ∀ (z : Fin n → ℝ),
      (∀ i, 0 ≤ z i) →
        (∀ j,
          (Matrix.mulVec (Matrix.map A (fun (q : ℚ) => (q : ℝ))) z) j ≤
            (b j : ℝ)) →
          dotProduct (fun (i : Fin n) => (c i : ℝ)) z ≤
            dotProduct (fun (i : Fin n) => (c i : ℝ))
                (fun (i : Fin n) => (x i : ℝ)) +
              (ε : ℝ) := by
    intro z hz0 hAz
    have hwd :=
      MathlibExt.Analysis.Convex.LPWeakDuality.weak_linear_programming_duality
        (Matrix.map A (fun (q : ℚ) => (q : ℝ)))
        (fun (j : Fin m) => (b j : ℝ)) (fun (i : Fin n) => (c i : ℝ))
        hz0 hAz hy0R hAtyR
    have hle :
        dotProduct (fun (j : Fin m) => (b j : ℝ))
            (fun (j : Fin m) => (y j : ℝ)) ≤
          dotProduct (fun (i : Fin n) => (c i : ℝ))
              (fun (i : Fin n) => (x i : ℝ)) + (ε : ℝ) := by
      calc dotProduct (fun (j : Fin m) => (b j : ℝ))
            (fun (j : Fin m) => (y j : ℝ))
          ≤ (ε : ℝ) + dotProduct (fun (i : Fin n) => (c i : ℝ))
              (fun (i : Fin n) => (x i : ℝ)) :=
            sub_le_iff_le_add.mp hgapεR
        _ = dotProduct (fun (i : Fin n) => (c i : ℝ))
              (fun (i : Fin n) => (x i : ℝ)) + (ε : ℝ) :=
            add_comm _ _
    exact hwd.trans hle
  exact ⟨⟨hx0R, hAxR⟩, ⟨hy0R, hAtyR⟩, ⟨hgap0R, hgapεR⟩, hbound⟩

/-- Zero-gap optimality: acceptance at `ε = 0` gives cast primal
feasibility, cast dual feasibility, universal primal optimality, and
universal dual optimality over the reals. -/
theorem optimal_of_checks_zero (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) (x : Fin n → ℚ) (y : Fin m → ℚ)
    (h : checksLPGap m n A b c x y (0 : ℚ) = true) :
    ((∀ i, 0 ≤ (x i : ℝ)) ∧
      (∀ j,
        (Matrix.mulVec (Matrix.map A (fun (q : ℚ) => (q : ℝ)))
            (fun (i : Fin n) => (x i : ℝ))) j ≤
          (b j : ℝ))) ∧
    ((∀ j, 0 ≤ (y j : ℝ)) ∧
      (∀ i,
        (c i : ℝ) ≤
          (Matrix.mulVec
              (Matrix.transpose (Matrix.map A (fun (q : ℚ) => (q : ℝ))))
              (fun (j : Fin m) => (y j : ℝ))) i)) ∧
    (∀ (x' : Fin n → ℝ),
      (∀ i, 0 ≤ x' i) →
        (∀ j,
          (Matrix.mulVec (Matrix.map A (fun (q : ℚ) => (q : ℝ))) x') j ≤
            (b j : ℝ)) →
          dotProduct (fun (i : Fin n) => (c i : ℝ)) x' ≤
            dotProduct (fun (i : Fin n) => (c i : ℝ))
              (fun (i : Fin n) => (x i : ℝ))) ∧
    (∀ (y' : Fin m → ℝ),
      (∀ j, 0 ≤ y' j) →
        (∀ i,
          (c i : ℝ) ≤
            (Matrix.mulVec
                (Matrix.transpose (Matrix.map A (fun (q : ℚ) => (q : ℝ))))
                y') i) →
          dotProduct (fun (j : Fin m) => (b j : ℝ))
              (fun (j : Fin m) => (y j : ℝ)) ≤
            dotProduct (fun (j : Fin m) => (b j : ℝ)) y') := by
  have h2 := real_feasible_and_gap_le_of_checks m n A b c x y 0 h
  obtain ⟨hPR, hDR, hgap, -⟩ := h2
  obtain ⟨hPR0, hPRAx⟩ := hPR
  obtain ⟨hDR0, hDRAty⟩ := hDR
  obtain ⟨hgap0, hgaple⟩ := hgap
  rw [Rat.cast_zero] at hgaple
  have heq : dotProduct (fun (i : Fin n) => (c i : ℝ))
        (fun (i : Fin n) => (x i : ℝ)) =
      dotProduct (fun (j : Fin m) => (b j : ℝ))
        (fun (j : Fin m) => (y j : ℝ)) := by
    have hzero :
        dotProduct (fun (j : Fin m) => (b j : ℝ))
            (fun (j : Fin m) => (y j : ℝ)) -
          dotProduct (fun (i : Fin n) => (c i : ℝ))
            (fun (i : Fin n) => (x i : ℝ)) = 0 :=
      le_antisymm hgaple hgap0
    exact (sub_eq_zero.mp hzero).symm
  have hopt :=
    MathlibExt.Analysis.Convex.LPCertificate.feasible_pair_equal_objectives_optimal
      (Matrix.map A (fun (q : ℚ) => (q : ℝ)))
      (fun (j : Fin m) => (b j : ℝ)) (fun (i : Fin n) => (c i : ℝ))
      hPR0 hPRAx hDR0 hDRAty heq
  exact ⟨⟨hPR0, hPRAx⟩, ⟨hDR0, hDRAty⟩, hopt.1, hopt.2⟩

end MathlibExt.Analysis.Convex.RationalLPCertificate
