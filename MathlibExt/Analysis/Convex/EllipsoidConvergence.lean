/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.EllipsoidVolume

/-!
# Convergence of the ellipsoid method

A run of the central-cut ellipsoid method keeps a set `P` inside the current ellipsoid while the
volume shrinks by a factor `exp(-1 / (2 (n + 1)))` per step. Hence, if
`exp(-N / (2 (n + 1))) vol E_0 ≤ vol P`, one of the first `N + 1` centres lies in `P`. The run is
given abstractly: the separation oracle is any choice of valid inequalities through the centres.

Source: M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial
Optimization, Handout 19 (4 May 2009), the algorithm, Lemma 7.1, Claim 7.2 and the remark after it.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.EllipsoidMethod

open Matrix MeasureTheory

variable {n : ℕ}

/-- **Ellipsoids have positive volume.** For positive definite `A`, `vol E(a, A) ≠ 0`. -/
theorem volume_ellipsoid_ne_zero {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (a : Fin n → ℝ) :
    volume (ellipsoid a A) ≠ 0 := by
  rw [volume_ellipsoid hA]
  exact mul_ne_zero (by simpa using hA.det_pos) volume_unitEllipsoid_pos.ne'

/-- **Ellipsoids have finite volume.** For positive definite `A`, `vol E(a, A) ≠ ∞`. -/
theorem volume_ellipsoid_ne_top {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (a : Fin n → ℝ) :
    volume (ellipsoid a A) ≠ ⊤ := by
  rw [volume_ellipsoid hA]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top volume_unitEllipsoid_lt_top.ne

/-- **Invariant of the ellipsoid method.** Consider a run of the central-cut ellipsoid method:
ellipsoids `E_k = E(a_k, A_k)` with `A_0` positive definite and `P ⊆ E_0`, where, whenever the
centre `a_k` is not in `P`, a vector `c_k ≠ 0` gives a valid inequality `cₖᵀ x ≤ cₖᵀ aₖ` on `P` and
`E_(k+1)` is the central-cut ellipsoid. If the first `k` centres miss `P`, then `A_k` is positive
definite, `P ⊆ E_k` and `vol E_k ≤ exp(-k / (2 (n + 1))) vol E_0` (Goemans, *Lecture notes on the
ellipsoid algorithm*, MIT 18.433, 2009, the algorithm and the remark after Claim 7.2). -/
theorem ellipsoidRun_invariant (hn : 2 ≤ n) {P : Set (Fin n → ℝ)} {a c : ℕ → Fin n → ℝ}
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} (hA0 : (A 0).PosDef) (hP0 : P ⊆ ellipsoid (a 0) (A 0))
    (hstep : ∀ k, a k ∉ P → c k ≠ 0 ∧ (∀ x ∈ P, c k ⬝ᵥ x ≤ c k ⬝ᵥ a k) ∧
      a (k + 1) = nextCenter (a k) (A k) (c k) ∧ A (k + 1) = nextMatrix (A k) (c k)) :
    ∀ k, (∀ j < k, a j ∉ P) → (A k).PosDef ∧ P ⊆ ellipsoid (a k) (A k) ∧
      volume (ellipsoid (a k) (A k)) ≤
        ENNReal.ofReal (Real.exp (-(k : ℝ) / (2 * ((n : ℝ) + 1)))) *
          volume (ellipsoid (a 0) (A 0)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨hA0, hP0, ?_⟩
    simp
  | succ k ih =>
    intro hout
    obtain ⟨hAk, hPk, hvk⟩ := ih fun j hj => hout j (Nat.lt_succ_of_lt hj)
    obtain ⟨hc, hsep, ha, hA⟩ := hstep k (hout k (Nat.lt_succ_self k))
    refine ⟨?_, ?_, ?_⟩
    · rw [hA]; exact nextMatrix_posDef hn hAk hc
    · intro x hx
      rw [ha, hA]
      exact halfEllipsoid_subset_nextEllipsoid hn hAk (a k) hc ⟨hPk hx, hsep x hx⟩
    · rw [ha, hA]
      refine (volume_nextEllipsoid_lt hn hAk (a k) hc).le.trans ?_
      calc ENNReal.ofReal (Real.exp (-1 / (2 * ((n : ℝ) + 1)))) * volume (ellipsoid (a k) (A k))
          ≤ ENNReal.ofReal (Real.exp (-1 / (2 * ((n : ℝ) + 1)))) *
              (ENNReal.ofReal (Real.exp (-(k : ℝ) / (2 * ((n : ℝ) + 1)))) *
                volume (ellipsoid (a 0) (A 0))) := by gcongr
        _ = ENNReal.ofReal (Real.exp (-((k + 1 : ℕ) : ℝ) / (2 * ((n : ℝ) + 1)))) *
              volume (ellipsoid (a 0) (A 0)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 3
          push_cast
          ring

/-- **The ellipsoid method finds a point.** In a run of the central-cut ellipsoid method as in
`ellipsoidRun_invariant`, if `exp(-N / (2 (n + 1))) vol E_0 ≤ vol P`, that is `N ≥ 2 (n + 1) ln (vol
E_0 / vol P)`, then some centre `a_k` with `k ≤ N` lies in `P` (Goemans, *Lecture notes on the
ellipsoid algorithm*, MIT 18.433, 2009, the remark after Claim 7.2: "If P is nonempty then the
Ellipsoid Algorithm should find x ∈ P in at most 2(n + 1) ln(Vol(E₀)/Vol(P)) steps"). No convexity
of `P` is needed beyond the separating inequalities, and `vol P > 0` is implied by the hypothesis.
-/
theorem ellipsoidRun_finds_point (hn : 2 ≤ n) {P : Set (Fin n → ℝ)} {a c : ℕ → Fin n → ℝ}
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} (hA0 : (A 0).PosDef) (hP0 : P ⊆ ellipsoid (a 0) (A 0))
    (hstep : ∀ k, a k ∉ P → c k ≠ 0 ∧ (∀ x ∈ P, c k ⬝ᵥ x ≤ c k ⬝ᵥ a k) ∧
      a (k + 1) = nextCenter (a k) (A k) (c k) ∧ A (k + 1) = nextMatrix (A k) (c k))
    {N : ℕ} (hN : ENNReal.ofReal (Real.exp (-(N : ℝ) / (2 * ((n : ℝ) + 1)))) *
      volume (ellipsoid (a 0) (A 0)) ≤ volume P) :
    ∃ k ≤ N, a k ∈ P := by
  by_contra h
  have hout : ∀ j < N + 1, a j ∉ P := fun j hj hj' => h ⟨j, Nat.lt_succ_iff.mp hj, hj'⟩
  obtain ⟨-, hPN, hvN⟩ := ellipsoidRun_invariant hn hA0 hP0 hstep (N + 1) hout
  have hlt : ENNReal.ofReal (Real.exp (-((N + 1 : ℕ) : ℝ) / (2 * ((n : ℝ) + 1)))) *
      volume (ellipsoid (a 0) (A 0)) <
      ENNReal.ofReal (Real.exp (-(N : ℝ) / (2 * ((n : ℝ) + 1)))) *
      volume (ellipsoid (a 0) (A 0)) := by
    apply ENNReal.mul_lt_mul_left (volume_ellipsoid_ne_zero hA0 _) (volume_ellipsoid_ne_top hA0 _)
    rw [ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.exp_lt_exp]
    have : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
    rw [div_lt_div_iff_of_pos_right this]
    push_cast
    linarith
  exact absurd ((measure_mono hPN).trans hvN |>.trans_lt hlt |>.trans_le hN) (lt_irrefl _)

end MathlibExt.Analysis.Convex.EllipsoidMethod
