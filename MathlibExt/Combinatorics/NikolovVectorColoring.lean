/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MatrixDiscrepancy
public import MathlibExt.Combinatorics.VectorDiscrepancy

/-!
# Nikolov's vector coloring bound

Nikolov's theorem gives unit vector colors for the columns of a column-admissible matrix
such that every colored row has Euclidean norm at most one. Its corollary
`nikolov2013VectorDiscrepancyUpperBound_holds` bounds the vector discrepancy of such a matrix
by one.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open MatrixDiscrepancy

namespace KomlosDiscrepancyWanted

/-- **Komlós conjecture for vector colorings (statement).** The statement that for all natural
numbers $m$ and $n \ge 1$ and every real $m \times n$ matrix $A$ whose columns all lie in the
closed Euclidean unit ball, there are unit vectors $u_1, \dots, u_n$ in the Euclidean space
$\mathbb{R}^n$ such that $\lVert \sum_{j=1}^{n} A_{ij} u_j \rVert \le 1$ for every row index $i$,
where $\lVert \cdot \rVert$ is the Euclidean norm.

Source: Nikolov, arXiv1301.4039, retained KomlosSDP.tex lines 115-139,
Theorem `thm:main`. Positive column dimension is explicit. -/
def nikolov2013VectorColoringBound : Prop :=
  ∀ (m n : ℕ), 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℝ, ColumnAdmissible A →
    ∃ u : Fin n → EuclideanSpace ℝ (Fin n), (∀ j, ‖u j‖ = 1) ∧
      ∀ i, ‖∑ j, A i j • u j‖ ≤ 1

/-- **Statement of Nikolov's bound on vector discrepancy.** This is the proposition that for all
natural numbers $m$ and $n$ with $n \ge 1$ and every real $m \times n$ matrix $A$ whose columns
all lie in the closed Euclidean unit ball, that is, $\sum_{i} A_{ij}^2 \le 1$ for every
column $j$, the vector discrepancy of $A$ is at most $1$.

This bounds the unit-vector relaxation, not the discrepancy over sign vectors.

Source: Nikolov, arXiv1301.4039, retained KomlosSDP.tex, Theorem `thm:main`,
and optimization catalogue C24a, line 55. -/
def nikolov2013VectorDiscrepancyUpperBound : Prop :=
  ∀ (m n : ℕ), 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℝ, ColumnAdmissible A →
    vectorDiscrepancy A ≤ 1

variable {m n : ℕ}

-- The map sends each row direction to its colored sum over the chosen columns.
private noncomputable def coloringMap (s : Finset (Fin n)) (a : Fin n → EuclideanSpace ℝ (Fin m))
    (u : Fin n → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∑ j ∈ s, InnerProductSpace.rankOne ℝ (u j) (a j)

private lemma norm_add_single_sq (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) (r : ℝ)
    (hx : x k = 0) : ‖x + EuclideanSpace.single k r‖ ^ 2 = ‖x‖ ^ 2 + r ^ 2 := by
  simp [norm_add_sq_real, EuclideanSpace.inner_single_right, hx, Real.norm_eq_abs]

private lemma residual_norm_sq (x a : EuclideanSpace ℝ (Fin m)) (ha : ‖a‖ ≤ 1) :
    ‖x - ⟪a, x⟫_ℝ • a‖ ^ 2 + ⟪a, x⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm a x, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  have ha' : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  nlinarith [mul_le_mul_of_nonneg_left ha' (sq_nonneg ⟪a, x⟫_ℝ)]

-- The map stays contractive, and its image uses only coordinates indexed by s.
private lemma exists_partial_coloring (a : Fin n → EuclideanSpace ℝ (Fin m))
    (ha : ∀ j, ‖a j‖ ≤ 1) (s : Finset (Fin n)) :
    ∃ u : Fin n → EuclideanSpace ℝ (Fin n), (∀ j ∈ s, ‖u j‖ = 1) ∧
      (∀ x k, k ∉ s → coloringMap s a u x k = 0) ∧
      ∀ x, ‖coloringMap s a u x‖ ≤ ‖x‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp [coloringMap], by simp [coloringMap]⟩
  | @insert k s hk ih =>
    obtain ⟨u, hu, hs, hnorm⟩ := ih
    let T := coloringMap s a u
    let r := Real.sqrt (1 - ‖T (a k)‖ ^ 2)
    have hT : ‖T (a k)‖ ≤ 1 := (hnorm (a k)).trans (ha k)
    have hr : r ^ 2 = 1 - ‖T (a k)‖ ^ 2 := by
      apply Real.sq_sqrt
      nlinarith [norm_nonneg (T (a k))]
    -- Cancel the old image of the column and complete its color to a unit vector.
    let v := -T (a k) + EuclideanSpace.single k r
    have hv : ‖v‖ = 1 := by
      have h := norm_add_single_sq (-T (a k)) k r (by simp [T, hs _ _ hk])
      simp only [norm_neg] at h
      change ‖-T (a k) + EuclideanSpace.single k r‖ = 1
      nlinarith [norm_nonneg (-T (a k) + EuclideanSpace.single k r)]
    let u' := Function.update u k v
    have hold (j) (hj : j ∈ s) : u' j = u j :=
      Function.update_of_ne (ne_of_mem_of_not_mem hj hk) ..
    have hstep (x) :
        coloringMap (insert k s) a u' x =
          T (x - ⟪a k, x⟫_ℝ • a k) + EuclideanSpace.single k (⟪a k, x⟫_ℝ * r) := by
      have hsum : coloringMap s a u' = T := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hold j hj]
      calc
        coloringMap (insert k s) a u' x = ⟪a k, x⟫_ℝ • v + T x := by
          simp only [coloringMap, Finset.sum_insert hk, add_apply]
          change ⟪a k, x⟫_ℝ • u' k + coloringMap s a u' x = _
          simp only [hsum, u', Function.update_self]
        _ = _ := by
          rw [map_sub, map_smul]
          simp only [v, smul_add, smul_neg, sub_eq_add_neg]
          have hsingle (c : ℝ) : c • EuclideanSpace.single k r =
              EuclideanSpace.single k (c * r) := by
            ext l
            by_cases h : l = k <;> simp [h]
          rw [hsingle]
          abel
    refine ⟨u', ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa [u'] using hv
      · rw [hold j hj]
        exact hu j hj
    · intro x l hl
      obtain ⟨hlk, hls⟩ := not_or.mp (Finset.mem_insert.not.mp hl)
      simp [hstep, T, hs _ _ hls, hlk]
    · intro x
      let c := ⟪a k, x⟫_ℝ
      let z := x - c • a k
      have hz : ‖T z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (hnorm z) 2
      have hcr : (c * r) ^ 2 ≤ c ^ 2 := by
        rw [mul_pow, hr]
        nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg ‖T (a k)‖)]
      rw [hstep]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [norm_add_single_sq _ _ _ (hs _ _ hk)]
      exact (add_le_add hz hcr).trans (residual_norm_sq x (a k) (ha k))

/-- **Nikolov's theorem: the Komlós conjecture holds for vector colorings.** For all natural
numbers $m$ and $n \ge 1$ and every real $m \times n$ matrix $A$ whose columns all have Euclidean
norm at most $1$, there are unit vectors $u_1, \dots, u_n$ in the Euclidean space $\mathbb{R}^n$
such that $\lVert \sum_{j=1}^{n} A_{ij} u_j \rVert \le 1$ for every row index $i$, where
$\lVert \cdot \rVert$ is the Euclidean norm.

Source: Nikolov, arXiv1301.4039, retained Theorem `thm:main`. -/
theorem nikolov2013VectorColoringBound_holds : nikolov2013VectorColoringBound := by
  intro m n _ A hA
  let a (j : Fin n) : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i => A i j)
  obtain ⟨u, hu, _, hnorm⟩ :=
    exists_partial_coloring a (columnAdmissible_iff_euclidean A |>.mp hA) Finset.univ
  refine ⟨u, fun j => hu j (Finset.mem_univ j), fun i => ?_⟩
  simpa [coloringMap, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_right, a]
    using hnorm (EuclideanSpace.single i 1)

/-- **Nikolov's bound on vector discrepancy.** For all natural numbers $m$ and $n$ with
$n \ge 1$ and every real $m \times n$ matrix $A$ whose columns all lie in the closed
Euclidean unit ball, that is, $\sum_{i} A_{ij}^2 \le 1$ for every column $j$, the vector
discrepancy of $A$ is at most $1$.

Source: Nikolov, arXiv1301.4039, retained Theorem `thm:main`; catalogue line 55. -/
theorem nikolov2013VectorDiscrepancyUpperBound_holds :
    nikolov2013VectorDiscrepancyUpperBound := by
  intro m n hn A hA
  obtain ⟨u, hu, hrows⟩ := nikolov2013VectorColoringBound_holds m n hn A hA
  exact vectorDiscrepancy_le_of_coloring A u hu hrows

end KomlosDiscrepancyWanted
