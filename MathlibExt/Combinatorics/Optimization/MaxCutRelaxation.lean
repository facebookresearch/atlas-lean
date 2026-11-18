/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Positive
public import MathlibExt.Combinatorics.Optimization.GoemansWilliamsonConstant

/-!
# The Goemans–Williamson relaxation of MAX CUT

M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and
satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145.

Vertices are a finite linearly ordered type `ι`, and `w i j` is the weight of the pair
`{i, j}`, read only for `i < j`, as in the paper's sums `∑_{i<j}`.

* `quadObjective` is the objective of their integer quadratic program (Q), §2;
  `quadObjective_cutSign` identifies it, at the `±1` vector of a vertex set `S`, with the weight
  `cutWeight w S` of the cut `δ(S)` (p. 1120).
* `vectorObjective` is the objective of the vector relaxation (P), §2, and `relaxationValue`
  its optimal value over unit vectors in `ℝ^m`. `cutWeight_le_relaxationValue` is the
  relaxation property `Z_P ≥ Z_MC` (p. 1120): every cut weighs at most the relaxation value.
* `sdpObjective` and `SDPFeasible` are the semidefinite form of (P) (§4 of the paper, and
  program (11) of Goemans's survey *Math. Programming* 79 (1997)): maximize
  `∑_{i<j} w_ij (1 - Y_ij) / 2` over positive semidefinite `Y` with unit diagonal.
  `sdpFeasible_gram` and `exists_gram_eq_of_sdpFeasible` show that these are exactly the Gram
  matrices of unit vectors, with the same objective.
* `hyperplaneExpectation` is the right-hand side `∑_{i<j} w_ij arccos(v_i · v_j) / π` of their
  Theorem 3.1, which is the expected weight of the random-hyperplane cut (that probabilistic
  identity is proved in `MathlibExt.Combinatorics.Optimization.RandomHyperplane`).
  `gwConstant_mul_vectorObjective_le` is the term-by-term comparison that proves their
  Theorem 3.3: for nonnegative weights and unit vectors, `α · (P-objective) ≤ ∑ w arccos / π`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Optimization.GoemansWilliamson

open Real Finset

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Ordered pairs of vertices.** The pairs `(i, j)` with `i < j`, indexing the sums
`∑_{i<j}` of Goemans and Williamson (*J. ACM* 42(6) (1995), §2). -/
def pairs (ι : Type*) [Fintype ι] [LinearOrder ι] : Finset (ι × ι) :=
  univ.filter fun p => p.1 < p.2

/-- **Objective of the MAX CUT quadratic program.** For `y : ι → ℝ`,
`∑_{i<j} w_ij (1 - y_i y_j) / 2`, the objective of program (Q) of Goemans and Williamson
(*J. ACM* 42(6) (1995), §2); on `±1` vectors it is the weight of a cut. -/
noncomputable def quadObjective (w : ι → ι → ℝ) (y : ι → ℝ) : ℝ :=
  ∑ p ∈ pairs ι, w p.1 p.2 * (1 - y p.1 * y p.2) / 2

/-- **Weight of a cut.** For a vertex set `S`, the total weight `w(S, S̄)` of the pairs `i < j`
with exactly one endpoint in `S` (Goemans and Williamson, *J. ACM* 42(6) (1995), §2). -/
def cutWeight (w : ι → ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ p ∈ pairs ι, if (p.1 ∈ S ↔ p.2 ∈ S) then 0 else w p.1 p.2

/-- **Sign vector of a cut.** `y_i = 1` for `i ∈ S` and `y_i = -1` otherwise. -/
def cutSign (S : Finset ι) (i : ι) : ℝ := if i ∈ S then 1 else -1

/-- **The quadratic program computes cut weights.** At the sign vector of `S`, the objective
of (Q) is the weight of the cut `δ(S)` (Goemans and Williamson, *J. ACM* 42(6) (1995), §2,
p. 1120). -/
theorem quadObjective_cutSign (w : ι → ι → ℝ) (S : Finset ι) :
    quadObjective w (cutSign S) = cutWeight w S := by
  unfold quadObjective cutWeight
  refine sum_congr rfl fun p _ => ?_
  unfold cutSign
  by_cases h1 : p.1 ∈ S <;> by_cases h2 : p.2 ∈ S <;> simp [h1, h2] <;> ring

/-- **Objective of the vector relaxation.** For vectors `v_i ∈ ℝ^m`,
`∑_{i<j} w_ij (1 - v_i · v_j) / 2`, the objective of the relaxation (P) of Goemans and
Williamson (*J. ACM* 42(6) (1995), §2). -/
noncomputable def vectorObjective {m : ℕ} (w : ι → ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ p ∈ pairs ι, w p.1 p.2 * (1 - inner ℝ (v p.1) (v p.2)) / 2

/-- **Value of the vector relaxation.** The supremum of the objective of (P) over families of
unit vectors in `ℝ^m` (Goemans and Williamson, *J. ACM* 42(6) (1995), §2; they take `m = n`,
the number of vertices). -/
noncomputable def relaxationValue (w : ι → ι → ℝ) (m : ℕ) : ℝ :=
  ⨆ v : {v : ι → EuclideanSpace ℝ (Fin m) // ∀ i, ‖v i‖ = 1}, vectorObjective w v.1

theorem abs_inner_le_one {m : ℕ} {u v : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) : |inner ℝ u v| ≤ 1 := by
  have := abs_real_inner_le_norm u v
  rwa [hu, hv, one_mul] at this

/-- **The relaxation objective is bounded on unit vectors.** For unit vectors the objective of
(P) is at most `∑_{i<j} |w_ij|`. -/
theorem vectorObjective_le_sum_abs {m : ℕ} (w : ι → ι → ℝ) {v : ι → EuclideanSpace ℝ (Fin m)}
    (hv : ∀ i, ‖v i‖ = 1) : vectorObjective w v ≤ ∑ p ∈ pairs ι, |w p.1 p.2| := by
  unfold vectorObjective
  refine sum_le_sum fun p _ => ?_
  have h := abs_le.1 (abs_inner_le_one (hv p.1) (hv p.2))
  have h1 : |1 - inner ℝ (v p.1) (v p.2)| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  calc w p.1 p.2 * (1 - inner ℝ (v p.1) (v p.2)) / 2
      ≤ |w p.1 p.2 * (1 - inner ℝ (v p.1) (v p.2))| / 2 := by
        gcongr; exact le_abs_self _
    _ = |w p.1 p.2| * |1 - inner ℝ (v p.1) (v p.2)| / 2 := by rw [abs_mul]
    _ ≤ |w p.1 p.2| * 2 / 2 := by gcongr
    _ = |w p.1 p.2| := by ring

/-- **Cuts embed in the vector relaxation.** For `m ≥ 1`, the vectors `v_i = y_i e₀`, with `y`
the sign vector of `S`, are unit vectors whose relaxation objective is the weight of the cut
`δ(S)` (Goemans and Williamson, *J. ACM* 42(6) (1995), §2: (P) reduces to (Q) for vectors in a
one-dimensional space). -/
theorem vectorObjective_cutSign_single {m : ℕ} (hm : 0 < m) (w : ι → ι → ℝ) (S : Finset ι) :
    (∀ i, ‖cutSign S i • EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ)‖ = 1) ∧
      vectorObjective w (fun i => cutSign S i • EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ))
        = cutWeight w S := by
  have hn : ‖EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ)‖ = 1 :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin m)).1 ⟨0, hm⟩
  constructor
  · intro i
    rw [norm_smul, hn, mul_one, Real.norm_eq_abs]
    unfold cutSign; split_ifs <;> norm_num
  · rw [← quadObjective_cutSign]
    unfold vectorObjective quadObjective
    refine sum_congr rfl fun p _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hn]
    ring

/-- **The vector relaxation bounds every cut.** For `m ≥ 1` and any vertex set `S`,
`w(S, S̄) ≤ Z_P`: the optimal value of (P) is an upper bound on the maximum cut (Goemans and
Williamson, *J. ACM* 42(6) (1995), §2, p. 1120). No sign condition on `w` is needed. -/
theorem cutWeight_le_relaxationValue {m : ℕ} (hm : 0 < m) (w : ι → ι → ℝ) (S : Finset ι) :
    cutWeight w S ≤ relaxationValue w m := by
  obtain ⟨hunit, hval⟩ := vectorObjective_cutSign_single hm w S
  have hbdd : BddAbove (Set.range fun v : {v : ι → EuclideanSpace ℝ (Fin m) // ∀ i, ‖v i‖ = 1} =>
      vectorObjective w v.1) := by
    refine ⟨∑ p ∈ pairs ι, |w p.1 p.2|, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact vectorObjective_le_sum_abs w v.2
  rw [← hval]
  exact le_ciSup hbdd (⟨_, hunit⟩ : {v : ι → EuclideanSpace ℝ (Fin m) // ∀ i, ‖v i‖ = 1})

/-- **Expected weight of the random-hyperplane cut.** `∑_{i<j} w_ij arccos(v_i · v_j) / π`,
the closed form of Goemans and Williamson's Theorem 3.1 (*J. ACM* 42(6) (1995)) for the
expected weight of the cut `{i : v_i · r ≥ 0}` cut out by a random hyperplane. Here it is only
the closed-form expression, defined for all vectors; the probabilistic identity is
`integral_cutWeight_hyperplane`, for unit vectors. For vectors that are not unit vectors it is not
that expectation, since `arccos (v_i · v_j)` is then not their angle (two zero vectors, which the
hyperplane never separates, would give `1/2`); every theorem below assumes unit vectors. -/
noncomputable def hyperplaneExpectation {m : ℕ} (w : ι → ι → ℝ)
    (v : ι → EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ p ∈ pairs ι, w p.1 p.2 * (arccos (inner ℝ (v p.1) (v p.2)) / π)

/-- **Goemans–Williamson Theorem 3.3, term-by-term comparison.** For nonnegative weights and
unit vectors, `α · ∑_{i<j} w_ij (1 - v_i · v_j) / 2 ≤ ∑_{i<j} w_ij arccos(v_i · v_j) / π`
(Goemans and Williamson, *J. ACM* 42(6) (1995), proof of Theorem 3.3 from Lemma 3.4). With
their Theorem 3.1 the right-hand side is the expected weight of the random-hyperplane cut. -/
theorem gwConstant_mul_vectorObjective_le {m : ℕ} {w : ι → ι → ℝ} (hw : ∀ i j, 0 ≤ w i j)
    {v : ι → EuclideanSpace ℝ (Fin m)} (hv : ∀ i, ‖v i‖ = 1) :
    gwConstant * vectorObjective w v ≤ hyperplaneExpectation w v := by
  unfold vectorObjective hyperplaneExpectation
  rw [mul_sum]
  refine sum_le_sum fun p _ => ?_
  have h := abs_le.1 (abs_inner_le_one (hv p.1) (hv p.2))
  have h34 := gwConstant_mul_le_arccos_div_pi h.1 h.2
  calc gwConstant * (w p.1 p.2 * (1 - inner ℝ (v p.1) (v p.2)) / 2)
      = w p.1 p.2 * (gwConstant * ((1 - inner ℝ (v p.1) (v p.2)) / 2)) := by ring
    _ ≤ w p.1 p.2 * (arccos (inner ℝ (v p.1) (v p.2)) / π) :=
        mul_le_mul_of_nonneg_left h34 (hw _ _)

/-- **The relaxation objective is nonnegative for nonnegative weights.** -/
theorem vectorObjective_nonneg {m : ℕ} {w : ι → ι → ℝ} (hw : ∀ i j, 0 ≤ w i j)
    {v : ι → EuclideanSpace ℝ (Fin m)} (hv : ∀ i, ‖v i‖ = 1) : 0 ≤ vectorObjective w v := by
  unfold vectorObjective
  refine sum_nonneg fun p _ => ?_
  have h := abs_le.1 (abs_inner_le_one (hv p.1) (hv p.2))
  have := hw p.1 p.2
  have : 0 ≤ 1 - inner ℝ (v p.1) (v p.2) := by linarith
  positivity

/-- **Goemans–Williamson Theorem 3.3 with the numerical constant.** For nonnegative weights and
unit vectors, `0.87856 · ∑_{i<j} w_ij (1 - v_i · v_j) / 2 ≤ ∑_{i<j} w_ij arccos(v_i · v_j) / π`
(Goemans and Williamson, *J. ACM* 42(6) (1995), Theorem 3.3 and Lemma 3.5). -/
theorem mul_vectorObjective_le_hyperplaneExpectation {m : ℕ} {w : ι → ι → ℝ}
    (hw : ∀ i j, 0 ≤ w i j) {v : ι → EuclideanSpace ℝ (Fin m)} (hv : ∀ i, ‖v i‖ = 1) :
    (0.87856 : ℝ) * vectorObjective w v ≤ hyperplaneExpectation w v :=
  (mul_le_mul_of_nonneg_right (le_of_lt lt_gwConstant) (vectorObjective_nonneg hw hv)).trans
    (gwConstant_mul_vectorObjective_le hw hv)

/-- **Objective of the MAX CUT semidefinite program.** For a matrix `Y`,
`∑_{i<j} w_ij (1 - Y_ij) / 2` (Goemans and Williamson, *J. ACM* 42(6) (1995), §4; program (11)
of Goemans, "Semidefinite programming in combinatorial optimization", *Math. Programming* 79
(1997), 143–161). -/
noncomputable def sdpObjective (w : ι → ι → ℝ) (Y : Matrix ι ι ℝ) : ℝ :=
  ∑ p ∈ pairs ι, w p.1 p.2 * (1 - Y p.1 p.2) / 2

omit [Fintype ι] [LinearOrder ι] in
/-- **Feasible matrices of the MAX CUT semidefinite program.** `Y` is positive semidefinite with
all diagonal entries equal to `1` (Goemans and Williamson, *J. ACM* 42(6) (1995), §4; Goemans,
*Math. Programming* 79 (1997), program (11)). -/
def SDPFeasible (Y : Matrix ι ι ℝ) : Prop := Y.PosSemidef ∧ ∀ i, Y i i = 1

/-- **Unit vectors give feasible matrices.** For unit vectors `v_i ∈ ℝ^m`, the Gram matrix
`Y_ij = v_i · v_j` is feasible for the semidefinite program, with the same objective as the
vector program (P) (Goemans and Williamson, *J. ACM* 42(6) (1995), §4). -/
theorem sdpFeasible_gram (w : ι → ι → ℝ) {m : ℕ} {v : ι → EuclideanSpace ℝ (Fin m)}
    (hv : ∀ i, ‖v i‖ = 1) :
    SDPFeasible (Matrix.gram ℝ v) ∧ sdpObjective w (Matrix.gram ℝ v) = vectorObjective w v := by
  refine ⟨⟨Matrix.posSemidef_gram ℝ v, fun i => ?_⟩, ?_⟩
  · rw [Matrix.gram_apply, real_inner_self_eq_norm_sq, hv i, one_pow]
  · simp [sdpObjective, vectorObjective, Matrix.gram_apply]

omit [Fintype ι] [LinearOrder ι] in
/-- **Feasible matrices are Gram matrices of unit vectors.** Every positive semidefinite `Y`
with unit diagonal is the Gram matrix of unit vectors `v_i ∈ ℝ^m` for some `m` (Goemans and
Williamson, *J. ACM* 42(6) (1995), §4, where `m = n` by an incomplete Cholesky decomposition;
here `m` comes from a decomposition `Y = ∑_k u_k u_kᵀ` and is not bounded). -/
theorem exists_gram_eq_of_sdpFeasible [Finite ι] {Y : Matrix ι ι ℝ} (hY : SDPFeasible Y) :
    ∃ m : ℕ, ∃ v : ι → EuclideanSpace ℝ (Fin m), (∀ i, ‖v i‖ = 1) ∧ Matrix.gram ℝ v = Y := by
  obtain ⟨m, u, hu⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hY.1
  let v : ι → EuclideanSpace ℝ (Fin m) := fun i => WithLp.toLp 2 fun k => u k i
  have hgram : Matrix.gram ℝ v = Y := by
    ext i j
    rw [hu, Matrix.gram_apply, Matrix.sum_apply]
    simp only [v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.vecMulVec_apply,
      star_trivial]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  refine ⟨m, v, fun i => ?_, hgram⟩
  have h : ‖v i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, ← Matrix.gram_apply (𝕜 := ℝ) v i i, hgram, hY.2 i]
  have := norm_nonneg (v i)
  nlinarith [sq_nonneg (‖v i‖ - 1)]

end MathlibExt.Combinatorics.Optimization.GoemansWilliamson
