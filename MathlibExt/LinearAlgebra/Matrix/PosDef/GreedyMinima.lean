/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Interval.Finset.Fin

/-!
# Greedy successive minima of a positive definite form on `ℤ^g`

Let `Y` be a real symmetric positive definite `g × g` matrix (`Matrix.PosDef`) and
`Q(x) = ᵗx Y x` (`x ⬝ᵥ Y *ᵥ x`) its quadratic form. This module chooses integral vectors
`v₁, …, v_g ∈ ℤ^g` greedily: each `v_k` minimizes `Q` over the integral vectors outside
`span_ℝ(v₁, …, v_{k-1})`. With `λ_k = Q(v_k)`:

* `Matrix.IsGreedyMinima`: the property of such a family; `Matrix.exists_isGreedyMinima`: one
  exists, and `Matrix.PosDef.greedyMinVec` is a chosen one, with values `Matrix.PosDef.succMin`;
* `Matrix.IsGreedyMinima.linearIndependent`: `v₁, …, v_g` are linearly independent;
* `Matrix.IsGreedyMinima.pos`, `Matrix.IsGreedyMinima.monotone`: `0 < λ₁ ≤ ⋯ ≤ λ_g`;
* `Matrix.IsGreedyMinima.le_of_notMem_span_Iic`: an integral `y` outside
  `span_ℝ(v₁, …, v_k)` has `λ_{k+1} ≤ Q(y)`;
* `Matrix.IsGreedyMinima.isLeast`: for `g ≥ 1`, `λ₁` is the least value of `Q` on `ℤ^g ∖ {0}`;
* `Matrix.IsGreedyMinima.exists_le_le_ne_zero`: some `v_i` with `i ≤ k` has a nonzero
  coordinate of index at least `k`.

The family is indexed by `Fin g`, so `v k`, for `k = 0, …, g - 1`, is `v_{k+1}` above.
The `λ_k` are a variant of the successive minima of O. Regev, *Lattices in computer science*,
lecture notes, Tel Aviv University, Fall 2004, Lecture 1, §3, Definition 7, p. 5 (for the lattice
`ℤ^g` with the norm `√Q`, squared): the proof of Minkowski's second theorem there (Theorem 3,
p. 8) uses only the two properties above, in
`MathlibExt.LinearAlgebra.Matrix.PosDef.MinkowskiSecondTheorem`.
-/

@[expose] public section

open Module

namespace Matrix

variable {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ}

open scoped MatrixOrder in
/-- A real positive definite matrix is `ᵗB B` for some invertible real matrix `B`. -/
theorem PosDef.exists_eq_transpose_mul_self (hY : Y.PosDef) :
    ∃ B : Matrix (Fin g) (Fin g) ℝ, Y = Bᵀ * B ∧ B.det ≠ 0 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg
  have hBt : Y = Bᵀ * B := by
    rw [hB, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  refine ⟨B, hBt, fun h ↦ hY.det_pos.ne' ?_⟩
  rw [hBt, det_mul, det_transpose, h, mul_zero]

/-- The quadratic form of `ᵗB B` is `x ↦ |Bx|²`: `ᵗx (ᵗB B) x = (Bx) ⬝ (Bx)`. -/
theorem dotProduct_transpose_mul_self_mulVec (B : Matrix (Fin g) (Fin g) ℝ) (x : Fin g → ℝ) :
    x ⬝ᵥ (Bᵀ * B) *ᵥ x = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The squared coordinates of a vector are bounded by a constant multiple of the positive
definite form: `x_i² ≤ K ᵗx Y x`. -/
private theorem PosDef.exists_sq_le_mul (hY : Y.PosDef) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : Fin g → ℝ) (i : Fin g), x i ^ 2 ≤ K * (x ⬝ᵥ Y *ᵥ x) := by
  obtain ⟨B, hYB, hB⟩ := hY.exists_eq_transpose_mul_self
  refine ⟨∑ i, ∑ j, B⁻¹ i j ^ 2, by positivity, fun x i ↦ ?_⟩
  have hx : x = B⁻¹ *ᵥ (B *ᵥ x) := by
    rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit hB), one_mulVec]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ B⁻¹ i j) (fun j ↦ (B *ᵥ x) j)
  rw [hYB, dotProduct_transpose_mul_self_mulVec]
  calc x i ^ 2 = (∑ j, B⁻¹ i j * (B *ᵥ x) j) ^ 2 := by
        conv_lhs => rw [hx]
        rfl
    _ ≤ (∑ j, B⁻¹ i j ^ 2) * ∑ j, (B *ᵥ x) j ^ 2 := hcs
    _ ≤ (∑ i, ∑ j, B⁻¹ i j ^ 2) * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x)) := by
        refine mul_le_mul ?_ (le_of_eq ?_) (by positivity) (by positivity)
        · exact Finset.single_le_sum (f := fun i ↦ ∑ j, B⁻¹ i j ^ 2)
            (fun i _ ↦ by positivity) (Finset.mem_univ i)
        · simp [dotProduct, sq]

/-- For a real positive definite matrix `Y`, only finitely many integral vectors `z` have
`ᵗz Y z ≤ c`. -/
theorem PosDef.finite_setOf_le (hY : Y.PosDef) (c : ℝ) :
    {z : Fin g → ℤ | (Int.cast ∘ z : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ z) ≤ c}.Finite := by
  obtain ⟨K, hK, hle⟩ := hY.exists_sq_le_mul
  set N : ℤ := ⌈K * c⌉
  refine (Fintype.piFinset fun _ ↦ Finset.Icc (-N) N).finite_toSet.subset fun z hz ↦ ?_
  rw [Set.mem_ofPred_eq] at hz
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h1 : ((z i : ℝ)) ^ 2 ≤ K * c :=
    (hle _ i).trans (mul_le_mul_of_nonneg_left hz hK)
  have h2 : ((z i ^ 2 : ℤ) : ℝ) ≤ N := by push_cast; exact h1.trans (Int.le_ceil _)
  have h3 : z i ^ 2 ≤ N := by exact_mod_cast h2
  have h4 : |z i| ≤ z i ^ 2 := by
    rcases eq_or_ne (z i) 0 with h | h
    · simp [h]
    · rw [← sq_abs]
      have : 1 ≤ |z i| := Int.one_le_abs h
      nlinarith
  exact abs_le.mp (h4.trans h3)

/-- Some standard basis vector of `ℝ^g` lies outside a proper subspace. -/
private theorem exists_single_notMem {W : Submodule ℝ (Fin g → ℝ)} (hW : W ≠ ⊤) :
    ∃ j : Fin g, (Pi.single j 1 : Fin g → ℝ) ∉ W := by
  by_contra! h
  apply hW
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  simpa using h j

/-- Let `Y` be a real positive definite `g × g` matrix and `W` a proper subspace of `ℝ^g`. Then
the quadratic form `Q(z) = ᵗz Y z` attains a minimum on the integral vectors `z ∉ W`.

Some standard basis vector `e_j` lies outside `W`, and only finitely many integral `z` have
`Q(z) ≤ Q(e_j)` (`Matrix.PosDef.finite_setOf_le`). -/
theorem PosDef.exists_min_notMem (hY : Y.PosDef) {W : Submodule ℝ (Fin g → ℝ)} (hW : W ≠ ⊤) :
    ∃ y : Fin g → ℤ, (Int.cast ∘ y : Fin g → ℝ) ∉ W ∧ ∀ z : Fin g → ℤ,
      (Int.cast ∘ z : Fin g → ℝ) ∉ W →
        (Int.cast ∘ y : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ y) ≤
          (Int.cast ∘ z : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ z) := by
  classical
  set q : (Fin g → ℤ) → ℝ := fun z ↦ (Int.cast ∘ z : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ z)
  obtain ⟨j, hj⟩ := exists_single_notMem hW
  have hjcast : (Int.cast ∘ (Pi.single j 1 : Fin g → ℤ) : Fin g → ℝ) = Pi.single j 1 := by
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  set S := {z : Fin g → ℤ | q z ≤ q (Pi.single j 1)} ∩ {z | (Int.cast ∘ z : Fin g → ℝ) ∉ W}
  have hS : S.Finite := (hY.finite_setOf_le _).subset Set.inter_subset_left
  have hne : S.Nonempty := ⟨Pi.single j 1, show q _ ≤ q _ from le_rfl, by simpa [hjcast] using hj⟩
  obtain ⟨y, hyS, hymin⟩ := Set.exists_min_image S q hS hne
  refine ⟨y, hyS.2, fun z hz ↦ ?_⟩
  by_cases hzq : q z ≤ q (Pi.single j 1)
  · exact hymin z ⟨hzq, hz⟩
  · exact hyS.1.trans (le_of_not_ge hzq)

/-- The span of fewer than `g` vectors is a proper subspace of `ℝ^g`. -/
theorem span_range_ne_top_of_card_lt {ι : Type*} [Fintype ι] (hι : Fintype.card ι < g)
    (f : ι → Fin g → ℝ) : Submodule.span ℝ (Set.range f) ≠ ⊤ := by
  intro h
  have := finrank_range_le_card (R := ℝ) f
  rw [Set.finrank, h, finrank_top, finrank_fin_fun] at this
  omega

/-- **Greedy successive minima** of a positive definite form on `ℤ^g`. For a real
`g × g` matrix `Y` with quadratic form `Q(x) = ᵗx Y x`, a family `v₁, …, v_g` of integral
vectors, indexed by `Fin g` (so that `v k` is $v_{k+1}$), is *greedy* when, for every `k`,
1. `v_k ∉ span_ℝ(v₁, …, v_{k-1})`, and
2. every integral `y ∉ span_ℝ(v₁, …, v_{k-1})` has `Q(v_k) ≤ Q(y)`,
that is, `v_k` minimizes `Q` over the integral vectors outside `span_ℝ(v₁, …, v_{k-1})`.
The values `λ_k = Q(v_k)` are a variant of the successive minima of Regev's Definition 7 for the
lattice `ℤ^g` with the norm `√Q`: when `Y` is positive definite they satisfy
`0 < λ₁ ≤ ⋯ ≤ λ_g`, and, for `g ≥ 1`, `λ₁` is the least value of `Q` on `ℤ^g ∖ {0}`.

Source: O. Regev, *Lattices in computer science*, lecture notes, Tel Aviv University, Fall 2004,
Lecture 1, §3, Definition 7, p. 5 (successive minima), and Claim 7, p. 6 (they are attained). -/
structure IsGreedyMinima (Y : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → Fin g → ℤ) : Prop where
  /-- `v_k` lies outside the span of the earlier vectors. -/
  notMem_span (k : Fin g) : (Int.cast ∘ v k : Fin g → ℝ) ∉
    Submodule.span ℝ ((fun i ↦ (Int.cast ∘ v i : Fin g → ℝ)) '' Set.Iio k)
  /-- `v_k` minimizes `Q` over the integral vectors outside the span of the earlier vectors. -/
  le_of_notMem_span (k : Fin g) (y : Fin g → ℤ) : (Int.cast ∘ y : Fin g → ℝ) ∉
      Submodule.span ℝ ((fun i ↦ (Int.cast ∘ v i : Fin g → ℝ)) '' Set.Iio k) →
    (Int.cast ∘ v k : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ v k) ≤
      (Int.cast ∘ y : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ y)

namespace PosDef

/-- A chosen family of **greedy successive minima vectors** of a real positive definite
`g × g` matrix `Y`: `hY.greedyMinVec k` minimizes `Q(x) = ᵗx Y x` over the integral vectors
outside the span of `hY.greedyMinVec i` for `i < k` (`Matrix.PosDef.isGreedyMinima_greedyMinVec`).

Source: O. Regev, *Lattices in computer science*, lecture notes, Tel Aviv University, Fall 2004,
Lecture 1, §3, Definition 7, p. 5, and Claim 7, p. 6 (a greedy variant). -/
noncomputable def greedyMinVec (hY : Y.PosDef) (k : Fin g) : Fin g → ℤ :=
  Classical.choose <| hY.exists_min_notMem <| span_range_ne_top_of_card_lt
    (by simp) fun i : Set.Iio k ↦ (Int.cast ∘ hY.greedyMinVec i : Fin g → ℝ)
termination_by k.val
decreasing_by all_goals exact Fin.lt_def.mp i.2

/-- The **greedy successive minima** `λ_{k+1} = Q(v_{k+1})` of a real positive definite
`g × g` matrix `Y`, for `Q(x) = ᵗx Y x` and the vectors `v` of `Matrix.PosDef.greedyMinVec`,
indexed by `k : Fin g`.

Source: O. Regev, *Lattices in computer science*, lecture notes, Tel Aviv University, Fall 2004,
Lecture 1, §3, Definition 7, p. 5 (a greedy variant of the successive minima). -/
noncomputable def succMin (hY : Y.PosDef) (k : Fin g) : ℝ :=
  (Int.cast ∘ hY.greedyMinVec k : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ hY.greedyMinVec k)

/-- The vectors `Matrix.PosDef.greedyMinVec` of a real positive definite matrix are greedy
successive minima vectors (`Matrix.IsGreedyMinima`). -/
theorem isGreedyMinima_greedyMinVec (hY : Y.PosDef) : IsGreedyMinima Y hY.greedyMinVec := by
  have key : ∀ k, _ := fun k : Fin g ↦ Classical.choose_spec <| hY.exists_min_notMem <|
    span_range_ne_top_of_card_lt (by simp) fun i : Set.Iio k ↦
      (Int.cast ∘ hY.greedyMinVec i : Fin g → ℝ)
  refine ⟨fun k ↦ ?_, fun k y hy ↦ ?_⟩
  · rw [greedyMinVec, Set.image_eq_range]
    exact (key k).1
  · rw [greedyMinVec]
    rw [Set.image_eq_range] at hy
    exact (key k).2 y hy

end PosDef

/-- **Greedy successive minima exist.** For a real positive definite `g × g` matrix `Y` there
are integral vectors `v₁, …, v_g` such that each `v_k` minimizes `Q(x) = ᵗx Y x` over the
integral vectors outside `span_ℝ(v₁, …, v_{k-1})` (`Matrix.IsGreedyMinima`).

The set of integral vectors outside a proper subspace contains a standard basis vector `e_j`,
and meets the set `{Q ≤ Q(e_j)}` in a finite set, so it has a minimizer of `Q`.

Source: O. Regev, *Lattices in computer science*, lecture notes, Tel Aviv University, Fall 2004,
Lecture 1, §3, Definition 7, p. 5, and Claim 7, p. 6 (a greedy variant). -/
theorem exists_isGreedyMinima (hY : Y.PosDef) : ∃ v, IsGreedyMinima Y v :=
  ⟨_, hY.isGreedyMinima_greedyMinVec⟩

namespace IsGreedyMinima

variable {v : Fin g → Fin g → ℤ}

/-- Greedy successive minima vectors `v₁, …, v_g` are linearly independent over `ℝ`. -/
theorem linearIndependent (hv : IsGreedyMinima Y v) :
    LinearIndependent ℝ fun i ↦ (Int.cast ∘ v i : Fin g → ℝ) := by
  classical
  set w := fun i ↦ (Int.cast ∘ v i : Fin g → ℝ)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra! h
  obtain ⟨i₀, hi₀⟩ := h
  set S := Finset.univ.filter fun i ↦ c i ≠ 0
  have hSne : S.Nonempty := ⟨i₀, by simp [S, hi₀]⟩
  set k := S.max' hSne
  have hk : c k ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hSne)).2
  have hgt : ∀ i, k < i → c i = 0 := fun i hi ↦ by
    by_contra h
    exact absurd (S.le_max' i (by simp [S, h])) (not_le.mpr hi)
  apply hv.notMem_span k
  have hrest : ∑ i ∈ Finset.univ.erase k, c i • w i ∈ Submodule.span ℝ (w '' Set.Iio k) := by
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, h, rfl⟩)
    · rw [hgt i h, zero_smul]
      exact Submodule.zero_mem _
  have heq : c k • w k = -∑ i ∈ Finset.univ.erase k, c i • w i := by
    have := Finset.add_sum_erase Finset.univ (fun i ↦ c i • w i) (Finset.mem_univ k)
    rw [eq_neg_iff_add_eq_zero, this]
    exact hc
  have hwk : w k = (c k)⁻¹ • (c k • w k) := by rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
  change w k ∈ _
  rw [hwk, heq]
  exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hrest)

/-- Greedy successive minima vectors `v₁, …, v_g` span `ℝ^g`. -/
theorem span_eq_top (hv : IsGreedyMinima Y v) :
    Submodule.span ℝ (Set.range fun i ↦ (Int.cast ∘ v i : Fin g → ℝ)) = ⊤ :=
  hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)

/-- Greedy successive minima vectors are nonzero. -/
theorem cast_ne_zero (hv : IsGreedyMinima Y v) (k : Fin g) : (Int.cast ∘ v k : Fin g → ℝ) ≠ 0 :=
  fun h ↦ hv.notMem_span k (h ▸ Submodule.zero_mem _)

/-- For a positive definite `Y`, the greedy successive minima are positive: `0 < λ_k`. -/
theorem pos (hY : Y.PosDef) (hv : IsGreedyMinima Y v) (k : Fin g) :
    0 < (Int.cast ∘ v k : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ v k) := by
  simpa using hY.dotProduct_mulVec_pos (hv.cast_ne_zero k)

/-- The greedy successive minima are nondecreasing: `λ₁ ≤ λ₂ ≤ ⋯ ≤ λ_g`. -/
theorem monotone (hv : IsGreedyMinima Y v) :
    Monotone fun k ↦ (Int.cast ∘ v k : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ v k) := fun i j hij ↦
  hv.le_of_notMem_span i (v j) fun h ↦ hv.notMem_span j
    (Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hij)) h)

/-- Every integral vector `y` outside `span_ℝ(v₁, …, v_k)` has `λ_{k+1} ≤ Q(y)`. In the
indexing by `Fin g`, `k` stands for `v_{k+1}`, so the span is over the `v i` with `i ≤ k`, and
the bound is by `Q(v (k + 1))`, for `k + 1 < g`. -/
theorem le_of_notMem_span_Iic (hv : IsGreedyMinima Y v) (k : Fin g) (hk : k.val + 1 < g)
    (y : Fin g → ℤ) (hy : (Int.cast ∘ y : Fin g → ℝ) ∉
      Submodule.span ℝ ((fun i ↦ (Int.cast ∘ v i : Fin g → ℝ)) '' Set.Iic k)) :
    (Int.cast ∘ v ⟨k + 1, hk⟩ : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ v ⟨k + 1, hk⟩) ≤
      (Int.cast ∘ y : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ y) := by
  refine hv.le_of_notMem_span _ y ?_
  convert hy using 4
  ext i
  simp only [Set.mem_Iio, Set.mem_Iic, Fin.lt_def, Fin.le_def]
  omega

/-- The first greedy successive minimum is at most the value of `Q` at every nonzero integral
vector: `λ₁ ≤ Q(y)` for `y ∈ ℤ^g ∖ {0}`. -/
theorem le_of_ne_zero (hv : IsGreedyMinima Y v) (hg : 0 < g) {y : Fin g → ℤ} (hy : y ≠ 0) :
    (Int.cast ∘ v ⟨0, hg⟩ : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ v ⟨0, hg⟩) ≤
      (Int.cast ∘ y : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ y) := by
  refine hv.le_of_notMem_span _ y ?_
  have : Set.Iio (⟨0, hg⟩ : Fin g) = ∅ := by
    ext i
    simp [Fin.lt_def]
  rw [this, Set.image_empty, Submodule.span_empty, Submodule.mem_bot]
  exact fun h ↦ hy (funext fun i ↦ by simpa using congrFun h i)

/-- The first greedy successive minimum is the least value of `Q` on the nonzero integral
vectors: `λ₁ = min {Q(y) : y ∈ ℤ^g, y ≠ 0}`.

Source: O. Regev, *Lattices in computer science*, lecture notes, Tel Aviv University, Fall 2004,
Lecture 1, §3, p. 5 (the first minimum `λ₁`). -/
theorem isLeast (hv : IsGreedyMinima Y v) (hg : 0 < g) :
    IsLeast {q | ∃ y : Fin g → ℤ, y ≠ 0 ∧ (Int.cast ∘ y : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ y) = q}
      ((Int.cast ∘ v ⟨0, hg⟩ : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ v ⟨0, hg⟩)) := by
  refine ⟨⟨v ⟨0, hg⟩, fun h ↦ hv.cast_ne_zero _ (by rw [h]; ext; simp), rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hv.le_of_ne_zero hg hy

/-- Among the greedy successive minima vectors `v i` with `i ≤ k`, some `v i` has a nonzero
coordinate `(v i)_j` with `k ≤ j`: the `k + 1` linearly independent vectors `v i`, `i ≤ k`, do not
all lie in the `k`-dimensional subspace of the vectors whose coordinates of index `≥ k` vanish. -/
theorem exists_le_le_ne_zero (hv : IsGreedyMinima Y v) (k : Fin g) :
    ∃ i ≤ k, ∃ j, k ≤ j ∧ v i j ≠ 0 := by
  by_contra! h
  set w := fun i ↦ (Int.cast ∘ v i : Fin g → ℝ)
  let W : Submodule ℝ (Fin g → ℝ) :=
    { carrier := {x | ∀ j, k ≤ j → x j = 0}
      add_mem' := fun hx hy j hj ↦ by simp [hx j hj, hy j hj]
      zero_mem' := fun j _ ↦ rfl
      smul_mem' := fun c x hx j hj ↦ by simp [hx j hj] }
  have hspan : Submodule.span ℝ (Set.range fun i : Set.Iic k ↦ w i) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ j hj
    simp [w, h i i.2 j hj]
  let f : W →ₗ[ℝ] (Fin k → ℝ) :=
    { toFun := fun x j ↦ (x : Fin g → ℝ) (Fin.castLE k.2.le j)
      map_add' := fun x y ↦ rfl
      map_smul' := fun c x ↦ rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    ext j
    by_cases hj : (j : ℕ) < k
    · exact congrFun hxy ⟨j, hj⟩
    · have hkj : k ≤ j := Fin.le_def.mpr (by omega)
      rw [x.2 j hkj, y.2 j hkj]
  have hli : LinearIndependent ℝ fun i : Set.Iic k ↦ w i :=
    hv.linearIndependent.comp _ Subtype.val_injective
  have h1 := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli] at h1
  have h2 := LinearMap.finrank_le_finrank_of_injective hf
  simp only [Fintype.card_Iic, Fin.card_Iic, finrank_fin_fun] at h1 h2
  omega

end IsGreedyMinima

namespace PosDef

/-- The greedy successive minima of a real positive definite matrix are positive. -/
theorem succMin_pos (hY : Y.PosDef) (k : Fin g) : 0 < hY.succMin k :=
  hY.isGreedyMinima_greedyMinVec.pos hY k

/-- The greedy successive minima of a real positive definite matrix are nondecreasing. -/
theorem monotone_succMin (hY : Y.PosDef) : Monotone hY.succMin :=
  hY.isGreedyMinima_greedyMinVec.monotone

/-- Every integral vector `y` outside the span of the vectors `hY.greedyMinVec i`, `i < k`, has
`hY.succMin k ≤ ᵗy Y y`. -/
theorem succMin_le_of_notMem_span (hY : Y.PosDef) (k : Fin g) (y : Fin g → ℤ)
    (hy : (Int.cast ∘ y : Fin g → ℝ) ∉
      Submodule.span ℝ ((fun i ↦ (Int.cast ∘ hY.greedyMinVec i : Fin g → ℝ)) '' Set.Iio k)) :
    hY.succMin k ≤ (Int.cast ∘ y : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ y) :=
  hY.isGreedyMinima_greedyMinVec.le_of_notMem_span k y hy

end PosDef

end Matrix
