/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Rat.HasseMinkowskiBinary
public import MathlibExt.NumberTheory.Rat.HasseMinkowskiQuaternary
public import MathlibExt.NumberTheory.Rat.HasseMinkowskiRankFive

/-!
# The Hasse–Minkowski theorem over `ℚ`

A quadratic form $f(x) = \sum_{i,j=1}^n a_{ij} x_i x_j$ with rational coefficients has a zero other
than $0$ in $\mathbb{Q}^n$ if and only if it has one in $\mathbb{R}^n$ and in $\mathbb{Q}_p^n$ for
every prime $p$ (`Rat.exists_quadratic_eq_zero_iff_forall_local`). If moreover $(a_{ij})$ is
symmetric with $\det(a_{ij}) \neq 0$, then for $c \in \mathbb{Q}$ the equation $f(x) = c$ is
solvable in $\mathbb{Q}^n$ if and only if it is solvable in $\mathbb{R}^n$ and in every
$\mathbb{Q}_p^n$ (`Rat.exists_quadratic_eq_iff_forall_local`).

Both are first proved for diagonal forms $a_1 x_1^2 + \dots + a_n x_n^2$
(`Rat.exists_diagonal_eq_zero_iff_forall_local`, and `Rat.exists_diagonal_eq_iff_forall_local`
when every $a_i \neq 0$). The general forms reduce to these:
`QuadraticForm.equivalent_weightedSumSquares` diagonalizes the form over $\mathbb{Q}$, and the
rational change of variables, with its inverse, is carried to $\mathbb{R}$ and to each
$\mathbb{Q}_p$.

The diagonal case is the induction on $n$ of A. V. Sutherland, *18.782 Introduction to Arithmetic
Geometry*, MIT, Fall 2013, Lecture 11, proof of Theorem 11.12, pp. 4–5: a zero coefficient gives a
zero at once; otherwise $n = 1$ has no local zero, and the cases $n = 2, 3, 4$ and the step to
$n \geq 5$ are `Rat.exists_binary_eq_zero_of_forall_local`,
`Rat.exists_ternary_eq_zero_of_forall_local`, `Rat.exists_quaternary_eq_zero_of_forall_local` and
`Rat.exists_diagonal_eq_zero_of_rank_ge_five`. Represented values reduce to zeros of
$f - c z^2$, by the argument in the proof of Lemma 10.2 (Lecture 10, p. 1).
-/

@[expose] public section

namespace Rat

section Field

variable {K : Type*} [Field K]

private theorem hmd_fin2_iff (c : Fin 2 → K) :
    (∃ x : Fin 2 → K, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0) ↔
      ∃ x y : K, (x, y) ≠ (0, 0) ∧ c 0 * x ^ 2 + c 1 * y ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x 0, x 1, fun h' => hx ?_, by simpa [Fin.sum_univ_two] using h⟩
    simp only [Prod.mk.injEq] at h'
    funext i
    fin_cases i <;> simp [h'.1, h'.2]
  · rintro ⟨x, y, hne, h⟩
    refine ⟨![x, y], fun h' => hne ?_, by simpa [Fin.sum_univ_two] using h⟩
    have h0 := congrFun h' 0
    have h1 := congrFun h' 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    rw [h0, h1]

private theorem hmd_fin3_iff (c : Fin 3 → K) :
    (∃ x : Fin 3 → K, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0) ↔
      ∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ c 0 * x ^ 2 + c 1 * y ^ 2 + c 2 * z ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x 0, x 1, x 2, fun h' => hx ?_, by simpa [Fin.sum_univ_three] using h⟩
    funext i
    fin_cases i <;> simp [h'.1, h'.2.1, h'.2.2]
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨![x, y, z], fun h' => hne ?_, by simpa [Fin.sum_univ_three] using h⟩
    exact ⟨by simpa using congrFun h' 0, by simpa using congrFun h' 1,
      by simpa using congrFun h' 2⟩

private theorem hmd_fin4_iff (c : Fin 4 → K) :
    (∃ x : Fin 4 → K, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0) ↔
      ∃ x₁ x₂ x₃ x₄ : K, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
        c 0 * x₁ ^ 2 + c 1 * x₂ ^ 2 + c 2 * x₃ ^ 2 + c 3 * x₄ ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x 0, x 1, x 2, x 3, fun h' => hx ?_, by simpa [Fin.sum_univ_four] using h⟩
    funext i
    fin_cases i <;> simp [h'.1, h'.2.1, h'.2.2.1, h'.2.2.2]
  · rintro ⟨x₁, x₂, x₃, x₄, hne, h⟩
    refine ⟨![x₁, x₂, x₃, x₄], fun h' => hne ?_, by simpa [Fin.sum_univ_four] using h⟩
    exact ⟨by simpa using congrFun h' 0, by simpa using congrFun h' 1,
      by simpa using congrFun h' 2, by simpa using congrFun h' 3⟩

private theorem hmd_map_ne_zero {L : Type*} [Field L] [CharZero L] {n : ℕ} {x : Fin n → ℚ}
    (hx : x ≠ 0) : (fun i => (x i : L)) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  exact Function.ne_iff.2 ⟨i, by simpa using hi⟩

private theorem hmd_cast {L : Type*} [Field L] [CharZero L] {n : ℕ} (a x : Fin n → ℚ) {c : ℚ}
    (h : ∑ i, a i * x i ^ 2 = c) : ∑ i, (a i : L) * (x i : L) ^ 2 = (c : L) := by
  have := congrArg (Rat.cast : ℚ → L) h
  push_cast at this
  exact this

end Field

/-- The induction on the number of variables, for nonzero coefficients. -/
private theorem hmd_aux : ∀ (n : ℕ) (a : Fin n → ℚ), (∀ i, a i ≠ 0) →
    (∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, (a i : ℝ) * x i ^ 2 = 0) →
    (∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0) →
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha hreal hpadic
    match n, ih, a, ha, hreal, hpadic with
    | 0, _, a, _, hreal, _ =>
      obtain ⟨x, hx, -⟩ := hreal
      exact absurd (Subsingleton.elim x 0) hx
    | 1, _, a, ha, hreal, _ =>
      obtain ⟨x, hx, h⟩ := hreal
      exfalso
      have hx0 : x 0 ≠ 0 := fun h0 => hx (funext fun i => by fin_cases i; exact h0)
      simp only [Fin.sum_univ_one] at h
      exact (mul_ne_zero (by exact_mod_cast ha 0) (pow_ne_zero 2 hx0)) h
    | 2, _, a, _, hreal, hpadic =>
      rw [hmd_fin2_iff] at hreal ⊢
      exact exists_binary_eq_zero_of_forall_local hreal fun p _ => (hmd_fin2_iff _).1 (hpadic p)
    | 3, _, a, ha, hreal, hpadic =>
      rw [hmd_fin3_iff] at hreal ⊢
      exact exists_ternary_eq_zero_of_forall_local (ha 0) (ha 1) (ha 2) hreal
        fun p _ => (hmd_fin3_iff _).1 (hpadic p)
    | 4, _, a, ha, hreal, hpadic =>
      rw [hmd_fin4_iff] at hreal ⊢
      exact exists_quaternary_eq_zero_of_forall_local (ha 0) (ha 1) (ha 2) (ha 3) hreal
        fun p _ => (hmd_fin4_iff _).1 (hpadic p)
    | k + 5, ih, a, ha, hreal, hpadic =>
      refine exists_diagonal_eq_zero_of_rank_ge_five (by omega) (fun m hm b hb hbr hbp => ?_)
        a ha hreal hpadic
      exact ih m (by omega) b hb hbr hbp

/-- **Hasse–Minkowski theorem for diagonal forms over $\mathbb{Q}$.** Let $a_1, \dots, a_n$ be
rational numbers. Then $a_1 x_1^2 + \dots + a_n x_n^2 = 0$ has a solution $x \neq 0$ in
$\mathbb{Q}^n$ if and only if it has a solution $x \neq 0$ in $\mathbb{R}^n$ and a solution
$x \neq 0$ in $\mathbb{Q}_p^n$ for every prime $p$.

The coefficients may be $0$, and $n$ may be $0$ (then no side holds).

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture
11, Theorem 11.12 and its proof, pp. 4–5, for diagonal forms, to which the proof there first
reduces, <https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>. -/
theorem exists_diagonal_eq_zero_iff_forall_local {n : ℕ} (a : Fin n → ℚ) :
    (∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      (∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, (a i : ℝ) * x i ^ 2 = 0) ∧
        ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧
          ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨⟨fun i => (x i : ℝ), hmd_map_ne_zero hx, by simpa using hmd_cast (L := ℝ) a x h⟩,
      fun p _ => ⟨fun i => (x i : ℚ_[p]), hmd_map_ne_zero hx,
        by simpa using hmd_cast (L := ℚ_[p]) a x h⟩⟩
  · rintro ⟨hreal, hpadic⟩
    by_cases ha : ∀ i, a i ≠ 0
    · exact hmd_aux n a ha hreal hpadic
    · push Not at ha
      obtain ⟨i, hi⟩ := ha
      refine ⟨Pi.single i 1, by simp, ?_⟩
      simp [Pi.single_apply, hi]

/-- **Hasse–Minkowski theorem for representations by diagonal forms over $\mathbb{Q}$.** Let
$a_1, \dots, a_n$ be nonzero rational numbers and let $c$ be a rational number. Then
$a_1 x_1^2 + \dots + a_n x_n^2 = c$ has a solution $x \in \mathbb{Q}^n$ if and only if it has a
solution $x \in \mathbb{R}^n$ and a solution $x \in \mathbb{Q}_p^n$ for every prime $p$.

The value $c = 0$ is allowed: then $x = 0$ is a solution over every field.

The proof applies `Rat.exists_diagonal_eq_zero_iff_forall_local` to
$-c z^2 + a_1 x_1^2 + \dots + a_n x_n^2$: a rational zero with $z \neq 0$ gives a solution, and a
zero with $z = 0$ is a nonzero zero of the form, which then takes every value
(`exists_sum_mul_sq_eq_of_isotropic`).

The statement follows from A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT,
Fall 2013, Lecture 11, Theorem 11.12, p. 4, which is about representing $0$,
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>, by the argument in the proof of
Lemma 10.2, Lecture 10, p. 1: a nondegenerate form that represents $0$ represents every element,
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes10.pdf>. -/
theorem exists_diagonal_eq_iff_forall_local {n : ℕ} (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) (c : ℚ) :
    (∃ x : Fin n → ℚ, ∑ i, a i * x i ^ 2 = c) ↔
      (∃ x : Fin n → ℝ, ∑ i, (a i : ℝ) * x i ^ 2 = c) ∧
        ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℚ_[p], ∑ i, (a i : ℚ_[p]) * x i ^ 2 = c := by
  constructor
  · rintro ⟨x, h⟩
    exact ⟨⟨fun i => (x i : ℝ), hmd_cast a x h⟩, fun p _ =>
      ⟨fun i => (x i : ℚ_[p]), hmd_cast a x h⟩⟩
  · rintro ⟨⟨xr, hxr⟩, hpadic⟩
    -- the form `-c z ^ 2 + ∑ aᵢ xᵢ ^ 2` in `n + 1` variables
    have key : ∀ (L : Type) [Field L] [CharZero L] (x : Fin n → L),
        ∑ i, (a i : L) * x i ^ 2 = c →
          (Fin.cons (1 : L) x : Fin (n + 1) → L) ≠ 0 ∧
            ∑ i, ((Fin.cons (-c) a : Fin (n + 1) → ℚ) i : L) *
              (Fin.cons (1 : L) x : Fin (n + 1) → L) i ^ 2 = 0 := by
      intro L _ _ x hx
      refine ⟨Function.ne_iff.2 ⟨0, by simp⟩, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, one_pow, mul_one, hx]
      push_cast
      ring
    obtain ⟨y, hy, h⟩ := (exists_diagonal_eq_zero_iff_forall_local
      (Fin.cons (-c) a : Fin (n + 1) → ℚ)).2
      ⟨⟨_, key ℝ xr hxr⟩, fun p _ => by
        obtain ⟨x, hx⟩ := hpadic p
        exact ⟨_, key ℚ_[p] x hx⟩⟩
    rw [Fin.sum_univ_succ] at h
    simp only [Fin.cons_zero, Fin.cons_succ] at h
    by_cases hz : y 0 = 0
    · have hx : Fin.tail y ≠ 0 := by
        intro ht
        apply hy
        rw [← Fin.cons_self_tail y, hz, ht]
        funext j
        refine Fin.cases ?_ (fun j => ?_) j <;> simp
      rw [hz] at h
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_add] at h
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      exact exists_sum_mul_sq_eq_of_isotropic two_ne_zero (x := Fin.tail y) (ha i)
        (by simpa using hi) h c
    · refine ⟨fun i => y i.succ / y 0, ?_⟩
      have e : ∑ i, a i * (y i.succ / y 0) ^ 2 = (∑ i, a i * y i.succ ^ 2) / y 0 ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
      rw [e, div_eq_iff (pow_ne_zero 2 hz)]
      linear_combination h

section General

open Matrix

private theorem hmd_qf_eq {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (x : Fin n → R) : ∑ i, ∑ j, M i j * x i * x j = x ⬝ᵥ (M *ᵥ x) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem hmd_qf_mulVec {R : Type*} [CommRing R] {n m : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (y : Fin m → R) :
    (P *ᵥ y) ⬝ᵥ (M *ᵥ (P *ᵥ y)) = y ⬝ᵥ ((Pᵀ * M * P) *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y Pᵀ, vecMul_transpose]

private theorem hmd_single_qf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (Pi.single i 1 : Fin n → ℚ) ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  simp [dotProduct, mulVec, Pi.single_apply]

private theorem hmd_polarize {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℚ}
    (h : ∀ y, y ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (N *ᵥ y)) (i j : Fin n) :
    M i j + M j i = N i j + N j i := by
  have hs : ∀ (L : Matrix (Fin n) (Fin n) ℚ),
      (Pi.single i 1 + Pi.single j 1 : Fin n → ℚ) ⬝ᵥ (L *ᵥ (Pi.single i 1 + Pi.single j 1)) =
        L i i + L i j + L j i + L j j := by
    intro L
    simp only [mulVec_add, dotProduct_add, add_dotProduct, hmd_single_qf]
    ring
  have h1 := h (Pi.single i 1)
  have h2 := h (Pi.single j 1)
  have h3 := h (Pi.single i 1 + Pi.single j 1)
  rw [hmd_single_qf, hmd_single_qf] at h1 h2
  rw [hs, hs] at h3
  linarith

private theorem hmd_qf_of_polar {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) K} (h : ∀ i j, M i j + M j i = N i j + N j i) (y : Fin n → K) :
    y ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (N *ᵥ y) := by
  rw [← hmd_qf_eq, ← hmd_qf_eq]
  have key : ∀ L : Matrix (Fin n) (Fin n) K, 2 * ∑ i, ∑ j, L i j * y i * y j =
      ∑ i, ∑ j, (L i j + L j i) * y i * y j := by
    intro L
    rw [two_mul]
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine mul_left_cancel₀ h2 ?_
  rw [key, key]
  simp only [h]

/-- Diagonalization over `ℚ`, as matrices: a change of variables `P` with inverse `R` turns the
form of `A` into a weighted sum of squares. -/
private theorem hmd_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    ∃ (m : ℕ) (P : Matrix (Fin n) (Fin m) ℚ) (R : Matrix (Fin m) (Fin n) ℚ) (w : Fin m → ℚ),
      R * P = 1 ∧ P * R = 1 ∧ ∀ y : Fin m → ℚ,
        (P *ᵥ y) ⬝ᵥ (A *ᵥ (P *ᵥ y)) = y ⬝ᵥ (diagonal w *ᵥ y) := by
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares
    (LinearMap.BilinMap.toQuadraticMap
      (toLinearMap₂' ℚ A : LinearMap.BilinMap ℚ (Fin n → ℚ) ℚ))
  refine ⟨_, LinearMap.toMatrix' e.toLinearEquiv.symm.toLinearMap,
    LinearMap.toMatrix' e.toLinearEquiv.toLinearMap, w, ?_, ?_, fun y => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  · rw [LinearMap.toMatrix'_mulVec, ← toLinearMap₂'_apply',
      ← LinearMap.BilinMap.toQuadraticMap_apply,
      ← e.map_app]
    have hy : ∀ k, e (e.symm y) k = y k := fun k =>
      congrFun (e.toLinearEquiv.apply_symm_apply y) k
    simp only [LinearEquiv.coe_coe, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
      mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun k _ => by erw [hy k]; ring

/-- The diagonalization over `ℚ` carries over to every field of characteristic `0`. -/
private theorem hmd_diag_map {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {P : Matrix (Fin n) (Fin m) ℚ} {w : Fin m → ℚ}
    (h : ∀ y : Fin m → ℚ, (P *ᵥ y) ⬝ᵥ (A *ᵥ (P *ᵥ y)) = y ⬝ᵥ (diagonal w *ᵥ y))
    (L : Type*) [Field L] [CharZero L] (y : Fin m → L) :
    ∑ i, ∑ j, (A i j : L) * (P.map (Rat.cast : ℚ → L) *ᵥ y) i *
        (P.map (Rat.cast : ℚ → L) *ᵥ y) j = ∑ k, (w k : L) * y k ^ 2 := by
  have hpol := hmd_polarize (M := Pᵀ * A * P) (N := diagonal w)
    (fun y => by rw [← hmd_qf_mulVec, h])
  have hpolL : ∀ i j, ((Pᵀ * A * P).map (Rat.castHom L)) i j +
      ((Pᵀ * A * P).map (Rat.castHom L)) j i =
        (diagonal fun k => (w k : L)) i j + (diagonal fun k => (w k : L)) j i := by
    intro i j
    have := congrArg (Rat.cast : ℚ → L) (hpol i j)
    rw [Rat.cast_add, Rat.cast_add] at this
    simp only [Matrix.map_apply, Rat.coe_castHom]
    rcases eq_or_ne i j with rfl | hij
    · simpa only [diagonal_apply_eq] using this
    · simpa only [diagonal_apply_ne _ hij, diagonal_apply_ne _ hij.symm, Rat.cast_zero,
        add_zero] using this
  have e := hmd_qf_of_polar two_ne_zero hpolL y
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map, ← hmd_qf_mulVec] at e
  simp only [Rat.coe_castHom] at e
  change ∑ i, ∑ j, (A.map (Rat.cast : ℚ → L)) i j * (P.map (Rat.cast : ℚ → L) *ᵥ y) i *
    (P.map (Rat.cast : ℚ → L) *ᵥ y) j = _
  rw [hmd_qf_eq, e]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem hmd_diag_sum {R : Type*} [CommRing R] {m : ℕ} (w y : Fin m → R) :
    y ⬝ᵥ (diagonal w *ᵥ y) = ∑ k, w k * y k ^ 2 := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem hmd_cast2 {L : Type*} [Field L] [CharZero L] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → ℚ) {c : ℚ} (h : ∑ i, ∑ j, A i j * x i * x j = c) :
    ∑ i, ∑ j, (A i j : L) * (x i : L) * (x j : L) = (c : L) := by
  have := congrArg (Rat.cast : ℚ → L) h
  push_cast at this
  exact this

/-- The change of variables of `hmd_diag`, over a field of characteristic `0`: the values of the
form of `A` are those of the weighted sum of squares. -/
private theorem hmd_values {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {P : Matrix (Fin n) (Fin m) ℚ} {R : Matrix (Fin m) (Fin n) ℚ} {w : Fin m → ℚ}
    (hPR : P * R = 1)
    (h : ∀ y : Fin m → ℚ, (P *ᵥ y) ⬝ᵥ (A *ᵥ (P *ᵥ y)) = y ⬝ᵥ (diagonal w *ᵥ y))
    (L : Type*) [Field L] [CharZero L] (x : Fin n → L) :
    (R.map (Rat.cast : ℚ → L) *ᵥ x = 0 → x = 0) ∧
      ∑ i, ∑ j, (A i j : L) * x i * x j =
        ∑ k, (w k : L) * (R.map (Rat.cast : ℚ → L) *ᵥ x) k ^ 2 := by
  have hPRL : P.map (Rat.castHom L) * R.map (Rat.castHom L) = 1 := by
    rw [← Matrix.map_mul, hPR, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [Rat.coe_castHom] at hPRL
  have hx : P.map (Rat.cast : ℚ → L) *ᵥ (R.map (Rat.cast : ℚ → L) *ᵥ x) = x := by
    rw [mulVec_mulVec, hPRL, one_mulVec]
  refine ⟨fun h0 => by rw [← hx, h0, mulVec_zero], ?_⟩
  rw [← hmd_diag_map h L, hx]

/-- **Hasse–Minkowski theorem for zeros of rational quadratic forms.** Let
$f(x) = \sum_{i,j=1}^n a_{ij} x_i x_j$ with $a_{ij} \in \mathbb{Q}$. Then $f$ has a zero
$x \neq 0$ in $\mathbb{Q}^n$ if and only if it has a zero $x \neq 0$ in $\mathbb{R}^n$ and a zero
$x \neq 0$ in $\mathbb{Q}_p^n$ for every prime $p$.

The matrix $(a_{ij})$ need not be symmetric (the source takes $a_{ij} = a_{ji}$; the form is the
same as that of the symmetrized matrix), and $n$ may be $0$ (then no side holds).

The proof diagonalizes the form over $\mathbb{Q}$ (`QuadraticForm.equivalent_weightedSumSquares`),
carries the change of variables to $\mathbb{R}$ and each $\mathbb{Q}_p$, and applies
`Rat.exists_diagonal_eq_zero_iff_forall_local`.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture
11, Theorem 11.12 and its proof, pp. 4–5, which first reduces to diagonal forms,
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>. -/
theorem exists_quadratic_eq_zero_iff_forall_local {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, ∑ j, A i j * x i * x j = 0) ↔
      (∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, ∑ j, (A i j : ℝ) * x i * x j = 0) ∧
        ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧
          ∑ i, ∑ j, (A i j : ℚ_[p]) * x i * x j = 0 := by
  obtain ⟨m, P, R, w, hRP, hPR, h⟩ := hmd_diag A
  have loc : ∀ (L : Type) [Field L] [CharZero L],
      (∃ x : Fin n → L, x ≠ 0 ∧ ∑ i, ∑ j, (A i j : L) * x i * x j = 0) →
        ∃ y : Fin m → L, y ≠ 0 ∧ ∑ k, (w k : L) * y k ^ 2 = 0 := by
    rintro L _ _ ⟨x, hx, hq⟩
    obtain ⟨hinj, hval⟩ := hmd_values hPR h L x
    exact ⟨_, fun h0 => hx (hinj h0), by rw [← hval, hq]⟩
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨⟨fun i => (x i : ℝ), hmd_map_ne_zero hx, by simpa using hmd_cast2 (L := ℝ) A x hq⟩,
      fun p _ => ⟨fun i => (x i : ℚ_[p]), hmd_map_ne_zero hx,
        by simpa using hmd_cast2 (L := ℚ_[p]) A x hq⟩⟩
  · rintro ⟨hr, hp⟩
    obtain ⟨y, hy, hy0⟩ := (exists_diagonal_eq_zero_iff_forall_local w).2
      ⟨loc ℝ hr, fun p _ => loc ℚ_[p] (hp p)⟩
    refine ⟨P *ᵥ y, fun h0 => hy ?_, ?_⟩
    · have := congrArg (R *ᵥ ·) h0
      simpa [mulVec_mulVec, hRP] using this
    · rw [hmd_qf_eq, h, hmd_diag_sum, hy0]

/-- **Hasse–Minkowski theorem for representations of rationals.** Let
$f(x) = \sum_{i,j=1}^n a_{ij} x_i x_j$ with $a_{ij} = a_{ji} \in \mathbb{Q}$ and
$\det(a_{ij}) \neq 0$, and let $c \in \mathbb{Q}$. Then $f(x) = c$ has a solution
$x \in \mathbb{Q}^n$ if and only if it has a solution $x \in \mathbb{R}^n$ and a solution
$x \in \mathbb{Q}_p^n$ for every prime $p$.

The value $c = 0$ is allowed: then $x = 0$ is a solution over every field.

The proof diagonalizes $f$ over $\mathbb{Q}$ to $w_1 y_1^2 + \dots + w_n y_n^2$, where every
$w_k \neq 0$ as $\det(a_{ij}) \neq 0$, and applies `Rat.exists_diagonal_eq_iff_forall_local`.

The statement follows from A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT,
Fall 2013, Lecture 11, Theorem 11.12, p. 4, which is about representing $0$,
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>, by the argument in the proof of
Lemma 10.2, Lecture 10, p. 1: a nondegenerate form that represents $0$ represents every element,
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes10.pdf>. -/
theorem exists_quadratic_eq_iff_forall_local {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : A.IsSymm) (hdet : A.det ≠ 0) (c : ℚ) :
    (∃ x : Fin n → ℚ, ∑ i, ∑ j, A i j * x i * x j = c) ↔
      (∃ x : Fin n → ℝ, ∑ i, ∑ j, (A i j : ℝ) * x i * x j = c) ∧
        ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℚ_[p],
          ∑ i, ∑ j, (A i j : ℚ_[p]) * x i * x j = c := by
  obtain ⟨m, P, R, w, hRP, hPR, h⟩ := hmd_diag A
  -- the weights are nonzero
  have hw : ∀ k, w k ≠ 0 := by
    intro k hk
    have hpol := hmd_polarize (M := Pᵀ * A * P) (N := diagonal w)
      (fun y => by rw [← hmd_qf_mulVec, h])
    have hsymm : ∀ i j, (Pᵀ * A * P) i j = (Pᵀ * A * P) j i := by
      intro i j
      have hT : (Pᵀ * A * P)ᵀ = Pᵀ * A * P := by
        rw [transpose_mul, transpose_mul, transpose_transpose, hA.eq, Matrix.mul_assoc]
      have := congrFun (congrFun hT j) i
      rw [transpose_apply] at this
      exact this
    have hcol : (Pᵀ * A * P) *ᵥ Pi.single k 1 = 0 := by
      funext i
      have hik := hpol i k
      rw [hsymm k i] at hik
      have hd : diagonal w i k + diagonal w k i = 0 := by
        rcases eq_or_ne i k with rfl | hne
        · simp [hk]
        · simp [diagonal_apply_ne _ hne, diagonal_apply_ne _ hne.symm]
      simp only [mulVec_single_one, Pi.zero_apply, Matrix.col_apply]
      linarith
    set v := P *ᵥ Pi.single k 1 with hv
    have hv0 : v ≠ 0 := by
      intro h0
      have := congrArg (R *ᵥ ·) h0
      simp only [hv, mulVec_mulVec, hRP, one_mulVec, mulVec_zero] at this
      have hk1 := congrFun this k
      simp only [Pi.single_eq_same, Pi.zero_apply] at hk1
      exact one_ne_zero hk1
    have hAv : A *ᵥ v = 0 := by
      have h1 : Pᵀ *ᵥ (A *ᵥ v) = 0 := by
        rw [hv, mulVec_mulVec, mulVec_mulVec]
        exact hcol
      have hRT : Rᵀ * Pᵀ = 1 := by rw [← transpose_mul, hPR, transpose_one]
      have := congrArg (Rᵀ *ᵥ ·) h1
      simp only [mulVec_zero] at this
      rwa [mulVec_mulVec, hRT, one_mulVec] at this
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hAv⟩)
  constructor
  · rintro ⟨x, hq⟩
    exact ⟨⟨fun i => (x i : ℝ), hmd_cast2 A x hq⟩, fun p _ =>
      ⟨fun i => (x i : ℚ_[p]), hmd_cast2 A x hq⟩⟩
  · rintro ⟨⟨xr, hr⟩, hp⟩
    obtain ⟨y, hy⟩ := (exists_diagonal_eq_iff_forall_local w hw c).2
      ⟨⟨_, by rw [← (hmd_values hPR h ℝ xr).2, hr]⟩, fun p _ => by
        obtain ⟨x, hx⟩ := hp p
        exact ⟨_, by rw [← (hmd_values hPR h ℚ_[p] x).2, hx]⟩⟩
    exact ⟨P *ᵥ y, by rw [hmd_qf_eq, h, hmd_diag_sum, hy]⟩

end General

end Rat
