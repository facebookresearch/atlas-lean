/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.Algebra.Group.Even
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation

/-!
# Isotropic quadratic forms over a field

Elementary facts about quadratic forms over a field that represent `0` nontrivially, used in
the proof of the Hasse–Minkowski theorem:

* `QuadraticMap.Nondegenerate.exists_apply_eq_of_isotropic`: over a field in which `2` is
  invertible, a nondegenerate quadratic form with a nonzero zero represents every element.
* `exists_sum_mul_sq_eq_of_isotropic` and its two-variable case
  `exists_mul_sq_add_mul_sq_eq_of_isotropic`: the same for diagonal forms `∑ aⱼ yⱼ²`, asking only
  that the zero have a nonzero coordinate with a nonzero coefficient.
* `exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff`: the diagonal binary form `a x² + b y²` has a
  nonzero zero if and only if `-ab` is a square.

Sources: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 9, Theorem 9.9, p. 3, Lecture 10, proof of Lemma 10.2, p. 1, and Lecture 11, §11.1,
p. 1.
-/

public section

namespace QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **A nondegenerate quadratic form with a nonzero zero represents every element.** Let $K$ be a
field in which $2$ is invertible (that is, of characteristic different from $2$), let $V$ be a
$K$-vector space and let $Q$ be a nondegenerate quadratic form on $V$. If $Q(v) = 0$ for some
nonzero $v \in V$, then $Q$ represents every element of $K$: for every $c \in K$ there is
$w \in V$ with $Q(w) = c$.

Nondegeneracy is `QuadraticMap.Nondegenerate`; as $2$ is invertible, it says that the symmetric
bilinear form $B$ with $Q(x) = B(x, x)$ is nondegenerate
(`QuadraticMap.nondegenerate_associated_iff`). The statement needs no finiteness of $V$.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 9, Theorem 9.9 and its proof, p. 3. -/
theorem Nondegenerate.exists_apply_eq_of_isotropic [Invertible (2 : K)]
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {v : V} (hv : v ≠ 0) (hQv : Q v = 0)
    (c : K) : ∃ w : V, Q w = c := by
  have hB : (polarBilin Q).Nondegenerate := nondegenerate_polar_iff.mpr hQ
  obtain ⟨w, hw⟩ : ∃ w : V, polar Q v w ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hv (hB.1 v fun w => by simpa using h w)
  refine ⟨((c - Q w) / polar Q v w) • v + w, ?_⟩
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_left, hQv, smul_eq_mul,
    smul_eq_mul]
  field_simp
  ring

end QuadraticMap

/-- **A diagonal form with a nonzero zero represents every element.** Let $K$ be a field in which
$2 \neq 0$, let $\iota$ be a finite type and let $a, x \colon \iota \to K$ with
$\sum_j a_j x_j^2 = 0$. If $a_i \neq 0$ and $x_i \neq 0$ for some $i \in \iota$, then for every
$t \in K$ there is $y \colon \iota \to K$ with $\sum_j a_j y_j^2 = t$.

When every $a_j \neq 0$, the form $\sum_j a_j y_j^2$ is nondegenerate and this is the diagonal case
of `QuadraticMap.Nondegenerate.exists_apply_eq_of_isotropic`; here only the coefficient at one
nonzero coordinate of the zero needs to be nonzero. The proof is the one of the source with
$w = e_i$: $y = s x + e_i$ for the $s \in K$ with $2 s a_i x_i + a_i = t$.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 9, Theorem 9.9 and its proof, p. 3,
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes9.pdf>. -/
theorem exists_sum_mul_sq_eq_of_isotropic {K ι : Type*} [Field K] [Fintype ι]
    (h2 : (2 : K) ≠ 0) {a x : ι → K} {i : ι} (hai : a i ≠ 0) (hxi : x i ≠ 0)
    (h : ∑ j, a j * x j ^ 2 = 0) (t : K) : ∃ y : ι → K, ∑ j, a j * y j ^ 2 = t := by
  classical
  set s := (t - a i) / (2 * a i * x i) with hs
  have hs' : 2 * s * (a i * x i) = t - a i := by
    rw [hs]
    field_simp [hai, hxi]
  refine ⟨fun j => s * x j + (Pi.single i (1 : K) : ι → K) j, ?_⟩
  have e : ∀ j, a j * (s * x j + (Pi.single i (1 : K) : ι → K) j) ^ 2 =
      s ^ 2 * (a j * x j ^ 2) + 2 * s * (a j * x j * (Pi.single i (1 : K) : ι → K) j) +
        a j * (Pi.single i (1 : K) : ι → K) j ^ 2 := fun j => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h, mul_zero, zero_add]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_pow, one_pow,
    zero_pow two_ne_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  linear_combination hs'

/-- **When a diagonal binary form has a nonzero zero.** Let $K$ be a field and let
$a, b \in K$. Then $a x^2 + b y^2$ has a zero $(x, y) \in K^2$ with $(x, y) \neq (0, 0)$ if and
only if $-ab$ is a square in $K$.

When $K$ has characteristic different from $2$ and $a, b \neq 0$, the form $a x^2 + b y^2$ is
nondegenerate, and this is the isotropy criterion for nondegenerate binary diagonal forms. In
characteristic $2$ the form is degenerate even for $a, b \neq 0$. The square criterion itself
holds over every field and for all $a, b$, including when $a = 0$ or $b = 0$, where both sides
are true.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 11, §11.1, p. 1, which states the criterion for the nondegenerate form
$a x^2 + b y^2$ and notes that it holds over any field. -/
theorem exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff {K : Type*} [Field K] (a b : K) :
    (∃ x y : K, (x, y) ≠ (0, 0) ∧ a * x ^ 2 + b * y ^ 2 = 0) ↔ IsSquare (-(a * b)) := by
  constructor
  · rintro ⟨x, y, hxy, h⟩
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    by_cases hy : y = 0
    · subst hy
      have hx : x = 0 := by simpa [ha] using h
      exact absurd (by simp [hx]) hxy
    refine ⟨a * x / y, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
    linear_combination (-a) * h
  · rintro ⟨c, hc⟩
    by_cases ha : a = 0
    · exact ⟨1, 0, by simp, by simp [ha]⟩
    refine ⟨c, a, by simp [ha], ?_⟩
    linear_combination a * hc.symm

/-- **A diagonal binary form with a nonzero zero represents every element.** Let $K$ be a field in
which $2 \neq 0$ and let $a, b \in K$ be nonzero. If $a x_0^2 + b y_0^2 = 0$ for some
$(x_0, y_0) \neq (0, 0)$ in $K^2$, then for every $t \in K$ there are $x, y \in K$ with
$a x^2 + b y^2 = t$.

This is the case of two variables of `exists_sum_mul_sq_eq_of_isotropic`.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 9, Theorem 9.9, p. 3, and Lecture 10, proof of Lemma 10.2, p. 1 ("the
non-degenerate quadratic form $ax^2 + by^2$ represents 0, hence it represents every element"),
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes10.pdf>. -/
theorem exists_mul_sq_add_mul_sq_eq_of_isotropic {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {x₀ y₀ : K} (h0 : (x₀, y₀) ≠ (0, 0))
    (hz : a * x₀ ^ 2 + b * y₀ ^ 2 = 0) (t : K) : ∃ x y : K, a * x ^ 2 + b * y ^ 2 = t := by
  have hz' : ∑ j, ![a, b] j * ![x₀, y₀] j ^ 2 = 0 := by simpa [Fin.sum_univ_two] using hz
  obtain ⟨y, hy⟩ : ∃ y : Fin 2 → K, ∑ j, ![a, b] j * y j ^ 2 = t := by
    by_cases hx : x₀ = 0
    · have hy₀ : y₀ ≠ 0 := fun hy₀ => h0 (by rw [hx, hy₀])
      exact exists_sum_mul_sq_eq_of_isotropic h2 (i := 1) (by simpa using hb)
        (by simpa using hy₀) hz' t
    · exact exists_sum_mul_sq_eq_of_isotropic h2 (i := 0) (by simpa using ha)
        (by simpa using hx) hz' t
  exact ⟨y 0, y 1, by simpa [Fin.sum_univ_two] using hy⟩
