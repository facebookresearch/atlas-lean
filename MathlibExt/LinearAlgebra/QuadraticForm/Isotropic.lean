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

/-!
# Isotropic quadratic forms over a field

Two elementary facts about quadratic forms over a field that represent `0` nontrivially, used in
the proof of the Hasse–Minkowski theorem:

* `QuadraticMap.Nondegenerate.exists_apply_eq_of_isotropic`: over a field in which `2` is
  invertible, a nondegenerate quadratic form with a nonzero zero represents every element.
* `exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff`: the diagonal binary form `a x² + b y²` has a
  nonzero zero if and only if `-ab` is a square.

Sources: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 9, Theorem 9.9, p. 3, and Lecture 11, §11.1, p. 1.
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
