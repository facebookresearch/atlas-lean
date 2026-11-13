/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.FunProp

@[expose] public section

namespace MathlibExt.Geometry.Manifold.MorseTheoryWanted

/-- **Morse quadratic form.** For natural numbers $k$ and $n$, the Morse quadratic form of index
$k$ on $\mathbb{R}^n$, with coordinates $v_0, \dots, v_{n-1}$, is the function
$Q_{k,n} \colon \mathbb{R}^n \to \mathbb{R}$ given by
$Q_{k,n}(v) = \sum_{i=0}^{n-1} \varepsilon_i v_i^2$, where $\varepsilon_i = -1$ if $i < k$ and
$\varepsilon_i = 1$ if $i \ge k$. In particular, if $k \ge n$ every coefficient is $-1$. -/
def morseQuadratic (k n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, (if (i : ℕ) < k then (-1 : ℝ) else 1) * (v i) ^ 2

/-- **The Morse quadratic form vanishes at the origin.** For all natural numbers $k$ and $n$, the
Morse quadratic form $Q_{k,n}$ of index $k$ on $\mathbb{R}^n$ satisfies $Q_{k,n}(0) = 0$. -/
lemma morseQuadratic_zero (k n : ℕ) : morseQuadratic k n 0 = 0 := by
  simp [morseQuadratic]

/-- **Smoothness of the Morse quadratic form.** For all natural numbers $k$ and $n$, the Morse
quadratic form $Q_{k,n} \colon \mathbb{R}^n \to \mathbb{R}$ of index $k$ is $C^\infty$. -/
lemma contDiff_morseQuadratic (k n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (morseQuadratic k n) := by
  unfold morseQuadratic
  fun_prop

/-- **The Morse quadratic form of index zero.** For every natural number $n$, the Morse quadratic
form $Q_{0,n}$ of index $0$ on $\mathbb{R}^n$ satisfies $Q_{0,n}(v) = \|v\|^2$ for every
$v \in \mathbb{R}^n$, where $\|v\|$ is the Euclidean norm of $v$. -/
lemma morseQuadratic_zero_index (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    morseQuadratic 0 n v = ‖v‖ ^ 2 := by
  have hone : ∀ i : Fin n, (if (i : ℕ) < 0 then (-1 : ℝ) else 1) = 1 := by
    intro i
    simp
  simp only [morseQuadratic, hone, one_mul]
  exact (EuclideanSpace.real_norm_sq_eq v).symm

/-- **The Morse quadratic form when the index is at least the dimension.** If $n \le k$, then the
Morse quadratic form $Q_{k,n}$ of index $k$ on $\mathbb{R}^n$ satisfies $Q_{k,n}(v) = -\|v\|^2$
for every $v \in \mathbb{R}^n$, where $\|v\|$ is the Euclidean norm of $v$. -/
lemma morseQuadratic_of_le {k n : ℕ} (h : n ≤ k) (v : EuclideanSpace ℝ (Fin n)) :
    morseQuadratic k n v = -‖v‖ ^ 2 := by
  have hif : ∀ i : Fin n, (if (i : ℕ) < k then (-1 : ℝ) else 1) = -1 := by
    intro i
    simp [lt_of_lt_of_le i.is_lt h]
  simp only [morseQuadratic, hif, neg_one_mul, Finset.sum_neg_distrib]
  rw [EuclideanSpace.real_norm_sq_eq]

end MathlibExt.Geometry.Manifold.MorseTheoryWanted
