/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

@[expose] public section

namespace MetaMathlibExt

variable {R : Type*} [CommRing R]

/-- **Entries of the Hurwitz matrix.** For sequences $a, b \colon \mathbb{N} \to R$ in a commutative
ring $R$ and indices $i, j \in \mathbb{N}$ (counted from zero), the Hurwitz entry $h_{ij}$ is $0$ if
$i \ge 2j + 2$; otherwise it is $a_{j - i/2}$ if $i$ is even and $b_{j - (i-1)/2}$ if $i$ is odd.

Source: Barry's definition in the Journal of Integer Sequences, vol. 15. -/
def hurwitzEntry (a b : ℕ → R) (i j : ℕ) : R :=
  if 2 * j + 2 ≤ i then 0
  else if i % 2 = 0 then a (j - i / 2)
  else b (j - (i - 1) / 2)

/-- **Hurwitz matrix.** For sequences $a, b \colon \mathbb{N} \to R$ in a commutative ring $R$ and
$n \in \mathbb{N}$, the Hurwitz matrix of order $n$ is the $(n+1) \times (n+1)$ matrix whose entry
in row $i$ and column $j$, for $0 \le i, j \le n$, is the Hurwitz entry $h_{ij}$ of $a$ and $b$.

Source: concept `jis_term_6793c0b8b44e37675229ccfc`,
`https://cs.uwaterloo.ca/journals/JIS/VOL15/Barry5/barry223.tex`. -/
def hurwitzMatrix (a b : ℕ → R) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => hurwitzEntry a b i.val j.val

/-- **Hurwitz transform.** For sequences $a, b \colon \mathbb{N} \to R$ in a commutative ring $R$,
the Hurwitz transform of $a$ and $b$ is the sequence whose $n$-th term, for $n \in \mathbb{N}$, is
the determinant of the Hurwitz matrix of $a$ and $b$ of order $n$. -/
def hurwitzTransform (a b : ℕ → R) (n : ℕ) : R :=
  (hurwitzMatrix a b n).det

/-- **Hurwitz transform of a single sequence.** For a sequence $a \colon \mathbb{N} \to R$ in a
commutative ring $R$, its Hurwitz transform is the Hurwitz transform of $a$ and the sequence
$(0^k)_{k \in \mathbb{N}}$, which is $1$ at $k = 0$ and $0$ for $k \ge 1$. -/
def hurwitzSingle (a : ℕ → R) (n : ℕ) : R :=
  hurwitzTransform a (fun k => (0 : R) ^ k) n

theorem hurwitzEntry_eq_zero_of_le (a b : ℕ → R) {i j : ℕ}
    (h : 2 * j + 2 ≤ i) : hurwitzEntry a b i j = 0 := by
  simp [hurwitzEntry, h]

theorem hurwitzEntry_of_even (a b : ℕ → R) {i j : ℕ}
    (h : ¬2 * j + 2 ≤ i) (he : i % 2 = 0) :
    hurwitzEntry a b i j = a (j - i / 2) := by
  simp [hurwitzEntry, h, he]

theorem hurwitzEntry_of_odd (a b : ℕ → R) {i j : ℕ}
    (h : ¬2 * j + 2 ≤ i) (ho : i % 2 ≠ 0) :
    hurwitzEntry a b i j = b (j - (i - 1) / 2) := by
  simp [hurwitzEntry, h, ho]

theorem hurwitz_half_le_of_even {i j : ℕ}
    (h : ¬2 * j + 2 ≤ i) (he : i % 2 = 0) : i / 2 ≤ j := by
  omega

theorem hurwitz_pred_half_le_of_odd {i j : ℕ}
    (h : ¬2 * j + 2 ≤ i) (_ho : i % 2 ≠ 0) : (i - 1) / 2 ≤ j := by
  omega

theorem hurwitzTransform_zero (a b : ℕ → R) :
    hurwitzTransform a b 0 = a 0 := by
  unfold hurwitzTransform hurwitzMatrix
  rw [Matrix.det_fin_one]
  simp [Matrix.of_apply, hurwitzEntry]

theorem hurwitzTransform_one (a b : ℕ → R) :
    hurwitzTransform a b 1 = a 0 * b 1 - a 1 * b 0 := by
  unfold hurwitzTransform hurwitzMatrix
  rw [Matrix.det_fin_two]
  simp [Matrix.of_apply, hurwitzEntry]

end MetaMathlibExt
