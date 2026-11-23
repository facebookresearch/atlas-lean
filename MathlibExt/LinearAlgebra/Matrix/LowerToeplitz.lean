/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic

@[expose]
public section

namespace Matrix

/-- **Lower-triangular Toeplitz matrix.** Let $R$ be a set with a zero element $0$ and let
$a = (a_0, a_1, a_2, \dots)$ be a sequence in $R$. The lower-triangular Toeplitz matrix of $a$
is the matrix with rows and columns indexed by $\mathbb{N}$ whose $(i, j)$ entry is $a_{i-j}$
when $j \le i$ and $0$ when $j > i$. In particular it is constant along each diagonal and
vanishes strictly above the main diagonal.

Source: Ming-Jian Ding and Jiang Zeng, "Some New Results on the Minuscule
Polynomials of Type A," Journal of Integer Sequences 28 (2025), lines 640-653.
URL: `https://cs.uwaterloo.ca/journals/JIS/VOL28/Zeng/zeng26.tex`.
Full TeX SHA-256:
`2a5a8d59641da82808dae4aea4c6583f460dd36bc175d9dce912a265a5ce7a1a`.
Exact source-span SHA-256 including terminal LF:
`63b54ec23b76494d198b28837c6622e4bbe92e064580f13cde8f3d1523ac28e3`.
Grounded concept: `jis_grounded_6e7ca1c0ec8f4d9d675959b3`. -/
def lowerToeplitz {R : Type*} [Zero R] (a : ℕ → R) : Matrix ℕ ℕ R :=
  fun i j => if j ≤ i then a (i - j) else 0

/-- **Entries on and below the diagonal of a lower-triangular Toeplitz matrix.** Let $R$ be a
set with a zero element and $a = (a_0, a_1, \dots)$ a sequence in $R$. For natural numbers
$j \le i$, the $(i, j)$ entry of the lower-triangular Toeplitz matrix of $a$ is $a_{i-j}$. -/
@[simp]
theorem lowerToeplitz_apply_of_le {R : Type*} [Zero R] (a : ℕ → R) {i j : ℕ}
    (h : j ≤ i) : lowerToeplitz a i j = a (i - j) := by
  simp [lowerToeplitz, h]

/-- **Entries above the diagonal of a lower-triangular Toeplitz matrix.** Let $R$ be a set with
a zero element and $a = (a_0, a_1, \dots)$ a sequence in $R$. For natural numbers $i < j$, the
$(i, j)$ entry of the lower-triangular Toeplitz matrix of $a$ is $0$. -/
@[simp]
theorem lowerToeplitz_apply_of_gt {R : Type*} [Zero R] (a : ℕ → R) {i j : ℕ}
    (h : i < j) : lowerToeplitz a i j = 0 := by
  simp [lowerToeplitz, Nat.not_le.mpr h]

/-- **Diagonal entries of a lower-triangular Toeplitz matrix.** Let $R$ be a set with a zero
element and $a = (a_0, a_1, \dots)$ a sequence in $R$. For every natural number $i$, the
$(i, i)$ entry of the lower-triangular Toeplitz matrix of $a$ is $a_0$. -/
@[simp]
theorem lowerToeplitz_apply_diag {R : Type*} [Zero R] (a : ℕ → R) (i : ℕ) :
    lowerToeplitz a i i = a 0 := by
  have h : i ≤ i := Nat.le_refl i
  rw [lowerToeplitz_apply_of_le a h, Nat.sub_self]

end Matrix
