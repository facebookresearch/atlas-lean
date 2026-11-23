/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Cast.Defs

namespace MetaMathlibExt

@[expose] public section

/-- **Tridiagonal Stieltjes production matrix.** Let $R$ be an additive monoid with one and let
$a_1, b_1, a, b \in R$. The Stieltjes matrix $S$ is the infinite matrix with rows and columns
indexed by $\mathbb{N} = \{0, 1, 2, \dots\}$ whose entries are $S_{i, i+1} = 1$ for every $i$,
$S_{0,0} = a_1$, $S_{1,0} = b_1$, $S_{i,i} = a$ and $S_{i+1,i} = b$ for every $i \ge 1$, and
$S_{i,j} = 0$ for all other $i, j$. So row $0$ is $a_1, 1, 0, \dots$, row $1$ is
$b_1, a, 1, 0, \dots$, and each row $i \ge 2$ has $b$ below the diagonal, $a$ on the diagonal, $1$
above the diagonal and $0$ elsewhere.

Source: statements `jis_0a625f6bc81227722525070e`, `jis_13957a12cbce86efa095f7c0`,
`jis_146fe3415fbde38090082db3`, `jis_a599499d0d7c9943d0ea6c2e`; concept
`jis_sem_ccb5c04c7ffe1e3f68d34c98`. -/
def stieltjesMatrix {R : Type*} [AddMonoidWithOne R] (a1 b1 a b : R) (i j : ℕ) : R :=
  if j = i + 1 then 1
  else if i = 0 ∧ j = 0 then a1
  else if i = 1 ∧ j = 0 then b1
  else if j = i then a
  else if j + 1 = i then b
  else 0

/-- **Specialized Stieltjes matrix.** Let $R$ be an additive monoid with one and let
$a, b, \lambda, \mu \in R$. The specialized Stieltjes matrix is the tridiagonal Stieltjes
production matrix with $a_1 = a + \lambda$, $b_1 = b + \mu$ and the same $a$ and $b$: the infinite
matrix $S$ with rows and columns indexed by $\mathbb{N} = \{0, 1, 2, \dots\}$ whose entries are
$S_{i, i+1} = 1$ for every $i$, $S_{0,0} = a + \lambda$, $S_{1,0} = b + \mu$, $S_{i,i} = a$ and
$S_{i+1,i} = b$ for every $i \ge 1$, and $S_{i,j} = 0$ for all other $i, j$.

This specialization corresponds to the inverse Riordan pair with numerator
$1 - \lambda x - \mu x^2$ over $1 + a x + b x^2$.

Source: statements `jis_0a625f6bc81227722525070e`, `jis_13957a12cbce86efa095f7c0`,
`jis_146fe3415fbde38090082db3`, `jis_a599499d0d7c9943d0ea6c2e`; concept
`jis_sem_ccb5c04c7ffe1e3f68d34c98`. -/
def stieltjesMatrixOf {R : Type*} [AddMonoidWithOne R] (a b lam mu : R) (i j : ℕ) : R :=
  stieltjesMatrix (a + lam) (b + mu) a b i j

end

end MetaMathlibExt
