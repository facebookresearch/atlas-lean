/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Primorial

/-!
# Fortunate numbers

The definition is taken from Antonín Čejchan, Michal Křížek, and Lawrence
Somer, *On Remarkable Properties of Primes Near Factorials and Primorials*,
Journal of Integer Sequences 25 (2022), Article 22.1.4.
-/

namespace MetaMathlibExt

@[expose]
public section

/-- **Fortunate numbers.** Write $q\#$ for the primorial of a natural number $q$, the product of
all primes $p \le q$. For natural numbers $q$ and $m$, $m$ is the Fortunate number of $q$ when
$q$ is prime, $m > 1$, $q\# + m$ is prime, and $q\# + k$ is not prime for any $k$ with
$1 < k < m$.

Source: Antonín Čejchan, Michal Křížek, and Lawrence Somer, *On Remarkable Properties of Primes
Near Factorials and Primorials*, Journal of Integer Sequences 25 (2022), Article 22.1.4. Stable
source identifiers: concept `jis_sem_a34930e523f9a76ac6ef3668`, statement
`jis_e3ac668676ad89d9b5e1b013`.
-/
def IsFortunateNumber (q m : ℕ) : Prop :=
  q.Prime ∧ 1 < m ∧ (primorial q + m).Prime ∧
    ∀ k, 1 < k → k < m → ¬ (primorial q + k).Prime

end

end MetaMathlibExt
