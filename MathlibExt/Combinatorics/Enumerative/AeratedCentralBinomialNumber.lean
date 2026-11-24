/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic

/-!
# Aerated central binomial numbers

Source: Paul Barry and A. Mesinga Mwafise, *Classical and Semi-Classical
Orthogonal Polynomials Defined by Riordan Arrays, and Their Moment Sequences*,
Journal of Integer Sequences 21 (2018), Article 18.1.5.
-/

namespace MetaMathlibExt

@[expose]
public section

/-- **Aerated central binomial numbers.** For a natural number $n$, the $n$-th aerated central
binomial number is $\binom{n}{n/2}$ if $n$ is even and $0$ if $n$ is odd. The sequence begins
$1, 0, 2, 0, 6, 0, 20, \dots$.

Source: stable source identifiers: concept `jis_sem_7b40d8a9f9fe5eaa13955a5f`,
statement `jis_f04d18af371ba88dde3aabdc`.
-/
def aeratedCentralBinomialNumber (n : ℕ) : ℕ :=
  if n % 2 = 0 then Nat.choose n (n / 2) else 0

end

end MetaMathlibExt
