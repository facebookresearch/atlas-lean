/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Jacobsthal–Lucas numbers

This module defines the standard Jacobsthal–Lucas sequence, OEIS A014551.

Sources:

* Kenan Kaygisiz and Adem Şahin, *Generalized Bivariate Lucas p-Polynomials and Hessenberg
  Matrices*, <https://cs.uwaterloo.ca/journals/JIS/VOL15/Kaygisiz/kaygisiz3.tex>.
* Yash Puri and Thomas Ward, *Arithmetic and Growth of Periodic Orbits*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

JIS concept: `jis_sem_bbf5bfb8ea55b99401341187`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Jacobsthal–Lucas numbers.** The Jacobsthal–Lucas numbers $j_0, j_1, j_2, \dots$ are the
natural numbers defined by $j_0 = 2$, $j_1 = 1$ and $j_{n+2} = j_{n+1} + 2 j_n$ for all
$n \ge 0$. The sequence begins $2, 1, 5, 7, 17, \dots$ (OEIS A014551). -/
def jacobsthalLucasNumber : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => jacobsthalLucasNumber (n + 1) + 2 * jacobsthalLucasNumber n

end

end MetaMathlibExt
