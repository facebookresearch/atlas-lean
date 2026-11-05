/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Fuss–Catalan numbers.** For natural numbers $k \ge 1$ (the chord arity) and $m$, the
Fuss–Catalan number is the natural-number quotient of $\binom{km}{m}$ by $(k-1)m+1$, that is
$\lfloor \binom{km}{m} / ((k-1)m+1) \rfloor$.

Source: JIS VOL23/Young, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Young/young5.tex>,
SHA-256 `5c6d6c8dc8aae4faa4a889e2251d51792c3ca6bc95285880041806013bf413bd`; concepts
`jis_term_ebafb51c3672353ca538423c` and `jis_sem_1faa20d56755b6a211607da7`. -/
public def fussCatalanNumber (k m : ℕ) (_hk : 1 ≤ k) : ℕ :=
  Nat.choose (k * m) m / ((k - 1) * m + 1)

end
end MetaMathlibExt
