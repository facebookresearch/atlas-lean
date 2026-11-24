/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Pentanacci numbers.** The pentanacci numbers $a_n$, for natural numbers $n$, are defined by
$a_0 = 1$, $a_1 = 1$, $a_2 = 2$, $a_3 = 4$, $a_4 = 8$ and
$a_{n+5} = a_{n+4} + a_{n+3} + a_{n+2} + a_{n+1} + a_n$ for every $n$, so each term from index
$5$ on is the sum of the five terms before it.

Their ordinary generating function is $1/(1 - t - t^2 - t^3 - t^4 - t^5)$; up to a shift of index
they form OEIS A001591.

Source: JIS concept `jis_sem_a98a2c489e24a91907e84283`; statements
`jis_6eb337f276c191430742e49f`, `jis_cb7e03aa435f1bbd253660ca`, `jis_f311834ff91269ae7cf94a4b`. -/
def pentanacciNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 8
  | n + 5 =>
      pentanacciNumber (n + 4) + pentanacciNumber (n + 3) +
        pentanacciNumber (n + 2) + pentanacciNumber (n + 1) +
        pentanacciNumber n

end MetaMathlibExt
