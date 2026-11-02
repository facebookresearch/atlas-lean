/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

/-- **Riordan numbers.** For a natural number $n$, the $n$-th Riordan number is the integer
$$r_n = \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} C_k,$$
where $C_k$ is the $k$-th Catalan number.

Source: concept `jis_sem_b3566ec6e9de67444c66370a`; closed form `jis_d7e3bdcfd9ce7889bf468982`
(Kirgizov lines 436-438); context-only interpretations, not formalized here:
`jis_8247c394aad205ae41f58753`, `jis_bb01b95ccd294d34ab3af40c`, `jis_c9a7f2b9564521a0b4242141`. -/
def riordanNumber (n : Nat) : Int :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : Int) ^ (n - k) * ((n.choose k : Int) * ((catalan k : Int)))

/-- **Riordan numbers as an alternating Catalan sum.** For every natural number $n$, the $n$-th
Riordan number $r_n$ equals
$$\sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} C_k,$$
where $C_k$ is the $k$-th Catalan number.

Source: concept `jis_sem_b3566ec6e9de67444c66370a`; closed form `jis_d7e3bdcfd9ce7889bf468982`;
context only `jis_8247c394aad205ae41f58753`, `jis_bb01b95ccd294d34ab3af40c`,
`jis_c9a7f2b9564521a0b4242141`. -/
theorem riordanNumber_eq_sum (n : Nat) :
    riordanNumber n =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : Int) ^ (n - k) * ((n.choose k : Int) * ((catalan k : Int))) :=
  rfl

end MetaMathlibExt
