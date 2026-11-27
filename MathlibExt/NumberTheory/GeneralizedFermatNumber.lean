/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity

@[expose] public section

namespace MetaMathlibExt

/-- **Generalized Fermat number.** For an even natural number $b$ and a positive integer $n$,
the generalized Fermat number is $F_n(b) = b^{2^n} + 1$ (also written $F_{b,n}$).

Source statement IDs: `jis_4d4fccc58f4ac8e97335289f` and
`jis_53ff876efdb3987b971a7ac6`; concept ID: `jis_sem_242eb546467a7c65d6fe7b54`.

Sources: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Castillo/castillo2.tex> and
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Witno/witno8.tex>.
-/
def generalizedFermatNumber (b n : ℕ) (_hb : Even b) (_hn : 0 < n) : ℕ :=
  b ^ (2 ^ n) + 1

end MetaMathlibExt

end
