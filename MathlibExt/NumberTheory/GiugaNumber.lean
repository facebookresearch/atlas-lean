/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Giuga number.** A natural number $n$ is a Giuga number if it is composite (that is,
$n \ge 2$ and $n$ is not prime) and $p$ divides $n/p - 1$ for every prime divisor $p$ of $n$.

Source: concept `jis_sem_21328b1a53d1200638319a18` ("giuga number", alias "Giuga number");
definition statement `jis_ab5baeda0dc2487540fe8982` (supporting statements
`jis_30e1c99899402cb3710121ac`, `jis_516f07f0ff485c60e52c40ed`, `jis_b646c8104f823e40db00d5de`).

Sources: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Oller/oller5.tex> and
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.tex>.
-/
public def IsGiugaNumber (n : ℕ) : Prop :=
  2 ≤ n ∧ ¬ Nat.Prime n ∧ ∀ p, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)

end

end MetaMathlibExt
