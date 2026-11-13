/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

/-- Coefficient model of `F (z ^ (k ^ i))` for `F : PowerSeries Complex`,
used in the defining equation of a `k`-Mahler function
(concept `jis_sem_5181d154d12c87e1c5d03365`, defining statement
`jis_e5b3733b8ba6a96c630ed094`,
source https://cs.uwaterloo.ca/journals/JIS/VOL16/Bell/bell2.tex). -/
public noncomputable def mahlerSubst
    (F : PowerSeries Complex) (k i : ℕ) : PowerSeries Complex :=
  PowerSeries.mk fun n =>
    if (k ^ i) ∣ n then PowerSeries.coeff (n / (k ^ i)) F else 0

/-- `IsKMahlerFunction k F`: `F ∈ Complex⟦z⟧` is a `k`-Mahler function,
i.e. `2 ≤ k` and there exist `d : ℕ` and polynomial coefficients
`a : Fin (d + 1) → Polynomial Complex` with `a 0 ≠ 0` and `a d ≠ 0` such that
`∑ i, (a i) * F (z ^ (k ^ i)) = 0` (concept `jis_sem_5181d154d12c87e1c5d03365`,
required clause from statement `jis_e5b3733b8ba6a96c630ed094`,
source https://cs.uwaterloo.ca/journals/JIS/VOL16/Bell/bell2.tex). -/
public noncomputable def IsKMahlerFunction (k : ℕ) (F : PowerSeries Complex) : Prop :=
  2 ≤ k ∧
    ∃ (d : ℕ) (a : Fin (d + 1) → Polynomial Complex),
      a ⟨0, Nat.zero_lt_succ d⟩ ≠ 0 ∧
        a ⟨d, Nat.lt_succ_self d⟩ ≠ 0 ∧
          ∑ i : Fin (d + 1),
              Polynomial.toPowerSeries (a i) * mahlerSubst F k i.val = 0

end MetaMathlibExt

end
