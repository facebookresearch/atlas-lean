/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq

/-!
# Parity of adjacent rows in a Delannoy array

Across one column step, the difference of two adjacent rows changes by twice the
upper entry in the preceding column. Thus its parity is independent of the column.
-/

namespace MetaMathlibExt.DelannoyConstructions

@[expose] public section

/-- **Parity of adjacent rows of a Delannoy array.** Let $R(m, n)$, for $m, n \in \mathbb{N}$, be
integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all $m, n$, and let
$m \in \mathbb{N}$. If $R(m, 0) \equiv R(m+1, 0) \pmod 2$, then $R(m, i) \equiv R(m+1, i) \pmod 2$
for all $i$; if $R(m, 0) \not\equiv R(m+1, 0) \pmod 2$, then
$R(m, i) \not\equiv R(m+1, i) \pmod 2$ for all $i$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 13
(`jis-2024-24.1.8-thm-13`). -/
public theorem delannoyArray_rows_parity (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (m : ℕ) :
    (R m 0 ≡ R (m + 1) 0 [ZMOD 2] → ∀ i, R m i ≡ R (m + 1) i [ZMOD 2]) ∧
      (¬ R m 0 ≡ R (m + 1) 0 [ZMOD 2] → ∀ i, ¬ R m i ≡ R (m + 1) i [ZMOD 2]) := by
  have step (i : ℕ) : R m (i + 1) ≡ R (m + 1) (i + 1) [ZMOD 2] ↔
      R m i ≡ R (m + 1) i [ZMOD 2] := by
    simp only [Int.modEq_iff_dvd]
    have hdiff : R (m + 1) (i + 1) - R m (i + 1) =
        (R (m + 1) i - R m i) + 2 * R m i := by
      rw [hR m i]
      omega
    rw [hdiff]
    have htwo : (2 : ℤ) ∣ 2 * R m i := ⟨R m i, rfl⟩
    exact ⟨fun h => by simpa only [add_sub_cancel_right] using Int.dvd_sub h htwo,
      fun h => Int.dvd_add h htwo⟩
  have parity (i : ℕ) : R m i ≡ R (m + 1) i [ZMOD 2] ↔ R m 0 ≡ R (m + 1) 0 [ZMOD 2] := by
    induction i with
    | zero => rfl
    | succ i ih => exact (step i).trans ih
  exact ⟨fun h i => (parity i).mpr h, fun h i hi => h ((parity i).mp hi)⟩

end -- public section

end MetaMathlibExt.DelannoyConstructions
