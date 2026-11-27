/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat

/-!
# Large terms of a floor division sequence

For a fixed numerator `n`, counting `d` in `[1, n]` with `k ≤ n / d` is the
same as counting `d` in `[1, n / k]`: both conditions reduce to `k * d ≤ n`.
-/

namespace MetaMathlibExt

/-- **Counting large terms of the floor sequence.** For every natural number $n$ and every
integer $k \ge 1$, exactly $\lfloor n/k \rfloor$ of the integers $d$ with $1 \le d \le n$
satisfy $\lfloor n/d \rfloor \ge k$; that is, exactly $\lfloor n/k \rfloor$ terms of the floor
sequence $\lfloor n/1 \rfloor, \dots, \lfloor n/n \rfloor$ are at least $k$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 1 (`jis-2024-24.2.5-lem-1`). -/
public theorem floor_div_sequence_card_ge (n k : ℕ) (hk : 1 ≤ k) :
    ((Finset.Icc 1 n).filter (fun d : ℕ => k ≤ n / d)).card = n / k := by
  have hfilter : (Finset.Icc 1 n).filter (fun d : ℕ => k ≤ n / d) =
      Finset.Icc 1 (n / k) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd, _⟩, hkd⟩
      refine ⟨hd, (Nat.le_div_iff_mul_le hk).mpr ?_⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkd
    · rintro ⟨hd, hdk⟩
      refine ⟨⟨hd, hdk.trans (Nat.div_le_self _ _)⟩, (Nat.le_div_iff_mul_le hd).mpr ?_⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).mp hdk
  simp [hfilter]

end MetaMathlibExt
