/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.Order

namespace MetaMathlibExt

@[expose] public section

/-- Van der Laan window predicate (concept `jis_term_73e55616c68e02e09fa349b5`,
raw phrase rank 204 `laan sequence`, source `a6b5613ec29d7f2bcc9e-nacin5.tex`
(SHA-256 `52008805cb731f6d0e329d46c8da38ea6055d8ced9031f7a81cf630ddd7b69a1`),
lines 92-96).

The source calls a non-negative sequence Van der Laan when, for every four
consecutive terms, the largest term equals the sum of the two smallest
(conjecture from the OEIS entry; only the predicate is formalized here).
This is a faithful total definition on naturals: the largest of four values
is their iterated `max`, and the sum of the two smallest is the minimum of
the six pair sums, which exactly represents the order-statistic statement
and handles repeated values. -/
public def IsVanDerLaanWindow (a b c d : ℕ) : Prop :=
  max (max a b) (max c d)
    = min (min (a + b) (a + c)) (min (min (a + d) (b + c)) (min (b + d) (c + d)))

/-- Van der Laan sequence predicate (concept `jis_term_73e55616c68e02e09fa349b5`,
source lines 92-96: every window of four consecutive terms satisfies
`IsVanDerLaanWindow`). -/
public def IsVanDerLaan (s : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, IsVanDerLaanWindow (s n) (s (n + 1)) (s (n + 2)) (s (n + 3))

/-- Ordered-window reduction (concept `jis_term_73e55616c68e02e09fa349b5`;
local reduction used by source lines 120-124 for increasing sequences).

An already ordered window `a ≤ b ≤ c ≤ d` is a Van der Laan window if and
only if the largest term is the sum of the two smallest, `d = a + b`. -/
public theorem isVanDerLaanWindow_ordered_iff {a b c d : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) : IsVanDerLaanWindow a b c d ↔ d = a + b := by
  have hmax : max (max a b) (max c d) = d := by omega
  have hmin : min (min (a + b) (a + c)) (min (min (a + d) (b + c)) (min (b + d) (c + d)))
      = a + b := by omega
  unfold IsVanDerLaanWindow
  rw [hmax, hmin]

/-- Constant window characterization (concept `jis_term_73e55616c68e02e09fa349b5`).

A constant window `(k, k, k, k)` has largest value `k` and smallest pair sum
`k + k`, so it is a Van der Laan window iff `k = 0`. -/
public theorem isVanDerLaanWindow_const_iff {k : ℕ} :
    IsVanDerLaanWindow k k k k ↔ k = 0 := by
  have hmax : max (max k k) (max k k) = k := by omega
  have hmin : min (min (k + k) (k + k)) (min (min (k + k) (k + k)) (min (k + k) (k + k)))
      = k + k := by omega
  unfold IsVanDerLaanWindow
  rw [hmax, hmin]
  constructor <;> intro h <;> omega

/-- Constant sequence characterization (concept `jis_term_73e55616c68e02e09fa349b5`,
source lines 92-96).

A constant non-negative sequence is Van der Laan iff its value is zero; in
particular the identically zero sequence claimed as one alternative in the
source conjecture satisfies the predicate. -/
public theorem isVanDerLaan_const_iff {k : ℕ} :
    IsVanDerLaan (fun _ => k) ↔ k = 0 := by
  constructor
  · intro h
    have h0 : IsVanDerLaanWindow k k k k := h 0
    exact isVanDerLaanWindow_const_iff.mp h0
  · intro hk n
    subst hk
    change IsVanDerLaanWindow 0 0 0 0
    unfold IsVanDerLaanWindow
    decide

end

end MetaMathlibExt
