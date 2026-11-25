/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.NumberTheory.PolygonalNumber
import Mathlib.Tactic.Ring

/-! # Odd squares and triangular numbers -/

namespace MetaMathlibExt

/-- **Odd squares and triangular numbers.** For every odd natural number $x$, the number
$(x^2 - 1)/8$ is a triangular number: there is a natural number $k$ with
$(x^2 - 1)/8 = p_3(k)$, where $p_3(k) = k(k+1)/2$ is the $k$-th $3$-gonal number.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 5
(arXiv Lemma 3.3; `jis-2024-24.5.1-lem-5`). -/
public theorem sq_sub_one_div_eight_eq_triangular (x : ℕ) (hx : Odd x) :
    ∃ k : ℕ, (x ^ 2 - 1) / 8 = Nat.polygonalNumber 3 k := by
  obtain ⟨k, rfl⟩ := hx
  refine ⟨k, ?_⟩
  have hsquare : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [hsquare, Nat.add_sub_cancel, Nat.polygonalNumber_three]
  omega

end MetaMathlibExt
