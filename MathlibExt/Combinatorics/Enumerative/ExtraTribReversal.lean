/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import MathlibExt.Combinatorics.Enumerative.ExtraTribLeftExtension

/-! # Reversal of extraTribs -/

namespace MetaMathlibExt

/-- **The reversal of an extraTrib is not an extraTrib.** If $S : \mathbb{Z} \to \mathbb{Z}$
is an extraTrib, then the sequence $n \mapsto |S(-n)|$ is not an extraTrib.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 20 (`jis-2025-25.5.4-thm-20`). -/
public theorem not_isExtraTrib_reversal (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    ¬ IsExtraTrib (fun n => |S (-n)|) := by
  rintro ⟨hRev, _⟩
  obtain ⟨hRec, N, hPos⟩ := hS
  have hForward := hRec N
  -- Use four terms of the positive tail, read in the opposite order.
  have hBackward := hRev (-N - 3)
  change |S (-(-N - 3 + 3))| =
    |S (-(-N - 3 + 2))| + |S (-(-N - 3 + 1))| + |S (-(-N - 3))| at hBackward
  have h0 : -(-N - 3 + 3) = N := by omega
  have h1 : -(-N - 3 + 2) = N + 1 := by omega
  have h2 : -(-N - 3 + 1) = N + 2 := by omega
  have h3 : -(-N - 3) = N + 3 := by omega
  have hPos1 := hPos (N + 1) (by omega)
  have hPos2 := hPos (N + 2) (by omega)
  simp only [h0, h1, h2, h3, abs_of_pos (hPos N le_rfl), abs_of_pos hPos1,
    abs_of_pos hPos2, abs_of_pos (hPos (N + 3) (by omega))] at hBackward
  omega

end MetaMathlibExt
