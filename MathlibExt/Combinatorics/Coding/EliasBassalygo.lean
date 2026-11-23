/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.ListDecoding

/-!
# The Elias–Bassalygo bound (alphabet-free form)

A code of minimum distance `d` has, by averaging, a Hamming ball of radius `e` holding at least
`|C| · Vol_q(n, e) / q ^ n` codewords; by the Johnson bound such a ball holds at most `n d`
codewords when `e < n - √(n (n - d))`. Hence `|C| · Vol_q(n, e) ≤ n d q ^ n`.

## References

* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025,
  Theorem 8.1.1, Lemma 8.1.2 and the proof of Theorem 8.1.1 (equations (8.1)–(8.2)).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.EliasBassalygo

open Finset MathlibExt.Combinatorics.Coding.ListDecoding

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- **Elias–Bassalygo bound** (alphabet-free form). Let `C` be a code of length `n` over a
nonempty alphabet with `q` letters, with distinct codewords at Hamming distance at least
`d ≤ n`, and let `e ≤ n` satisfy `n (n - d) < (n - e)²`, that is `e < n - √(n (n - d))`. Then
`|C| · Vol_q(n, e) ≤ n d q ^ n`, where `Vol_q(n, e) = ∑_{i=0}^{e} C(n, i) (q - 1) ^ i`.

This is the proof of Theorem 8.1.1 of Guruswami, Rudra and Sudan, *Essential Coding Theory*
(draft of August 26, 2025), combining Lemma 8.1.2 with the alphabet-free Johnson bound (their
Theorem 7.3.3, list size `n d`) instead of the `q`-ary Johnson bound of Theorem 7.3.1. With the
entropy estimate for the volume it gives the rate bound `R ≤ 1 - H_q(1 - √(1 - δ)) + o(1)`, which
is weaker than their `R ≤ 1 - H_q(J_q(δ)) + o(1)` since `J_q(δ) ≥ 1 - √(1 - δ)`; that asymptotic
form is not stated here. -/
theorem card_mul_sum_le [Nonempty α] (C : Finset (Fin n → α)) {d e : ℕ} (hen : e ≤ n)
    (hdn : d ≤ n) (hdist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hJ : n * (n - d) < (n - e) ^ 2) :
    C.card * ∑ i ∈ range (e + 1), n.choose i * (Fintype.card α - 1) ^ i ≤
      n * d * Fintype.card α ^ n := by
  obtain ⟨y, hy⟩ := exists_mul_card_filter_ge C e
  have hK := isListDecodable_of_johnson C hen hdn hdist hJ y
  calc C.card * ∑ i ∈ range (e + 1), n.choose i * (Fintype.card α - 1) ^ i
      ≤ Fintype.card α ^ n * (C.filter fun c => hammingDist y c ≤ e).card := hy
    _ ≤ Fintype.card α ^ n * (n * d) := Nat.mul_le_mul_left _ hK
    _ = n * d * Fintype.card α ^ n := by ring

end MathlibExt.Combinatorics.Coding.EliasBassalygo
