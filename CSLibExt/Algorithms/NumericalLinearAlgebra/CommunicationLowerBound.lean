/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.LoomisWhitney

/-!
# Communication lower bounds for matrix-multiplication-like computations

Ballard, Demmel, Holtz and Schwartz (*Minimizing communication in numerical linear algebra*,
SIAM J. Matrix Anal. Appl. 32 (2011); arXiv:0905.2485, Section 2) bound the number of words that
a sequential machine with a fast memory of `M` words must move between fast and slow memory to
evaluate a computation of the form

`c(i, j) = f_{ij}(g_{ijk}(a(i, k), b(k, j)) for k ∈ S_{ij}, …)`  for `(i, j) ∈ S_C`,

which covers classical (`O(n³)`) dense and sparse matrix multiplication, LU, Cholesky and `LDLᵀ`.
Their argument, following Irony, Toledo and Tiskin (J. Parallel Distrib. Comput. 64 (2004)), is:

1. cut the instruction stream into *segments*, each containing exactly `M` loads and stores
   (the last one possibly fewer);
2. during one segment at most `4M` operands of each kind can be used (at most `2M` were in fast
   memory at its start or read during it, at most `2M` are left in fast memory at its end or
   written during it), provided no operand is created and discarded within the segment
   without memory traffic (no "S2/D2" operands);
3. by the discrete Loomis–Whitney inequality a segment therefore evaluates at most
   `√((4M)³) = 8 M^{3/2}` of the `g_{ijk}`;
4. so there are at least `⌊G / (8 M^{3/2})⌋` complete segments, and at least
   `G / (8 √M) - M` words are moved, `G` being the number of evaluations of the `g_{ijk}`.

Step 1 and the operand count of step 2 are statements about the machine; they are the
hypotheses here. This file proves steps 3 and 4: the evaluations are a finite set `G` of index
triples `(i, j, k)`; the segments are finite sets of triples covering `G`; in each segment the
operands `a(i, k)`, `b(k, j)` and `c(i, j)` used are the projections of the segment onto the
pairs `(i, k)`, `(j, k)` and `(i, j)`, and each has at most `4M` elements. Aliasing between the
arrays `a`, `b`, `c` is allowed, as in the source, since each projection is bounded separately.

## Main results

* `card_le_of_card_image_le`: a segment that uses at most `4M` operands of each kind evaluates at
  most `8 M √M` of the `g_{ijk}` (step 3).
* `card_div_sub_le_words`: **the bandwidth lower bound** `G / (8 √M) - M ≤ W` for the number `W` of
  words moved (Theorem 2 of arXiv:0905.2485, in this segment-counting form).
* `matmul_card_div_sub_le_words`: for dense `n × r` times `r × m` classical matrix multiplication,
  `n m r / (8 √M) - M ≤ W`, the `Ω(n³ / √M)` bound of Hong and Kung (1981) and Irony, Toledo
  and Tiskin (2004) for `n = m = r`.
* `exists_card_div_sub_le_words_of_parallel`: with the work shared among `P` processors, some
  processor moves at least `G / (8 P √M) - M` words.

## Cost model

The cost is the number `W` of words moved between fast and slow memory; arithmetic is free.
The model is the one of arXiv:0905.2485, Section 2; Strassen-like algorithms, which do not
evaluate every product `a(i, k) b(k, j)`, are outside it.
-/

@[expose] public section

namespace Cslib.Algorithms.NumericalLinearAlgebra.CommunicationLowerBound

open Finset MathlibExt.Combinatorics.LoomisWhitney

variable {ι κ μ : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

/-- **Evaluations per segment.** If a set `E` of index triples `(i, j, k)` uses at most `4M`
operands `a(i, k)`, at most `4M` operands `b(k, j)` (indexed by `(j, k)`) and at most `4M`
accumulators `c(i, j)`, then `|E| ≤ 8 M √M = √((4M)³)` (Ballard, Demmel, Holtz and Schwartz,
arXiv:0905.2485, Section 2, the bound `F = √((4M)³)` obtained from Lemma 1). -/
theorem card_le_of_card_image_le (E : Finset (ι × κ × μ)) (M : ℕ)
    (hA : (E.image projXZ).card ≤ 4 * M) (hB : (E.image projYZ).card ≤ 4 * M)
    (hC : (E.image projXY).card ≤ 4 * M) :
    (E.card : ℝ) ≤ 8 * M * √(M : ℝ) := by
  have hLW := card_sq_le_card_mul_card_mul_card E
  have hsq : E.card ^ 2 ≤ (4 * M) * (4 * M) * (4 * M) :=
    hLW.trans (Nat.mul_le_mul (Nat.mul_le_mul hB hA) hC)
  have hsqR : (E.card : ℝ) ^ 2 ≤ (8 * M * √(M : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
    have : ((E.card ^ 2 : ℕ) : ℝ) ≤ (((4 * M) * (4 * M) * (4 * M) : ℕ) : ℝ) := by
      exact_mod_cast hsq
    push_cast at this
    nlinarith [this]
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).1 hsqR

/-- **Bandwidth lower bound, segment-counting form.** Let `G` be the finite set of index
triples `(i, j, k)` whose `g_{ijk}(a(i, k), b(k, j))` the computation evaluates. Suppose the
execution is cut into `s` segments whose triples cover `G`, each segment using at most `4M`
operands `a(i, k)`, `b(k, j)` and `c(i, j)` of each kind, and every segment but possibly the last
containing `M` loads and stores, so that the number `W` of words moved satisfies
`M (s - 1) ≤ W`. Then `G / (8 √M) - M ≤ W` (Ballard, Demmel, Holtz and Schwartz,
arXiv:0905.2485, Theorem 2). -/
theorem card_div_sub_le_words (G : Finset (ι × κ × μ)) {s : ℕ}
    (seg : Fin s → Finset (ι × κ × μ)) (M W : ℕ)
    (hcover : G ⊆ univ.biUnion seg)
    (hA : ∀ t, ((seg t).image projXZ).card ≤ 4 * M)
    (hB : ∀ t, ((seg t).image projYZ).card ≤ 4 * M)
    (hC : ∀ t, ((seg t).image projXY).card ≤ 4 * M)
    (hW : M * (s - 1) ≤ W) :
    (G.card : ℝ) / (8 * √(M : ℝ)) - M ≤ W := by
  have hG : (G.card : ℝ) ≤ s * (8 * M * √(M : ℝ)) := by
    have h1 : G.card ≤ ∑ t, (seg t).card :=
      (card_le_card hcover).trans card_biUnion_le
    have h2 : ((∑ t, (seg t).card : ℕ) : ℝ) ≤ ∑ _t : Fin s, (8 * M * √(M : ℝ)) := by
      push_cast
      exact sum_le_sum fun t _ => card_le_of_card_image_le (seg t) M (hA t) (hB t) (hC t)
    calc (G.card : ℝ) ≤ ((∑ t, (seg t).card : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2
      _ = _ := by simp
  have hWR : (M : ℝ) * ((s - 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
  have hs1 : (s : ℝ) - 1 ≤ ((s - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos s with h | h
    · simp [h]
    · rw [Nat.cast_sub h]; simp
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp
  · have hsqrt : 0 < √(M : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hM)
    have hdiv : (G.card : ℝ) / (8 * √(M : ℝ)) ≤ s * M := by
      rw [div_le_iff₀ (by positivity)]
      calc (G.card : ℝ) ≤ s * (8 * M * √(M : ℝ)) := hG
        _ = s * M * (8 * √(M : ℝ)) := by ring
    nlinarith [mul_le_mul_of_nonneg_left hs1 hM0]

/-- **Communication lower bound for classical matrix multiplication.** Multiplying a dense
`n × r` matrix by a dense `r × m` matrix by evaluating all `n m r` products `A(i, k) B(k, j)`,
under the segment hypotheses of `card_div_sub_le_words`, moves at least `n m r / (8 √M) - M`
words (Hong and Kung 1981; Irony, Toledo and Tiskin 2004, Lemma 2.1; Ballard, Demmel, Holtz and
Schwartz, arXiv:0905.2485, Theorem 2 applied to `C = A B`). -/
theorem matmul_card_div_sub_le_words {n m r s : ℕ}
    (seg : Fin s → Finset (Fin n × Fin m × Fin r)) (M W : ℕ)
    (hcover : ∀ p, ∃ t, p ∈ seg t)
    (hA : ∀ t, ((seg t).image projXZ).card ≤ 4 * M)
    (hB : ∀ t, ((seg t).image projYZ).card ≤ 4 * M)
    (hC : ∀ t, ((seg t).image projXY).card ≤ 4 * M)
    (hW : M * (s - 1) ≤ W) :
    ((n * m * r : ℕ) : ℝ) / (8 * √(M : ℝ)) - M ≤ W := by
  have hcov : (univ : Finset (Fin n × Fin m × Fin r)) ⊆ univ.biUnion seg := by
    intro p _
    obtain ⟨t, ht⟩ := hcover p
    exact mem_biUnion.2 ⟨t, mem_univ _, ht⟩
  have := card_div_sub_le_words univ seg M W hcov hA hB hC hW
  simpa [card_univ, Fintype.card_prod, Fintype.card_fin, mul_assoc] using this

/-- **Parallel bandwidth lower bound.** Let the evaluations `G` be shared among `P > 0`
processors, processor `q` evaluating the triples `Gq q` (together covering `G`), each with a local
memory of `M` words and with an execution satisfying the segment hypotheses of
`card_div_sub_le_words` for `W q` words moved. Then some processor moves at least
`G / (8 P √M) - M` words: at least one processor performs at least `G / P` evaluations
(Ballard, Demmel, Holtz and Schwartz, arXiv:0905.2485, Section 3.1, the argument of
Corollary 5, there stated as `Ω(G / √(P · NNZ) - NNZ / P)` under memory balance,
`M = O(NNZ / P)`). -/
theorem exists_card_div_sub_le_words_of_parallel (G : Finset (ι × κ × μ)) {P : ℕ} (hP : 0 < P)
    (Gq : Fin P → Finset (ι × κ × μ)) (hcover : G ⊆ univ.biUnion Gq)
    (s : Fin P → ℕ) (seg : (q : Fin P) → Fin (s q) → Finset (ι × κ × μ)) (M : ℕ)
    (W : Fin P → ℕ)
    (hseg : ∀ q, Gq q ⊆ univ.biUnion (seg q))
    (hA : ∀ q t, ((seg q t).image projXZ).card ≤ 4 * M)
    (hB : ∀ q t, ((seg q t).image projYZ).card ≤ 4 * M)
    (hC : ∀ q t, ((seg q t).image projXY).card ≤ 4 * M)
    (hW : ∀ q, M * (s q - 1) ≤ W q) :
    ∃ q, (G.card : ℝ) / (P * (8 * √(M : ℝ))) - M ≤ W q := by
  -- some processor performs at least `|G| / P` evaluations
  obtain ⟨q, -, hq⟩ : ∃ q ∈ (univ : Finset (Fin P)), (G.card : ℝ) / P ≤ (Gq q).card := by
    by_contra hcon
    push Not at hcon
    have hsum : (G.card : ℝ) ≤ ∑ q, ((Gq q).card : ℝ) := by
      exact_mod_cast (card_le_card hcover).trans card_biUnion_le
    have hlt : ∑ q : Fin P, ((Gq q).card : ℝ) < ∑ _q : Fin P, (G.card : ℝ) / P :=
      sum_lt_sum_of_nonempty ⟨⟨0, hP⟩, mem_univ _⟩ fun q _ => hcon q (mem_univ q)
    have hP' : (0 : ℝ) < P := by exact_mod_cast hP
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    rw [mul_div_cancel₀ _ hP'.ne'] at hlt
    linarith
  refine ⟨q, ?_⟩
  have h := card_div_sub_le_words (Gq q) (seg q) M (W q) (hseg q) (hA q) (hB q) (hC q) (hW q)
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hden : (0 : ℝ) ≤ 8 * √(M : ℝ) := by positivity
  calc (G.card : ℝ) / (P * (8 * √(M : ℝ))) - M = (G.card : ℝ) / P / (8 * √(M : ℝ)) - M := by
        rw [div_div]
    _ ≤ ((Gq q).card : ℝ) / (8 * √(M : ℝ)) - M := by gcongr
    _ ≤ W q := h

end Cslib.Algorithms.NumericalLinearAlgebra.CommunicationLowerBound
