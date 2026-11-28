/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.BilinearRecursion
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
public import CSLibExt.Complexity.Algebraic.SquareMatrixMultiplicationBounds

/-!
# Gate counts for recursive bilinear matrix-multiplication circuits

Exact sizes of the block encoder and decoder, the one-step size recurrence
for `recursiveCircuit`, its closed form, and an upper-bound invariant. The
charged primitive is the gate (`add`/`mul` nodes); constants and input
references are free, and a linear combination is charged per
(output, source) pair even at zero coefficients, so the counts are exact
for the construction as written.
-/

set_option autoImplicit false

universe u

namespace Cslib.Complexity.Algebraic

@[expose] public section

/-- **Size of the block encoder.** One linear combination over all terms and both
input blocks, charged per (output, source) pair. -/
theorem blockEncoder_size {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    (blockEncoder terms k).size = 4 * terms.length * q ^ (2 * (k + 1)) := by
  have hpow : q ^ (2 * (k + 1)) = (q ^ k * q ^ k) * q ^ 2 := by
    rw [show 2 * (k + 1) = (k + k) + 2 by ring, pow_add, pow_add]
  simp only [blockEncoder, ArithmeticCircuit.size_linearCombination,
    MatrixMultiplicationExponent.MatrixCoordinate, Fintype.card_prod, Fintype.card_sum,
    Fintype.card_fin]
  rw [hpow]
  ring

/-- **Size of the block decoder.** One linear combination reassembling every output
block from the per-term results. -/
theorem blockDecoder_size {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    (blockDecoder terms k).size = 2 * terms.length * q ^ (2 * (k + 1)) := by
  have hpow : q ^ (2 * (k + 1)) = q ^ (k + 1) * q ^ (k + 1) := by
    rw [show 2 * (k + 1) = (k + 1) + (k + 1) by ring, pow_add]
  simp only [blockDecoder, ArithmeticCircuit.size_linearCombination,
    Fintype.card_prod, Fintype.card_fin]
  rw [hpow]
  ring

/-- **Base case of the size recurrence.** The level-zero circuit is the one-gate
outer-product circuit. -/
@[simp] theorem recursiveCircuit_size_zero {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) :
    (recursiveCircuit terms 0).size = 1 := by
  simp only [recursiveCircuit, outerMatrixCircuit_size, mul_one]

/-- **One-step size recurrence.** Each level adds one recursive copy per term plus
the encoder and decoder sizes. -/
theorem recursiveCircuit_size_succ {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    (recursiveCircuit terms (k + 1)).size =
      terms.length * (recursiveCircuit terms k).size +
        6 * terms.length * q ^ (2 * (k + 1)) := by
  simp only [recursiveCircuit, ArithmeticCircuit.size_subst, ArithmeticCircuit.size_parallel,
    blockEncoder_size, blockDecoder_size]
  ring

/-- **Closed form of the size recurrence.** Multiplying the recurrence solution
through by `terms.length - q ^ 2` clears the division. -/
theorem recursiveCircuit_size_closed {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    ((terms.length : ℤ) - (q : ℤ) ^ 2) * (recursiveCircuit terms k).size +
        6 * terms.length * (q : ℤ) ^ 2 * (q : ℤ) ^ (2 * k) =
      ((terms.length : ℤ) - (q : ℤ) ^ 2 + 6 * terms.length * (q : ℤ) ^ 2) *
        (terms.length : ℤ) ^ k := by
  induction k with
  | zero =>
    simp [recursiveCircuit_size_zero]
  | succ k ih =>
    have hrecZ : ((recursiveCircuit terms (k + 1)).size : ℤ)
        = (terms.length : ℤ) * ((recursiveCircuit terms k).size : ℤ)
          + 6 * (terms.length : ℤ) * (q : ℤ) ^ (2 * (k + 1)) := by
      exact_mod_cast recursiveCircuit_size_succ terms k
    have hpow : (q : ℤ) ^ (2 * (k + 1)) = (q : ℤ) ^ (2 * k) * (q : ℤ) ^ 2 := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    rw [hrecZ, hpow, pow_succ]
    linear_combination (terms.length : ℤ) * ih

/-- **Upper-bound invariant for the size.** With at most `r` terms per level and
`q ^ 2 < r`, the size plus the scaled geometric term stays below the pure
exponential. -/
theorem recursiveCircuit_size_le {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)))
    {r : ℕ} (hlen : terms.length ≤ r) (hqr : q ^ 2 < r) (k : ℕ) :
    (recursiveCircuit terms k).size + 6 * r * q ^ 2 * q ^ (2 * k) ≤
      (1 + 6 * r * q ^ 2) * r ^ k := by
  induction k with
  | zero =>
    simp [recursiveCircuit_size_zero]
  | succ k ih =>
    have hQ1 : q ^ 2 + 1 ≤ r := hqr
    have hpow : q ^ (2 * (k + 1)) = q ^ (2 * k) * q ^ 2 := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    have hLr2 : terms.length + r * q ^ 2 ≤ r * r := by
      calc terms.length + r * q ^ 2 ≤ r + r * q ^ 2 := add_le_add_left hlen _
        _ = r * (q ^ 2 + 1) := by ring
        _ ≤ r * r := mul_le_mul_right hQ1 _
    have hrec := recursiveCircuit_size_succ terms k
    have hrpow : r ^ (k + 1) = r ^ k * r := by rw [pow_succ]
    rw [hrec, hpow, hrpow]
    nlinarith [mul_le_mul_right ih r, mul_le_mul_right hlen ((recursiveCircuit terms k).size),
      mul_le_mul_right hLr2 (6 * q ^ (2 * k) * q ^ 2)]

/-- **Zero-padding embedding.** Inputs of `n`-by-`n` matrices are embedded into the
input positions of `N`-by-`N` matrices, padding with zeros outside the range. -/
private def padEmbed (F : Type u) [Field F] {n N : ℕ} :
    ArithmeticCircuit F ((Fin n × Fin n) ⊕ (Fin n × Fin n))
      ((Fin N × Fin N) ⊕ (Fin N × Fin N)) where
  size := 0
  gate := fun i => nomatch i
  output
    | Sum.inl (i, j) =>
      if h : i.val < n ∧ j.val < n then
        ArithmeticOperand.input (Sum.inl (Fin.castLT i h.1, Fin.castLT j h.2))
      else ArithmeticOperand.constant 0
    | Sum.inr (i, j) =>
      if h : i.val < n ∧ j.val < n then
        ArithmeticOperand.input (Sum.inr (Fin.castLT i h.1, Fin.castLT j h.2))
      else ArithmeticOperand.constant 0

/-- **Output projection.** Outputs of `N`-by-`N` matrices are projected back to the
`n`-by-`n` output positions. -/
private def padProject (F : Type u) [Field F] {n N : ℕ} (hnN : n ≤ N) :
    ArithmeticCircuit F (Fin N × Fin N) (Fin n × Fin n) where
  size := 0
  gate := fun i => nomatch i
  output := fun p => ArithmeticOperand.input (Fin.castLE hnN p.1, Fin.castLE hnN p.2)

/-- **Monotonicity of matrix-multiplication circuit size.** A circuit for `N`-by-`N`
matrices restricts to one for `n`-by-`n` matrices with no extra gates, by
zero-padding the inputs and projecting the outputs. -/
theorem IsMatrixMultiplication.exists_size_le_of_le {F : Type u} [Field F]
    {n N : ℕ} (hnN : n ≤ N) {c : MatrixArithmeticCircuit F N N N}
    (hc : IsMatrixMultiplication c) :
    ∃ c' : MatrixArithmeticCircuit F n n n, IsMatrixMultiplication c' ∧
      c'.size ≤ c.size := by
  refine ⟨(padProject F hnN).subst (c.subst (padEmbed F)), ?_, ?_⟩
  · intro A B i j
    set A' : Matrix (Fin N) (Fin N) F :=
      Matrix.of fun a b =>
        if h : a.val < n ∧ b.val < n then
          A (Fin.castLT a h.1) (Fin.castLT b h.2)
        else 0 with hA'def
    set B' : Matrix (Fin N) (Fin N) F :=
      Matrix.of fun a b =>
        if h : a.val < n ∧ b.val < n then
          B (Fin.castLT a h.1) (Fin.castLT b h.2)
        else 0 with hB'def
    have hA' : ∀ a b : Fin N, A' a b =
        (if h : a.val < n ∧ b.val < n then
          A (Fin.castLT a h.1) (Fin.castLT b h.2)
        else 0) := fun a b => rfl
    have hB' : ∀ a b : Fin N, B' a b =
        (if h : a.val < n ∧ b.val < n then
          B (Fin.castLT a h.1) (Fin.castLT b h.2)
        else 0) := fun a b => rfl
    have hemb : (fun a => (padEmbed F).evaluate (matrixInput A B) a)
        = matrixInput A' B' := by
      funext a
      cases a with
      | inl p =>
        obtain ⟨p1, p2⟩ := p
        simp only [ArithmeticCircuit.evaluate, padEmbed,
          ArithmeticOperand.evaluate, matrixInput, Sum.elim_inl, hA' p1 p2]
        by_cases h : p1.val < n ∧ p2.val < n <;> simp [h]
      | inr p =>
        obtain ⟨p1, p2⟩ := p
        simp only [ArithmeticCircuit.evaluate, padEmbed,
          ArithmeticOperand.evaluate, matrixInput, Sum.elim_inr, hB' p1 p2]
        by_cases h : p1.val < n ∧ p2.val < n <;> simp [h]
    have hproj : ∀ (x : (Fin N × Fin N) → F) (p : Fin n × Fin n),
        (padProject F hnN).evaluate x p
          = x (Fin.castLE hnN p.1, Fin.castLE hnN p.2) := by
      intro x p
      obtain ⟨p1, p2⟩ := p
      simp [ArithmeticCircuit.evaluate, padProject, ArithmeticOperand.evaluate]
    simp only [ArithmeticCircuit.evaluate_subst, hemb, hproj]
    rw [hc A' B' (Fin.castLE hnN i) (Fin.castLE hnN j)]
    set u : Fin N := Fin.castLE hnN i with hu_def
    set v : Fin N := Fin.castLE hnN j with hv_def
    have hu_val : u.val = i.val := rfl
    have hv_val : v.val = j.val := rfl
    have hu_lt : u.val < n := by rw [hu_val]; exact i.isLt
    have hv_lt : v.val < n := by rw [hv_val]; exact j.isLt
    rw [Matrix.mul_apply, Matrix.mul_apply]
    set s : Finset (Fin N) := Finset.univ.image (Fin.castLE hnN) with hs_def
    have hmem : ∀ k : Fin N, k ∈ s ↔ k.val < n := by
      intro k
      simp only [hs_def, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, rfl⟩
        have h1 : (Fin.castLE hnN a).val = a.val := rfl
        rw [h1]; exact a.isLt
      · intro hk
        exact ⟨Fin.castLT k hk, Fin.ext rfl⟩
    have hvanish : ∀ k : Fin N, k ∉ s → A' u k * B' k v = 0 := by
      intro k hk
      have hkn : ¬ k.val < n := fun hh => hk ((hmem k).mpr hh)
      have hA0 : A' u k = 0 := by
        have hneg : ¬ (u.val < n ∧ k.val < n) := fun h => hkn h.2
        simp [hA' u k, hneg]
      rw [hA0, zero_mul]
    have hsum1 : (∑ k : Fin N, A' u k * B' k v)
        = Finset.sum s (fun k => A' u k * B' k v) :=
      (Finset.sum_subset (Finset.subset_univ s)
        (fun k _ hk => hvanish k hk)).symm
    have hinj : Function.Injective (Fin.castLE hnN) := by
      intro a b hab
      have hval : (Fin.castLE hnN a).val = (Fin.castLE hnN b).val :=
        congrArg Fin.val hab
      have hval' : a.val = b.val := hval
      exact Fin.ext hval'
    have hsum2 : Finset.sum s (fun k => A' u k * B' k v)
        = ∑ k : Fin n, A' u (Fin.castLE hnN k) * B' (Fin.castLE hnN k) v := by
      rw [hs_def]
      exact Finset.sum_image (fun a _ b _ hab => hinj hab)
    have hpoint : ∀ k : Fin n, A' u (Fin.castLE hnN k) * B' (Fin.castLE hnN k) v
        = A i k * B k j := by
      intro k
      have hk : (Fin.castLE hnN k).val < n := by
        have h1 : (Fin.castLE hnN k).val = k.val := rfl
        rw [h1]; exact k.isLt
      have hA1 : A' u (Fin.castLE hnN k) = A i k := by
        have hcond : u.val < n ∧ (Fin.castLE hnN k).val < n := ⟨hu_lt, hk⟩
        simp only [hA' u (Fin.castLE hnN k), dite_eq_left hcond]
        congr 1
      have hB1 : B' (Fin.castLE hnN k) v = B k j := by
        have hcond : (Fin.castLE hnN k).val < n ∧ v.val < n := ⟨hk, hv_lt⟩
        simp only [hB' (Fin.castLE hnN k) v, dite_eq_left hcond]
        congr 1
      rw [hA1, hB1]
    rw [hsum1, hsum2]
    exact Finset.sum_congr rfl (fun k _ => hpoint k)
  · have hE : (@padEmbed F _ n N).size = 0 := rfl
    have hP : (@padProject F _ n N hnN).size = 0 := rfl
    rw [ArithmeticCircuit.size_subst, ArithmeticCircuit.size_subst, hE, hP,
      zero_add, add_zero]

/-- **Rpow size bound.** The recursive-circuit size is bounded by the
`r`-exponential rewritten as a power of `q ^ k` through `Real.logb`. -/
theorem recursiveCircuit_size_le_rpow {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)))
    {r : ℕ} (hq : 2 ≤ q) (hlen : terms.length ≤ r) (hqr : q ^ 2 < r) (k : ℕ) :
    ((recursiveCircuit terms k).size : ℝ) ≤
      (1 + 6 * r * q ^ 2) * ((q ^ k : ℕ) : ℝ) ^ Real.logb q r := by
  have hle := recursiveCircuit_size_le terms hlen hqr k
  have hleR : ((recursiveCircuit terms k).size : ℝ)
      + 6 * (r : ℝ) * (q : ℝ) ^ 2 * (q : ℝ) ^ (2 * k) ≤
      (1 + 6 * (r : ℝ) * (q : ℝ) ^ 2) * (r : ℝ) ^ k := by
    exact_mod_cast hle
  have hnn : (0 : ℝ) ≤ 6 * (r : ℝ) * (q : ℝ) ^ 2 * (q : ℝ) ^ (2 * k) := by
    positivity
  have hdrop : ((recursiveCircuit terms k).size : ℝ) ≤
      (1 + 6 * (r : ℝ) * (q : ℝ) ^ 2) * (r : ℝ) ^ k := by
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (by omega : 0 < q)
  have hq1 : (q : ℝ) ≠ 1 := by
    exact_mod_cast (by omega : q ≠ 1)
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le (q ^ 2)) hqr
  have hident : (r : ℝ) ^ k = ((q ^ k : ℕ) : ℝ) ^ Real.logb (q : ℝ) (r : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hqpos.le, mul_comm ((k : ℕ) : ℝ),
      Real.rpow_mul hqpos.le, Real.rpow_logb hqpos hq1 hrpos]
  rw [hident] at hdrop
  exact hdrop

/-- **Existence bound from trilinear rank.** Padding up to a power of the base
gives a circuit whose size is controlled by the rank. -/
theorem exists_circuit_size_le_rpow_of_rank {F : Type u} [Field F] {q r : ℕ}
    (hq : 2 ≤ q) (hqr : q ^ 2 < r)
    (h : MatrixMultiplicationExponent.HasTrilinearRankAtMost
      (MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q) r)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ c : MatrixArithmeticCircuit F n n n, IsMatrixMultiplication c ∧
      (c.size : ℝ) ≤ r * (1 + 6 * r * q ^ 2) * (n : ℝ) ^ Real.logb q r := by
  have hq1 : 1 < q := by omega
  have hn0 : n ≠ 0 := by omega
  have hlt : n < q ^ (Nat.log q n).succ := Nat.lt_pow_succ_log_self hq1 n
  have hlt1 : n < q ^ (Nat.log q n + 1) := by
    rwa [Nat.succ_eq_add_one] at hlt
  have hle : n ≤ q ^ (Nat.log q n + 1) := le_of_lt hlt1
  have hlog : q ^ Nat.log q n ≤ n := Nat.pow_log_le_self q hn0
  have hqk : q ^ (Nat.log q n + 1) ≤ q * n := by
    rw [pow_succ]
    calc q ^ Nat.log q n * q ≤ n * q :=
        mul_le_mul_of_nonneg_right hlog (Nat.zero_le q)
      _ = q * n := by ring
  obtain ⟨terms, hlen, hcorr⟩ :=
    exists_recursiveCircuit_isMatrixMultiplication h (Nat.log q n + 1)
  obtain ⟨c, hc, hsize⟩ := IsMatrixMultiplication.exists_size_le_of_le hle hcorr
  refine ⟨c, hc, ?_⟩
  have hbound :=
    recursiveCircuit_size_le_rpow terms hq hlen hqr (Nat.log q n + 1)
  have hsizeR : (c.size : ℝ)
      ≤ ((recursiveCircuit terms (Nat.log q n + 1)).size : ℝ) := by
    exact_mod_cast hsize
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqne : (q : ℝ) ≠ 1 := by exact_mod_cast (by omega : q ≠ 1)
  have hrpos : (0 : ℝ) < (r : ℝ) :=
    by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hqr
  have hq1R : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by
    have h4 : (2 : ℕ) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    norm_num at h4
    have hr1 : 1 ≤ r := by omega
    exact_mod_cast hr1
  have hlognn : (0 : ℝ) ≤ Real.logb (q : ℝ) (r : ℝ) :=
    Real.logb_nonneg hq1R hr1R
  have hqkR : (((q ^ (Nat.log q n + 1) : ℕ)) : ℝ) ≤ (q : ℝ) * (n : ℝ) := by
    have h2 : (((q ^ (Nat.log q n + 1) : ℕ)) : ℝ) ≤ (((q * n : ℕ)) : ℝ) := by
      exact_mod_cast hqk
    rwa [Nat.cast_mul] at h2
  have hpow : (((q ^ (Nat.log q n + 1) : ℕ)) : ℝ) ^ Real.logb q r
      ≤ (r : ℝ) * (n : ℝ) ^ Real.logb q r := by
    calc (((q ^ (Nat.log q n + 1) : ℕ)) : ℝ) ^ Real.logb q r
        ≤ ((q : ℝ) * (n : ℝ)) ^ Real.logb q r :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hqkR hlognn
      _ = (q : ℝ) ^ Real.logb q r * (n : ℝ) ^ Real.logb q r :=
          Real.mul_rpow hqpos.le (Nat.cast_nonneg n)
      _ = (r : ℝ) * (n : ℝ) ^ Real.logb q r := by
          rw [Real.rpow_logb hqpos hqne hrpos]
  have hnnA : (0 : ℝ) ≤ 1 + 6 * r * q ^ 2 := by positivity
  have hfin : (1 + 6 * r * q ^ 2)
        * (((q ^ (Nat.log q n + 1) : ℕ)) : ℝ) ^ Real.logb q r
      ≤ (1 + 6 * r * q ^ 2) * ((r : ℝ) * (n : ℝ) ^ Real.logb q r) :=
    mul_le_mul_of_nonneg_left hpow hnnA
  have hcomb : (c.size : ℝ)
      ≤ (1 + 6 * r * q ^ 2) * ((r : ℝ) * (n : ℝ) ^ Real.logb q r) :=
    le_trans (le_trans hsizeR hbound) hfin
  convert hcomb using 1
  ring

/-- **Strassen recursion.** The rank-seven decomposition yields recursive
circuits with the classical size bound at every level. -/
theorem exists_strassen_recursiveCircuit (F : Type u) [Field F] :
    ∃ terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)),
      terms.length ≤ 7 ∧
      ∀ k, IsMatrixMultiplication (recursiveCircuit terms k) ∧
        (recursiveCircuit terms k).size + 168 * 4 ^ k ≤ 169 * 7 ^ k := by
  obtain ⟨terms, hlength, hterms⟩ :=
    MatrixMultiplicationExponent.squareMatrixMultiplicationTensor_rank_le_seven F
  refine ⟨terms, hlength, fun k => ?_⟩
  refine ⟨recursiveCircuit_isMatrixMultiplication terms hterms k, ?_⟩
  have h42 : (2 : ℕ) ^ (2 * k) = 4 ^ k := by
    rw [pow_mul]
    norm_num
  have h := recursiveCircuit_size_le terms hlength (show 2 ^ 2 < 7 by decide) k
  rw [h42] at h
  norm_num at h
  exact h

/-- **Circuit exponent from rank.** The square circuit exponent is at most `Real.logb q r`
when the `q`-tensor has trilinear rank at most `r`. -/
theorem squareMatrixMultiplicationCircuitExponent_le_logb {F : Type u} [Field F]
    {q r : ℕ} (hq : 2 ≤ q) (hqr : q ^ 2 < r)
    (h : MatrixMultiplicationExponent.HasTrilinearRankAtMost
      (MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q) r) :
    squareMatrixMultiplicationCircuitExponent F ≤ ENNReal.ofReal (Real.logb q r) := by
  have hq1 : 1 < q := by omega
  have hr1 : 1 ≤ r := by
    have h4 : (2 : ℕ) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    norm_num at h4
    omega
  have hlognn : 0 ≤ Real.logb (q : ℝ) (r : ℝ) :=
    Real.logb_nonneg (by exact_mod_cast hq1) (by exact_mod_cast hr1)
  rw [squareMatrixMultiplicationCircuitExponent_le_iff F hlognn]
  refine ⟨by norm_num, hlognn, fun ε hε => ?_⟩
  have hrpos : (0 : ℝ) < (r : ℝ) :=
    by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hqr
  have hCpos : (0 : ℝ) < (r : ℝ) * (1 + 6 * (r : ℝ) * (q : ℝ) ^ 2) := by
    have hC1 : (0 : ℝ) < 1 + 6 * (r : ℝ) * (q : ℝ) ^ 2 := by positivity
    exact mul_pos hrpos hC1
  refine ⟨(r : ℝ) * (1 + 6 * (r : ℝ) * (q : ℝ) ^ 2), hCpos, 1, by norm_num, ?_⟩
  intro n hn
  obtain ⟨c, hc, hsize⟩ := exists_circuit_size_le_rpow_of_rank hq hqr h hn
  rw [MatrixMultiplicationExponent.rectangularInnerDimension_one]
  refine ⟨c, hc, ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrpow : (n : ℝ) ^ Real.logb (q : ℝ) (r : ℝ)
      ≤ (n : ℝ) ^ (Real.logb (q : ℝ) (r : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  calc (c.size : ℝ)
      ≤ (r : ℝ) * (1 + 6 * (r : ℝ) * (q : ℝ) ^ 2)
        * (n : ℝ) ^ Real.logb (q : ℝ) (r : ℝ) := hsize
    _ ≤ (r : ℝ) * (1 + 6 * (r : ℝ) * (q : ℝ) ^ 2)
        * (n : ℝ) ^ (Real.logb (q : ℝ) (r : ℝ) + ε) :=
      mul_le_mul_of_nonneg_left hrpow hCpos.le

/-- **Tensor exponent from rank.** The rank-defined `matrixMultiplicationExponent`
is at most `Real.logb q r` when the `q`-tensor has trilinear rank at most `r`. -/
theorem matrixMultiplicationExponent_le_logb {F : Type u} [Field F] [Infinite F]
    {q r : ℕ} (hq : 2 ≤ q) (hqr : q ^ 2 < r)
    (h : MatrixMultiplicationExponent.HasTrilinearRankAtMost
      (MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F q) r) :
    MatrixMultiplicationExponent.matrixMultiplicationExponent F ≤
      ENNReal.ofReal (Real.logb q r) := by
  rw [← SquareMatrixMultiplicationBoundsWanted.squareOperationRankBridge]
  exact squareMatrixMultiplicationCircuitExponent_le_logb hq hqr h

end

end Cslib.Complexity.Algebraic
