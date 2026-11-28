/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.BilinearRecursion

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

end

end Cslib.Complexity.Algebraic
