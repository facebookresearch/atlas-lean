/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData

/-! Exact source operators for compact tensor replay. The full source input and rational spatial
matrix bindings are explicit prerequisites of the final action theorem. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Genuine right monomial followed by the actual second quadratic diagonal. -/
def generatedNinthLowerSpinTensorPre (i : Fin 11) : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph
    (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactSecondPhaseRows i)) *
      monsterMonomialPermutationHolomorph (generatedNinthLowerSpinCompactRight i)

/-- Genuine first quadratic diagonal, left monomial and complete central Pauli. -/
def generatedNinthLowerSpinTensorPost (i : Fin 11) : SpinHolomorph :=
  spinHolomorphIncl (generatedNinthLowerSpinCompactPauli i) *
    monsterMonomialPermutationHolomorph (generatedNinthLowerSpinCompactLeft i) *
      monsterMonomialDiagonalHolomorph
        (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactFirstPhaseRows i))

/-- One pair of individual genuine Fourier factors; the second acts first. -/
def generatedNinthLowerSpinTensorPair (p : Fin 12 × Fin 12) : SpinHolomorph :=
  generatedNinthLowerSpinHadamard p.1 * generatedNinthLowerSpinHadamard p.2

/-- Exact finite source-address conditions for both compact monomial boundaries. -/
def generatedNinthLowerSpinTensorAddressCondition (i : Fin 11) (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedNinthLowerSpinTensorPreLabel i n =
      nortonUIntegerLabel ((generatedNinthLowerSpinCompactRight i).symm t) ∧
    generatedNinthLowerSpinTensorPreSign i n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactSecondPhaseRows i))
          t) ∧
    generatedNinthLowerSpinTensorPostLabel i n = nortonUIntegerLabel
      ((generatedNinthLowerSpinCompactLeft i).symm
        (t + spinTranslation (generatedNinthLowerSpinCompactPauli i))) ∧
    generatedNinthLowerSpinTensorPostSign i n =
      nortonUIntegerSign (spinPhase (generatedNinthLowerSpinCompactPauli i) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactFirstPhaseRows i))
            ((generatedNinthLowerSpinCompactLeft i).symm
              (t + spinTranslation (generatedNinthLowerSpinCompactPauli i))))

/-- Finite Fourier label covariance uses every one of the original twelve source coordinates. -/
def generatedNinthLowerSpinTensorFourierAddressCondition (k : Fin 12) (n : Fin 4096) : Prop :=
  nortonUIntegerLabel (golayLabelCoefficients n + Pi.single k 1) =
    ⟨(Nat.xor n.val (2 ^ k.val)) % 4096, Nat.mod_lt _ (by decide)⟩

/-- Exact address and sign certificates identify the whole genuine pre-boundary operator. -/
theorem generatedNinth_lower_spin_tensor_pre_embed (i : Fin 11)
    (h : ∀ n, generatedNinthLowerSpinTensorAddressCondition i n)
    (v : NortonUIntegerVector) :
    (generatedNinthLowerSpinTensorPre i).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedNinthLowerSpinTensorPreInteger i v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedNinthLowerSpinTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (monsterMonomialQuadratic
    (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactSecondPhaseRows i)) t) *
      (v (nortonUIntegerLabel ((generatedNinthLowerSpinCompactRight i).symm t)) : ℝ) =
        (generatedNinthLowerSpinTensorPreSign i (nortonUIntegerLabel t) *
          v (generatedNinthLowerSpinTensorPreLabel i (nortonUIntegerLabel t)) : ℤ)
  rw [ht.1, ht.2.1, Int.cast_mul, nortonUIntegerSign_real]

/-- The post-boundary certificate keeps the complete actual Pauli central sign. -/
theorem generatedNinth_lower_spin_tensor_post_embed (i : Fin 11)
    (h : ∀ n, generatedNinthLowerSpinTensorAddressCondition i n)
    (v : NortonUIntegerVector) :
    (generatedNinthLowerSpinTensorPost i).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedNinthLowerSpinTensorPostInteger i v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedNinthLowerSpinTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (spinPhase (generatedNinthLowerSpinCompactPauli i) t) *
    (qSign (monsterMonomialQuadratic
      (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactFirstPhaseRows i))
        ((generatedNinthLowerSpinCompactLeft i).symm
          (t + spinTranslation (generatedNinthLowerSpinCompactPauli i)))) *
      ((v (nortonUIntegerLabel ((generatedNinthLowerSpinCompactLeft i).symm
        (t + spinTranslation (generatedNinthLowerSpinCompactPauli i))))) : ℝ)) =
      (generatedNinthLowerSpinTensorPostSign i (nortonUIntegerLabel t) *
        v (generatedNinthLowerSpinTensorPostLabel i (nortonUIntegerLabel t)) : ℤ)
  rw [ht.2.2.1, ht.2.2.2, Int.cast_mul, Int.cast_mul,
    nortonUIntegerSign_real, nortonUIntegerSign_real]
  ring

/-- Computable two-term labels are the already proved genuine individual Fourier numerator. -/
theorem generatedNinth_lower_spin_tensor_fourier_integer (k : Fin 12)
    (h : ∀ n, generatedNinthLowerSpinTensorFourierAddressCondition k n)
    (v : NortonUIntegerVector) :
    generatedNinthLowerSpinHadamardInteger k v =
      generatedNinthLowerSpinTensorFourierInteger k v := by
  funext n
  have hn := h n
  unfold generatedNinthLowerSpinTensorFourierAddressCondition at hn
  simp only [generatedNinthLowerSpinHadamardInteger,
    generatedNinthLowerSpinTensorFourierInteger, hn]
  congr 1
  by_cases hb : n.val.testBit k.val
  · simp [nortonUIntegerSign, golayLabelCoefficients, hb]
  · simp [nortonUIntegerSign, golayLabelCoefficients, hb]

/-- Every pair update is normalized by exactly two in the genuine real spin space. -/
theorem generatedNinth_lower_spin_tensor_pair_embed (p : Fin 12 × Fin 12)
    (haddress : ∀ k n, generatedNinthLowerSpinTensorFourierAddressCondition k n)
    (v w : NortonUIntegerVector)
    (h : ∀ n, generatedNinthLowerSpinTensorFourierInteger p.1
      (generatedNinthLowerSpinTensorFourierInteger p.2 v) n = 2 * w n) :
    (generatedNinthLowerSpinTensorPair p).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed w := by
  change (generatedNinthLowerSpinHadamard p.1).val
    ((generatedNinthLowerSpinHadamard p.2).val (nortonUIntegerEmbed v)) = _
  rw [generatedNinth_lower_spin_hadamard_integer_embed,
    generatedNinth_lower_spin_tensor_fourier_integer p.2 (haddress p.2), map_smul,
    generatedNinth_lower_spin_hadamard_integer_embed,
    generatedNinth_lower_spin_tensor_fourier_integer p.1 (haddress p.1)]
  have he : nortonUIntegerEmbed (generatedNinthLowerSpinTensorFourierInteger p.1
      (generatedNinthLowerSpinTensorFourierInteger p.2 v)) =
        (2 : ℝ) • nortonUIntegerEmbed w := by
    ext t
    simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, h, Int.cast_mul, Int.cast_ofNat]
  rw [he, smul_smul, smul_smul]
  have hs : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) * 2 = 1 := by
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp [hn]
    nlinarith
  rw [hs, one_smul]

/-- A chain of certified pair stages acts on the whole spin vector, retaining every coordinate. -/
theorem generatedNinth_lower_spin_tensor_pair_replay
    (pairs : List (Fin 12 × Fin 12)) (states : ℕ → NortonUIntegerVector)
    (haddress : ∀ k n, generatedNinthLowerSpinTensorFourierAddressCondition k n)
    (hstep : ∀ s p, pairs[s]? = some p → ∀ n,
      generatedNinthLowerSpinTensorFourierInteger p.1
        (generatedNinthLowerSpinTensorFourierInteger p.2 (states s)) n =
          2 * states (s + 1) n) :
    ((pairs.reverse.map generatedNinthLowerSpinTensorPair).prod).val
      (nortonUIntegerEmbed (states 0)) = nortonUIntegerEmbed (states pairs.length) := by
  induction pairs generalizing states with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    change ((ps.reverse.map generatedNinthLowerSpinTensorPair).prod).val
      ((generatedNinthLowerSpinTensorPair p).val (nortonUIntegerEmbed (states 0))) = _
    rw [generatedNinth_lower_spin_tensor_pair_embed p haddress (states 0) (states 1)
      (hstep 0 p (by simp))]
    have ht : ∀ s q, ps[s]? = some q → ∀ n,
        generatedNinthLowerSpinTensorFourierInteger q.1
          (generatedNinthLowerSpinTensorFourierInteger q.2 (states (s + 1))) n =
            2 * states (s + 1 + 1) n := by
      intro s q hq
      exact hstep (s + 1) q (by simpa using hq)
    simpa only [List.length_cons] using ih (fun s => states (s + 1)) ht

private theorem pair_prod (pairs : List (Fin 12 × Fin 12)) :
    ((pairs.flatMap (fun p => [p.1, p.2])).map generatedNinthLowerSpinHadamard).prod =
      (pairs.map generatedNinthLowerSpinTensorPair).prod := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [ih]
    rfl

set_option maxHeartbeats 8000000 in
-- Check that the paired circuit contains precisely the original finite Fourier word.
/-- Paired application order covers every genuine original Fourier factor exactly once. -/
theorem generatedNinth_lower_spin_tensor_pair_word : ∀ i : Fin 11,
    generatedNinthLowerSpinCompactHadamardWord i =
      (generatedNinthLowerSpinTensorPairWord i).reverse.flatMap (fun p => [p.1, p.2]) := by
  decide +kernel

/-- The compact operator is exactly the pre-boundary, complete pair chain and post-boundary. -/
theorem generatedNinth_lower_spin_tensor_compact_factorization (i : Fin 11) :
    generatedNinthLowerSpinCompact i = generatedNinthLowerSpinTensorPost i *
      (((generatedNinthLowerSpinTensorPairWord i).reverse.map
        generatedNinthLowerSpinTensorPair).prod) * generatedNinthLowerSpinTensorPre i := by
  rw [generatedNinthLowerSpinCompact, generatedNinth_lower_spin_tensor_pair_word, pair_prod]
  simp only [generatedNinthLowerSpinTensorPre, generatedNinthLowerSpinTensorPost, mul_assoc]

/-- Full-column replay from explicit finite cache obligations. Source input and spatial bindings
can use this exact integer action without assumptions about any tensor coordinate being zero. -/
theorem generatedNinth_lower_spin_tensor_column_replay (i : Fin 11) (j : Fin 24)
    (haddress : ∀ n, generatedNinthLowerSpinTensorAddressCondition i n)
    (hfourier : ∀ k n, generatedNinthLowerSpinTensorFourierAddressCondition k n)
    (hstart : ∀ n, generatedNinthLowerSpinTensorStageInteger i 0 n j =
      generatedNinthLowerSpinTensorPreInteger i
        (fun m => generatedNinthLowerSpinTensorSpatialInteger i m j) n)
    (hstep : ∀ s p, (generatedNinthLowerSpinTensorPairWord i)[s]? = some p → ∀ n,
      generatedNinthLowerSpinTensorFourierInteger p.1
        (generatedNinthLowerSpinTensorFourierInteger p.2
          (fun m => generatedNinthLowerSpinTensorStageInteger i s m j)) n =
            2 * generatedNinthLowerSpinTensorStageInteger i (s + 1) n j)
    (hfinish : ∀ n, generatedNinthLowerSpinTensorPostInteger i
      (fun m => generatedNinthLowerSpinTensorStageInteger i
        (generatedNinthLowerSpinTensorPairWord i).length m j) n =
          (generatedNinthLowerSpinTensorSpatialDenominator i : ℤ) *
            generatedNinthLowerSpinTensorInputInteger n j) :
    (generatedNinthLowerSpinCompact i).val
      (nortonUIntegerEmbed (fun n => generatedNinthLowerSpinTensorSpatialInteger i n j)) =
        (generatedNinthLowerSpinTensorSpatialDenominator i : ℝ) •
          nortonUIntegerEmbed (fun n => generatedNinthLowerSpinTensorInputInteger n j) := by
  rw [generatedNinth_lower_spin_tensor_compact_factorization]
  change (generatedNinthLowerSpinTensorPost i).val
    ((((generatedNinthLowerSpinTensorPairWord i).reverse.map
      generatedNinthLowerSpinTensorPair).prod).val
        ((generatedNinthLowerSpinTensorPre i).val
          (nortonUIntegerEmbed (fun n => generatedNinthLowerSpinTensorSpatialInteger i n j)))) = _
  rw [generatedNinth_lower_spin_tensor_pre_embed i haddress]
  have hzero : generatedNinthLowerSpinTensorPreInteger i
      (fun n => generatedNinthLowerSpinTensorSpatialInteger i n j) =
        (fun n => generatedNinthLowerSpinTensorStageInteger i 0 n j) := by
    funext n
    exact (hstart n).symm
  rw [hzero, generatedNinth_lower_spin_tensor_pair_replay
    (generatedNinthLowerSpinTensorPairWord i)
    (fun s n => generatedNinthLowerSpinTensorStageInteger i s n j) hfourier hstep,
    generatedNinth_lower_spin_tensor_post_embed i haddress]
  ext t
  simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, hfinish,
    Int.cast_mul, Int.cast_natCast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
