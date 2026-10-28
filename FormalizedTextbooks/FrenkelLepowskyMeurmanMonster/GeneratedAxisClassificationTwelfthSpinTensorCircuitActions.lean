/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorCircuitData

/-! Exact source operators for compact tensor replay. The full source input and rational spatial
matrix bindings are explicit prerequisites of the final action theorem. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Genuine right monomial followed by the actual second quadratic diagonal. -/
def generatedTwelfthSpinTensorPre (i : Fin 12) : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph
    (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactSecondPhaseRows i)) *
      monsterMonomialPermutationHolomorph (generatedTwelfthSpinCompactRight i)

/-- Genuine first quadratic diagonal, left monomial and complete central Pauli. -/
def generatedTwelfthSpinTensorPost (i : Fin 12) : SpinHolomorph :=
  spinHolomorphIncl (generatedTwelfthSpinCompactPauli i) *
    monsterMonomialPermutationHolomorph (generatedTwelfthSpinCompactLeft i) *
      monsterMonomialDiagonalHolomorph
        (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactFirstPhaseRows i))

/-- One pair of individual genuine Fourier factors; the second acts first. -/
def generatedTwelfthSpinTensorPair (p : Fin 12 × Fin 12) : SpinHolomorph :=
  generatedNinthLowerSpinHadamard p.1 * generatedNinthLowerSpinHadamard p.2

/-- Exact finite source-address conditions for both compact monomial boundaries. -/
def generatedTwelfthSpinTensorAddressCondition (i : Fin 12) (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedTwelfthSpinTensorPreLabel i n =
      nortonUIntegerLabel ((generatedTwelfthSpinCompactRight i).symm t) ∧
    generatedTwelfthSpinTensorPreSign i n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactSecondPhaseRows i))
          t) ∧
    generatedTwelfthSpinTensorPostLabel i n = nortonUIntegerLabel
      ((generatedTwelfthSpinCompactLeft i).symm
        (t + spinTranslation (generatedTwelfthSpinCompactPauli i))) ∧
    generatedTwelfthSpinTensorPostSign i n =
      nortonUIntegerSign (spinPhase (generatedTwelfthSpinCompactPauli i) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactFirstPhaseRows i))
            ((generatedTwelfthSpinCompactLeft i).symm
              (t + spinTranslation (generatedTwelfthSpinCompactPauli i))))

/-- Finite Fourier label covariance uses every one of the original twelve source coordinates. -/
def generatedTwelfthSpinTensorFourierAddressCondition (k : Fin 12) (n : Fin 4096) : Prop :=
  nortonUIntegerLabel (golayLabelCoefficients n + Pi.single k 1) =
    ⟨(Nat.xor n.val (2 ^ k.val)) % 4096, Nat.mod_lt _ (by decide)⟩

/-- Exact address and sign certificates identify the whole genuine pre-boundary operator. -/
theorem generatedTwelfth_spin_tensor_pre_embed (i : Fin 12)
    (h : ∀ n, generatedTwelfthSpinTensorAddressCondition i n)
    (v : NortonUIntegerVector) :
    (generatedTwelfthSpinTensorPre i).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedTwelfthSpinTensorPreInteger i v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedTwelfthSpinTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (monsterMonomialQuadratic
    (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactSecondPhaseRows i)) t) *
      (v (nortonUIntegerLabel ((generatedTwelfthSpinCompactRight i).symm t)) : ℝ) =
        (generatedTwelfthSpinTensorPreSign i (nortonUIntegerLabel t) *
          v (generatedTwelfthSpinTensorPreLabel i (nortonUIntegerLabel t)) : ℤ)
  rw [ht.1, ht.2.1, Int.cast_mul, nortonUIntegerSign_real]

/-- The post-boundary certificate keeps the complete actual Pauli central sign. -/
theorem generatedTwelfth_spin_tensor_post_embed (i : Fin 12)
    (h : ∀ n, generatedTwelfthSpinTensorAddressCondition i n)
    (v : NortonUIntegerVector) :
    (generatedTwelfthSpinTensorPost i).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedTwelfthSpinTensorPostInteger i v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedTwelfthSpinTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (spinPhase (generatedTwelfthSpinCompactPauli i) t) *
    (qSign (monsterMonomialQuadratic
      (generatedTwelfthSpinCompactPhase (generatedTwelfthSpinCompactFirstPhaseRows i))
        ((generatedTwelfthSpinCompactLeft i).symm
          (t + spinTranslation (generatedTwelfthSpinCompactPauli i)))) *
      ((v (nortonUIntegerLabel ((generatedTwelfthSpinCompactLeft i).symm
        (t + spinTranslation (generatedTwelfthSpinCompactPauli i))))) : ℝ)) =
      (generatedTwelfthSpinTensorPostSign i (nortonUIntegerLabel t) *
        v (generatedTwelfthSpinTensorPostLabel i (nortonUIntegerLabel t)) : ℤ)
  rw [ht.2.2.1, ht.2.2.2, Int.cast_mul, Int.cast_mul,
    nortonUIntegerSign_real, nortonUIntegerSign_real]
  ring

/-- Computable two-term labels are the already proved genuine individual Fourier numerator. -/
theorem generatedTwelfth_spin_tensor_fourier_integer (k : Fin 12)
    (h : ∀ n, generatedTwelfthSpinTensorFourierAddressCondition k n)
    (v : NortonUIntegerVector) :
    generatedNinthLowerSpinHadamardInteger k v =
      generatedTwelfthSpinTensorFourierInteger k v := by
  funext n
  have hn := h n
  unfold generatedTwelfthSpinTensorFourierAddressCondition at hn
  simp only [generatedNinthLowerSpinHadamardInteger,
    generatedTwelfthSpinTensorFourierInteger, hn]
  congr 1
  by_cases hb : n.val.testBit k.val
  · simp [nortonUIntegerSign, golayLabelCoefficients, hb]
  · simp [nortonUIntegerSign, golayLabelCoefficients, hb]

/-- Every pair update is normalized by exactly two in the genuine real spin space. -/
theorem generatedTwelfth_spin_tensor_pair_embed (p : Fin 12 × Fin 12)
    (haddress : ∀ k n, generatedTwelfthSpinTensorFourierAddressCondition k n)
    (v w : NortonUIntegerVector)
    (h : ∀ n, generatedTwelfthSpinTensorFourierInteger p.1
      (generatedTwelfthSpinTensorFourierInteger p.2 v) n = 2 * w n) :
    (generatedTwelfthSpinTensorPair p).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed w := by
  change (generatedNinthLowerSpinHadamard p.1).val
    ((generatedNinthLowerSpinHadamard p.2).val (nortonUIntegerEmbed v)) = _
  rw [generatedNinth_lower_spin_hadamard_integer_embed,
    generatedTwelfth_spin_tensor_fourier_integer p.2 (haddress p.2), map_smul,
    generatedNinth_lower_spin_hadamard_integer_embed,
    generatedTwelfth_spin_tensor_fourier_integer p.1 (haddress p.1)]
  have he : nortonUIntegerEmbed (generatedTwelfthSpinTensorFourierInteger p.1
      (generatedTwelfthSpinTensorFourierInteger p.2 v)) =
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
theorem generatedTwelfth_spin_tensor_pair_replay
    (pairs : List (Fin 12 × Fin 12)) (states : ℕ → NortonUIntegerVector)
    (haddress : ∀ k n, generatedTwelfthSpinTensorFourierAddressCondition k n)
    (hstep : ∀ s p, pairs[s]? = some p → ∀ n,
      generatedTwelfthSpinTensorFourierInteger p.1
        (generatedTwelfthSpinTensorFourierInteger p.2 (states s)) n =
          2 * states (s + 1) n) :
    ((pairs.reverse.map generatedTwelfthSpinTensorPair).prod).val
      (nortonUIntegerEmbed (states 0)) = nortonUIntegerEmbed (states pairs.length) := by
  induction pairs generalizing states with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    change ((ps.reverse.map generatedTwelfthSpinTensorPair).prod).val
      ((generatedTwelfthSpinTensorPair p).val (nortonUIntegerEmbed (states 0))) = _
    rw [generatedTwelfth_spin_tensor_pair_embed p haddress (states 0) (states 1)
      (hstep 0 p (by simp))]
    have ht : ∀ s q, ps[s]? = some q → ∀ n,
        generatedTwelfthSpinTensorFourierInteger q.1
          (generatedTwelfthSpinTensorFourierInteger q.2 (states (s + 1))) n =
            2 * states (s + 1 + 1) n := by
      intro s q hq
      exact hstep (s + 1) q (by simpa using hq)
    simpa only [List.length_cons] using ih (fun s => states (s + 1)) ht

private theorem pair_prod (pairs : List (Fin 12 × Fin 12)) :
    ((pairs.flatMap (fun p => [p.1, p.2])).map generatedNinthLowerSpinHadamard).prod =
      (pairs.map generatedTwelfthSpinTensorPair).prod := by
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
theorem generatedTwelfth_spin_tensor_pair_word : ∀ i : Fin 12,
    generatedTwelfthSpinCompactHadamardWord i =
      (generatedTwelfthSpinTensorPairWord i).reverse.flatMap (fun p => [p.1, p.2]) := by
  decide +kernel

/-- The compact operator is exactly the pre-boundary, complete pair chain and post-boundary. -/
theorem generatedTwelfth_spin_tensor_compact_factorization (i : Fin 12) :
    generatedTwelfthSpinCompact i = generatedTwelfthSpinTensorPost i *
      (((generatedTwelfthSpinTensorPairWord i).reverse.map
        generatedTwelfthSpinTensorPair).prod) * generatedTwelfthSpinTensorPre i := by
  rw [generatedTwelfthSpinCompact, generatedTwelfth_spin_tensor_pair_word, pair_prod]
  simp only [generatedTwelfthSpinTensorPre, generatedTwelfthSpinTensorPost, mul_assoc]

/-- Full-column replay from explicit finite cache obligations. Source input and spatial bindings
can use this exact integer action without assumptions about any tensor coordinate being zero. -/
theorem generatedTwelfth_spin_tensor_column_replay (i : Fin 12) (j : Fin 24)
    (haddress : ∀ n, generatedTwelfthSpinTensorAddressCondition i n)
    (hfourier : ∀ k n, generatedTwelfthSpinTensorFourierAddressCondition k n)
    (hstart : ∀ n, generatedTwelfthSpinTensorStageInteger i 0 n j =
      generatedTwelfthSpinTensorPreInteger i
        (fun m => generatedTwelfthSpinTensorSpatialInteger i m j) n)
    (hstep : ∀ s p, (generatedTwelfthSpinTensorPairWord i)[s]? = some p → ∀ n,
      generatedTwelfthSpinTensorFourierInteger p.1
        (generatedTwelfthSpinTensorFourierInteger p.2
          (fun m => generatedTwelfthSpinTensorStageInteger i s m j)) n =
            2 * generatedTwelfthSpinTensorStageInteger i (s + 1) n j)
    (hfinish : ∀ n, generatedTwelfthSpinTensorPostInteger i
      (fun m => generatedTwelfthSpinTensorStageInteger i
        (generatedTwelfthSpinTensorPairWord i).length m j) n =
          (generatedTwelfthSpinTensorSpatialDenominator i : ℤ) *
            generatedTwelfthSpinTensorInputInteger n j) :
    (generatedTwelfthSpinCompact i).val
      (nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorSpatialInteger i n j)) =
        (generatedTwelfthSpinTensorSpatialDenominator i : ℝ) •
          nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorInputInteger n j) := by
  rw [generatedTwelfth_spin_tensor_compact_factorization]
  change (generatedTwelfthSpinTensorPost i).val
    ((((generatedTwelfthSpinTensorPairWord i).reverse.map
      generatedTwelfthSpinTensorPair).prod).val
        ((generatedTwelfthSpinTensorPre i).val
          (nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorSpatialInteger i n j)))) = _
  rw [generatedTwelfth_spin_tensor_pre_embed i haddress]
  have hzero : generatedTwelfthSpinTensorPreInteger i
      (fun n => generatedTwelfthSpinTensorSpatialInteger i n j) =
        (fun n => generatedTwelfthSpinTensorStageInteger i 0 n j) := by
    funext n
    exact (hstart n).symm
  rw [hzero, generatedTwelfth_spin_tensor_pair_replay
    (generatedTwelfthSpinTensorPairWord i)
    (fun s n => generatedTwelfthSpinTensorStageInteger i s n j) hfourier hstep,
    generatedTwelfth_spin_tensor_post_embed i haddress]
  ext t
  simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, hfinish,
    Int.cast_mul, Int.cast_natCast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
