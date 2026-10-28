/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorCircuitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinCompactOriented

/-! Exact source operators for compact tensor replay. The full source input and rational spatial
matrix bindings are explicit prerequisites of the final action theorem. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Genuine right monomial followed by the actual second quadratic diagonal. -/
def generatedTwelfthIncomingSpinTensorPre (i : Fin 1) : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph
    (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactSecondPhaseRows i)) *
      monsterMonomialPermutationHolomorph (generatedTwelfthIncomingSpinCompactRight i)

/-- Genuine first quadratic diagonal, left monomial and complete central Pauli. -/
def generatedTwelfthIncomingSpinTensorPost (i : Fin 1) : SpinHolomorph :=
  spinHolomorphIncl (generatedTwelfthIncomingSpinCompactOrientedPauli i) *
    monsterMonomialPermutationHolomorph (generatedTwelfthIncomingSpinCompactLeft i) *
      monsterMonomialDiagonalHolomorph
        (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactFirstPhaseRows i))

/-- One pair of individual genuine Fourier factors; the second acts first. -/
def generatedTwelfthIncomingSpinTensorPair (p : Fin 12 × Fin 12) : SpinHolomorph :=
  generatedNinthLowerSpinHadamard p.1 * generatedNinthLowerSpinHadamard p.2

/-- Exact finite source-address conditions for both compact monomial boundaries. -/
def generatedTwelfthIncomingSpinTensorAddressCondition (i : Fin 1) (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedTwelfthIncomingSpinTensorPreLabel i n =
      nortonUIntegerLabel ((generatedTwelfthIncomingSpinCompactRight i).symm t) ∧
    generatedTwelfthIncomingSpinTensorPreSign i n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactSecondPhaseRows i))
          t) ∧
    generatedTwelfthIncomingSpinTensorPostLabel i n = nortonUIntegerLabel
      ((generatedTwelfthIncomingSpinCompactLeft i).symm
        (t + spinTranslation (generatedTwelfthIncomingSpinCompactOrientedPauli i))) ∧
    generatedTwelfthIncomingSpinTensorPostSign i n =
      nortonUIntegerSign (spinPhase (generatedTwelfthIncomingSpinCompactOrientedPauli i) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactFirstPhaseRows i))
            ((generatedTwelfthIncomingSpinCompactLeft i).symm
              (t + spinTranslation (generatedTwelfthIncomingSpinCompactOrientedPauli i))))

/-- Finite Fourier label covariance uses every one of the original twelve source coordinates. -/
def generatedTwelfthIncomingSpinTensorFourierAddressCondition (k : Fin 12) (n : Fin 4096) : Prop :=
  nortonUIntegerLabel (golayLabelCoefficients n + Pi.single k 1) =
    ⟨(Nat.xor n.val (2 ^ k.val)) % 4096, Nat.mod_lt _ (by decide)⟩

/-- Exact address and sign certificates identify the whole genuine pre-boundary operator. -/
theorem generatedTwelfth_incoming_spin_tensor_pre_embed (i : Fin 1)
    (h : ∀ n, generatedTwelfthIncomingSpinTensorAddressCondition i n)
    (v : NortonUIntegerVector) :
    (generatedTwelfthIncomingSpinTensorPre i).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedTwelfthIncomingSpinTensorPreInteger i v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedTwelfthIncomingSpinTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (monsterMonomialQuadratic
    (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactSecondPhaseRows i)) t) *
      (v (nortonUIntegerLabel ((generatedTwelfthIncomingSpinCompactRight i).symm t)) : ℝ) =
        (generatedTwelfthIncomingSpinTensorPreSign i (nortonUIntegerLabel t) *
          v (generatedTwelfthIncomingSpinTensorPreLabel i (nortonUIntegerLabel t)) : ℤ)
  rw [ht.1, ht.2.1, Int.cast_mul, nortonUIntegerSign_real]

/-- The post-boundary certificate keeps the complete actual Pauli central sign. -/
theorem generatedTwelfth_incoming_spin_tensor_post_embed (i : Fin 1)
    (h : ∀ n, generatedTwelfthIncomingSpinTensorAddressCondition i n)
    (v : NortonUIntegerVector) :
    (generatedTwelfthIncomingSpinTensorPost i).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedTwelfthIncomingSpinTensorPostInteger i v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedTwelfthIncomingSpinTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (spinPhase (generatedTwelfthIncomingSpinCompactOrientedPauli i) t) *
    (qSign (monsterMonomialQuadratic
      (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactFirstPhaseRows i))
        ((generatedTwelfthIncomingSpinCompactLeft i).symm
          (t + spinTranslation (generatedTwelfthIncomingSpinCompactOrientedPauli i)))) *
      ((v (nortonUIntegerLabel ((generatedTwelfthIncomingSpinCompactLeft i).symm
        (t + spinTranslation (generatedTwelfthIncomingSpinCompactOrientedPauli i))))) : ℝ)) =
      (generatedTwelfthIncomingSpinTensorPostSign i (nortonUIntegerLabel t) *
        v (generatedTwelfthIncomingSpinTensorPostLabel i (nortonUIntegerLabel t)) : ℤ)
  rw [ht.2.2.1, ht.2.2.2, Int.cast_mul, Int.cast_mul,
    nortonUIntegerSign_real, nortonUIntegerSign_real]
  ring

/-- Computable two-term labels are the already proved genuine individual Fourier numerator. -/
theorem generatedTwelfth_incoming_spin_tensor_fourier_integer (k : Fin 12)
    (h : ∀ n, generatedTwelfthIncomingSpinTensorFourierAddressCondition k n)
    (v : NortonUIntegerVector) :
    generatedNinthLowerSpinHadamardInteger k v =
      generatedTwelfthIncomingSpinTensorFourierInteger k v := by
  funext n
  have hn := h n
  unfold generatedTwelfthIncomingSpinTensorFourierAddressCondition at hn
  simp only [generatedNinthLowerSpinHadamardInteger,
    generatedTwelfthIncomingSpinTensorFourierInteger, hn]
  congr 1
  by_cases hb : n.val.testBit k.val
  · simp [nortonUIntegerSign, golayLabelCoefficients, hb]
  · simp [nortonUIntegerSign, golayLabelCoefficients, hb]

/-- Every pair update is normalized by exactly two in the genuine real spin space. -/
theorem generatedTwelfth_incoming_spin_tensor_pair_embed (p : Fin 12 × Fin 12)
    (haddress : ∀ k n, generatedTwelfthIncomingSpinTensorFourierAddressCondition k n)
    (v w : NortonUIntegerVector)
    (h : ∀ n, generatedTwelfthIncomingSpinTensorFourierInteger p.1
      (generatedTwelfthIncomingSpinTensorFourierInteger p.2 v) n = 2 * w n) :
    (generatedTwelfthIncomingSpinTensorPair p).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed w := by
  change (generatedNinthLowerSpinHadamard p.1).val
    ((generatedNinthLowerSpinHadamard p.2).val (nortonUIntegerEmbed v)) = _
  rw [generatedNinth_lower_spin_hadamard_integer_embed,
    generatedTwelfth_incoming_spin_tensor_fourier_integer p.2 (haddress p.2), map_smul,
    generatedNinth_lower_spin_hadamard_integer_embed,
    generatedTwelfth_incoming_spin_tensor_fourier_integer p.1 (haddress p.1)]
  have he : nortonUIntegerEmbed (generatedTwelfthIncomingSpinTensorFourierInteger p.1
      (generatedTwelfthIncomingSpinTensorFourierInteger p.2 v)) =
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
theorem generatedTwelfth_incoming_spin_tensor_pair_replay
    (pairs : List (Fin 12 × Fin 12)) (states : ℕ → NortonUIntegerVector)
    (haddress : ∀ k n, generatedTwelfthIncomingSpinTensorFourierAddressCondition k n)
    (hstep : ∀ s p, pairs[s]? = some p → ∀ n,
      generatedTwelfthIncomingSpinTensorFourierInteger p.1
        (generatedTwelfthIncomingSpinTensorFourierInteger p.2 (states s)) n =
          2 * states (s + 1) n) :
    ((pairs.reverse.map generatedTwelfthIncomingSpinTensorPair).prod).val
      (nortonUIntegerEmbed (states 0)) = nortonUIntegerEmbed (states pairs.length) := by
  induction pairs generalizing states with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    change ((ps.reverse.map generatedTwelfthIncomingSpinTensorPair).prod).val
      ((generatedTwelfthIncomingSpinTensorPair p).val (nortonUIntegerEmbed (states 0))) = _
    rw [generatedTwelfth_incoming_spin_tensor_pair_embed p haddress (states 0) (states 1)
      (hstep 0 p (by simp))]
    have ht : ∀ s q, ps[s]? = some q → ∀ n,
        generatedTwelfthIncomingSpinTensorFourierInteger q.1
          (generatedTwelfthIncomingSpinTensorFourierInteger q.2 (states (s + 1))) n =
            2 * states (s + 1 + 1) n := by
      intro s q hq
      exact hstep (s + 1) q (by simpa using hq)
    simpa only [List.length_cons] using ih (fun s => states (s + 1)) ht

private theorem pair_prod (pairs : List (Fin 12 × Fin 12)) :
    ((pairs.flatMap (fun p => [p.1, p.2])).map generatedNinthLowerSpinHadamard).prod =
      (pairs.map generatedTwelfthIncomingSpinTensorPair).prod := by
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
theorem generatedTwelfth_incoming_spin_tensor_pair_word : ∀ i : Fin 1,
    generatedTwelfthIncomingSpinCompactHadamardWord i =
      (generatedTwelfthIncomingSpinTensorPairWord i).reverse.flatMap (fun p => [p.1, p.2]) := by
  decide +kernel

/-- The compact operator is exactly the pre-boundary, complete pair chain and post-boundary. -/
theorem generatedTwelfth_incoming_spin_tensor_compact_factorization (i : Fin 1) :
    generatedTwelfthIncomingSpinCompactOriented i = generatedTwelfthIncomingSpinTensorPost i *
      (((generatedTwelfthIncomingSpinTensorPairWord i).reverse.map
        generatedTwelfthIncomingSpinTensorPair).prod) * generatedTwelfthIncomingSpinTensorPre i := by
  rw [generatedTwelfthIncomingSpinCompactOriented, generatedTwelfth_incoming_spin_tensor_pair_word, pair_prod]
  simp only [generatedTwelfthIncomingSpinTensorPre, generatedTwelfthIncomingSpinTensorPost, mul_assoc]

/-- Full-column replay from explicit finite cache obligations. Source input and spatial bindings
can use this exact integer action without assumptions about any tensor coordinate being zero. -/
theorem generatedTwelfth_incoming_spin_tensor_column_replay (i : Fin 1) (j : Fin 24)
    (haddress : ∀ n, generatedTwelfthIncomingSpinTensorAddressCondition i n)
    (hfourier : ∀ k n, generatedTwelfthIncomingSpinTensorFourierAddressCondition k n)
    (hstart : ∀ n, generatedTwelfthIncomingSpinTensorStageInteger i 0 n j =
      generatedTwelfthIncomingSpinTensorPreInteger i
        (fun m => generatedTwelfthIncomingSpinTensorSpatialInteger i m j) n)
    (hstep : ∀ s p, (generatedTwelfthIncomingSpinTensorPairWord i)[s]? = some p → ∀ n,
      generatedTwelfthIncomingSpinTensorFourierInteger p.1
        (generatedTwelfthIncomingSpinTensorFourierInteger p.2
          (fun m => generatedTwelfthIncomingSpinTensorStageInteger i s m j)) n =
            2 * generatedTwelfthIncomingSpinTensorStageInteger i (s + 1) n j)
    (hfinish : ∀ n, generatedTwelfthIncomingSpinTensorPostInteger i
      (fun m => generatedTwelfthIncomingSpinTensorStageInteger i
        (generatedTwelfthIncomingSpinTensorPairWord i).length m j) n =
          generatedTwelfthIncomingSpinTensorOutputInteger n j) :
    (generatedTwelfthIncomingSpinCompactOriented i).val
      (nortonUIntegerEmbed (fun n => generatedTwelfthIncomingSpinTensorSpatialInteger i n j)) =
        nortonUIntegerEmbed (fun n => generatedTwelfthIncomingSpinTensorOutputInteger n j) := by
  rw [generatedTwelfth_incoming_spin_tensor_compact_factorization]
  change (generatedTwelfthIncomingSpinTensorPost i).val
    ((((generatedTwelfthIncomingSpinTensorPairWord i).reverse.map
      generatedTwelfthIncomingSpinTensorPair).prod).val
        ((generatedTwelfthIncomingSpinTensorPre i).val
          (nortonUIntegerEmbed (fun n => generatedTwelfthIncomingSpinTensorSpatialInteger i n j)))) = _
  rw [generatedTwelfth_incoming_spin_tensor_pre_embed i haddress]
  have hzero : generatedTwelfthIncomingSpinTensorPreInteger i
      (fun n => generatedTwelfthIncomingSpinTensorSpatialInteger i n j) =
        (fun n => generatedTwelfthIncomingSpinTensorStageInteger i 0 n j) := by
    funext n
    exact (hstart n).symm
  rw [hzero, generatedTwelfth_incoming_spin_tensor_pair_replay
    (generatedTwelfthIncomingSpinTensorPairWord i)
    (fun s n => generatedTwelfthIncomingSpinTensorStageInteger i s n j) hfourier hstep,
    generatedTwelfth_incoming_spin_tensor_post_embed i haddress]
  ext t
  simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, hfinish,
    Int.cast_mul, Int.cast_natCast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
