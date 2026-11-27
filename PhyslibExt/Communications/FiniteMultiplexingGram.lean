/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite multiplexing and the Gram matrix

## i. Overview

For finitely many waveforms and symbols, the matched-filter
output vector is the Gram matrix of the waveforms times the
symbol vector, so cross-user interference is exactly the
off-diagonal Gram action. Orthonormal waveform families
(FDMA carriers, disjoint TDMA slots, CDMA codes) recover the
symbols exactly. A two-waveform skew pair is a concrete
nonorthogonal example: its Gram entry `G 0 1 = 1/√2` adds the
predicted term to the first matched output.

## ii. Key results

- `matchedOutput_eq_gram_mulVec`: matched output is the Gram
  matrix times the symbol vector.
- `norm_matchedOutput_sub_le_interference`: deviation from the
  desired symbol is bounded by the interference norm.
- `fdma_matchedOutput_eq`, `tdma_matchedOutput_eq`,
  `cdma_matchedOutput_eq`: exact recovery for the three classical
  orthonormal families.
- `gram_skewPair_zero_one`, `skewPair_matchedOutput_zero`: the
  skew-pair interference term.

## iii. Table of contents

- A. Matched outputs and the Gram matrix

## iv. References

- B. P. Lathi and Z. Ding, *Modern Digital and Analog Communication
Systems*, fifth edition, Oxford University Press, 2019: orthogonal signaling, matched filtering and multiuser
  interference.

## A. Matched outputs and the Gram matrix

(multiplex Gram).
-/

@[expose] public section

namespace PhyslibExt.Communications.FiniteMultiplexingGram

open scoped InnerProductSpace Matrix

/-- Synchronous superposition `∑_k a_k u_k` of user waveforms `u_k` with symbols `a_k`. -/
noncomputable def superpose {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : κ → EuclideanSpace ℂ ι) (a : κ → ℂ) : EuclideanSpace ℂ ι :=
  ∑ k, a k • u k

/-- Matched-filter output of user `j`: `⟪u_j, ∑_k a_k u_k⟫`. -/
noncomputable def matchedOutput {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : κ → EuclideanSpace ℂ ι) (a : κ → ℂ) (j : κ) : ℂ :=
  ⟪u j, superpose u a⟫_ℂ

/-- The user waveform matrix: rows are samples, column `j` is the waveform `u j`. -/
def waveformMatrix {ι κ : Type} (u : κ → EuclideanSpace ℂ ι) : Matrix ι κ ℂ :=
  Matrix.of fun t j => u j t

/-- FDMA carrier of frequency `k` on `ZMod N`: `t ↦ N^{-1/2} · exp(2πi k t / N)`. -/
noncomputable def fdmaCarrier (N : ℕ) [NeZero N] (k : ZMod N) : EuclideanSpace ℂ (ZMod N) :=
  WithLp.toLp 2 fun t => ((Real.sqrt N)⁻¹ : ℂ) * ZMod.stdAddChar (k * t)

/-- The named CDMA spread-code pair `(1,1)/√2` and `(1,-1)/√2`. -/
noncomputable def cdmaCode : Fin 2 → EuclideanSpace ℂ (Fin 2) :=
  ![WithLp.toLp 2 ![((Real.sqrt 2)⁻¹ : ℂ), ((Real.sqrt 2)⁻¹ : ℂ)],
    WithLp.toLp 2 ![((Real.sqrt 2)⁻¹ : ℂ), -((Real.sqrt 2)⁻¹ : ℂ)]]

/-- A nonorthogonal normalized pair: `(1,0)` and `(1,1)/√2`. -/
noncomputable def skewPair : Fin 2 → EuclideanSpace ℂ (Fin 2) :=
  ![WithLp.toLp 2 ![1, 0],
    WithLp.toLp 2 ![((Real.sqrt 2)⁻¹ : ℂ), ((Real.sqrt 2)⁻¹ : ℂ)]]

/-- Inner product on `EuclideanSpace ℂ` as an explicit coordinate sum. -/
private theorem inner_eq_sum_star_mul {ι : Type} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℂ = ∑ t, star (x t) * y t := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

/-- The Gram matrix of the columns is `Uᴴ U` for the waveform matrix `U`. -/
lemma gram_eq_conjTranspose_mul_waveformMatrix {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : κ → EuclideanSpace ℂ ι) :
    Matrix.gram ℂ u = (waveformMatrix u)ᴴ * waveformMatrix u := by
  ext i j
  rw [Matrix.gram_apply, inner_eq_sum_star_mul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro t _
  rfl

/-- Matched projections of `∑ a_k u_k` are `G a`, with `G_jk = ⟪u_j, u_k⟫`.
No normalization is needed for this identity. -/
lemma matchedOutput_eq_gram_mulVec {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : κ → EuclideanSpace ℂ ι) (a : κ → ℂ) :
    matchedOutput u a = (Matrix.gram ℂ u).mulVec a := by
  funext j
  simp only [matchedOutput, superpose, inner_sum, inner_smul_right, Matrix.mulVec,
    dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.gram_apply]
  exact mul_comm _ _

/-- With normalized columns, the matched output of user `j` is its own symbol plus the
Gram-weighted interference `∑_{k ≠ j} G_jk a_k`. -/
lemma matchedOutput_sub_eq_interference {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (u : κ → EuclideanSpace ℂ ι) (hnorm : ∀ j, ‖u j‖ = 1)
    (a : κ → ℂ) (j : κ) :
    matchedOutput u a j - a j = ∑ k ∈ Finset.univ.erase j, Matrix.gram ℂ u j k * a k := by
  have h := congrFun (matchedOutput_eq_gram_mulVec u a) j
  rw [h]
  have hmul : (Matrix.gram ℂ u).mulVec a j
      = ∑ k, Matrix.gram ℂ u j k * a k := by
    simp only [Matrix.mulVec, dotProduct]
  rw [hmul, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hdiag : Matrix.gram ℂ u j j * a j = a j := by
    rw [Matrix.gram_apply, inner_self_eq_norm_sq_to_K, hnorm j]
    simp
  rw [hdiag, add_sub_cancel_left]

/-- Interference bound: `‖y_j - a_j‖ ≤ ∑_{k ≠ j} ‖G_jk‖ ‖a_k‖`. -/
lemma norm_matchedOutput_sub_le_interference {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (u : κ → EuclideanSpace ℂ ι) (hnorm : ∀ j, ‖u j‖ = 1)
    (a : κ → ℂ) (j : κ) :
    ‖matchedOutput u a j - a j‖ ≤
      ∑ k ∈ Finset.univ.erase j, ‖Matrix.gram ℂ u j k‖ * ‖a k‖ := by
  have h1 : ‖∑ k ∈ Finset.univ.erase j, Matrix.gram ℂ u j k * a k‖
      ≤ ∑ k ∈ Finset.univ.erase j, ‖Matrix.gram ℂ u j k * a k‖ := by
    apply norm_sum_le
  have h2 : (∑ k ∈ Finset.univ.erase j, ‖Matrix.gram ℂ u j k * a k‖)
      = ∑ k ∈ Finset.univ.erase j, ‖Matrix.gram ℂ u j k‖ * ‖a k‖ := by
    apply Finset.sum_congr rfl
    intro k _
    rw [norm_mul]
  rw [matchedOutput_sub_eq_interference u hnorm a j, ← h2]
  exact h1

/-- Orthogonal recovery: orthonormal waveforms give `y = a`. -/
lemma matchedOutput_eq_of_orthonormal {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : κ → EuclideanSpace ℂ ι) (horth : Orthonormal ℂ u) (a : κ → ℂ) :
    matchedOutput u a = a := by
  classical
  obtain ⟨hnorm, hpair⟩ := horth
  rw [matchedOutput_eq_gram_mulVec u a,
    Matrix.gram_eq_one_iff_orthonormal.mpr ⟨hnorm, hpair⟩, Matrix.one_mulVec]

/-- FDMA: carriers at distinct DFT frequencies are orthonormal. -/
lemma orthonormal_fdmaCarrier {κ : Type} (N : ℕ) [NeZero N] (f : κ → ZMod N)
    (hf : Function.Injective f) :
    Orthonormal ℂ fun j => fdmaCarrier N (f j) := by
  classical
  have hNpos : 0 < N := by
    have hcard := ZMod.card N
    have hpos := Fintype.card_pos (α := ZMod N)
    omega
  have hNne : ((N : ℝ)) ≠ 0 := by exact_mod_cast ne_of_gt hNpos
  have hc_sq : ((Real.sqrt N)⁻¹ : ℂ) ^ 2 * (N : ℂ) = 1 := by
    norm_cast
    have hsqrt : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
    rw [inv_pow, hsqrt]
    exact inv_mul_cancel₀ hNne
  have hstar_c : star (((Real.sqrt N)⁻¹ : ℂ)) = ((Real.sqrt N)⁻¹ : ℂ) := by simp
  have charSum : ∀ d : ZMod N, (∑ t, ZMod.stdAddChar (d * t))
      = (if d = 0 then (N : ℂ) else 0) := by
    intro d
    by_cases hd : d = 0
    · simp only [hd, zero_mul]
      simp [ZMod.card]
    · rw [ite_eq_right hd]
      have h := AddChar.sum_mulShift d (ZMod.isPrimitive_stdAddChar N)
      rw [ite_eq_right hd] at h
      simpa only [mul_comm, Nat.cast_zero] using h
  have innerForm : ∀ a b : ZMod N, ⟪fdmaCarrier N a, fdmaCarrier N b⟫_ℂ
      = (if a = b then (1 : ℂ) else 0) := by
    intro a b
    have hstar : ∀ x : ZMod N, star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
      intro x
      have hR : 0 < ringChar (ZMod N) := by rw [ZMod.ringChar_zmod_n]; exact hNpos
      have h := AddChar.starComp_apply hR (φ := ZMod.stdAddChar) x
      rw [AddChar.inv_apply] at h
      exact h
    have hinner : ⟪fdmaCarrier N a, fdmaCarrier N b⟫_ℂ
        = ((Real.sqrt N)⁻¹ : ℂ) ^ 2 * ∑ t, ZMod.stdAddChar ((b - a) * t) := by
      rw [inner_eq_sum_star_mul]
      simp only [fdmaCarrier, WithLp.toLp]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      have hreassoc : (ZMod.stdAddChar (-(a * t)) * ((Real.sqrt N)⁻¹ : ℂ))
          * (((Real.sqrt N)⁻¹ : ℂ) * ZMod.stdAddChar (b * t))
          = ((Real.sqrt N)⁻¹ : ℂ) ^ 2
            * (ZMod.stdAddChar (-(a * t)) * ZMod.stdAddChar (b * t)) := by ring
      have harg : (-(a * t) + b * t) = (b - a) * t := by ring
      rw [star_mul, hstar_c, hstar, hreassoc, ← AddChar.map_add_eq_mul, harg]
    rw [hinner, charSum]
    by_cases hab : a = b
    · subst hab
      simp only [sub_self, eq_self_iff_true, ite_true]
      exact hc_sq
    · have hne : b - a ≠ 0 := fun h => hab (sub_eq_zero.mp h).symm
      rw [ite_eq_right hne, ite_eq_right hab, mul_zero]
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · have hself : ⟪fdmaCarrier N (f j), fdmaCarrier N (f j)⟫_ℂ = 1 := by
      rw [innerForm]
      simp
    rw [inner_self_eq_norm_sq_to_K] at hself
    have h2 : ‖fdmaCarrier N (f j)‖ ^ 2 = 1 := by
      have h1 : (((‖fdmaCarrier N (f j)‖ ^ 2 : ℝ)) : ℂ) = ((1 : ℝ) : ℂ) := by
        push_cast
        exact hself
      exact Complex.ofReal_inj.mp h1
    have hmem : ‖fdmaCarrier N (f j)‖ = 1 ∨ ‖fdmaCarrier N (f j)‖ = -1 :=
      sq_eq_one_iff.mp h2
    rcases hmem with h | h
    · exact h
    · have hnn := norm_nonneg (fdmaCarrier N (f j))
      linarith
  · have hne : f i ≠ f j := fun h => hij (hf h)
    show ⟪fdmaCarrier N (f i), fdmaCarrier N (f j)⟫_ℂ = 0
    rw [innerForm, ite_eq_right hne]

/-- FDMA recovery for users on distinct DFT frequencies. -/
lemma fdma_matchedOutput_eq {κ : Type} [Fintype κ] (N : ℕ) [NeZero N]
    (f : κ → ZMod N) (hf : Function.Injective f) (a : κ → ℂ) :
    matchedOutput (fun j => fdmaCarrier N (f j)) a = a := by
  exact matchedOutput_eq_of_orthonormal _ (orthonormal_fdmaCarrier N f hf) a

/-- FDMA fixture: two carriers at frequencies `1` and `3` on `ZMod 4`. -/
lemma fdma_two_carriers_matchedOutput_eq (a : Fin 2 → ℂ) :
    matchedOutput (fun j => fdmaCarrier 4 (![1, 3] j)) a = a := by
  have hf : Function.Injective (![1, 3] : Fin 2 → ZMod 4) := by
    intro i j h
    revert h
    fin_cases i <;> fin_cases j <;> intro h
    · rfl
    · simp at h
      exact absurd h (by decide)
    · simp at h
      exact absurd h (by decide)
    · rfl
  exact fdma_matchedOutput_eq 4 ![1, 3] hf a

/-- TDMA: unit-norm waveforms supported on pairwise disjoint slots are orthonormal. -/
lemma orthonormal_of_disjoint_slots {ι κ : Type} [Fintype ι]
    (u : κ → EuclideanSpace ℂ ι) (S : κ → Finset ι)
    (hsupp : ∀ j t, t ∉ S j → u j t = 0)
    (hdisj : Pairwise fun j k => Disjoint (S j) (S k)) (hnorm : ∀ j, ‖u j‖ = 1) :
    Orthonormal ℂ u := by
  refine ⟨hnorm, fun i j hij => ?_⟩
  show ⟪u i, u j⟫_ℂ = 0
  rw [inner_eq_sum_star_mul]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : t ∈ S i
  · have htj : t ∉ S j := Finset.disjoint_left.mp (hdisj hij) ht
    rw [hsupp j t htj, mul_zero]
  · rw [hsupp i t ht, star_zero, zero_mul]

/-- TDMA recovery for unit-norm users on pairwise disjoint time slots. -/
lemma tdma_matchedOutput_eq {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : κ → EuclideanSpace ℂ ι) (S : κ → Finset ι)
    (hsupp : ∀ j t, t ∉ S j → u j t = 0)
    (hdisj : Pairwise fun j k => Disjoint (S j) (S k)) (hnorm : ∀ j, ‖u j‖ = 1)
    (a : κ → ℂ) :
    matchedOutput u a = a := by
  exact matchedOutput_eq_of_orthonormal u
    (orthonormal_of_disjoint_slots u S hsupp hdisj hnorm) a

/-- TDMA recovery for one-coordinate slots: user `j` owns sample `s j`, `s` injective. -/
lemma tdmaCoordinate_matchedOutput_eq {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (s : κ → ι) (hs : Function.Injective s) (a : κ → ℂ) :
    matchedOutput (fun j => EuclideanSpace.single (s j) (1 : ℂ)) a = a := by
  have hbase : Orthonormal ℂ (fun (t : ι) => EuclideanSpace.single t (1 : ℂ)) :=
    EuclideanSpace.orthonormal_single
  obtain ⟨hnorm_base, hpair_base⟩ := hbase
  refine matchedOutput_eq_of_orthonormal _ ⟨?_, ?_⟩ a
  · intro j
    exact hnorm_base (s j)
  · intro i j hij
    exact hpair_base (fun h => hij (hs h))

/-- CDMA: the codes `(1,1)/√2` and `(1,-1)/√2` are orthonormal. -/
lemma orthonormal_cdmaCode : Orthonormal ℂ cdmaCode := by
  refine ⟨?_, ?_⟩
  · intro j
    fin_cases j
    · rw [EuclideanSpace.norm_eq]
      simp only [Fin.sum_univ_two, cdmaCode, WithLp.toLp]
      simp
      norm_num
    · rw [EuclideanSpace.norm_eq]
      simp only [Fin.sum_univ_two, cdmaCode, WithLp.toLp]
      simp
      norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · rw [inner_eq_sum_star_mul]
      simp only [Fin.sum_univ_two, cdmaCode, WithLp.toLp]
      simp
    · rw [inner_eq_sum_star_mul]
      simp only [Fin.sum_univ_two, cdmaCode, WithLp.toLp]
      simp
    · exact (hij rfl).elim

/-- CDMA recovery for the named code pair. -/
lemma cdma_matchedOutput_eq (a : Fin 2 → ℂ) :
    matchedOutput cdmaCode a = a := by
  exact matchedOutput_eq_of_orthonormal _ orthonormal_cdmaCode a

/-- The nonorthogonal pair has normalized columns. -/
lemma norm_skewPair (j : Fin 2) : ‖skewPair j‖ = 1 := by
  fin_cases j
  · rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, skewPair, WithLp.toLp]
    simp
  · rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, skewPair, WithLp.toLp]
    simp
    norm_num

/-- The cross Gram entry of the nonorthogonal pair is `1/√2`. -/
lemma gram_skewPair_zero_one :
    Matrix.gram ℂ skewPair 0 1 = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [Matrix.gram_apply, inner_eq_sum_star_mul]
  simp only [Fin.sum_univ_two, skewPair, WithLp.toLp]
  simp

/-- A nonorthogonal interferer contributes its Gram term: `y_0 = a_0 + a_1/√2`. -/
lemma skewPair_matchedOutput_zero (a : Fin 2 → ℂ) :
    matchedOutput skewPair a 0 = a 0 + ((Real.sqrt 2)⁻¹ : ℂ) * a 1 := by
  have h := congrFun (matchedOutput_eq_gram_mulVec skewPair a) 0
  rw [h]
  have hmul : (Matrix.gram ℂ skewPair).mulVec a 0
      = ∑ k, Matrix.gram ℂ skewPair 0 k * a k := by
    simp only [Matrix.mulVec, dotProduct]
  rw [hmul, Fin.sum_univ_two, gram_skewPair_zero_one]
  have hdiag : Matrix.gram ℂ skewPair 0 0 = 1 := by
    rw [Matrix.gram_apply, inner_self_eq_norm_sq_to_K, norm_skewPair 0]
    simp
  rw [hdiag, one_mul]

end PhyslibExt.Communications.FiniteMultiplexingGram
