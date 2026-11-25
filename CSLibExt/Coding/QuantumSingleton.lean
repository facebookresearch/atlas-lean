/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.QuantumCodeDistance
import MathlibExt.Quantum.PauliExpansion
import Mathlib.LinearAlgebra.Trace

/-!
# The quantum Singleton bound

`quantum_singleton_bound` bounds the dimension of a quantum code in terms of its length
and distance. For a block `s`, let `E(s)` be the sum of squared Pauli coefficients of the
projector indexed by errors supported on that block. For `|s| < d`, summing the scalar compression
identities over these errors gives `2^k * 4^|s| * E(t) ≤ 2^n * E(s)` for any disjoint block `t`.
If both blocks have fewer than `d` qubits, exchanging them and cancelling their positive sums gives
`k + |s| + |t| ≤ n`.
-/

public section

open scoped Matrix
open Matrix Cslib.CodingTheory.QuantumCode Cslib.CodingTheory.CSS
open MathlibExt.Quantum.PauliExpansion MathlibExt.Quantum.PauliXZ

namespace Cslib.CodingTheory.QuantumSingletonWanted

private abbrev Bits (n : ℕ) := Fin n → ZMod 2
private abbrev Label (n : ℕ) := Bits n × Bits n
private abbrev Operator (n : ℕ) := Matrix (Bits n) (Bits n) ℂ

variable {n : ℕ}

private noncomputable abbrev H (e : Label n) := hermPauli e.1 e.2

-- The sign picked up on conjugating one Hermitian Pauli by another.
private def pairing (e f : Label n) : ZMod 2 := e.2 ⬝ᵥ f.1 + e.1 ⬝ᵥ f.2

private def charSign (e f : Label n) : ℝ := (-1) ^ (pairing e f).val

private theorem charSign_add (e g f : Label n) :
    charSign (e + g) f = charSign e f * charSign g f := by
  have hadd : pairing (e + g) f = pairing e f + pairing g f := by
    simp only [pairing, Prod.fst_add, Prod.snd_add, add_dotProduct]
    abel
  apply Complex.ofReal_injective
  simpa [charSign, hadd, sign] using sign_add (pairing e f) (pairing g f)

private theorem conjugate_pauli (e f : Label n) :
    H e * H f * H e = (charSign e f : ℂ) • H f := by
  have hsign : (charSign e f : ℂ) = sign (e.2 ⬝ᵥ f.1) * sign (f.2 ⬝ᵥ e.1) := by
    rw [← sign_add, dotProduct_comm f.2 e.1]
    simp [charSign, pairing, sign]
  have hcomm : H e * H f = (charSign e f : ℂ) • (H f * H e) := by
    unfold H hermPauli
    rw [smul_mul_smul_comm, smul_mul_smul_comm, pauliXZ_mul, pauliXZ_mul]
    simp only [smul_smul, hsign, sign]
    rw [add_comm f.1 e.1, add_comm f.2 e.2]
    congr 1
    have h := sign_mul_self (f.2 ⬝ᵥ e.1)
    unfold sign at h
    linear_combination -(Complex.I ^ (∑ i, (e.1 i).val * (e.2 i).val) *
      Complex.I ^ (∑ i, (f.1 i).val * (f.2 i).val) * (-1) ^ (e.2 ⬝ᵥ f.1).val) * h
  rw [hcomm, Matrix.smul_mul, Matrix.mul_assoc, hermPauli_mul_self, mul_one]

private noncomputable def coeff (P : Operator n) (e : Label n) : ℝ :=
  (pauliCoeff P e.1 e.2).re

private theorem ofReal_coeff {P : Operator n} (hP : Pᴴ = P) (e : Label n) :
    (coeff P e : ℂ) = pauliCoeff P e.1 e.2 :=
  Complex.ext rfl (by simp [im_pauliCoeff_eq_zero hP])

private theorem trace_pauli_mul {P : Operator n} (hP : Pᴴ = P) (e : Label n) :
    (H e * P).trace = (coeff P e : ℂ) * 2 ^ n := by
  rw [ofReal_coeff hP, pauliCoeff, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))]

-- Expand just the conjugated projector, then pair its expansion with P by taking the trace.
private theorem trace_conjugate_mul {P : Operator n} (hP : Pᴴ = P) (e : Label n) :
    (H e * P * H e * P).trace =
      (↑(∑ f : Label n, charSign e f * coeff P f ^ 2) : ℂ) * 2 ^ n := by
  classical
  have hexp : (∑ f : Label n, (coeff P f : ℂ) • H f) = P := by
    simpa only [Fintype.sum_prod_type, ofReal_coeff hP, H] using
      (sum_pauliCoeff_smul_hermPauli P)
  conv_lhs => arg 1; lhs; lhs; rhs; rw [← hexp]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.smul_mul, trace_sum,
    trace_smul, smul_eq_mul, conjugate_pauli, trace_pauli_mul hP, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow, Finset.sum_mul]
  exact Finset.sum_congr rfl fun f _ => by ring

private theorem trace_projector {P : Operator n} (hPP : P * P = P) :
    P.trace = (Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) : ℂ) := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hPP]
  simpa only [Matrix.trace_toLin'_eq] using (LinearMap.IsIdempotentElem.isProj_range _ hi).trace

-- For a detectable error the compression is scalar. Taking its trace first alone,
-- then against the error, relates one squared coefficient to a signed sum of all of them.
private theorem detected_identity {P : Operator n} {k d : ℕ} (hP : Pᴴ = P)
    (hPP : P * P = P) (ht : P.trace = (2 : ℂ) ^ k) (hd : HasDistanceAtLeast P d)
    (e : Label n) (he : pauliWeight e.1 e.2 < d) :
    2 ^ n * coeff P e ^ 2 = 2 ^ k * ∑ f : Label n, charSign e f * coeff P f ^ 2 := by
  obtain ⟨c, hc⟩ := hd e.1 e.2 he
  let z := Complex.I ^ (∑ i, (e.1 i).val * (e.2 i).val) * c
  have hcompress : P * H e * P = z • P := by
    change P * (_ • pauli e.1 e.2) * P = z • P
    rw [Matrix.mul_smul, Matrix.smul_mul, hc, smul_smul]
  have htrace : (coeff P e : ℂ) * 2 ^ n = z * 2 ^ k := by
    rw [← trace_pauli_mul hP, ← ht, ← smul_eq_mul z _, ← trace_smul, ← hcompress,
      trace_mul_cycle, hPP, trace_mul_comm (H e)]
  have hprod : (H e * P * H e * P).trace = z * ((coeff P e : ℂ) * 2 ^ n) := by
    rw [← trace_pauli_mul hP, ← smul_eq_mul z _, ← trace_smul, ← Matrix.mul_smul,
      ← hcompress, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [trace_conjugate_mul hP] at hprod
  push_cast at hprod
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  apply Complex.ofReal_injective
  push_cast
  apply mul_right_cancel₀ h2
  linear_combination ((coeff P e : ℂ) * 2 ^ n) * htrace - (2 : ℂ) ^ k * hprod

-- Pauli labels supported on a block of qubits form an additive subgroup.
private def supported (s : Finset (Fin n)) : AddSubgroup (Label n) where
  carrier := {e | ∀ i ∉ s, e.1 i = 0 ∧ e.2 i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro e f he hf i hi
    simp [(he i hi).1, (he i hi).2, (hf i hi).1, (hf i hi).2]
  neg_mem' := by
    intro e he i hi
    simp [(he i hi).1, (he i hi).2]

open scoped Classical in
private theorem card_supported (s : Finset (Fin n)) :
    Fintype.card (supported s) = (2 ^ s.card) ^ 2 := by
  let ext (x : s → ZMod 2 × ZMod 2) (i : Fin n) := if hi : i ∈ s then x ⟨i, hi⟩ else 0
  let equiv : supported s ≃ (s → ZMod 2 × ZMod 2) :=
    { toFun := fun e i => (e.val.1 i, e.val.2 i)
      invFun := fun x => ⟨(fun i => (ext x i).1, fun i => (ext x i).2), by
        intro i hi
        simp [ext, hi]⟩
      left_inv := by
        intro e
        apply Subtype.ext
        apply Prod.ext <;> funext i <;> by_cases hi : i ∈ s <;> simp [ext, hi, e.prop i]
      right_inv := by
        intro x
        funext i
        simp [ext] }
  rw [Fintype.card_congr equiv]
  simp [pow_two, ← mul_pow]

private theorem charSign_disjoint {s t : Finset (Fin n)} (hst : Disjoint s t)
    (e : supported s) (f : supported t) : charSign e.val f.val = 1 := by
  have hh (i : Fin n) : e.val.2 i * f.val.1 i = 0 ∧ e.val.1 i * f.val.2 i = 0 := by
    by_cases hi : i ∈ s
    · obtain ⟨h₁, h₂⟩ := f.prop i (Finset.disjoint_left.mp hst hi)
      simp [h₁, h₂]
    · obtain ⟨h₁, h₂⟩ := e.prop i hi
      simp [h₁, h₂]
  simp [charSign, pairing, dotProduct, fun i => (hh i).1, fun i => (hh i).2]

open scoped Classical in
private theorem charSum_nonneg (s : Finset (Fin n)) (f : Label n) :
    0 ≤ ∑ e : supported s, charSign e.val f := by
  classical
  by_cases h : ∀ e : supported s, charSign e.val f = 1
  · simp [h]
  obtain ⟨g, hg⟩ := not_forall.mp h
  have hshift := Equiv.sum_comp (Equiv.addLeft g) (fun e : supported s => charSign e.val f)
  simp only [Equiv.coe_addLeft, AddSubgroup.coe_add, charSign_add, ← Finset.mul_sum] at hshift
  have hz := sub_eq_zero.mpr hshift
  rw [← sub_one_mul] at hz
  exact ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hg)).ge

open scoped Classical in
private noncomputable def energy (P : Operator n) (s : Finset (Fin n)) : ℝ :=
  ∑ e : supported s, coeff P e.val ^ 2

open scoped Classical in
private theorem energy_pos {P : Operator n} (hP : Pᴴ = P) {k : ℕ}
    (ht : P.trace = (2 : ℂ) ^ k) (s : Finset (Fin n)) : 0 < energy P s := by
  have hI : H (0 : Label n) = 1 := by
    ext i j
    simp [H, hermPauli, pauliXZ, Matrix.one_apply]
  have hcoeff := trace_pauli_mul hP (0 : Label n)
  rw [hI, one_mul, ht] at hcoeff
  have hne : coeff P 0 ≠ 0 := by
    intro hz
    simp [hz] at hcoeff
  apply Finset.sum_pos' (fun e _ => sq_nonneg _)
  exact ⟨0, Finset.mem_univ _, sq_pos_of_ne_zero hne⟩

open scoped Classical in
private theorem block_inequality {P : Operator n} {k d : ℕ} (hP : Pᴴ = P)
    (hPP : P * P = P) (ht : P.trace = (2 : ℂ) ^ k) (hd : HasDistanceAtLeast P d)
    {s t : Finset (Fin n)} (hst : Disjoint s t) (hs : s.card < d) :
    2 ^ k * ((2 : ℝ) ^ s.card) ^ 2 * energy P t ≤ 2 ^ n * energy P s := by
  classical
  have hw (e : supported s) : pauliWeight e.val.1 e.val.2 < d := by
    apply lt_of_le_of_lt (Finset.card_le_card ?_) hs
    intro i hi
    by_contra hn
    obtain ⟨h₁, h₂⟩ := e.prop i hn
    simp [h₁, h₂] at hi
  let w (f : Label n) := (∑ e : supported s, charSign e.val f) * coeff P f ^ 2
  have hsum : 2 ^ n * energy P s = 2 ^ k * ∑ f, w f := by
    unfold energy
    rw [Finset.mul_sum]
    simp_rw [detected_identity hP hPP ht hd _ (hw _)]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp [w, Finset.sum_mul]
  have hle : ∑ f : supported t, w f.val ≤ ∑ f, w f := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun f => f ∈ supported t) w]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun f _ =>
      mul_nonneg (charSum_nonneg s _) (sq_nonneg _))
  have hlocal (f : supported t) : w f.val = ((2 : ℝ) ^ s.card) ^ 2 * coeff P f.val ^ 2 := by
    simp [w, fun e => charSign_disjoint hst e f, card_supported]
  rw [hsum, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [hlocal, ← Finset.mul_sum, energy] using hle

/-- **The quantum Singleton bound.** Let `P` be the orthogonal projector onto a code of dimension
`2 ^ k`, with `k ≥ 1`, in the space of `n` qubits, and suppose the code has distance at least `d`:
every Pauli operator `X^a Z^b` of weight less than `d` satisfies `P X^a Z^b P = c P`. Then
`k + 2 (d - 1) ≤ n`, that is `n - k ≥ 2 (d - 1)` (J. Preskill, Ph219 lecture notes, Chapter 7,
Section 7.8.3, equation (7.103), proved there through equations (7.105)–(7.112)). -/
theorem quantum_singleton_bound {n k d : ℕ}
    (P : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hk : 1 ≤ k) (hdim : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = 2 ^ k)
    (hd : HasDistanceAtLeast P d) :
    k + 2 * (d - 1) ≤ n := by
  classical
  -- At distance zero the bound is just the ambient dimension bound.
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · simp only [Nat.zero_sub, mul_zero, add_zero]
    apply (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp
    have hh := (Matrix.toLin' P).finrank_range_le
    simpa [hdim, Module.finrank_fintype_fun_eq_card] using hh
  have ht : P.trace = (2 : ℂ) ^ k := by
    rw [trace_projector hPP, hdim]
    norm_cast
  -- Take as many as d - 1 qubits twice, stopping if the qubits run out.
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ (α := Fin n))
    (n := min (d - 1) n) (by simp)
  obtain ⟨t, hts, htt⟩ := Finset.exists_subset_card_eq (s := sᶜ)
    (n := min (d - 1) (n - s.card)) (by simp)
  have hst : Disjoint s t := disjoint_compl_right.mono_right hts
  have h₁ := block_inequality hP hPP ht hd hst (by omega)
  have h₂ := block_inequality hP hPP ht hd hst.symm (by omega)
  have hp := mul_le_mul h₁ h₂ (by positivity [energy_pos hP ht s])
    (by positivity [energy_pos hP ht s])
  have hpow : (2 : ℝ) ^ (2 * (k + s.card + t.card)) ≤ 2 ^ (2 * n) := by
    apply le_of_mul_le_mul_right _
      (mul_pos (energy_pos hP ht s) (energy_pos hP ht t))
    convert hp using 1 <;> simp only [two_mul, pow_add] <;> ring
  have := (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mp hpow
  omega

end Cslib.CodingTheory.QuantumSingletonWanted
