/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.QuantumCodeDistance

/-!
# CSS codes correct `⌊(d - 1) / 2⌋` errors

`Cslib.CodingTheory.CSSWanted.isCorrectable_css`: let `C₂ ⊆ C₁ ⊆ F₂ⁿ` be binary linear codes
whose nonzero words, in `C₁` and in `C₂^⊥`, all have Hamming weight at least `d`. Then every Pauli
error `X^a Z^b` acting on at most `⌊(d - 1) / 2⌋` qubits is correctable on the CSS code
`Q_{C₁, C₂}`, all by one recovery channel.

## Proof

The code has distance at least `d` (`Cslib.CodingTheory.QuantumCode.HasDistanceAtLeast`): if
`X^a Z^b` has weight less than `d`, then `P X^a Z^b P` is a scalar multiple of the projector `P`
onto the code. Then `Cslib.CodingTheory.QuantumCode.isCorrectable_of_hasDistanceAtLeast`, which
rests on the Knill–Laflamme conditions, gives the recovery channel. Both `a` and `b` have Hamming
weight less than `d`, and it suffices to compute the matrix elements between the codewords `|c_w⟩`,
`w ∈ C₂^⊥`, which span the code.

* The codewords are superpositions of basis states `|v⟩` with `v ∈ C₁`. If `a ∉ C₁`, then
  `X^a Z^b` maps them to superpositions of `|v⟩` with `v ∈ C₁ + a`, which is disjoint from `C₁`,
  so `P X^a Z^b P = 0`.
* If `a ∈ C₁`, then `a = 0`, since every nonzero word of `C₁` has weight at least `d`.
* A phase flip shifts the index: `Z^b |c_w⟩ = |c_{w + b}⟩`. If `b ∉ C₂^⊥`, then for all
  `w, w' ∈ C₂^⊥` the word `w' + w + b` lies outside `C₂^⊥`, hence outside `C₁^⊥ ⊆ C₂^⊥`, so
  `|c_{w + b}⟩` is orthogonal to `|c_{w'}⟩` and `P Z^b P = 0`.
* If `b ∈ C₂^⊥`, then `b = 0`, and `X^0 Z^0` is the identity, so `P X^0 Z^0 P = P`.

Calderbank and Shor give this intuition in Section III (bit errors are corrected by `C₁`, phase
errors by `C₂^⊥` in the rotated basis) and prove the theorem in Section IV by an explicit decoder;
the argument here checks the Knill–Laflamme conditions instead.

## Source

A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54
(1996), 1098–1105 (arXiv:quant-ph/9512032), Section III (statement before equation (5)) and
Section IV.
-/

@[expose] public section

open scoped Matrix
open Cslib.CodingTheory Cslib.CodingTheory.LinearCode Cslib.CodingTheory.CSS
  MathlibExt.QuantumInformation.Finite.KnillLaflamme

namespace Cslib.CodingTheory.CSSWanted

/-- If `star x ⬝ᵥ (M *ᵥ y) = 0` for all `x` and `y` in a set `S` spanning the range of a
self-adjoint matrix `P`, then the compression `P * M * P` vanishes. -/
private theorem mul_mul_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {P M : Matrix ι ι ℂ}
    (hP : Pᴴ = P) {S : Set (ι → ℂ)}
    (hrange : LinearMap.range (Matrix.toLin' P) = Submodule.span ℂ S)
    (h : ∀ x ∈ S, ∀ y ∈ S, star x ⬝ᵥ (M *ᵥ y) = 0) : P * M * P = 0 := by
  have hspan : ∀ x ∈ Submodule.span ℂ S, ∀ y ∈ Submodule.span ℂ S,
      star x ⬝ᵥ (M *ᵥ y) = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      induction hx using Submodule.span_induction with
      | mem x hx' => exact h x hx' y hy'
      | zero => simp
      | add x₁ x₂ _ _ h₁ h₂ => rw [star_add, add_dotProduct, h₁, h₂, add_zero]
      | smul c x _ hx => rw [star_smul, smul_dotProduct, hx, smul_zero]
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ => rw [Matrix.mulVec_add, dotProduct_add, h₁, h₂, add_zero]
    | smul c y _ hy => rw [Matrix.mulVec_smul, dotProduct_smul, hy, smul_zero]
  have hcol : ∀ j, P.col j ∈ Submodule.span ℂ S := fun j => by
    rw [← hrange]
    exact ⟨Pi.single j 1, by rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]⟩
  ext i j
  rw [Matrix.zero_apply, ← hspan _ (hcol i) _ (hcol j), Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.star_apply, Matrix.col_apply, ← Matrix.conjTranspose_apply, hP]
  rfl

section Helpers

variable {n : ℕ}

/-- The identity `X^0 Z^0`. -/
private theorem pauli_zero_zero : pauli (0 : Fin n → ZMod 2) 0 = 1 := by
  ext u v
  simp [pauli, Matrix.one_apply, sign_zero]

private theorem hammingNorm_le_pauliWeight_left (a b : Fin n → ZMod 2) :
    hammingNorm a ≤ QuantumCode.pauliWeight a b :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Or.inl hi

private theorem hammingNorm_le_pauliWeight_right (a b : Fin n → ZMod 2) :
    hammingNorm b ≤ QuantumCode.pauliWeight a b :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Or.inr hi

/-- A bit flip `X^a` with `a ∉ C₁` moves the support `C₁` of the codewords off itself, so all
matrix elements `⟨c_{w'}| X^a Z^b |c_w⟩` vanish. -/
private theorem inner_pauli_eq_zero_of_notMem (C₁ : LinearCode (ZMod 2) (Fin n))
    [DecidablePred (· ∈ C₁)] {a : Fin n → ZMod 2} (ha : a ∉ C₁) (b w w' : Fin n → ZMod 2) :
    star (codeword C₁ w') ⬝ᵥ (pauli a b *ᵥ codeword C₁ w) = 0 := by
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [Pi.star_apply, pauli_mulVec_apply]
  unfold codeword
  by_cases hu : u ∈ C₁
  · have hua : u + a ∉ C₁ := fun h => ha (by simpa using C₁.sub_mem h hu)
    simp [hua]
  · simp [hu]

/-- A phase flip `Z^b` with `b ∉ C₂^⊥` maps each codeword `|c_w⟩`, `w ∈ C₂^⊥`, to a state
orthogonal to every codeword `|c_{w'}⟩`, `w' ∈ C₂^⊥`. -/
private theorem inner_pauli_zero_eq_zero_of_notMem_dual {C₁ C₂ : LinearCode (ZMod 2) (Fin n)}
    [DecidablePred (· ∈ C₁)] (hC : C₂ ≤ C₁) {b w w' : Fin n → ZMod 2} (hb : b ∉ dual C₂)
    (hw : w ∈ dual C₂) (hw' : w' ∈ dual C₂) :
    star (codeword C₁ w') ⬝ᵥ (pauli 0 b *ᵥ codeword C₁ w) = 0 := by
  rw [pauli_zero_mulVec_codeword]
  refine inner_codeword_eq_zero C₁ fun h => hb ?_
  have h₂ : w' + (w + b) ∈ dual C₂ := mem_dual.2 fun c hc => mem_dual.1 h c (hC hc)
  have hb' : b = w' + (w + b) - w' - w := by abel
  rw [hb']
  exact (dual C₂).sub_mem ((dual C₂).sub_mem h₂ hw') hw

end Helpers

/-- **CSS codes correct `⌊(d - 1) / 2⌋` errors.** Let `C₂ ⊆ C₁ ⊆ F₂ⁿ` be binary linear codes such
that every nonzero word of `C₁` and every nonzero word of `C₂^⊥` has Hamming weight at least
`d`. Let `P` be the orthogonal projector onto the CSS code `Q_{C₁, C₂}`, the span of the
codewords `|c_w⟩` with `w ∈ C₂^⊥`. Then every Pauli error `X^a Z^b` acting on at most
`t = ⌊(d - 1) / 2⌋` qubits (that is, `2 |supp a ∪ supp b| + 1 ≤ d`) is correctable on the code,
all by one recovery channel (A. R. Calderbank and P. W. Shor, Phys. Rev. A 54 (1996), Section III:
"if `C₁` and `C₂^⊥` have minimum distance `d`, then the quantum code `Q_{C₁,C₂}` can correct
`t = ⌊(d-1)/2⌋` errors", proved in Section IV). Calderbank and Shor allow an arbitrary
decoherence of the `t` qubits; its Kraus operators are linear combinations of such Pauli
operators, and correctable families are closed under linear combinations (E. Knill and
R. Laflamme, Phys. Rev. A 55 (1997), Theorem 3.1), so the Pauli form is equivalent. -/
theorem isCorrectable_css {n d : ℕ} (C₁ C₂ : LinearCode (ZMod 2) (Fin n))
    [DecidablePred (· ∈ C₁)] (hC : C₂ ≤ C₁)
    (hd₁ : ∀ c ∈ C₁, c ≠ 0 → d ≤ hammingNorm c)
    (hd₂ : ∀ c ∈ dual C₂, c ≠ 0 → d ≤ hammingNorm c)
    (P : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hrange : LinearMap.range (Matrix.toLin' P) =
      Submodule.span ℂ (codeword C₁ '' (dual C₂ : Set (Fin n → ZMod 2)))) :
    IsCorrectable P (fun e : {e : (Fin n → ZMod 2) × (Fin n → ZMod 2) //
        2 * (Finset.univ.filter fun i => e.1 i ≠ 0 ∨ e.2 i ≠ 0).card + 1 ≤ d} =>
      pauli e.1.1 e.1.2) := by
  refine QuantumCode.isCorrectable_of_hasDistanceAtLeast hP hPP fun a b hab => ?_
  have hwa := (hammingNorm_le_pauliWeight_left a b).trans_lt hab
  have hwb := (hammingNorm_le_pauliWeight_right a b).trans_lt hab
  by_cases ha : a ∈ C₁
  · obtain rfl : a = 0 := by
      by_contra hne
      exact absurd (hd₁ a ha hne) (by omega)
    by_cases hb : b ∈ dual C₂
    · obtain rfl : b = 0 := by
        by_contra hne
        exact absurd (hd₂ b hb hne) (by omega)
      exact ⟨1, by rw [pauli_zero_zero, Matrix.mul_one, hPP, one_smul]⟩
    · refine ⟨0, ?_⟩
      rw [zero_smul]
      refine mul_mul_eq_zero hP hrange ?_
      rintro _ ⟨w', hw', rfl⟩ _ ⟨w, hw, rfl⟩
      exact inner_pauli_zero_eq_zero_of_notMem_dual hC hb hw hw'
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    refine mul_mul_eq_zero hP hrange ?_
    rintro _ ⟨w', -, rfl⟩ _ ⟨w, -, rfl⟩
    exact inner_pauli_eq_zero_of_notMem C₁ ha b w w'

end Cslib.CodingTheory.CSSWanted
