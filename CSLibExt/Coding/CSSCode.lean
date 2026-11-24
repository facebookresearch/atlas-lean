/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.LinearCode
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Calderbank–Shor–Steane (CSS) codewords

Calderbank and Shor build quantum error-correcting codes from two binary linear codes
`{0} ⊂ C₂ ⊂ C₁ ⊂ F₂ⁿ`. Basis states of `n` qubits are indexed by vectors `v ∈ F₂ⁿ`, and for
`w ∈ F₂ⁿ` the codeword state is (up to the normalisation `2 ^ (-dim C₁ / 2)`)
`|c_w⟩ = ∑_{v ∈ C₁} (-1)^{v · w} |v⟩` (Calderbank and Shor 1996, equation (2), where `v`
runs over `C₁` through a generator matrix). The quantum code `Q_{C₁, C₂}` is spanned by the
`|c_w⟩` with `w ∈ C₂^⊥`.

This file defines `|c_w⟩` as a function `F₂ⁿ → ℂ` and proves the facts stated after equation (2):
`|c_{w₁}⟩ = |c_{w₂}⟩` when `w₁ + w₂ ∈ C₁^⊥`, and `⟨c_{w₁}|c_{w₂}⟩ = 0` otherwise, together
with the norm `⟨c_w|c_w⟩ = |C₁|`. It also defines the Pauli operators `X^a Z^b` and proves how
they act on codewords: a phase flip `Z^b` sends `|c_w⟩` to `|c_{w+b}⟩`, and a bit flip `X^a` with
`a ∈ C₁` multiplies `|c_w⟩` by `(-1)^{a · w}`. That bit and phase errors are corrected by the
classical codes `C₁` and `C₂^⊥` is proved in `CSLibExt.Coding.CSSCodeCorrection`
(`Cslib.CodingTheory.CSSWanted.isCorrectable_css`).

## Source

A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54
(1996), 1098–1105 (arXiv:quant-ph/9512032), Sections II–III, equations (2)–(6).
-/

@[expose] public section

open scoped Matrix

namespace Cslib.CodingTheory.CSS

open Cslib.CodingTheory Cslib.CodingTheory.LinearCode

variable {n : ℕ}

/-- **Sign of a binary digit.** The complex number `(-1) ^ x` for `x ∈ F₂ = ZMod 2`: `1` for
`x = 0` and `-1` for `x = 1`. -/
def sign (x : ZMod 2) : ℂ := (-1) ^ x.val

theorem sign_add (x y : ZMod 2) : sign (x + y) = sign x * sign y := by
  rw [sign, sign, sign, ZMod.val_add, ← pow_add, neg_one_pow_eq_pow_mod_two (n := x.val + y.val)]

theorem sign_zero : sign 0 = 1 := by simp [sign]

theorem sign_one : sign 1 = -1 := by
  rw [sign, ZMod.val_one, pow_one]

theorem sign_mul_self (x : ZMod 2) : sign x * sign x = 1 := by
  rw [sign, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

theorem star_sign (x : ZMod 2) : star (sign x) = sign x := by
  simp [sign]

private theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Binary vectors are their own negatives.** `x + x = 0` for every `x ∈ F₂ⁿ`. -/
theorem add_self_eq_zero (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = t
  fin_cases t <;> decide

/-- **CSS codeword.** For a binary linear code `C₁ ⊆ F₂ⁿ` and `w ∈ F₂ⁿ`, the unnormalised state
`|c_w⟩ = ∑_{v ∈ C₁} (-1)^{v · w} |v⟩` on `n` qubits, as a function `F₂ⁿ → ℂ`
(A. R. Calderbank and P. W. Shor, Phys. Rev. A 54 (1996), Section III, equation (2), without the
factor `2 ^ (-dim C₁ / 2)`). -/
noncomputable def codeword (C₁ : LinearCode (ZMod 2) (Fin n)) [DecidablePred (· ∈ C₁)]
    (w : Fin n → ZMod 2) :
    (Fin n → ZMod 2) → ℂ :=
  fun v => if v ∈ C₁ then sign (v ⬝ᵥ w) else 0

/-- **CSS codewords depend on `w` modulo `C₁^⊥`.** If `w₁ + w₂ ∈ C₁^⊥`, then
`|c_{w₁}⟩ = |c_{w₂}⟩`, since `v · w₁ = v · w₂` for every `v ∈ C₁` (A. R. Calderbank and
P. W. Shor, Phys. Rev. A 54 (1996), Section III, after equation (2)). -/
theorem codeword_eq_of_add_mem_dual (C₁ : LinearCode (ZMod 2) (Fin n)) [DecidablePred (· ∈ C₁)]
    {w₁ w₂ : Fin n → ZMod 2} (h : w₁ + w₂ ∈ dual C₁) :
    codeword C₁ w₁ = codeword C₁ w₂ := by
  funext v
  unfold codeword
  split_ifs with hv
  · have h0 : (w₁ + w₂) ⬝ᵥ v = 0 := mem_dual.1 h v hv
    have : v ⬝ᵥ w₁ = v ⬝ᵥ w₂ := by
      rw [dotProduct_comm, dotProduct_comm v w₂]
      rw [add_dotProduct] at h0
      have h2 : (2 : ZMod 2) = 0 := rfl
      calc w₁ ⬝ᵥ v = w₁ ⬝ᵥ v + (w₁ ⬝ᵥ v + w₂ ⬝ᵥ v) := by rw [h0, add_zero]
        _ = 2 * (w₁ ⬝ᵥ v) + w₂ ⬝ᵥ v := by ring
        _ = w₂ ⬝ᵥ v := by rw [h2, zero_mul, zero_add]
    rw [this]
  · rfl

/-- **Character sums over a binary linear code.** If some codeword `c ∈ C` has `c · u ≠ 0`, then
`∑_{v ∈ C} (-1)^{v · u} = 0`: translating by `c` is a bijection of `C` that flips every sign
(A. R. Calderbank and P. W. Shor, Phys. Rev. A 54 (1996), Section III, after equation (2)). -/
theorem sum_sign_eq_zero (C : LinearCode (ZMod 2) (Fin n)) [DecidablePred (· ∈ C)]
    {u : Fin n → ZMod 2}
    (h : ∃ c ∈ C, c ⬝ᵥ u ≠ 0) :
    ∑ v : Fin n → ZMod 2, (if v ∈ C then sign (v ⬝ᵥ u) else 0) = 0 := by
  obtain ⟨c, hc, hcu⟩ := h
  have hc1 : c ⬝ᵥ u = 1 := by
    rcases zmod_two_cases (c ⬝ᵥ u) with h0 | h1
    · exact absurd h0 hcu
    · exact h1
  set S := ∑ v : Fin n → ZMod 2, (if v ∈ C then sign (v ⬝ᵥ u) else 0)
  have hshift : S = ∑ v : Fin n → ZMod 2, (if v + c ∈ C then sign ((v + c) ⬝ᵥ u) else 0) :=
    (Equiv.sum_comp (Equiv.addRight c) _).symm
  have hneg : S = -S := by
    conv_lhs => rw [hshift]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hmem : v + c ∈ C ↔ v ∈ C := by
      constructor
      · intro hv
        have := C.sub_mem hv hc
        simpa using this
      · intro hv; exact C.add_mem hv hc
    by_cases hv : v ∈ C
    · simp only [hmem.2 hv, hv, ite_true, add_dotProduct, sign_add, hc1, sign_one]
      ring
    · have hv' : v + c ∉ C := fun h => hv (hmem.1 h)
      simp [hv, hv']
  have : (2 : ℂ) * S = 0 := by linear_combination hneg
  simpa using this

/-- **Distinct CSS codewords are orthogonal.** If `w₁ + w₂ ∉ C₁^⊥`, then
`⟨c_{w₁}|c_{w₂}⟩ = ∑_v conj (c_{w₁} v) * c_{w₂} v = 0` (A. R. Calderbank and P. W. Shor, Phys.
Rev. A 54 (1996), Section III, after equation (2): "`⟨c_{w₁}|c_{w₂}⟩ = 0` if
`w₁ + w₂ ∉ C₁^⊥`"). -/
theorem inner_codeword_eq_zero (C₁ : LinearCode (ZMod 2) (Fin n)) [DecidablePred (· ∈ C₁)]
    {w₁ w₂ : Fin n → ZMod 2} (h : w₁ + w₂ ∉ dual C₁) :
    ∑ v, star (codeword C₁ w₁ v) * codeword C₁ w₂ v = 0 := by
  have h' : ∃ c ∈ C₁, c ⬝ᵥ (w₁ + w₂) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (mem_dual.2 fun c hc => by rw [dotProduct_comm]; exact hcon c hc)
  rw [← sum_sign_eq_zero C₁ h']
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold codeword
  split_ifs with hv
  · rw [star_sign, ← sign_add, ← dotProduct_add]
  · simp

/-- **Norm of a CSS codeword.** `⟨c_w|c_w⟩ = |C₁|`, so `2 ^ (-dim C₁ / 2) |c_w⟩` is a unit vector
(A. R. Calderbank and P. W. Shor, Phys. Rev. A 54 (1996), Section III, equation (2)). -/
theorem inner_codeword_self (C₁ : LinearCode (ZMod 2) (Fin n)) [DecidablePred (· ∈ C₁)]
    (w : Fin n → ZMod 2) :
    ∑ v, star (codeword C₁ w v) * codeword C₁ w v =
      ((Finset.univ.filter fun v : Fin n → ZMod 2 => v ∈ C₁).card : ℂ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold codeword
  split_ifs with hv
  · rw [star_sign, sign_mul_self, Nat.cast_one]
  · simp

/-- **Pauli operator `X^a Z^b` on `n` qubits.** For `a, b ∈ F₂ⁿ`, the matrix on `ℂ^{F₂ⁿ}` sending
the basis state `|v⟩` to `(-1)^{b · v} |v + a⟩`: the phase flips `Z` on the qubits in the
support of `b`, followed by the bit flips `X` on the qubits in the support of `a`
(A. R. Calderbank and P. W. Shor, Phys. Rev. A 54 (1996), Section III: bit errors
`|0⟩ ↔ |1⟩` and phase errors `|1⟩ ↦ -|1⟩`). -/
noncomputable def pauli (a b : Fin n → ZMod 2) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  Matrix.of fun u v => if u = v + a then sign (b ⬝ᵥ v) else 0

/-- **Action of a Pauli operator on a vector.**
`(X^a Z^b x)(u) = (-1)^{b · (u + a)} x (u + a)` for every `x : F₂ⁿ → ℂ`. -/
theorem pauli_mulVec_apply (a b : Fin n → ZMod 2) (x : (Fin n → ZMod 2) → ℂ)
    (u : Fin n → ZMod 2) : (pauli a b *ᵥ x) u = sign (b ⬝ᵥ (u + a)) * x (u + a) := by
  classical
  have hsub : ∀ v : Fin n → ZMod 2, u = v + a ↔ v = u + a := by
    intro v
    constructor
    · rintro rfl; rw [add_assoc, add_self_eq_zero, add_zero]
    · rintro rfl; rw [add_assoc, add_self_eq_zero, add_zero]
  simp only [Matrix.mulVec, dotProduct, pauli, Matrix.of_apply, ite_mul, zero_mul]
  simp_rw [hsub]
  rw [Finset.sum_ite_eq' Finset.univ (u + a)]
  simp

/-- **A phase flip shifts the CSS codeword.** `Z^b |c_w⟩ = |c_{w+b}⟩`: phase errors in the
original basis act on the index `w`, which is why they are corrected by the code `C₂^⊥` in the
rotated basis (A. R. Calderbank and P. W. Shor, Phys. Rev. A 54 (1996), Section III, discussion
after equation (6)). -/
theorem pauli_zero_mulVec_codeword (C₁ : LinearCode (ZMod 2) (Fin n)) [DecidablePred (· ∈ C₁)]
    (b w : Fin n → ZMod 2) :
    pauli 0 b *ᵥ codeword C₁ w = codeword C₁ (w + b) := by
  funext u
  rw [pauli_mulVec_apply, add_zero]
  unfold codeword
  split_ifs with hu
  · rw [← sign_add, dotProduct_add, dotProduct_comm b u, add_comm]
  · rw [mul_zero]

/-- **A bit flip by a codeword of `C₁` fixes the CSS codeword up to sign.** If `a ∈ C₁`, then
`X^a |c_w⟩ = (-1)^{a · w} |c_w⟩` (A. R. Calderbank and P. W. Shor, Phys. Rev. A 54 (1996),
Section III: in the `|c_w⟩` representation the codewords are superpositions of `|v⟩` with
`v ∈ C₁`). -/
theorem pauli_mulVec_codeword_of_mem (C₁ : LinearCode (ZMod 2) (Fin n))
    [DecidablePred (· ∈ C₁)]
    {a : Fin n → ZMod 2} (ha : a ∈ C₁) (w : Fin n → ZMod 2) :
    pauli a 0 *ᵥ codeword C₁ w = sign (a ⬝ᵥ w) • codeword C₁ w := by
  funext u
  rw [pauli_mulVec_apply, zero_dotProduct, sign_zero, one_mul, Pi.smul_apply, smul_eq_mul]
  unfold codeword
  have hmem : u + a ∈ C₁ ↔ u ∈ C₁ := by
    constructor
    · intro hu
      have := C₁.sub_mem hu ha
      simpa using this
    · intro hu; exact C₁.add_mem hu ha
  by_cases hu : u ∈ C₁
  · simp only [hmem.2 hu, hu, ite_true, add_dotProduct, sign_add, mul_comm]
  · have hu' : u + a ∉ C₁ := fun h => hu (hmem.1 h)
    simp [hu, hu']

end Cslib.CodingTheory.CSS
