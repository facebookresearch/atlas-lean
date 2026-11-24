/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.QuantumCodeDistance

/-!
# The three-qubit bit-flip code

The three-qubit bit-flip (repetition) code encodes one qubit as `a|0⟩ + b|1⟩ ↦ a|000⟩ + b|111⟩`.
Its code space is spanned by `|000⟩` and `|111⟩`, and it protects against a single bit flip: the
syndrome `Z₁Z₂, Z₂Z₃` locates the flipped qubit, which is then flipped back (J. Preskill, Ph219
lecture notes, Chapter 7, Section 7.1, equation (7.2) and "A three-qubit code would suffice to
protect against a single bit flip"; each cluster of Shor's nine-qubit code is such a code).

Basis states of three qubits are indexed by `F₂³ = Fin 3 → ZMod 2`, as for CSS codes, and a bit
flip on the qubits in the support of `a` is the Pauli operator `X^a = pauli a 0`. This file proves
that the identity and the three single bit flips are correctable on the code, by checking the
Knill–Laflamme conditions with `(X^a)ᴴ X^b = X^{a + b}`.

## Source

J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7
(Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.1.
-/

@[expose] public section

open scoped Matrix
open Matrix MathlibExt.QuantumInformation.Finite.KnillLaflamme

namespace Cslib.CodingTheory.BitFlip

open Cslib.CodingTheory.CSS Cslib.CodingTheory.QuantumCode

/-- **Code space of the three-qubit bit-flip code.** The orthogonal projector
`|000⟩⟨000| + |111⟩⟨111|` onto the span of `|000⟩` and `|111⟩`, as a diagonal matrix on the
basis indexed by `F₂³` (J. Preskill, Ph219 lecture notes, Chapter 7, Section 7.1). -/
noncomputable def codeProjector : Matrix (Fin 3 → ZMod 2) (Fin 3 → ZMod 2) ℂ :=
  diagonal fun v => if v = 0 ∨ v = 1 then 1 else 0

/-- **Single bit flips on three qubits.** The flip pattern of an error that acts on at most one
qubit: `none` is no error (`0 ∈ F₂³`) and `some i` flips qubit `i` (the unit vector `e_i`). -/
def singleFlip : Option (Fin 3) → (Fin 3 → ZMod 2)
  | none => 0
  | some i => Pi.single i 1

/-- **The code projector is an orthogonal projector.** `Pᴴ = P` and `P * P = P` for the
projector onto the span of `|000⟩` and `|111⟩`. -/
theorem codeProjector_isProj :
    codeProjectorᴴ = codeProjector ∧ codeProjector * codeProjector = codeProjector := by
  refine ⟨?_, ?_⟩
  · rw [codeProjector, diagonal_conjTranspose]
    congr 1
    funext v
    by_cases h : v = 0 ∨ v = 1 <;>
      simp only [Pi.star_apply, h, ite_true, ite_false, star_one, star_zero]
  · rw [codeProjector, diagonal_mul_diagonal]
    congr 1
    funext v
    by_cases h : v = 0 ∨ v = 1 <;> simp only [h, ite_true, ite_false, mul_one, mul_zero]

-- The combinatorial core: two code basis states differ by a pattern of weight at most two only
-- when the pattern is zero.
private theorem code_flip_iff :
    ∀ e e' : Option (Fin 3), ∀ u v : Fin 3 → ZMod 2,
      ((u = 0 ∨ u = 1) ∧ (v = 0 ∨ v = 1) ∧ u = v + (singleFlip e + singleFlip e')) ↔
        (singleFlip e + singleFlip e' = 0 ∧ u = v ∧ (u = 0 ∨ u = 1)) := by
  decide

/-- **Knill–Laflamme conditions for the bit-flip code.** With `P` the projector onto the span of
`|000⟩` and `|111⟩` and `E e = X^{singleFlip e}` the identity or a single bit flip,
`P (E e)ᴴ (E e') P = c P` with `c = 1` if `e = e'` and `c = 0` otherwise (J. Preskill, Ph219
lecture notes, Chapter 7, equation (7.19), for the code of Section 7.1). -/
theorem knillLaflamme_bitFlip (e e' : Option (Fin 3)) :
    ∃ c : ℂ, codeProjector * (pauli (singleFlip e) 0)ᴴ * pauli (singleFlip e') 0 *
      codeProjector = c • codeProjector := by
  classical
  refine ⟨if singleFlip e + singleFlip e' = 0 then 1 else 0, ?_⟩
  rw [Matrix.mul_assoc codeProjector, conjTranspose_pauli_mul_pauli, zero_dotProduct, sign_zero,
    one_smul, add_zero]
  ext u v
  have key := code_flip_iff e e' u v
  simp only [codeProjector, diagonal_mul, mul_diagonal, pauli, of_apply, zero_dotProduct,
    sign_zero, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  by_cases hu : u = 0 ∨ u = 1 <;> by_cases hv : v = 0 ∨ v = 1 <;>
    by_cases hc : singleFlip e + singleFlip e' = 0 <;> by_cases huv : u = v <;>
    by_cases h : u = v + (singleFlip e + singleFlip e') <;> simp_all

/-- **The three-qubit bit-flip code corrects any single bit flip.** On the code spanned by
`|000⟩` and `|111⟩`, the errors `1, X₁, X₂, X₃` (no error, or a bit flip on one of the three
qubits) are correctable by one recovery channel (J. Preskill, Ph219 lecture notes, Chapter 7,
Section 7.1: "A three-qubit code would suffice to protect against a single bit flip"). Proof:
the Knill–Laflamme conditions hold, and they are sufficient. -/
theorem isCorrectable_bitFlip :
    IsCorrectable codeProjector fun e : Option (Fin 3) => pauli (singleFlip e) 0 :=
  MathlibExt.QuantumInformation.Finite.KnillLaflamme.isCorrectable_of_knillLaflamme _
    codeProjector_isProj.1 codeProjector_isProj.2 _ knillLaflamme_bitFlip

end Cslib.CodingTheory.BitFlip
