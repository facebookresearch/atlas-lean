/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.CSSCode
public import MathlibExt.QuantumInformation.Finite.KnillLaflamme
public import Mathlib.InformationTheory.Hamming

/-!
# Distance of a quantum code

Basis states of `n` qubits are indexed by `F₂ⁿ`, and `pauli a b = X^a Z^b` is the Pauli operator
of `CSLibExt.Coding.CSSCode`. Its *weight* is the number of qubits on which it acts nontrivially.
A code with projector `P` has distance at least `d` when every Pauli operator `E` of weight less
than `d` satisfies `P E P = c_E P`; equivalently, in an orthonormal basis of the code,
`⟨ī|E|j̄⟩ = c_E δ_ij` (J. Preskill, Ph219 lecture notes, Chapter 7, Section 7.3.1, equation
(7.34), where the distance is the minimum weight of a Pauli operator violating this).

Main results:
* `conjTranspose_pauli_mul_pauli`:
  `(X^a Z^b)ᴴ X^{a'} Z^{b'} = (-1)^{b · (a + a')} X^{a + a'} Z^{b + b'}`, so products of Pauli
  operators are Pauli operators up to a sign;
* `pauliWeight_add_le`: the weight of such a product is at most the sum of the weights;
* `isCorrectable_of_hasDistanceAtLeast`: a code of distance at least `2t + 1` corrects every
  Pauli error of weight at most `t` (Preskill, Section 7.3.1: "a QECC with distance `d = 2t + 1`
  can correct `t` errors").

## Source

J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7
(Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Sections 7.2, 7.3.1 and
7.9.1.
-/

@[expose] public section

open scoped Matrix
open Matrix MathlibExt.QuantumInformation.Finite.KnillLaflamme

namespace Cslib.CodingTheory.QuantumCode

open Cslib.CodingTheory.CSS

variable {n : ℕ}

private theorem add_add_cancel_right (x y : Fin n → ZMod 2) : x + y + y = x := by
  rw [add_assoc, add_self_eq_zero, add_zero]

/-- **Product of two Pauli operators.** For `a, b, a', b' ∈ F₂ⁿ`,
`(X^a Z^b)ᴴ (X^{a'} Z^{b'}) = (-1)^{b · (a + a')} X^{a + a'} Z^{b + b'}`: the Pauli operators are
closed under products up to a sign (J. Preskill, Ph219 lecture notes, Chapter 7, Section 7.9.1:
the `n`-qubit Pauli operators form a group, and any two of them commute or anticommute). -/
theorem conjTranspose_pauli_mul_pauli (a b a' b' : Fin n → ZMod 2) :
    (pauli a b)ᴴ * pauli a' b' = sign (b ⬝ᵥ (a + a')) • pauli (a + a') (b + b') := by
  classical
  ext u v
  have hP : ∀ (c e x y : Fin n → ZMod 2),
      pauli c e x y = if x = y + c then sign (e ⬝ᵥ y) else 0 := fun _ _ _ _ => rfl
  have hPh : ∀ (c e x y : Fin n → ZMod 2),
      (pauli c e)ᴴ x y = if y = x + c then sign (e ⬝ᵥ x) else 0 := by
    intro c e x y
    rw [conjTranspose_apply, hP]
    split_ifs
    · exact star_sign _
    · exact star_zero _
  rw [mul_apply, Matrix.smul_apply, hP]
  simp only [hPh, hP, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  by_cases h : u = v + (a + a')
  · have h' : u + a = v + a' := by
      rw [h, add_assoc, add_comm a a', ← add_assoc v, ← add_assoc, add_add_cancel_right]
    simp only [h'.symm, h, ite_true, smul_eq_mul]
    rw [← sign_add, ← sign_add]
    congr 1
    rw [dotProduct_add, add_dotProduct]
    abel
  · have h' : ¬ u + a = v + a' := by
      intro h'
      apply h
      rw [← add_add_cancel_right u a, h', add_assoc, add_comm a' a]
    simp only [Ne.symm h', h, ite_false, smul_zero]

/-- **Weight of a Pauli operator.** The number of qubits `i` on which `X^a Z^b` acts
nontrivially, that is with `a i ≠ 0` or `b i ≠ 0` (J. Preskill, Ph219 lecture notes, Chapter 7,
Section 7.2: "the weight is the number of qubits acted on by a nontrivial Pauli matrix"). -/
def pauliWeight (a b : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => a i ≠ 0 ∨ b i ≠ 0).card

/-- **Pauli weight as a Hamming norm.** The weight of `X^a Z^b` is the Hamming norm (number of
nonzero entries) of the vector `i ↦ (a i, b i)` over `F₂ × F₂`, the symplectic representation of
the Pauli operator up to phase (J. Preskill, Ph219 lecture notes, Chapter 7, Section 7.9.2). -/
theorem pauliWeight_eq_hammingNorm (a b : Fin n → ZMod 2) :
    pauliWeight a b = hammingNorm fun i => (a i, b i) := by
  classical
  unfold pauliWeight hammingNorm
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Prod.ext_iff, Prod.fst_zero,
    Prod.snd_zero, not_and_or]

/-- **Weight of a product of Pauli operators.** The Pauli operator `X^{a + a'} Z^{b + b'}`, the
product of `X^a Z^b` and `X^{a'} Z^{b'}` up to a sign, has weight at most the sum of their
weights: it acts trivially wherever both act trivially. -/
theorem pauliWeight_add_le (a b a' b' : Fin n → ZMod 2) :
    pauliWeight (a + a') (b + b') ≤ pauliWeight a b + pauliWeight a' b' := by
  classical
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.add_apply] at hi ⊢
  by_contra hcon
  simp only [not_or, ne_eq, not_not] at hcon
  obtain ⟨⟨ha, hb⟩, ha', hb'⟩ := hcon
  rw [ha, hb, ha', hb', add_zero] at hi
  exact hi.elim (· rfl) (· rfl)

/-- **Distance of a quantum code (lower bound).** The code with projector `P` on `n` qubits has
distance at least `d` if every Pauli operator `X^a Z^b` of weight less than `d` satisfies
`P X^a Z^b P = c P` for some scalar `c`. In an orthonormal basis `|ī⟩` of the code this is
`⟨ī| X^a Z^b |j̄⟩ = c δ_ij`; the distance of J. Preskill, Ph219 lecture notes, Chapter 7,
equation (7.34), is the least weight of a Pauli operator for which this fails. -/
def HasDistanceAtLeast (P : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (d : ℕ) : Prop :=
  ∀ a b : Fin n → ZMod 2, pauliWeight a b < d → ∃ c : ℂ, P * pauli a b * P = c • P

/-- **A code of distance `2t + 1` corrects `t` errors.** Let `P` be an orthogonal projector on
`n` qubits whose code has distance at least `d`. Then the Pauli errors `X^a Z^b` of weight `t`
with `2t + 1 ≤ d` are correctable on the code, all by one recovery channel (J. Preskill, Ph219
lecture notes, Chapter 7, Section 7.3.1: "a QECC with distance `d = 2t + 1` can correct `t`
errors"). Proof: `(X^a Z^b)ᴴ X^{a'} Z^{b'}` is, up to a sign, a Pauli operator of weight at most
`2t < d`, so the Knill–Laflamme conditions hold. -/
theorem isCorrectable_of_hasDistanceAtLeast {P : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hP : Pᴴ = P) (hPP : P * P = P) {d : ℕ} (hd : HasDistanceAtLeast P d) :
    IsCorrectable P (fun e : {e : (Fin n → ZMod 2) × (Fin n → ZMod 2) //
        2 * pauliWeight e.1 e.2 + 1 ≤ d} => pauli e.1.1 e.1.2) := by
  refine MathlibExt.QuantumInformation.Finite.KnillLaflamme.isCorrectable_of_knillLaflamme P hP
    hPP _ fun e e' => ?_
  have hw : pauliWeight (e.1.1 + e'.1.1) (e.1.2 + e'.1.2) < d := by
    have := pauliWeight_add_le e.1.1 e.1.2 e'.1.1 e'.1.2
    have h1 := e.2
    have h2 := e'.2
    omega
  obtain ⟨c, hc⟩ := hd _ _ hw
  refine ⟨sign (e.1.2 ⬝ᵥ (e.1.1 + e'.1.1)) * c, ?_⟩
  rw [Matrix.mul_assoc P, conjTranspose_pauli_mul_pauli, Matrix.mul_smul, Matrix.smul_mul, hc,
    smul_smul]

end Cslib.CodingTheory.QuantumCode
