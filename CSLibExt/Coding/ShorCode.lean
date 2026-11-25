/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.QuantumCodeDistance

/-!
# Shor's nine-qubit code

Shor's code encodes one qubit into nine. Its basis codewords repeat a three-qubit cat state three
times:
`|0̄⟩ = [(|000⟩ + |111⟩)/√2]^{⊗3}` and `|1̄⟩ = [(|000⟩ - |111⟩)/√2]^{⊗3}`
(J. Preskill, Ph219 lecture notes, Chapter 7, equation (7.1)). This file defines the two
codewords, without the normalisation `2^{-3/2}`, as functions on the basis `F₂⁹` of nine qubits.
It also proves that the distance is at most three: the weight-three operator `Z₁Z₄Z₇` maps
`|0̄⟩` to `|1̄⟩`, so it violates the distance condition. That the distance is exactly three,
hence that the code corrects any error on one qubit, is proved in
`CSLibExt.Coding.ShorCodeDistance`
(`Cslib.CodingTheory.ShorCodeWanted.shorCodeword_distance_three`).

## Source

J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7
(Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.1.
-/

@[expose] public section

namespace Cslib.CodingTheory.Shor

open Cslib.CodingTheory.CSS Cslib.CodingTheory.QuantumCode
open scoped Matrix

/-- **Codewords of Shor's nine-qubit code.** For `x ∈ F₂`, the unnormalised state
`|x̄⟩ = [|000⟩ + (-1)^x |111⟩]^{⊗3}` on nine qubits, as a function `F₂⁹ → ℂ`: the amplitude of
`|v⟩` is `0` unless each block `(v₀v₁v₂)`, `(v₃v₄v₅)`, `(v₆v₇v₈)` is `000` or `111`, and is then
`(-1)^{x m}` with `m` the number of blocks equal to `111` (J. Preskill, Ph219 lecture notes,
Chapter 7, equation (7.1), without the factor `2^{-3/2}`). -/
noncomputable def shorCodeword (x : ZMod 2) : (Fin 9 → ZMod 2) → ℂ := fun v =>
  if v 0 = v 1 ∧ v 1 = v 2 ∧ v 3 = v 4 ∧ v 4 = v 5 ∧ v 6 = v 7 ∧ v 7 = v 8 then
    sign (x * (v 0 + v 3 + v 6))
  else 0

/-- **Shor's code has distance at most three.** The Pauli operator `Z₁Z₄Z₇ = X^0 Z^b`, with `b`
supported on the first qubit of each block, has weight three, and there is no scalar `λ` with
`⟨x̄| Z₁Z₄Z₇ |ȳ⟩ = λ δ_{xy}` for the two Shor codewords: `⟨0̄| Z₁Z₄Z₇ |1̄⟩ ≠ 0`, because
`Z₁Z₄Z₇` multiplies the amplitude of each code basis state by `(-1)^{v₀ + v₃ + v₆}` and so maps
`|0̄⟩` to `|1̄⟩`. So the distance condition of J. Preskill, Ph219 lecture notes, Chapter 7,
equation (7.34), fails at weight three (compare equation (7.8), where `Z₁Z₄Z₇` flips the encoded
qubit). -/
theorem shorCodeword_violation_weight_three :
    ∃ a b : Fin 9 → ZMod 2, pauliWeight a b = 3 ∧ ¬ ∃ l : ℂ, ∀ x y : ZMod 2,
      star (shorCodeword x) ⬝ᵥ (pauli a b *ᵥ shorCodeword y) = if x = y then l else 0 := by
  classical
  set b : Fin 9 → ZMod 2 := Pi.single 0 1 + Pi.single 3 1 + Pi.single 6 1 with hb
  refine ⟨0, b, by decide, ?_⟩
  rintro ⟨l, hl⟩
  have h01 := hl 0 1
  simp only [show ¬ ((0 : ZMod 2) = 1) by decide, ite_false] at h01
  have hdot : ∀ u : Fin 9 → ZMod 2, b ⬝ᵥ u = u 0 + u 3 + u 6 := by
    intro u
    simp [hb, dotProduct, Fin.sum_univ_succ, Pi.single_apply, add_mul, add_assoc]
  -- every term of the sum is the indicator of the code basis states
  have hterm : ∀ u : Fin 9 → ZMod 2,
      star (shorCodeword 0) u * (pauli 0 b *ᵥ shorCodeword 1) u =
        if u 0 = u 1 ∧ u 1 = u 2 ∧ u 3 = u 4 ∧ u 4 = u 5 ∧ u 6 = u 7 ∧ u 7 = u 8 then 1 else 0 := by
    intro u
    rw [pauli_mulVec_apply, add_zero, hdot, Pi.star_apply]
    simp only [shorCodeword, zero_mul, one_mul]
    split_ifs
    · rw [CSS.sign_zero, star_one, one_mul, sign_mul_self]
    · simp
  have hsum : star (shorCodeword 0) ⬝ᵥ (pauli 0 b *ᵥ shorCodeword 1) =
      ((Finset.univ.filter fun u : Fin 9 → ZMod 2 =>
        u 0 = u 1 ∧ u 1 = u 2 ∧ u 3 = u 4 ∧ u 4 = u 5 ∧ u 6 = u 7 ∧ u 7 = u 8).card : ℂ) := by
    rw [dotProduct, Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_boole]
  rw [hsum, Nat.cast_eq_zero, Finset.card_eq_zero] at h01
  have h0 : (0 : Fin 9 → ZMod 2) ∈ Finset.univ.filter fun u : Fin 9 → ZMod 2 =>
      u 0 = u 1 ∧ u 1 = u 2 ∧ u 3 = u 4 ∧ u 4 = u 5 ∧ u 6 = u 7 ∧ u 7 = u 8 := by
    simp
  rw [h01] at h0
  exact Finset.notMem_empty _ h0

end Cslib.CodingTheory.Shor
