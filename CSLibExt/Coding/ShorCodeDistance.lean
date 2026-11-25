/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.ShorCode

/-!
# Shor's code has distance three

`shorCodeword_distance_three`: every Pauli operator `X^a Z^b` on nine qubits of weight at most two
satisfies `⟨x̄| X^a Z^b |ȳ⟩ = λ δ_{xy}` for the two codewords `|0̄⟩`, `|1̄⟩` of Shor's code
(`Cslib.CodingTheory.Shor.shorCodeword`), and the weight-three operator `Z₁Z₄Z₇` violates this
(`Cslib.CodingTheory.Shor.shorCodeword_violation_weight_three`). So Shor's code has distance
three.

## Proof

Both codewords are supported on the basis states `v ∈ F₂⁹` that are constant on each block
`(v₀v₁v₂)`, `(v₃v₄v₅)`, `(v₆v₇v₈)`. These states form a subspace `C`, on which `|x̄⟩` has
amplitude `(-1)^{x (v₀ + v₃ + v₆)}`.

* If `a ∉ C`, then `X^a` maps the states of `C` outside `C`, so every matrix element
  `⟨x̄| X^a Z^b |ȳ⟩` vanishes.
* If `a ∈ C`, then `a` is zero or one on each block, and weight at most two forces `a = 0`.
* For `a = 0`, the squared amplitude of `|x̄⟩` is the indicator of `C`, so `⟨x̄| Z^b |x̄⟩` does not
  depend on `x`. Weight at most two leaves a block on which `b` has even parity. Translating by
  the indicator `c` of that block preserves `C`, multiplies the amplitudes of `|x̄⟩` by `(-1)^x`
  (so `X^c` maps `|x̄⟩` to `(-1)^x |x̄⟩`; compare D. Gottesman, Section 3.1, equations (3.2) and
  (3.3), for `X₁X₂X₃`) and fixes the phase `(-1)^{b · v}` of `Z^b`. For `x ≠ y` it therefore
  reverses the sign of every term of `⟨x̄| Z^b |ȳ⟩`, which vanishes.

This computation on the codewords avoids the stabilizer formalism. Gottesman (Section 3.1)
argues through the stabilizer instead: every Pauli operator of weight one or two anticommutes
with some element of the stabilizer, except `Z_a Z_b` with `a` and `b` in the same block, which
lies in the stabilizer.

## Sources

J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7
(Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Sections 7.1 and 7.3.1.

D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, Caltech (1997),
arXiv:quant-ph/9705052, Section 3.1.
-/

@[expose] public section

open scoped Matrix
open Cslib.CodingTheory.CSS Cslib.CodingTheory.Shor Cslib.CodingTheory.QuantumCode

namespace Cslib.CodingTheory.ShorCodeWanted

/-- The support of the Shor codewords: basis states `v ∈ F₂⁹` that are constant on each of the
blocks `(v₀v₁v₂)`, `(v₃v₄v₅)` and `(v₆v₇v₈)`. -/
private def IsBlockConstant (v : Fin 9 → ZMod 2) : Prop :=
  v 0 = v 1 ∧ v 1 = v 2 ∧ v 3 = v 4 ∧ v 4 = v 5 ∧ v 6 = v 7 ∧ v 7 = v 8

private theorem shorCodeword_of_isBlockConstant (x : ZMod 2) {v : Fin 9 → ZMod 2}
    (hv : IsBlockConstant v) : shorCodeword x v = sign (x * (v 0 + v 3 + v 6)) :=
  ite_eq_left hv

private theorem shorCodeword_of_not_isBlockConstant (x : ZMod 2) {v : Fin 9 → ZMod 2}
    (hv : ¬ IsBlockConstant v) : shorCodeword x v = 0 :=
  ite_eq_right hv

/-- The support of the Shor codewords is closed under addition. -/
private theorem isBlockConstant_add {u v : Fin 9 → ZMod 2} (hu : IsBlockConstant u)
    (hv : IsBlockConstant v) : IsBlockConstant (u + v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hv
  simp only [IsBlockConstant, Pi.add_apply]
  exact ⟨by rw [h1, k1], by rw [h2, k2], by rw [h3, k3], by rw [h4, k4], by rw [h5, k5],
    by rw [h6, k6]⟩

/-- Translating by `c` constant on blocks multiplies the amplitudes of `|x̄⟩` by
`(-1)^{x (c₀ + c₃ + c₆)}`. -/
private theorem shorCodeword_add {c : Fin 9 → ZMod 2} (hc : IsBlockConstant c) (x : ZMod 2)
    (u : Fin 9 → ZMod 2) :
    shorCodeword x (u + c) = sign (x * (c 0 + c 3 + c 6)) * shorCodeword x u := by
  by_cases hu : IsBlockConstant u
  · rw [shorCodeword_of_isBlockConstant x (isBlockConstant_add hu hc),
      shorCodeword_of_isBlockConstant x hu, ← sign_add]
    congr 1
    simp only [Pi.add_apply]
    ring
  · have huc : ¬ IsBlockConstant (u + c) := fun h => hu (by
      have := isBlockConstant_add h hc
      rwa [add_assoc, CSS.add_self_eq_zero, add_zero] at this)
    rw [shorCodeword_of_not_isBlockConstant x hu, shorCodeword_of_not_isBlockConstant x huc,
      mul_zero]

/-- If `a` is not constant on blocks, `X^a` maps the support of the codewords outside it, so
every matrix element `⟨x̄| X^a Z^b |ȳ⟩` vanishes. -/
private theorem inner_pauli_eq_zero {a : Fin 9 → ZMod 2} (ha : ¬ IsBlockConstant a)
    (b : Fin 9 → ZMod 2) (x y : ZMod 2) :
    star (shorCodeword x) ⬝ᵥ (pauli a b *ᵥ shorCodeword y) = 0 := by
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [Pi.star_apply, pauli_mulVec_apply]
  by_cases hu : IsBlockConstant u
  · have hua : ¬ IsBlockConstant (u + a) := fun h => ha (by
      have := isBlockConstant_add hu h
      rwa [← add_assoc, CSS.add_self_eq_zero, zero_add] at this)
    rw [shorCodeword_of_not_isBlockConstant y hua, mul_zero, mul_zero]
  · rw [shorCodeword_of_not_isBlockConstant x hu, star_zero, zero_mul]

/-- The squared amplitude of `|x̄⟩` does not depend on `x`: it is the amplitude of `|0̄⟩`, the
indicator of the support. -/
private theorem star_shorCodeword_mul_self (x : ZMod 2) (u : Fin 9 → ZMod 2) :
    star (shorCodeword x u) * shorCodeword x u = shorCodeword 0 u := by
  by_cases hu : IsBlockConstant u
  · rw [shorCodeword_of_isBlockConstant x hu, shorCodeword_of_isBlockConstant 0 hu, star_sign,
      sign_mul_self, zero_mul, sign_zero]
  · rw [shorCodeword_of_not_isBlockConstant x hu, shorCodeword_of_not_isBlockConstant 0 hu,
      mul_zero]

/-- The diagonal matrix elements `⟨x̄| Z^b |x̄⟩` do not depend on `x`. -/
private theorem inner_pauli_zero_self (b : Fin 9 → ZMod 2) (x : ZMod 2) :
    star (shorCodeword x) ⬝ᵥ (pauli 0 b *ᵥ shorCodeword x) =
      star (shorCodeword 0) ⬝ᵥ (pauli 0 b *ᵥ shorCodeword 0) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Pi.star_apply, pauli_mulVec_apply, add_zero]
  rw [mul_left_comm, star_shorCodeword_mul_self, mul_left_comm (star _),
    star_shorCodeword_mul_self]

/-- If some `c` constant on blocks has `(x + y) (c₀ + c₃ + c₆) + b · c = 1`, then translating by
`c` reverses the sign of every term of `⟨x̄| Z^b |ȳ⟩`, so this matrix element vanishes. -/
private theorem inner_pauli_zero_eq_zero {x y : ZMod 2} {b c : Fin 9 → ZMod 2}
    (hc : IsBlockConstant c) (h : (x + y) * (c 0 + c 3 + c 6) + b ⬝ᵥ c = 1) :
    star (shorCodeword x) ⬝ᵥ (pauli 0 b *ᵥ shorCodeword y) = 0 := by
  have hterm : ∀ u, star (shorCodeword x) (u + c) * (pauli 0 b *ᵥ shorCodeword y) (u + c) =
      -(star (shorCodeword x) u * (pauli 0 b *ᵥ shorCodeword y) u) := by
    intro u
    have hs : sign (x * (c 0 + c 3 + c 6)) * sign (y * (c 0 + c 3 + c 6)) * sign (b ⬝ᵥ c) =
        -1 := by
      rw [← sign_add, ← sign_add, ← add_mul, h, sign_one]
    simp only [Pi.star_apply, pauli_mulVec_apply, add_zero, shorCodeword_add hc, dotProduct_add,
      sign_add, star_mul', star_sign]
    linear_combination (star (shorCodeword x u) * sign (b ⬝ᵥ u) * shorCodeword y u) * hs
  have hneg : star (shorCodeword x) ⬝ᵥ (pauli 0 b *ᵥ shorCodeword y) =
      -(star (shorCodeword x) ⬝ᵥ (pauli 0 b *ᵥ shorCodeword y)) := by
    conv_lhs => rw [dotProduct, ← Equiv.sum_comp (Equiv.addRight c)]
    rw [dotProduct, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun u _ => hterm u
  have h2 : (2 : ℂ) * (star (shorCodeword x) ⬝ᵥ (pauli 0 b *ᵥ shorCodeword y)) = 0 := by
    linear_combination hneg
  simpa using h2

/-- Three distinct qubits on which `X^a Z^b` acts nontrivially give it weight at least three. -/
private theorem three_le_pauliWeight {a b : Fin 9 → ZMod 2} {i j k : Fin 9} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hi : a i ≠ 0 ∨ b i ≠ 0) (hj : a j ≠ 0 ∨ b j ≠ 0)
    (hk : a k ≠ 0 ∨ b k ≠ 0) : 3 ≤ pauliWeight a b := by
  classical
  rw [← Finset.card_eq_three.2 ⟨i, j, k, hij, hik, hjk, rfl⟩]
  refine Finset.card_le_card fun l hl => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl <;> simpa

/-- A bit flip `X^a` with `a` constant on blocks and weight at most two is the identity. -/
private theorem eq_zero_of_isBlockConstant {a b : Fin 9 → ZMod 2} (hw : pauliWeight a b < 3)
    (ha : IsBlockConstant a) : a = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha
  have hblock : ∀ i j k : Fin 9, i ≠ j → i ≠ k → j ≠ k → a i = a j → a j = a k → a i = 0 := by
    intro i j k hij hik hjk hj hk
    by_contra h
    have := three_le_pauliWeight (b := b) hij hik hjk (Or.inl h) (Or.inl (by rwa [← hj]))
      (Or.inl (by rwa [← hk, ← hj]))
    omega
  have e0 := hblock 0 1 2 (by decide) (by decide) (by decide) h1 h2
  have e3 := hblock 3 4 5 (by decide) (by decide) (by decide) h3 h4
  have e6 := hblock 6 7 8 (by decide) (by decide) (by decide) h5 h6
  funext i
  fin_cases i <;> simp_all

/-- Weight at most two leaves a block on which `b` has even parity; its indicator `c` is constant
on blocks with `c₀ + c₃ + c₆ + b · c = 1`. -/
private theorem exists_isBlockConstant {a b : Fin 9 → ZMod 2} (hw : pauliWeight a b < 3) :
    ∃ c, IsBlockConstant c ∧ c 0 + c 3 + c 6 + b ⬝ᵥ c = 1 := by
  by_contra hne
  push Not at hne
  -- otherwise `b` has odd parity, hence a nonzero entry, on each block
  have hblock : ∀ (c : Fin 9 → ZMod 2) (i j k : Fin 9),
      c = Pi.single i 1 + Pi.single j 1 + Pi.single k 1 → IsBlockConstant c →
      c 0 + c 3 + c 6 = 1 → b i ≠ 0 ∨ b j ≠ 0 ∨ b k ≠ 0 := by
    rintro c i j k rfl hc hc1
    have h := hne _ hc
    rw [hc1, dotProduct_add, dotProduct_add, dotProduct_single, dotProduct_single,
      dotProduct_single, mul_one, mul_one, mul_one] at h
    contrapose! h
    rw [h.1, h.2.1, h.2.2, add_zero, add_zero, add_zero]
  have hb0 := hblock _ 0 1 2 rfl (by unfold IsBlockConstant; decide) (by decide)
  have hb1 := hblock _ 3 4 5 rfl (by unfold IsBlockConstant; decide) (by decide)
  have hb2 := hblock _ 6 7 8 rfl (by unfold IsBlockConstant; decide) (by decide)
  rcases hb0 with h0 | h0 | h0 <;> rcases hb1 with h1 | h1 | h1 <;>
    rcases hb2 with h2 | h2 | h2 <;>
    exact absurd (three_le_pauliWeight (a := a) (by decide) (by decide) (by decide) (Or.inr h0)
      (Or.inr h1) (Or.inr h2)) (by omega)

/-- **Shor's code has distance three.** Every Pauli operator `X^a Z^b` on nine qubits of weight at
most two satisfies `⟨x̄| X^a Z^b |ȳ⟩ = λ δ_{xy}` for some scalar `λ` and the two Shor codewords
`x, y ∈ F₂` (which have equal norms), and some Pauli operator of weight three violates this. By
the definition of J. Preskill, Ph219 lecture notes, Chapter 7, equation (7.34) (the distance is
the minimum weight of a violating Pauli operator), Shor's code is a `[[9, 1, 3]]` code
(D. Gottesman, PhD thesis (1997), Section 3.1: "The distance of this code is in fact three"); by
Preskill's Section 7.3.1 it corrects any error on one qubit. The weight-three half is proved as
`Cslib.CodingTheory.Shor.shorCodeword_violation_weight_three`. -/
theorem shorCodeword_distance_three :
    (∀ a b : Fin 9 → ZMod 2, pauliWeight a b < 3 → ∃ l : ℂ, ∀ x y : ZMod 2,
      star (shorCodeword x) ⬝ᵥ (pauli a b *ᵥ shorCodeword y) = if x = y then l else 0) ∧
    ∃ a b : Fin 9 → ZMod 2, pauliWeight a b = 3 ∧ ¬ ∃ l : ℂ, ∀ x y : ZMod 2,
      star (shorCodeword x) ⬝ᵥ (pauli a b *ᵥ shorCodeword y) = if x = y then l else 0 := by
  refine ⟨fun a b hw => ?_, shorCodeword_violation_weight_three⟩
  by_cases ha : IsBlockConstant a
  · obtain ⟨c, hc, hbc⟩ := exists_isBlockConstant hw
    obtain rfl := eq_zero_of_isBlockConstant hw ha
    refine ⟨star (shorCodeword 0) ⬝ᵥ (pauli 0 b *ᵥ shorCodeword 0), fun x y => ?_⟩
    split_ifs with hxy
    · rw [hxy, inner_pauli_zero_self]
    · have hxy' : x + y = 1 := by
        have key : ∀ x y : ZMod 2, x ≠ y → x + y = 1 := by decide
        exact key x y hxy
      exact inner_pauli_zero_eq_zero hc (by rw [hxy', one_mul, hbc])
  · exact ⟨0, fun x y => by rw [ite_self, inner_pauli_eq_zero ha]⟩

end Cslib.CodingTheory.ShorCodeWanted
