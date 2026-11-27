/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraph
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Order.RelIso.Basic

/-!
# Normal forms of Type 3 exact covering system digraphs

Translation by a multiple of three gives first offset `0` or `1`.
Reflection, swapping and translation make the second offset positive when necessary.

Statements from Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and
Non-Standard Binary Representations of Integers*, INTEGERS 26 (2026), Article A107.
-/

namespace MetaMathlibExt

private theorem swapIso (x y : ℤ) :
    Nonempty (ecsdAdj ![-2, -2] ![x, y] ≃r ecsdAdj ![-2, -2] ![y, x]) := by
  refine ⟨⟨Equiv.refl _, ?_⟩⟩
  intro m n
  rw [ecsdAdj_two, ecsdAdj_two]
  exact or_comm

private theorem transIso (a₁ a₂ k b₁ b₂ : ℤ) (h1 : b₁ = a₁ + 3 * k)
    (h2 : b₂ = a₂ + 3 * k) :
    Nonempty (ecsdAdj ![-2, -2] ![a₁, a₂] ≃r ecsdAdj ![-2, -2] ![b₁, b₂]) := by
  refine ⟨⟨Equiv.addRight k, ?_⟩⟩
  intro m n
  change ecsdAdj _ _ (m + k) (n + k) ↔ ecsdAdj _ _ m n
  rw [ecsdAdj_two, ecsdAdj_two]
  omega

private theorem negIso (x y : ℤ) :
    Nonempty (ecsdAdj ![-2, -2] ![x, y] ≃r ecsdAdj ![-2, -2] ![-x, -y]) := by
  obtain ⟨e, _⟩ := ecsdAdj_neg_shift_relIso ![-2, -2] ![x, y] 0
  have offsets : (fun i : Fin 2 => -(![x, y] i) + (![-2, -2] i - 1) * 0) = ![-x, -y] := by
    apply funext
    rw [Fin.forall_fin_two]
    constructor <;> simp
  exact ⟨offsets ▸ e⟩

private theorem toZeroForm (x y : ℤ) (hOdd : Odd (x - y)) (hdiv : 3 ∣ x) :
    ∃ a : ℕ, Odd a ∧ Nonempty (ecsdAdj ![-2, -2] ![x, y] ≃r ecsdAdj ![-2, -2] ![0, (a : ℤ)]) := by
  obtain ⟨t, ht⟩ := hdiv
  let k : ℤ := -t
  let b : ℤ := y + 3 * k
  have hx0 : (0 : ℤ) = x + 3 * k := by omega
  have hb : b = y + 3 * k := rfl
  have hOddb : Odd b := by
    rw [Int.odd_iff] at hOdd ⊢
    omega
  obtain ⟨e1⟩ := transIso x y k 0 b hx0 hb
  by_cases hsign : 0 ≤ b
  · refine ⟨b.natAbs, hOddb.natAbs, ?_⟩
    rw [Int.natAbs_of_nonneg hsign]
    exact ⟨e1⟩
  · refine ⟨b.natAbs, hOddb.natAbs, ?_⟩
    rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge hsign)]
    obtain ⟨e2⟩ := negIso 0 b
    simp only [neg_zero] at e2
    exact ⟨e1.trans e2⟩

private theorem toOneOrTwoOfModOne (x y : ℤ) (hOdd : Odd (x - y)) (hmod : x % 3 = 1)
    (hy12 : y % 3 = 1 ∨ y % 3 = 2) :
    (∃ a : ℕ, Even a ∧ a % 3 = 1 ∧
      Nonempty (ecsdAdj ![-2, -2] ![x, y] ≃r ecsdAdj ![-2, -2] ![1, (a : ℤ)])) ∨
    ∃ a : ℤ, Even a ∧ a % 3 = 2 ∧
      Nonempty (ecsdAdj ![-2, -2] ![x, y] ≃r ecsdAdj ![-2, -2] ![1, a]) := by
  have hdiv := Int.mul_ediv_add_emod x 3
  rw [hmod] at hdiv
  let t : ℤ := x / 3
  have hx : x = 3 * t + 1 := by omega
  let k : ℤ := -t
  let b : ℤ := y + 3 * k
  have h1 : (1 : ℤ) = x + 3 * k := by omega
  have hb : b = y + 3 * k := rfl
  have hdiff : (1 : ℤ) - b = x - y := by omega
  have hOdd1b : Odd ((1 : ℤ) - b) := by
    rw [hdiff]
    exact hOdd
  have hEvenb : Even b := by
    rw [Int.odd_iff] at hOdd1b
    rw [Int.even_iff]
    omega
  obtain ⟨e1⟩ := transIso x y k 1 b h1 hb
  rcases hy12 with hy1 | hy2
  · have hb1 : b % 3 = 1 := by omega
    by_cases hsign : 0 ≤ b
    · refine Or.inl ⟨b.natAbs, hEvenb.natAbs, ?_, ?_⟩
      · have h := Int.natAbs_emod_of_nonneg hsign (3 : ℤ)
        rw [hb1] at h
        simpa using h.symm
      · rw [Int.natAbs_of_nonneg hsign]
        exact ⟨e1⟩
    · have hdiv2 := Int.mul_ediv_add_emod b 3
      rw [hb1] at hdiv2
      let t2 : ℤ := b / 3
      have hb_eq : b = 3 * t2 + 1 := by omega
      let k2 : ℤ := -t2
      have hs1 : (1 : ℤ) = b + 3 * k2 := by omega
      have hs2 : 2 - b = 1 + 3 * k2 := by omega
      obtain ⟨eswap⟩ := swapIso 1 b
      obtain ⟨etrans⟩ := transIso b 1 k2 1 (2 - b) hs1 hs2
      have hEven2b : Even (2 - b) := by
        rw [Int.even_iff] at hEvenb ⊢
        omega
      have hb2mod : (2 - b) % 3 = 1 := by omega
      have hpos : 0 ≤ 2 - b := by omega
      refine Or.inl ⟨(2 - b).natAbs, hEven2b.natAbs, ?_, ?_⟩
      · have h := Int.natAbs_emod_of_nonneg hpos (3 : ℤ)
        rw [hb2mod] at h
        simpa using h.symm
      · rw [Int.natAbs_of_nonneg hpos]
        exact ⟨e1.trans (eswap.trans etrans)⟩
  · have hb2 : b % 3 = 2 := by omega
    exact Or.inr ⟨b, hEvenb, hb2, ⟨e1⟩⟩

private theorem modThreeCases (a : ℤ) (h : ¬ (3 : ℤ) ∣ a) : a % 3 = 1 ∨ a % 3 = 2 := by
  have h0 : 0 ≤ a % 3 := Int.emod_nonneg _ (by decide)
  have hlt : a % 3 < (3 : ℤ).natAbs := Int.emod_lt _ (by decide)
  simp at hlt
  have hne : a % 3 ≠ 0 := fun heq => h (Int.dvd_iff_emod_eq_zero.mpr heq)
  omega

private theorem oddSwap (x y : ℤ) (h : Odd (x - y)) : Odd (y - x) := by
  rw [Int.odd_iff] at h ⊢
  omega

private theorem oddNeg (x y : ℤ) (h : Odd (x - y)) : Odd (-x - -y) := by
  rw [Int.odd_iff] at h ⊢
  omega

/-- **Normal forms of the ECSDs $G(-2n + a_1, -2n + a_2)$.** For all integers $a_1, a_2$ with
$a_1 - a_2$ odd, the exact covering system digraph $G(-2n + a_1, -2n + a_2)$, with an edge
$m \to -2m + a_1$ and an edge $m \to -2m + a_2$ for every integer $m$, is isomorphic as a
digraph to one of the following: $G(-2n, -2n + a)$ for an odd natural number $a$ (Type 3.1);
$G(-2n + 1, -2n + a)$ for an even natural number $a$ with $a \equiv 1 \pmod 3$ (Type 3.2); or
$G(-2n + 1, -2n + a)$ for an even integer $a$ with $a \equiv 2 \pmod 3$ (Type 3.3).

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 5
(`integers-2026-A107-thm-5`). -/
public theorem ecsd_type_three_relIso (a₁ a₂ : ℤ) (h : Odd (a₁ - a₂)) :
    (∃ a : ℕ, Odd a ∧
        Nonempty (ecsdAdj ![-2, -2] ![a₁, a₂] ≃r ecsdAdj ![-2, -2] ![0, (a : ℤ)])) ∨
      (∃ a : ℕ, Even a ∧ a % 3 = 1 ∧
        Nonempty (ecsdAdj ![-2, -2] ![a₁, a₂] ≃r ecsdAdj ![-2, -2] ![1, (a : ℤ)])) ∨
      ∃ a : ℤ, Even a ∧ a % 3 = 2 ∧
        Nonempty (ecsdAdj ![-2, -2] ![a₁, a₂] ≃r ecsdAdj ![-2, -2] ![1, a]) := by
  by_cases h1 : (3 : ℤ) ∣ a₁
  · obtain ⟨a, haOdd, he⟩ := toZeroForm a₁ a₂ h h1
    exact Or.inl ⟨a, haOdd, he⟩
  · by_cases h2 : (3 : ℤ) ∣ a₂
    · have hswap : Odd (a₂ - a₁) := oddSwap a₁ a₂ h
      obtain ⟨a, haOdd, ⟨e⟩⟩ := toZeroForm a₂ a₁ hswap h2
      obtain ⟨eswap⟩ := swapIso a₁ a₂
      exact Or.inl ⟨a, haOdd, ⟨eswap.trans e⟩⟩
    · have ha1 := modThreeCases a₁ h1
      have ha2 := modThreeCases a₂ h2
      rcases ha1 with ha1one | ha1two
      · have hBC := toOneOrTwoOfModOne a₁ a₂ h ha1one ha2
        exact Or.inr hBC
      · have hNegOdd : Odd (-a₁ - -a₂) := oddNeg a₁ a₂ h
        have hNegMod : (-a₁) % 3 = 1 := by omega
        have hNegY12 : (-a₂) % 3 = 1 ∨ (-a₂) % 3 = 2 := by
          rcases ha2 with hy1 | hy2
          · have hneg2 : (-a₂) % 3 = 2 := by omega
            exact Or.inr hneg2
          · have hneg1 : (-a₂) % 3 = 1 := by omega
            exact Or.inl hneg1
        have hBC := toOneOrTwoOfModOne (-a₁) (-a₂) hNegOdd hNegMod hNegY12
        obtain ⟨eneg⟩ := negIso a₁ a₂
        rcases hBC with ⟨a, haEven, haMod, ⟨e⟩⟩ | ⟨a, haEven, haMod, ⟨e⟩⟩
        · exact Or.inr (Or.inl ⟨a, haEven, haMod, ⟨eneg.trans e⟩⟩)
        · exact Or.inr (Or.inr ⟨a, haEven, haMod, ⟨eneg.trans e⟩⟩)

end MetaMathlibExt
