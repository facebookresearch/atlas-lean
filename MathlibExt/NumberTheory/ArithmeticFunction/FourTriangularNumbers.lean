/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.Divisors

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt.FourTriangular

/-- Triangular numbers `T(u) = u * (u + 1) / 2`, spelled as in the Wanted statement. -/
private def ftnTri (u : ℕ) : ℕ := u * (u + 1) / 2

/-- `t2(a)`: number of pairs `(u, v)` with `T(u) + T(v) = a`. -/
private def ftnTriPairCount (a : ℕ) : ℕ :=
  ((Finset.range (a + 1) ×ˢ Finset.range (a + 1)).filter
    (fun p => ftnTri p.1 + ftnTri p.2 = a)).card

/-- `S(N)`: Gaussian integers of norm `N`. Its count is `g(N)`. -/
private def ftnGaussNormSet (N : ℕ) : Set GaussianInt := { z | z.norm = (N : ℤ) }

/-- `Reg(N)`: Gaussian integers of norm `N` with `|im| < re`. -/
private def ftnGaussNormRegion (N : ℕ) : Set GaussianInt :=
  { z | |z.im| < z.re ∧ z.norm = (N : ℤ) }

/-- `h(N) = ∑_{d | N} χ₄(d)`, valued in `ℤ`. -/
private noncomputable def ftnChiFourDivisorSum (N : ℕ) : ℤ :=
  ∑ d ∈ N.divisors, ZMod.χ₄ (d : ZMod 4)

/-- `Quad(N)`: quadruples `(a, x, b, y)` of positive naturals with
`a * x + b * y = N`, `x` odd, `y` odd. -/
private def ftnOddQuad (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)))).filter
    (fun q => q.1 * q.2.1 + q.2.2.1 * q.2.2.2 = N ∧ Odd q.2.1 ∧ Odd q.2.2.2)

/-- `V(N)`: quadruples `(c, X, b, Y)` of positive naturals with
`c * X + b * Y = N`, `X` odd, `Y` even. -/
private def ftnLiouvilleTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N) ×ˢ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)))).filter
    (fun q => q.1 * q.2.1 + q.2.2.1 * q.2.2.2 = N ∧ Odd q.2.1 ∧ Even q.2.2.2)

private lemma ftn_mem_oddQuad (N a x b y : ℕ) :
    ((a, (x, (b, y))) : ℕ × ℕ × ℕ × ℕ) ∈ ftnOddQuad N ↔
      1 ≤ a ∧ 1 ≤ x ∧ 1 ≤ b ∧ 1 ≤ y ∧
        a * x + b * y = N ∧ Odd x ∧ Odd y := by
  rw [ftnOddQuad]
  constructor
  · intro h
    obtain ⟨hmem, hpred⟩ := Finset.mem_filter.mp h
    obtain ⟨haM, hrest1⟩ := Finset.mem_product.mp hmem
    obtain ⟨hxM, hrest2⟩ := Finset.mem_product.mp hrest1
    obtain ⟨hbM, hyM⟩ := Finset.mem_product.mp hrest2
    obtain ⟨ha1, -⟩ := Finset.mem_Icc.mp haM
    obtain ⟨hx1, -⟩ := Finset.mem_Icc.mp hxM
    obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp hbM
    obtain ⟨hy1, -⟩ := Finset.mem_Icc.mp hyM
    obtain ⟨heq, hxo, hyo⟩ := hpred
    exact ⟨ha1, hx1, hb1, hy1, heq, hxo, hyo⟩
  · rintro ⟨ha1, hx1, hb1, hy1, heq, hxo, hyo⟩
    have haN : a ≤ N := by
      have h1 : a * 1 ≤ a * x := mul_le_mul_right (by omega) a
      rw [mul_one] at h1
      have h2 : a * x ≤ a * x + b * y := Nat.le_add_right _ _
      omega
    have hbN : b ≤ N := by
      have h1 : b * 1 ≤ b * y := mul_le_mul_right (by omega) b
      rw [mul_one] at h1
      have h2 : b * y ≤ a * x + b * y := Nat.le_add_left _ _
      omega
    have hxN : x ≤ N := by
      have h1 : 1 * x ≤ a * x := mul_le_mul_left (by omega) x
      rw [one_mul] at h1
      have h2 : a * x ≤ a * x + b * y := Nat.le_add_right _ _
      omega
    have hyN : y ≤ N := by
      have h1 : 1 * y ≤ b * y := mul_le_mul_left (by omega) y
      rw [one_mul] at h1
      have h2 : b * y ≤ a * x + b * y := Nat.le_add_left _ _
      omega
    rw [Finset.mem_filter]
    refine ⟨?_, ⟨heq, hxo, hyo⟩⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, haN⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hx1, hxN⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb1, hbN⟩,
      Finset.mem_Icc.mpr ⟨hy1, hyN⟩⟩⟩⟩

private lemma ftn_mem_liouvilleTriples (N c X b Y : ℕ) :
    ((c, (X, (b, Y))) : ℕ × ℕ × ℕ × ℕ) ∈ ftnLiouvilleTriples N ↔
      1 ≤ c ∧ 1 ≤ X ∧ 1 ≤ b ∧ 1 ≤ Y ∧
        c * X + b * Y = N ∧ Odd X ∧ Even Y := by
  rw [ftnLiouvilleTriples]
  constructor
  · intro h
    obtain ⟨hmem, hpred⟩ := Finset.mem_filter.mp h
    obtain ⟨hcM, hrest1⟩ := Finset.mem_product.mp hmem
    obtain ⟨hXM, hrest2⟩ := Finset.mem_product.mp hrest1
    obtain ⟨hbM, hYM⟩ := Finset.mem_product.mp hrest2
    obtain ⟨hc1, -⟩ := Finset.mem_Icc.mp hcM
    obtain ⟨hX1, -⟩ := Finset.mem_Icc.mp hXM
    obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp hbM
    obtain ⟨hY1, -⟩ := Finset.mem_Icc.mp hYM
    obtain ⟨heq, hXo, hYe⟩ := hpred
    exact ⟨hc1, hX1, hb1, hY1, heq, hXo, hYe⟩
  · rintro ⟨hc1, hX1, hb1, hY1, heq, hXo, hYe⟩
    have hcN : c ≤ N := by
      have h1 : c * 1 ≤ c * X := mul_le_mul_right (by omega) c
      rw [mul_one] at h1
      have h2 : c * X ≤ c * X + b * Y := Nat.le_add_right _ _
      omega
    have hbN : b ≤ N := by
      have h1 : b * 1 ≤ b * Y := mul_le_mul_right (by omega) b
      rw [mul_one] at h1
      have h2 : b * Y ≤ c * X + b * Y := Nat.le_add_left _ _
      omega
    have hXN : X ≤ N := by
      have h1 : 1 * X ≤ c * X := mul_le_mul_left (by omega) X
      rw [one_mul] at h1
      have h2 : c * X ≤ c * X + b * Y := Nat.le_add_right _ _
      omega
    have hYN : Y ≤ N := by
      have h1 : 1 * Y ≤ b * Y := mul_le_mul_left (by omega) Y
      rw [one_mul] at h1
      have h2 : b * Y ≤ c * X + b * Y := Nat.le_add_left _ _
      omega
    rw [Finset.mem_filter]
    refine ⟨?_, ⟨heq, hXo, hYe⟩⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hc1, hcN⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hX1, hXN⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb1, hbN⟩,
      Finset.mem_Icc.mpr ⟨hY1, hYN⟩⟩⟩⟩

private lemma ftn_wanted_card_eq_quadruple_card (j : ℕ) :
    Fintype.card { t : Fin 4 → Fin (j + 1) //
      (∑ i, ((t i).val * ((t i).val + 1) / 2)) = j } =
    (((Finset.range (j + 1) ×ˢ Finset.range (j + 1)) ×ˢ
      (Finset.range (j + 1) ×ˢ Finset.range (j + 1))).filter
      (fun q => ftnTri q.1.1 + ftnTri q.1.2 + ftnTri q.2.1 + ftnTri q.2.2 = j)).card := by
  rw [Fintype.card_subtype]
  refine Finset.card_nbij'
    (fun t => (((t 0).val, (t 1).val), ((t 2).val, (t 3).val)))
    (fun q => ![⟨q.1.1 % (j + 1), Nat.mod_lt _ (Nat.zero_lt_succ j)⟩,
      ⟨q.1.2 % (j + 1), Nat.mod_lt _ (Nat.zero_lt_succ j)⟩,
      ⟨q.2.1 % (j + 1), Nat.mod_lt _ (Nat.zero_lt_succ j)⟩,
      ⟨q.2.2 % (j + 1), Nat.mod_lt _ (Nat.zero_lt_succ j)⟩])
    ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht ⊢
    obtain ⟨-, hsum⟩ := ht
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_product]
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (t 0).isLt,
        Finset.mem_range.mpr (t 1).isLt⟩,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr (t 2).isLt,
        Finset.mem_range.mpr (t 3).isLt⟩⟩
    · rw [Fin.sum_univ_four] at hsum
      simpa only [ftnTri] using hsum
  · intro q hq
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := q
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    obtain ⟨hmem, hsum⟩ := hq
    have ha : a < j + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hmem).1).1
    have hb : b < j + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hmem).1).2
    have hc : c < j + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).1
    have hd : d < j + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Fin.sum_univ_four]
    change (a % (j + 1)) * ((a % (j + 1)) + 1) / 2 + (b % (j + 1)) * ((b % (j + 1)) + 1) / 2 +
        (c % (j + 1)) * ((c % (j + 1)) + 1) / 2 + (d % (j + 1)) * ((d % (j + 1)) + 1) / 2 = j
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt hd]
    simpa only [ftnTri] using hsum
  · intro t _
    have e0 : (⟨(t 0).val % (j + 1), Nat.mod_lt _ (Nat.zero_lt_succ j)⟩ : Fin (j + 1)) =
        t 0 := Fin.ext (Nat.mod_eq_of_lt (t 0).isLt)
    have e1 : (⟨(t 1).val % (j + 1), Nat.mod_lt _ (Nat.zero_lt_succ j)⟩ : Fin (j + 1)) =
        t 1 := Fin.ext (Nat.mod_eq_of_lt (t 1).isLt)
    have e2 : (⟨(t 2).val % (j + 1), Nat.mod_lt _ (Nat.zero_lt_succ j)⟩ : Fin (j + 1)) =
        t 2 := Fin.ext (Nat.mod_eq_of_lt (t 2).isLt)
    have e3 : (⟨(t 3).val % (j + 1), Nat.mod_lt _ (Nat.zero_lt_succ j)⟩ : Fin (j + 1)) =
        t 3 := Fin.ext (Nat.mod_eq_of_lt (t 3).isLt)
    simp only [e0, e1, e2, e3]
    funext i
    fin_cases i <;> rfl
  · intro q hq
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := q
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    obtain ⟨hmem, -⟩ := hq
    have ha : a < j + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hmem).1).1
    have hb : b < j + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hmem).1).2
    have hc : c < j + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).1
    have hd : d < j + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).2
    change (((a % (j + 1), b % (j + 1)), (c % (j + 1), d % (j + 1)))) = (((a, b), (c, d)))
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt hd]

private lemma ftn_le_tri (u : ℕ) : u ≤ ftnTri u := by
  rcases eq_or_ne u 0 with rfl | hne
  · exact Nat.zero_le _
  · have hpos : 0 < u := Nat.pos_of_ne_zero hne
    have heven : Even (u * (u + 1)) := Nat.even_mul_succ_self u
    have h2 : 2 * (u * (u + 1) / 2) = u * (u + 1) := Nat.two_mul_div_two_of_even heven
    have hle : 2 * u ≤ u * (u + 1) := by
      calc 2 * u = u * 2 := by ring
      _ ≤ u * (u + 1) := mul_le_mul_right (by omega) u
    simp only [ftnTri]
    omega

private lemma ftn_pair_filter_eq (a M : ℕ) (h : a ≤ M) :
    ((Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
      (fun p => ftnTri p.1 + ftnTri p.2 = a)) =
    ((Finset.range (a + 1) ×ˢ Finset.range (a + 1)).filter
      (fun p => ftnTri p.1 + ftnTri p.2 = a)) := by
  ext ⟨u, v⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨-, -⟩, hsum⟩
    have h1 : u ≤ a := by
      have htri := ftn_le_tri u
      omega
    have h2 : v ≤ a := by
      have htri := ftn_le_tri v
      omega
    refine ⟨⟨by omega, by omega⟩, hsum⟩
  · rintro ⟨⟨hu, hv⟩, hsum⟩
    exact ⟨⟨by omega, by omega⟩, hsum⟩

private lemma ftn_fiber_eq_product (j a : ℕ) (haj : a ≤ j) :
    ((((Finset.range (j + 1) ×ˢ Finset.range (j + 1)) ×ˢ
      (Finset.range (j + 1) ×ˢ Finset.range (j + 1))).filter
      (fun q => ftnTri q.1.1 + ftnTri q.1.2 + ftnTri q.2.1 + ftnTri q.2.2 = j)).filter
      (fun q => ftnTri q.1.1 + ftnTri q.1.2 = a)) =
    (((Finset.range (j + 1) ×ˢ Finset.range (j + 1)).filter
      (fun p => ftnTri p.1 + ftnTri p.2 = a)) ×ˢ
     ((Finset.range (j + 1) ×ˢ Finset.range (j + 1)).filter
      (fun p => ftnTri p.1 + ftnTri p.2 = j - a))) := by
  rw [Finset.filter_filter]
  rw [← Finset.filter_product _ _]
  apply Finset.filter_congr
  intro x _
  obtain ⟨⟨u, v⟩, ⟨w, z⟩⟩ := x
  constructor
  · rintro ⟨hfull, hfib⟩
    have hfull' : ftnTri u + ftnTri v + ftnTri w + ftnTri z = j := hfull
    have hfib' : ftnTri u + ftnTri v = a := hfib
    refine ⟨hfib', ?_⟩
    change ftnTri w + ftnTri z = j - a
    omega
  · rintro ⟨hfib, h34⟩
    have hfib' : ftnTri u + ftnTri v = a := hfib
    have h34' : ftnTri w + ftnTri z = j - a := h34
    refine ⟨?_, hfib'⟩
    change ftnTri u + ftnTri v + ftnTri w + ftnTri z = j
    omega

private lemma ftn_fiber_card (j a : ℕ) (ha : a ∈ Finset.range (j + 1)) :
    ((((Finset.range (j + 1) ×ˢ Finset.range (j + 1)) ×ˢ
      (Finset.range (j + 1) ×ˢ Finset.range (j + 1))).filter
      (fun q => ftnTri q.1.1 + ftnTri q.1.2 + ftnTri q.2.1 + ftnTri q.2.2 = j)).filter
      (fun q => ftnTri q.1.1 + ftnTri q.1.2 = a)).card =
    ftnTriPairCount a * ftnTriPairCount (j - a) := by
  have haj : a ≤ j := by
    have hmem := Finset.mem_range.mp ha
    omega
  rw [ftn_fiber_eq_product j a haj, Finset.card_product]
  simp only [ftn_pair_filter_eq a j haj, ftn_pair_filter_eq (j - a) j (Nat.sub_le j a),
    ftnTriPairCount]

private lemma ftn_quadruple_card_eq_sum_antidiagonal (j : ℕ) :
    (((Finset.range (j + 1) ×ˢ Finset.range (j + 1)) ×ˢ
      (Finset.range (j + 1) ×ˢ Finset.range (j + 1))).filter
      (fun q => ftnTri q.1.1 + ftnTri q.1.2 + ftnTri q.2.1 + ftnTri q.2.2 = j)).card =
    ∑ p ∈ Finset.antidiagonal j, ftnTriPairCount p.1 * ftnTriPairCount p.2 := by
  have Hmap : (↑(((Finset.range (j + 1) ×ˢ Finset.range (j + 1)) ×ˢ
      (Finset.range (j + 1) ×ˢ Finset.range (j + 1))).filter
      (fun q => ftnTri q.1.1 + ftnTri q.1.2 + ftnTri q.2.1 + ftnTri q.2.2 = j) :
      Finset ((ℕ × ℕ) × (ℕ × ℕ))) : Set ((ℕ × ℕ) × (ℕ × ℕ))).MapsTo
      (fun q : (ℕ × ℕ) × (ℕ × ℕ) => ftnTri q.1.1 + ftnTri q.1.2)
      (Finset.range (j + 1)) := by
    intro q hq
    have hsum : ftnTri q.1.1 + ftnTri q.1.2 + ftnTri q.2.1 + ftnTri q.2.2 = j :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    have hle : ftnTri q.1.1 + ftnTri q.1.2 ≤ j := by omega
    rw [Finset.mem_coe, Finset.mem_range]
    change ftnTri q.1.1 + ftnTri q.1.2 < j + 1
    omega
  rw [Finset.card_eq_sum_card_fiberwise Hmap]
  trans ∑ a ∈ Finset.range (j + 1), ftnTriPairCount a * ftnTriPairCount (j - a)
  · apply Finset.sum_congr rfl
    intro a ha
    exact ftn_fiber_card j a ha
  · exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p : ℕ × ℕ => ftnTriPairCount p.1 * ftnTriPairCount p.2) j).symm

private lemma ftn_norm_pair (x y : ℤ) :
    (⟨x, y⟩ : GaussianInt).norm = x * x + y * y := by
  rw [Zsqrtd.norm_def]
  dsimp only
  ring

private lemma ftn_phi_injective :
    Function.Injective (fun p : ℕ × ℕ =>
      (⟨(p.1 : ℤ) + (p.2 : ℤ) + 1, (p.1 : ℤ) - (p.2 : ℤ)⟩ : GaussianInt)) := by
  intro p q h
  obtain ⟨u, v⟩ := p
  obtain ⟨u', v'⟩ := q
  have hre : (u : ℤ) + (v : ℤ) + 1 = (u' : ℤ) + (v' : ℤ) + 1 :=
    congrArg Zsqrtd.re h
  have him : (u : ℤ) - (v : ℤ) = (u' : ℤ) - (v' : ℤ) := congrArg Zsqrtd.im h
  have hu : u = u' := by
    have hcast : (u : ℤ) = (u' : ℤ) := by omega
    exact_mod_cast hcast
  have hv : v = v' := by
    have hcast : (v : ℤ) = (v' : ℤ) := by omega
    exact_mod_cast hcast
  rw [hu, hv]

private lemma ftn_phi_mem_region (a u v : ℕ) (hT : ftnTri u + ftnTri v = a) :
    (⟨(u : ℤ) + (v : ℤ) + 1, (u : ℤ) - (v : ℤ)⟩ : GaussianInt) ∈
      ftnGaussNormRegion (4 * a + 1) := by
  have e1 : 2 * ftnTri u = u * (u + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self u)
  have e2 : 2 * ftnTri v = v * (v + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self v)
  have key : ((u:ℤ)+(v:ℤ)+1) * ((u:ℤ)+(v:ℤ)+1) + ((u:ℤ)-(v:ℤ)) * ((u:ℤ)-(v:ℤ))
      = 2 * ((u:ℤ) * ((u:ℤ)+1) + (v:ℤ) * ((v:ℤ)+1)) + 1 := by ring
  have e1c : (2:ℤ) * ((ftnTri u : ℕ):ℤ) = (u:ℤ) * ((u:ℤ)+1) := by
    exact_mod_cast e1
  have e2c : (2:ℤ) * ((ftnTri v : ℕ):ℤ) = (v:ℤ) * ((v:ℤ)+1) := by
    exact_mod_cast e2
  have hTc : ((ftnTri u : ℕ):ℤ) + ((ftnTri v : ℕ):ℤ) = ((a : ℕ):ℤ) := by
    exact_mod_cast hT
  have hnorm : (⟨((u:ℤ)+(v:ℤ)+1), ((u:ℤ)-(v:ℤ))⟩ : GaussianInt).norm =
      ((4 * a + 1 : ℕ):ℤ) := by
    have hcast4 : (((4 * a + 1 : ℕ)):ℤ) = 4 * ((a:ℕ):ℤ) + 1 := by
      push_cast
      ring
    rw [ftn_norm_pair, hcast4]
    linear_combination key - 2 * e1c - 2 * e2c + 4 * hTc
  have habs : |(⟨((u:ℤ)+(v:ℤ)+1), ((u:ℤ)-(v:ℤ))⟩ : GaussianInt).im| <
      (⟨((u:ℤ)+(v:ℤ)+1), ((u:ℤ)-(v:ℤ))⟩ : GaussianInt).re := by
    dsimp only
    rw [abs_lt]
    constructor <;> omega
  exact ⟨habs, hnorm⟩

private lemma ftn_triPairCount_eq_ncard_region (a : ℕ) :
    ftnTriPairCount a = (ftnGaussNormRegion (4 * a + 1)).ncard := by
  have himg : ftnGaussNormRegion (4 * a + 1) =
      ((((Finset.range (a + 1) ×ˢ Finset.range (a + 1)).filter
        (fun p => ftnTri p.1 + ftnTri p.2 = a)) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).image
        (fun p => (⟨(p.1 : ℤ) + (p.2 : ℤ) + 1, (p.1 : ℤ) - (p.2 : ℤ)⟩ :
          GaussianInt)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hlt, hnorm⟩ := hz
      rw [abs_lt] at hlt
      obtain ⟨hlt1, hlt2⟩ := hlt
      set P := z.re with hPdef
      set Q := z.im with hQdef
      have hnormPQ : P * P + Q * Q = ((4 * a + 1 : ℕ) : ℤ) := by
        have h1 : (⟨P, Q⟩ : GaussianInt).norm = P * P + Q * Q :=
          ftn_norm_pair P Q
        have hzpair : (⟨P, Q⟩ : GaussianInt) = z := Zsqrtd.ext_iff.mpr ⟨rfl, rfl⟩
        rw [hzpair] at h1
        rw [h1] at hnorm
        exact hnorm
      have hP2 : P % 2 = 0 ∨ P % 2 = 1 := by omega
      have hQ2 : Q % 2 = 0 ∨ Q % 2 = 1 := by omega
      have hnorm2 : (P * P + Q * Q) % 2 = 1 := by
        rw [hnormPQ]
        omega
      have hPQmod : (P + Q) % 2 = 1 := by
        rcases hP2 with hP|hP <;> rcases hQ2 with hQ|hQ
        · exfalso
          have eP : P * P % 2 = 0 := by rw [Int.mul_emod, hP]; decide
          have eQ : Q * Q % 2 = 0 := by rw [Int.mul_emod, hQ]; decide
          have hz : (P * P + Q * Q) % 2 = 0 := by rw [Int.add_emod, eP, eQ]; decide
          omega
        · rw [Int.add_emod, hP, hQ]; decide
        · rw [Int.add_emod, hP, hQ]; decide
        · exfalso
          have eP : P * P % 2 = 1 := by rw [Int.mul_emod, hP]; decide
          have eQ : Q * Q % 2 = 1 := by rw [Int.mul_emod, hQ]; decide
          have hz : (P * P + Q * Q) % 2 = 0 := by rw [Int.add_emod, eP, eQ]; decide
          omega
      have hsubmod : (P - Q) % 2 = (P + Q) % 2 := by omega
      have hUmod : (P + Q - 1) % 2 = 0 := by omega
      have hVmod : (P - Q - 1) % 2 = 0 := by omega
      have hPQ1 : 1 ≤ P + Q := by omega
      have hPQ1' : 1 ≤ P - Q := by omega
      set U := ((P + Q - 1) / 2).toNat with hUdef
      set V := ((P - Q - 1) / 2).toNat with hVdef
      have hU0 : 0 ≤ (P + Q - 1) / 2 :=
        Int.ediv_nonneg (by omega) (by norm_num)
      have hV0 : 0 ≤ (P - Q - 1) / 2 :=
        Int.ediv_nonneg (by omega) (by norm_num)
      have hUZ : ((U : ℕ) : ℤ) = (P + Q - 1) / 2 := Int.toNat_of_nonneg hU0
      have hVZ : ((V : ℕ) : ℤ) = (P - Q - 1) / 2 := Int.toNat_of_nonneg hV0
      have hU2 : 2 * ((U : ℕ):ℤ) = P + Q - 1 := by omega
      have hV2 : 2 * ((V : ℕ):ℤ) = P - Q - 1 := by omega
      have hPre : P = ((U:ℕ):ℤ) + ((V:ℕ):ℤ) + 1 := by omega
      have hQe : Q = ((U:ℕ):ℤ) - ((V:ℕ):ℤ) := by omega
      have hexpand : P * P + Q * Q
          = 2 * (((U:ℤ) * ((U:ℤ)+1) + (V:ℤ) * ((V:ℤ)+1))) + 1 := by
        have key : ((U:ℤ)+(V:ℤ)+1) * ((U:ℤ)+(V:ℤ)+1) +
            ((U:ℤ)-(V:ℤ)) * ((U:ℤ)-(V:ℤ))
            = 2 * ((U:ℤ)*((U:ℤ)+1) + (V:ℤ)*((V:ℤ)+1)) + 1 := by ring
        rw [hPre, hQe, key]
      have eU : 2 * ftnTri U = U * (U + 1) :=
        Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self U)
      have eV : 2 * ftnTri V = V * (V + 1) :=
        Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self V)
      have hsum : ftnTri U + ftnTri V = a := by
        have eUc : (2:ℤ) * ((ftnTri U : ℕ):ℤ) = (U:ℤ) * ((U:ℤ)+1) := by
          exact_mod_cast eU
        have eVc : (2:ℤ) * ((ftnTri V : ℕ):ℤ) = (V:ℤ) * ((V:ℤ)+1) := by
          exact_mod_cast eV
        have hTc : (((4 * a + 1 : ℕ)):ℤ) = 4 * ((a:ℕ):ℤ) + 1 := by
          push_cast
          ring
        rw [hTc] at hnormPQ
        omega
      have hUa : U ≤ a := by
        have hle := ftn_le_tri U
        omega
      have hVa : V ≤ a := by
        have hle := ftn_le_tri V
        omega
      rw [Set.mem_image]
      refine ⟨(U, V), ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, hsum⟩
      · exact Zsqrtd.ext_iff.mpr ⟨hPre.symm, hQe.symm⟩
    · rintro ⟨⟨u, v⟩, hmem, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, Finset.mem_range] at hmem
      obtain ⟨⟨hu, hv⟩, hT⟩ := hmem
      exact ftn_phi_mem_region a u v hT
  rw [himg, Set.ncard_image_of_injective _ ftn_phi_injective,
    Set.ncard_coe_finset]
  rfl

private lemma ftn_le_of_norm (z : GaussianInt) (N : ℕ)
    (hnorm : z.re * z.re + z.im * z.im = ((N : ℕ) : ℤ)) :
    -(N:ℤ) ≤ z.re ∧ z.re ≤ (N:ℤ) ∧ -(N:ℤ) ≤ z.im ∧ z.im ≤ (N:ℤ) := by
  have h1 : z.re * z.re ≤ ((N:ℕ):ℤ) := by
    have him2 : 0 ≤ z.im * z.im := mul_self_nonneg _
    omega
  have h2 : z.im * z.im ≤ ((N:ℕ):ℤ) := by
    have hre2 : 0 ≤ z.re * z.re := mul_self_nonneg _
    omega
  have hNN : N ≤ N * N := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · exact Nat.zero_le _
    · calc N = N * 1 := by ring
        _ ≤ N * N := mul_le_mul_of_nonneg_left hpos (Nat.zero_le N)
  have hsq_re : z.re ^ 2 ≤ (((N:ℕ):ℤ)) ^ 2 := by
    rw [pow_two, pow_two]
    exact le_trans h1 (by exact_mod_cast hNN)
  have hsq_im : z.im ^ 2 ≤ (((N:ℕ):ℤ)) ^ 2 := by
    rw [pow_two, pow_two]
    exact le_trans h2 (by exact_mod_cast hNN)
  obtain ⟨hr1, hr2⟩ := abs_le_of_sq_le_sq' hsq_re (Nat.cast_nonneg N)
  obtain ⟨hi1, hi2⟩ := abs_le_of_sq_le_sq' hsq_im (Nat.cast_nonneg N)
  exact ⟨hr1, hr2, hi1, hi2⟩

private lemma ftn_norm_eq_of_mem (N : ℕ) (z : GaussianInt)
    (hzm : z ∈ ftnGaussNormSet N) :
    z.re * z.re + z.im * z.im = ((N : ℕ) : ℤ) := by
  have h2 : z.norm = ((N:ℕ):ℤ) := hzm
  have h1 := ftn_norm_pair z.re z.im
  have hzpair : (⟨z.re, z.im⟩ : GaussianInt) = z := Zsqrtd.ext_iff.mpr ⟨rfl, rfl⟩
  rw [hzpair] at h1
  rw [h1] at h2
  exact h2

private lemma ftn_gaussNormSet_finite (N : ℕ) : (ftnGaussNormSet N).Finite := by
  have hinj : Set.InjOn (fun z : GaussianInt => (z.re, z.im))
      (ftnGaussNormSet N) := by
    intro a _ b _ hab
    exact Zsqrtd.ext_iff.mpr
      ⟨congrArg Prod.fst hab, congrArg Prod.snd hab⟩
  have hbd : ∀ z ∈ ftnGaussNormSet N,
      -(N:ℤ) ≤ z.re ∧ z.re ≤ (N:ℤ) ∧ -(N:ℤ) ≤ z.im ∧ z.im ≤ (N:ℤ) := by
    intro z hzm
    exact ftn_le_of_norm z N (ftn_norm_eq_of_mem N z hzm)
  have hre : (fun z : GaussianInt => z.re) '' ftnGaussNormSet N ⊆
      Set.Icc (-((N:ℕ):ℤ)) ((N:ℕ):ℤ) := by
    rintro x hx
    obtain ⟨z, hzm, hzx⟩ := hx
    rw [← hzx]
    dsimp only
    rw [Set.mem_Icc]
    obtain ⟨hr1, hr2, -, -⟩ := hbd z hzm
    exact ⟨hr1, hr2⟩
  have him : (fun z : GaussianInt => z.im) '' ftnGaussNormSet N ⊆
      Set.Icc (-((N:ℕ):ℤ)) ((N:ℕ):ℤ) := by
    rintro x hx
    obtain ⟨z, hzm, hzx⟩ := hx
    rw [← hzx]
    dsimp only
    rw [Set.mem_Icc]
    obtain ⟨-, -, hi1, hi2⟩ := hbd z hzm
    exact ⟨hi1, hi2⟩
  have hpair : (fun z : GaussianInt => (z.re, z.im)) '' ftnGaussNormSet N ⊆
      ((fun z : GaussianInt => z.re) '' ftnGaussNormSet N) ×ˢ
        ((fun z : GaussianInt => z.im) '' ftnGaussNormSet N) := by
    rintro x hx
    obtain ⟨z, hzm, hzx⟩ := hx
    rw [← hzx]
    dsimp only
    exact ⟨⟨z, hzm, rfl⟩, ⟨z, hzm, rfl⟩⟩
  have hfin : ((fun z : GaussianInt => z.re) '' ftnGaussNormSet N) ×ˢ
      ((fun z : GaussianInt => z.im) '' ftnGaussNormSet N) |>.Finite :=
    ((Set.finite_Icc _ _).subset hre).prod ((Set.finite_Icc _ _).subset him)
  exact Set.Finite.of_finite_image (hfin.subset hpair) hinj

private lemma ftn_rot_re (w : GaussianInt) :
    ((⟨0, 1⟩ : GaussianInt) * w).re = -w.im := by
  rw [Zsqrtd.re_mul]
  dsimp only
  ring

private lemma ftn_rot_im (w : GaussianInt) :
    ((⟨0, 1⟩ : GaussianInt) * w).im = w.re := by
  rw [Zsqrtd.im_mul]
  dsimp only
  ring

private lemma ftn_rot_norm (w : GaussianInt) :
    ((⟨0, 1⟩ : GaussianInt) * w).norm = w.norm := by
  have hu : (⟨0, 1⟩ : GaussianInt).norm = 1 := by
    rw [ftn_norm_pair]
    norm_num
  calc ((⟨0, 1⟩ : GaussianInt) * w).norm
      = (⟨0, 1⟩ : GaussianInt).norm * w.norm := Zsqrtd.norm_mul _ _
    _ = w.norm := by rw [hu, one_mul]

private lemma ftn_rot_ne_zero : (⟨0, 1⟩ : GaussianInt) ≠ 0 := by decide

private def ftnGaussNormRegion1 (N : ℕ) : Set GaussianInt :=
  { z | |z.re| < z.im ∧ z.norm = (N : ℤ) }

private def ftnGaussNormRegion2 (N : ℕ) : Set GaussianInt :=
  { z | |z.im| < -z.re ∧ z.norm = (N : ℤ) }

private def ftnGaussNormRegion3 (N : ℕ) : Set GaussianInt :=
  { z | |z.re| < -z.im ∧ z.norm = (N : ℤ) }

private lemma ftn_odd_norm_one_region (z : GaussianInt) (hN : Odd z.norm) :
    |z.im| < z.re ∨ |z.re| < z.im ∨ |z.im| < -z.re ∨ |z.re| < -z.im := by
  by_contra h
  push Not at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hab : |z.re| = |z.im| := by
    apply le_antisymm
    · rw [abs_le]
      exact ⟨by linarith, h0⟩
    · rw [abs_le]
      exact ⟨by linarith, h1⟩
  have hsq : z.re * z.re = z.im * z.im := by
    have h2 : |z.re| ^ 2 = |z.im| ^ 2 := congrArg (· ^ 2) hab
    rw [sq_abs, sq_abs, pow_two, pow_two] at h2
    exact h2
  have hnorm2 : z.re * z.re + z.im * z.im = z.norm :=
    (ftn_norm_pair z.re z.im).symm
  obtain ⟨k, hk⟩ := hN
  omega

private lemma ftn_region1_eq_image (N : ℕ) :
    ftnGaussNormRegion1 N =
      (fun w : GaussianInt => (⟨0, 1⟩ : GaussianInt) * w) ''
        ftnGaussNormRegion N := by
  ext z
  constructor
  · rintro ⟨hC, hn⟩
    refine ⟨⟨z.im, -z.re⟩, ?_, ?_⟩
    · constructor
      · rwa [abs_neg]
      · have h1 := ftn_norm_pair z.im (-z.re)
        have h3 : z.re * z.re + z.im * z.im = ((N:ℕ):ℤ) := by
          have h4 := ftn_norm_pair z.re z.im
          have h2 : z.norm = ((N:ℕ):ℤ) := hn
          have hzpair : (⟨z.re, z.im⟩ : GaussianInt) = z :=
            Zsqrtd.ext_iff.mpr ⟨rfl, rfl⟩
          rw [hzpair] at h4
          rw [h4] at h2
          exact h2
        rw [h1]
        linear_combination h3
    · have e1 : ((⟨0, 1⟩ : GaussianInt) * ⟨z.im, -z.re⟩).re = z.re := by
        simp
      have e2 : ((⟨0, 1⟩ : GaussianInt) * ⟨z.im, -z.re⟩).im = z.im := by
        simp
      exact Zsqrtd.ext_iff.mpr ⟨e1, e2⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hC, hn⟩ := hw
    refine ⟨?_, ?_⟩ <;> dsimp only
    · rw [ftn_rot_re, ftn_rot_im, abs_neg]
      exact hC
    · rw [ftn_rot_norm]
      exact hn

private lemma ftn_region2_eq_image (N : ℕ) :
    ftnGaussNormRegion2 N =
      (fun w : GaussianInt => (⟨0, 1⟩ : GaussianInt) * w) ''
        ftnGaussNormRegion1 N := by
  ext z
  constructor
  · rintro ⟨hC, hn⟩
    refine ⟨⟨z.im, -z.re⟩, ?_, ?_⟩
    · constructor
      · exact hC
      · have h1 := ftn_norm_pair z.im (-z.re)
        have h3 : z.re * z.re + z.im * z.im = ((N:ℕ):ℤ) := by
          have h4 := ftn_norm_pair z.re z.im
          have h2 : z.norm = ((N:ℕ):ℤ) := hn
          have hzpair : (⟨z.re, z.im⟩ : GaussianInt) = z :=
            Zsqrtd.ext_iff.mpr ⟨rfl, rfl⟩
          rw [hzpair] at h4
          rw [h4] at h2
          exact h2
        rw [h1]
        linear_combination h3
    · have e1 : ((⟨0, 1⟩ : GaussianInt) * ⟨z.im, -z.re⟩).re = z.re := by
        simp
      have e2 : ((⟨0, 1⟩ : GaussianInt) * ⟨z.im, -z.re⟩).im = z.im := by
        simp
      exact Zsqrtd.ext_iff.mpr ⟨e1, e2⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hC, hn⟩ := hw
    refine ⟨?_, ?_⟩ <;> dsimp only
    · rw [ftn_rot_re, ftn_rot_im, neg_neg]
      exact hC
    · rw [ftn_rot_norm]
      exact hn

private lemma ftn_region3_eq_image (N : ℕ) :
    ftnGaussNormRegion3 N =
      (fun w : GaussianInt => (⟨0, 1⟩ : GaussianInt) * w) ''
        ftnGaussNormRegion2 N := by
  ext z
  constructor
  · rintro ⟨hC, hn⟩
    refine ⟨⟨z.im, -z.re⟩, ?_, ?_⟩
    · constructor
      · rwa [abs_neg]
      · have h1 := ftn_norm_pair z.im (-z.re)
        have h3 : z.re * z.re + z.im * z.im = ((N:ℕ):ℤ) := by
          have h4 := ftn_norm_pair z.re z.im
          have h2 : z.norm = ((N:ℕ):ℤ) := hn
          have hzpair : (⟨z.re, z.im⟩ : GaussianInt) = z :=
            Zsqrtd.ext_iff.mpr ⟨rfl, rfl⟩
          rw [hzpair] at h4
          rw [h4] at h2
          exact h2
        rw [h1]
        linear_combination h3
    · have e1 : ((⟨0, 1⟩ : GaussianInt) * ⟨z.im, -z.re⟩).re = z.re := by
        simp
      have e2 : ((⟨0, 1⟩ : GaussianInt) * ⟨z.im, -z.re⟩).im = z.im := by
        simp
      exact Zsqrtd.ext_iff.mpr ⟨e1, e2⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hC, hn⟩ := hw
    refine ⟨?_, ?_⟩ <;> dsimp only
    · rw [ftn_rot_re, ftn_rot_im, abs_neg]
      exact hC
    · rw [ftn_rot_norm]
      exact hn

private lemma ftn_region_disjoint (N : ℕ) :
    Disjoint (ftnGaussNormRegion N) (ftnGaussNormRegion1 N) ∧
    Disjoint (ftnGaussNormRegion N) (ftnGaussNormRegion2 N) ∧
    Disjoint (ftnGaussNormRegion N) (ftnGaussNormRegion3 N) ∧
    Disjoint (ftnGaussNormRegion1 N) (ftnGaussNormRegion2 N) ∧
    Disjoint (ftnGaussNormRegion1 N) (ftnGaussNormRegion3 N) ∧
    Disjoint (ftnGaussNormRegion2 N) (ftnGaussNormRegion3 N) := by
  have d01 : Disjoint (ftnGaussNormRegion N) (ftnGaussNormRegion1 N) := by
    rw [Set.disjoint_left]
    intro z h0 h1
    obtain ⟨hC0, -⟩ := h0
    obtain ⟨hC1, -⟩ := h1
    rw [abs_lt] at hC0 hC1
    omega
  have d02 : Disjoint (ftnGaussNormRegion N) (ftnGaussNormRegion2 N) := by
    rw [Set.disjoint_left]
    intro z h0 h1
    obtain ⟨hC0, -⟩ := h0
    obtain ⟨hC1, -⟩ := h1
    rw [abs_lt] at hC0 hC1
    omega
  have d03 : Disjoint (ftnGaussNormRegion N) (ftnGaussNormRegion3 N) := by
    rw [Set.disjoint_left]
    intro z h0 h1
    obtain ⟨hC0, -⟩ := h0
    obtain ⟨hC1, -⟩ := h1
    rw [abs_lt] at hC0 hC1
    omega
  have d12 : Disjoint (ftnGaussNormRegion1 N) (ftnGaussNormRegion2 N) := by
    rw [Set.disjoint_left]
    intro z h0 h1
    obtain ⟨hC0, -⟩ := h0
    obtain ⟨hC1, -⟩ := h1
    rw [abs_lt] at hC0 hC1
    omega
  have d13 : Disjoint (ftnGaussNormRegion1 N) (ftnGaussNormRegion3 N) := by
    rw [Set.disjoint_left]
    intro z h0 h1
    obtain ⟨hC0, -⟩ := h0
    obtain ⟨hC1, -⟩ := h1
    rw [abs_lt] at hC0 hC1
    omega
  have d23 : Disjoint (ftnGaussNormRegion2 N) (ftnGaussNormRegion3 N) := by
    rw [Set.disjoint_left]
    intro z h0 h1
    obtain ⟨hC0, -⟩ := h0
    obtain ⟨hC1, -⟩ := h1
    rw [abs_lt] at hC0 hC1
    omega
  exact ⟨d01, d02, d03, d12, d13, d23⟩

private lemma ftn_gaussNormSet_eq_union (N : ℕ) (hN : Odd N) :
    ftnGaussNormSet N = ftnGaussNormRegion N ∪ ftnGaussNormRegion1 N ∪
      ftnGaussNormRegion2 N ∪ ftnGaussNormRegion3 N := by
  have hoddN : Odd (((N : ℕ)) : ℤ) := hN.natCast
  ext z
  constructor
  · intro hz
    have hnorm : z.norm = (((N : ℕ)) : ℤ) := hz
    have hoddZ : Odd z.norm := hnorm.symm ▸ hoddN
    rcases ftn_odd_norm_one_region z hoddZ with h0 | h1 | h2 | h3
    · exact Or.inl (Or.inl (Or.inl ⟨h0, hnorm⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨h1, hnorm⟩))
    · exact Or.inl (Or.inr ⟨h2, hnorm⟩)
    · exact Or.inr ⟨h3, hnorm⟩
  · rintro (((h0 | h1) | h2) | h3)
    · exact h0.2
    · exact h1.2
    · exact h2.2
    · exact h3.2

private lemma ftn_ncard_gaussNormSet_eq_four_mul (N : ℕ) (hN : Odd N) :
    (ftnGaussNormSet N).ncard = 4 * (ftnGaussNormRegion N).ncard := by
  have hunion := ftn_gaussNormSet_eq_union N hN
  have hfinS := ftn_gaussNormSet_finite N
  have sub0 : ftnGaussNormRegion N ⊆ ftnGaussNormSet N := by
    intro z hz
    obtain ⟨-, hn⟩ := hz
    exact hn
  have sub1 : ftnGaussNormRegion1 N ⊆ ftnGaussNormSet N := by
    intro z hz
    obtain ⟨-, hn⟩ := hz
    exact hn
  have sub2 : ftnGaussNormRegion2 N ⊆ ftnGaussNormSet N := by
    intro z hz
    obtain ⟨-, hn⟩ := hz
    exact hn
  have sub3 : ftnGaussNormRegion3 N ⊆ ftnGaussNormSet N := by
    intro z hz
    obtain ⟨-, hn⟩ := hz
    exact hn
  have fin0 : (ftnGaussNormRegion N).Finite := hfinS.subset sub0
  have fin1 : (ftnGaussNormRegion1 N).Finite := hfinS.subset sub1
  have fin2 : (ftnGaussNormRegion2 N).Finite := hfinS.subset sub2
  have fin3 : (ftnGaussNormRegion3 N).Finite := hfinS.subset sub3
  have hinj : Function.Injective
      (fun w : GaussianInt => (⟨0, 1⟩ : GaussianInt) * w) :=
    mul_right_injective₀ ftn_rot_ne_zero
  have n1 : (ftnGaussNormRegion1 N).ncard = (ftnGaussNormRegion N).ncard := by
    rw [ftn_region1_eq_image N, Set.ncard_image_of_injective _ hinj]
  have n2 : (ftnGaussNormRegion2 N).ncard = (ftnGaussNormRegion1 N).ncard := by
    rw [ftn_region2_eq_image N, Set.ncard_image_of_injective _ hinj]
  have n3 : (ftnGaussNormRegion3 N).ncard = (ftnGaussNormRegion2 N).ncard := by
    rw [ftn_region3_eq_image N, Set.ncard_image_of_injective _ hinj]
  obtain ⟨d01, d02, d03, d12, d13, d23⟩ := ftn_region_disjoint N
  have e1 : (ftnGaussNormRegion N ∪ ftnGaussNormRegion1 N).ncard =
      (ftnGaussNormRegion N).ncard + (ftnGaussNormRegion1 N).ncard :=
    Set.ncard_union_eq d01 fin0 fin1
  have dj02 : Disjoint (ftnGaussNormRegion N ∪ ftnGaussNormRegion1 N)
      (ftnGaussNormRegion2 N) := by
    rw [Set.disjoint_left]
    rintro z (h0 | h1) h2
    · exact Set.disjoint_left.mp d02 h0 h2
    · exact Set.disjoint_left.mp d12 h1 h2
  have e2 : ((ftnGaussNormRegion N ∪ ftnGaussNormRegion1 N) ∪
      ftnGaussNormRegion2 N).ncard =
      (ftnGaussNormRegion N ∪ ftnGaussNormRegion1 N).ncard +
        (ftnGaussNormRegion2 N).ncard :=
    Set.ncard_union_eq dj02 (fin0.union fin1) fin2
  have dj03 : Disjoint ((ftnGaussNormRegion N ∪ ftnGaussNormRegion1 N) ∪
      ftnGaussNormRegion2 N) (ftnGaussNormRegion3 N) := by
    rw [Set.disjoint_left]
    rintro z ((h0 | h1) | h2) h3
    · exact Set.disjoint_left.mp d03 h0 h3
    · exact Set.disjoint_left.mp d13 h1 h3
    · exact Set.disjoint_left.mp d23 h2 h3
  have e3 : (((ftnGaussNormRegion N ∪ ftnGaussNormRegion1 N) ∪
      ftnGaussNormRegion2 N) ∪ ftnGaussNormRegion3 N).ncard =
      ((ftnGaussNormRegion N ∪ ftnGaussNormRegion1 N) ∪
        ftnGaussNormRegion2 N).ncard + (ftnGaussNormRegion3 N).ncard :=
    Set.ncard_union_eq dj03 ((fin0.union fin1).union fin2) fin3
  have m2 : (ftnGaussNormRegion2 N).ncard = (ftnGaussNormRegion N).ncard :=
    n2.trans n1
  have m3 : (ftnGaussNormRegion3 N).ncard = (ftnGaussNormRegion N).ncard :=
    n3.trans m2
  rw [hunion, e3, e2, e1, n1, m2, m3]
  ring

private lemma ftn_gauss_norm_mul (p : ℕ) (w : GaussianInt) :
    (((p : ℕ) : GaussianInt) * w).norm = (p : ℤ) ^ 2 * w.norm := by
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_natCast]
  ring

private lemma ftn_gauss_dvd_of_mem_three (p N : ℕ) (hp : Nat.Prime p)
    (hmod : p % 4 = 3) (hdvd : p ∣ N) (z : GaussianInt)
    (hz : z ∈ ftnGaussNormSet N) : ((p : ℕ) : GaussianInt) ∣ z := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hprime : Prime ((p : ℕ) : GaussianInt) :=
    GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p hmod
  have hnorm : z.norm = ((N : ℕ) : ℤ) := hz
  have hmul : ((N : ℕ) : GaussianInt) = z * star z := by
    have e : ((z.norm : ℤ) : GaussianInt) = z * star z :=
      Zsqrtd.norm_eq_mul_conj z
    rw [hnorm] at e
    have c : ((((N : ℕ)) : ℤ) : GaussianInt) = ((N : ℕ) : GaussianInt) := by
      norm_cast
    rwa [c] at e
  have hpdvd : ((p : ℕ) : GaussianInt) ∣ z * star z := by
    rw [← hmul]
    obtain ⟨t, ht⟩ := hdvd
    exact ⟨((t : ℕ) : GaussianInt), by exact_mod_cast ht⟩
  rcases (hprime.dvd_mul).mp hpdvd with h | h
  · exact h
  · obtain ⟨w, hw⟩ := h
    refine ⟨star w, ?_⟩
    have e2 : star (((p : ℕ) : GaussianInt) * w) =
        ((p : ℕ) : GaussianInt) * star w := by
      rw [star_mul, star_natCast, mul_comm (star w) _]
    rw [← e2, ← hw, star_star]

private lemma ftn_ncard_gaussNormSet_of_prime_three (p N : ℕ) (hp : Nat.Prime p)
    (hmod : p % 4 = 3) (hdvd : p ∣ N) :
    (ftnGaussNormSet N).ncard =
      if p ^ 2 ∣ N then (ftnGaussNormSet (N / p ^ 2)).ncard else 0 := by
  have hinj : Function.Injective
      (fun w : GaussianInt => ((p : ℕ) : GaussianInt) * w) :=
    mul_right_injective₀ (by exact_mod_cast hp.ne_zero)
  by_cases h2 : p ^ 2 ∣ N
  · rw [ite_eq_left h2]
    have eN : ((N : ℕ) : ℤ) = (p : ℤ) ^ 2 * (((N / p ^ 2 : ℕ)) : ℤ) := by
      have hNM : p ^ 2 * (N / p ^ 2) = N := by
        rw [mul_comm]
        exact Nat.div_mul_cancel h2
      have hcast : (↑(p ^ 2 * (N / p ^ 2)) : ℤ) = ((N : ℕ) : ℤ) := by
        exact_mod_cast hNM
      have hpow : (((p ^ 2 : ℕ)) : ℤ) = (p : ℤ) ^ 2 := Nat.cast_pow p 2
      rw [Nat.cast_mul, hpow] at hcast
      exact hcast.symm
    have himg : ftnGaussNormSet N =
        (fun w : GaussianInt => ((p : ℕ) : GaussianInt) * w) ''
          ftnGaussNormSet (N / p ^ 2) := by
      ext z
      constructor
      · intro hz
        obtain ⟨w₀, hw₀⟩ := ftn_gauss_dvd_of_mem_three p N hp hmod hdvd z hz
        have hnormz : ((N : ℕ) : ℤ) = (p : ℤ) ^ 2 * w₀.norm := by
          have e := ftn_gauss_norm_mul p w₀
          rw [← hw₀] at e
          have hzN : z.norm = ((N : ℕ) : ℤ) := hz
          rw [hzN] at e
          exact e
        have hcancel : w₀.norm = (((N / p ^ 2 : ℕ)) : ℤ) := by
          have hp2 : (p : ℤ) ^ 2 ≠ 0 := by
            have hne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
            exact pow_ne_zero 2 hne
          have e : (p : ℤ) ^ 2 * w₀.norm =
              (p : ℤ) ^ 2 * (((N / p ^ 2 : ℕ)) : ℤ) := by
            rw [← hnormz, eN]
          exact mul_left_cancel₀ hp2 e
        exact ⟨w₀, hcancel, hw₀.symm⟩
      · rintro ⟨w, hw, rfl⟩
        have hwN : w.norm = (((N / p ^ 2 : ℕ)) : ℤ) := hw
        have e := ftn_gauss_norm_mul p w
        rw [hwN, ← eN] at e
        exact e
    rw [himg, Set.ncard_image_of_injective _ hinj]
  · rw [ite_eq_right h2]
    have hempty : ftnGaussNormSet N = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hz
      obtain ⟨w₀, hw₀⟩ := ftn_gauss_dvd_of_mem_three p N hp hmod hdvd z hz
      have hnormz : ((N : ℕ) : ℤ) = (p : ℤ) ^ 2 * w₀.norm := by
        have e := ftn_gauss_norm_mul p w₀
        rw [← hw₀] at e
        have hzN : z.norm = ((N : ℕ) : ℤ) := hz
        rw [hzN] at e
        exact e
      have hdvdZ : (((p ^ 2 : ℕ)) : ℤ) ∣ ((N : ℕ) : ℤ) := by
        have hcast : (((p ^ 2 : ℕ)) : ℤ) = (p : ℤ) ^ 2 := Nat.cast_pow p 2
        rw [hcast]
        exact ⟨w₀.norm, hnormz⟩
      exact h2 (Int.natCast_dvd_natCast.mp hdvdZ)
    rw [hempty, Set.ncard_empty]

private lemma ftn_gauss_norm_nonneg (z : GaussianInt) : 0 ≤ z.norm := by
  have h1 := ftn_norm_pair z.re z.im
  have hz : (⟨z.re, z.im⟩ : GaussianInt) = z := Zsqrtd.ext_iff.mpr ⟨rfl, rfl⟩
  rw [hz] at h1
  rw [h1]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

private lemma ftn_gauss_norm_dvd {x y : GaussianInt} (h : x ∣ y) :
    x.norm ∣ y.norm := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v.norm, by rw [hv, Zsqrtd.norm_mul]⟩

private lemma ftn_gauss_N_eq (N : ℕ) (z : GaussianInt)
    (hz : z ∈ ftnGaussNormSet N) :
    ((N : ℕ) : GaussianInt) = z * star z := by
  have e : ((z.norm : ℤ) : GaussianInt) = z * star z :=
    Zsqrtd.norm_eq_mul_conj z
  have hnorm : z.norm = ((N : ℕ) : ℤ) := hz
  rw [hnorm] at e
  have c : ((((N : ℕ)) : ℤ) : GaussianInt) = ((N : ℕ) : GaussianInt) := by
    norm_cast
  rwa [c] at e

private lemma ftn_gauss_star_dvd (a b : GaussianInt) (h : a ∣ star b) :
    star a ∣ b := by
  obtain ⟨w, hw⟩ := h
  refine ⟨star w, ?_⟩
  have e : b = star w * star a := by
    have e1 : star (star b) = star (a * w) := congrArg star hw
    rwa [star_star, star_mul] at e1
  rw [mul_comm (star a) (star w)]
  exact e

private lemma ftn_prime_of_norm_prime (z : GaussianInt) (p : ℕ) (hp : Nat.Prime p)
    (hz : z.norm = ((p : ℕ) : ℤ)) : Prime z := by
  rw [← irreducible_iff_prime]
  constructor
  · intro hu
    have h1 : z.norm = 1 :=
      (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) z).mpr hu
    rw [hz] at h1
    exact hp.ne_one (by exact_mod_cast h1)
  · intro x y hxy
    have hnab : x.norm * y.norm = ((p : ℕ) : ℤ) := by
      have e := congrArg Zsqrtd.norm hxy
      rw [Zsqrtd.norm_mul, hz] at e
      exact e.symm
    have ha_nn := ftn_gauss_norm_nonneg x
    have hb_nn := ftn_gauss_norm_nonneg y
    have hAB : x.norm.natAbs * y.norm.natAbs = p := by
      have h := congrArg Int.natAbs hnab
      rwa [Int.natAbs_mul, Int.natAbs_natCast] at h
    have hdvdA : x.norm.natAbs ∣ p := ⟨y.norm.natAbs, hAB.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvdA with hA1 | hAp
    · left
      have h1 : x.norm = 1 := by
        have e : (((x.norm.natAbs : ℕ)) : ℤ) = x.norm :=
          Int.natAbs_of_nonneg ha_nn
        rw [hA1, Nat.cast_one] at e
        exact e.symm
      exact (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) x).mp h1
    · right
      have hB1 : y.norm.natAbs = 1 := by
        rw [hAp] at hAB
        have h2 : p * y.norm.natAbs = p * 1 := by rw [hAB, mul_one]
        exact mul_left_cancel₀ hp.ne_zero h2
      have h1 : y.norm = 1 := by
        have e : (((y.norm.natAbs : ℕ)) : ℤ) = y.norm :=
          Int.natAbs_of_nonneg hb_nn
        rw [hB1, Nat.cast_one] at e
        exact e.symm
      exact (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) y).mp h1

private lemma ftn_int_prime_dvd_of_dvd_four_mul_sq (p : ℕ) (hp : Nat.Prime p)
    (hmod : p % 4 = 1) (c : ℤ) (h : ((p : ℕ) : ℤ) ∣ 4 * c ^ 2) :
    ((p : ℕ) : ℤ) ∣ c := by
  have hprimeZ : Prime (((p : ℕ)) : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases (hprimeZ.dvd_mul).mp h with h4 | hc2
  · exfalso
    have h2 : ((p : ℕ) : ℤ) ∣ 2 := by
      have e4 : (4 : ℤ) = 2 * 2 := by norm_num
      rw [e4] at h4
      rcases (hprimeZ.dvd_mul).mp h4 with h | h <;> exact h
    have h2N : p ∣ 2 := by
      have h1 : ((p : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) := by
        have c2 : (((2 : ℕ)) : ℤ) = 2 := by norm_num
        rw [c2]
        exact h2
      exact Int.natCast_dvd_natCast.mp h1
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2N
    have heq : p = 2 := by
      have h2le := hp.two_le
      omega
    rw [heq] at hmod
    norm_num at hmod
  · rw [pow_two] at hc2
    rcases (hprimeZ.dvd_mul).mp hc2 with h | h <;> exact h

private lemma ftn_split_prime_not_dvd (p a b : ℕ) (hp : Nat.Prime p)
    (hmod : p % 4 = 1) (hab : a ^ 2 + b ^ 2 = p) :
    ¬ ((⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)) ∣
      star ((⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)) := by
  intro hd
  have habZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = ((p : ℕ) : ℤ) := by exact_mod_cast hab
  have hnorm_pi : ((⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)).norm = ((p : ℕ) : ℤ) := by
    rw [ftn_norm_pair]
    have h2 := habZ
    rw [pow_two, pow_two] at h2
    exact h2
  have hpa : ((p : ℕ) : ℤ) ∣ (a : ℤ) := by
    have hsum : ((((⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)) +
        star ((⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)))).norm = 4 * (a : ℤ) ^ 2 := by
      rw [Zsqrtd.star_mk, Zsqrtd.add_def, ftn_norm_pair]
      ring
    have hdvds := dvd_add (dvd_refl _) hd
    have hnorm_dvd := ftn_gauss_norm_dvd hdvds
    rw [hnorm_pi, hsum] at hnorm_dvd
    exact ftn_int_prime_dvd_of_dvd_four_mul_sq p hp hmod _ hnorm_dvd
  have hpb : ((p : ℕ) : ℤ) ∣ (b : ℤ) := by
    have hprimeZ : Prime (((p : ℕ)) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hb2 : ((p : ℕ) : ℤ) ∣ (b : ℤ) ^ 2 := by
      have hbeq : (b : ℤ) ^ 2 = ((p : ℕ) : ℤ) - (a : ℤ) ^ 2 := by
        linear_combination habZ
      rw [hbeq]
      have ha2 : ((p : ℕ) : ℤ) ∣ (a : ℤ) ^ 2 := by
        rw [pow_two]
        exact dvd_mul_of_dvd_left hpa _
      exact dvd_sub (dvd_refl _) ha2
    rw [pow_two] at hb2
    rcases (hprimeZ.dvd_mul).mp hb2 with h | h <;> exact h
  obtain ⟨s, hs⟩ := hpa
  obtain ⟨t, ht⟩ := hpb
  rw [hs, ht] at habZ
  have hfac : ((p : ℕ) : ℤ) * (((p : ℕ) : ℤ) * (s ^ 2 + t ^ 2) - 1) = 0 := by
    linear_combination habZ
  rcases mul_eq_zero.mp hfac with hP0 | hS1
  · exact hp.ne_zero (by exact_mod_cast hP0)
  · have hdvd1 : (p : ℕ) ∣ 1 := by
      have h1 : ((p : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) := by
        rw [Nat.cast_one]
        exact ⟨s ^ 2 + t ^ 2, (eq_of_sub_eq_zero hS1).symm⟩
      exact Int.natCast_dvd_natCast.mp h1
    exact hp.ne_one (Nat.dvd_one.mp hdvd1)

private lemma ftn_split_prime_exists (p : ℕ) (hp : Nat.Prime p)
    (hmod : p % 4 = 1) :
    ∃ π : GaussianInt, π.norm = ((p : ℕ) : ℤ) ∧ Prime π ∧
      ((p : ℕ) : GaussianInt) = π * star π ∧
      ¬ π ∣ star π := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (by omega : p % 4 ≠ 3)
  have hnorm_pi : ((⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)).norm = ((p : ℕ) : ℤ) := by
    rw [ftn_norm_pair]
    have habZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = ((p : ℕ) : ℤ) := by
      exact_mod_cast hab
    rw [pow_two, pow_two] at habZ
    exact habZ
  have hprod : ((p : ℕ) : GaussianInt) =
      (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) *
        star ((⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)) := by
    have e : (((⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt).norm : ℤ) : GaussianInt) =
        _ * star _ :=
      Zsqrtd.norm_eq_mul_conj _
    rw [hnorm_pi] at e
    have c : ((((p : ℕ)) : ℤ) : GaussianInt) = ((p : ℕ) : GaussianInt) := by
      norm_cast
    rwa [c] at e
  exact ⟨_, hnorm_pi, ftn_prime_of_norm_prime _ p hp hnorm_pi, hprod,
    ftn_split_prime_not_dvd p a b hp hmod hab⟩

private lemma ftn_gauss_image_eq (c : GaussianInt) (p N M : ℕ)
    (hnorm_c : c.norm = ((p : ℕ) : ℤ)) (hNM : p * M = N) (hp0 : p ≠ 0) :
    (fun w : GaussianInt => c * w) '' ftnGaussNormSet M =
      {z ∈ ftnGaussNormSet N | c ∣ z} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwM : w.norm = ((M : ℕ) : ℤ) := hw
    have e : (c * w).norm = ((N : ℕ) : ℤ) := by
      rw [Zsqrtd.norm_mul, hnorm_c, hwM]
      exact_mod_cast hNM
    exact ⟨e, dvd_mul_right c w⟩
  · rintro ⟨hzS, ⟨w₀, hw₀⟩⟩
    have hcancel : w₀.norm = ((M : ℕ) : ℤ) := by
      have hne : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp0
      have e1 : ((N : ℕ) : ℤ) = ((p : ℕ) : ℤ) * w₀.norm := by
        have e := congrArg Zsqrtd.norm hw₀
        rw [Zsqrtd.norm_mul, hnorm_c] at e
        have hzN : z.norm = ((N : ℕ) : ℤ) := hzS
        rw [hzN] at e
        exact e
      have e2 : ((N : ℕ) : ℤ) = ((p : ℕ) : ℤ) * ((M : ℕ) : ℤ) := by
        exact_mod_cast hNM.symm
      have e : ((p : ℕ) : ℤ) * w₀.norm = ((p : ℕ) : ℤ) * ((M : ℕ) : ℤ) := by
        rw [← e1, e2]
      exact mul_left_cancel₀ hne e
    exact ⟨w₀, hcancel, hw₀.symm⟩

private lemma ftn_gauss_union_eq (π : GaussianInt) (p N : ℕ)
    (hprime_pi : Prime π) (hprod : ((p : ℕ) : GaussianInt) = π * star π)
    (hdvd : p ∣ N) :
    ftnGaussNormSet N =
      {z ∈ ftnGaussNormSet N | π ∣ z} ∪
        {z ∈ ftnGaussNormSet N | star π ∣ z} := by
  obtain ⟨t, ht⟩ := hdvd
  ext z
  constructor
  · intro hz
    have hpi_N : π ∣ ((N : ℕ) : GaussianInt) :=
      dvd_trans ⟨star π, hprod⟩ ⟨((t : ℕ) : GaussianInt), by exact_mod_cast ht⟩
    have hpdvd : π ∣ z * star z := by
      rw [← ftn_gauss_N_eq N z hz]
      exact hpi_N
    rcases (hprime_pi.dvd_mul).mp hpdvd with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, ftn_gauss_star_dvd π z h⟩
  · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz

private lemma ftn_gauss_inter_sup (π : GaussianInt) (p N : ℕ)
    (hprod : ((p : ℕ) : GaussianInt) = π * star π) :
    {z ∈ ftnGaussNormSet N | ((p : ℕ) : GaussianInt) ∣ z} ⊆
      {z ∈ ftnGaussNormSet N | π ∣ z} ∩
        {z ∈ ftnGaussNormSet N | star π ∣ z} := by
  rintro z ⟨hzS, hpdvd⟩
  constructor
  · exact ⟨hzS, dvd_trans ⟨star π, hprod⟩ hpdvd⟩
  · exact ⟨hzS, dvd_trans ⟨π, by rw [hprod]; ring⟩ hpdvd⟩

private lemma ftn_gauss_inter_sub (π : GaussianInt) (p N : ℕ)
    (hprime_pi : Prime π) (hprod : ((p : ℕ) : GaussianInt) = π * star π)
    (hndvd : ¬ π ∣ star π) :
    {z ∈ ftnGaussNormSet N | π ∣ z} ∩
        {z ∈ ftnGaussNormSet N | star π ∣ z} ⊆
      {z ∈ ftnGaussNormSet N | ((p : ℕ) : GaussianInt) ∣ z} := by
  rintro z ⟨⟨hzS, hpi_z⟩, ⟨-, hstar_z⟩⟩
  obtain ⟨w, hw⟩ := hstar_z
  have hdiv : π ∣ star π * w := by
    rw [← hw]
    exact hpi_z
  have hpiw : π ∣ w := by
    rcases (hprime_pi.dvd_mul).mp hdiv with h1 | h1
    · exact absurd h1 hndvd
    · exact h1
  obtain ⟨v, hv⟩ := hpiw
  exact ⟨hzS, ⟨v, by rw [hw, hv, hprod]; ring⟩⟩

private lemma ftn_ncard_gaussNormSet_of_prime_one (p N : ℕ) (hp : Nat.Prime p)
    (hmod : p % 4 = 1) (hdvd : p ∣ N) :
    (ftnGaussNormSet N).ncard +
        (if p ^ 2 ∣ N then (ftnGaussNormSet (N / p ^ 2)).ncard else 0) =
      2 * (ftnGaussNormSet (N / p)).ncard := by
  obtain ⟨π, hnorm_pi, hprime_pi, hprod, hndvd⟩ :=
    ftn_split_prime_exists p hp hmod
  have hfinS := ftn_gaussNormSet_finite N
  have hNdiv : p * (N / p) = N := Nat.mul_div_cancel' hdvd
  have hA_img : (fun w : GaussianInt => π * w) '' ftnGaussNormSet (N / p) =
      {z ∈ ftnGaussNormSet N | π ∣ z} :=
    ftn_gauss_image_eq π p N (N / p) hnorm_pi hNdiv hp.ne_zero
  have hB_img : (fun w : GaussianInt => star π * w) '' ftnGaussNormSet (N / p) =
      {z ∈ ftnGaussNormSet N | star π ∣ z} :=
    ftn_gauss_image_eq (star π) p N (N / p)
      (by rw [Zsqrtd.norm_conj]; exact hnorm_pi) hNdiv hp.ne_zero
  have hunion := ftn_gauss_union_eq π p N hprime_pi hprod hdvd
  have hAB_sub := ftn_gauss_inter_sub π p N hprime_pi hprod hndvd
  have hAB_sup := ftn_gauss_inter_sup π p N hprod
  have hpi_ne : π ≠ 0 := by
    intro h
    have e : ((p : ℕ) : GaussianInt) = 0 := by rw [hprod, h, zero_mul]
    exact hp.ne_zero (by exact_mod_cast e)
  have hstar_ne : star π ≠ 0 := by
    intro h
    have e : ((p : ℕ) : GaussianInt) = 0 := by rw [hprod, h, mul_zero]
    exact hp.ne_zero (by exact_mod_cast e)
  have hfinA : ({z ∈ ftnGaussNormSet N | π ∣ z} : Set GaussianInt).Finite :=
    hfinS.subset (fun z hz => by obtain ⟨h, -⟩ := hz; exact h)
  have hfinB : ({z ∈ ftnGaussNormSet N | star π ∣ z} : Set GaussianInt).Finite :=
    hfinS.subset (fun z hz => by obtain ⟨h, -⟩ := hz; exact h)
  have hnc := Set.ncard_union_add_ncard_inter _ _ hfinA hfinB
  rw [← hunion] at hnc
  have hAncard : ({z ∈ ftnGaussNormSet N | π ∣ z} : Set GaussianInt).ncard =
      (ftnGaussNormSet (N / p)).ncard := by
    rw [← hA_img]
    exact Set.ncard_image_of_injective _ (mul_right_injective₀ hpi_ne)
  have hBncard : ({z ∈ ftnGaussNormSet N | star π ∣ z} : Set GaussianInt).ncard =
      (ftnGaussNormSet (N / p)).ncard := by
    rw [← hB_img]
    exact Set.ncard_image_of_injective _ (mul_right_injective₀ hstar_ne)
  rw [hAncard, hBncard] at hnc
  by_cases h2 : p ^ 2 ∣ N
  · rw [ite_eq_left h2]
    have hNdiv2 : p ^ 2 * (N / p ^ 2) = N := by
      rw [mul_comm]
      exact Nat.div_mul_cancel h2
    have hnorm_p : (((p : ℕ) : GaussianInt)).norm = (((p ^ 2 : ℕ)) : ℤ) := by
      rw [Zsqrtd.norm_natCast, Nat.cast_pow p 2, pow_two]
    have hAB_img : (fun w : GaussianInt => ((p : ℕ) : GaussianInt) * w) ''
        ftnGaussNormSet (N / p ^ 2) =
        {z ∈ ftnGaussNormSet N | ((p : ℕ) : GaussianInt) ∣ z} :=
      ftn_gauss_image_eq _ (p ^ 2) N (N / p ^ 2) hnorm_p hNdiv2
        (pow_ne_zero 2 hp.ne_zero)
    have hinter : {z ∈ ftnGaussNormSet N | π ∣ z} ∩
        {z ∈ ftnGaussNormSet N | star π ∣ z} =
        {z ∈ ftnGaussNormSet N | ((p : ℕ) : GaussianInt) ∣ z} :=
      Set.Subset.antisymm hAB_sub hAB_sup
    rw [hinter, ← hAB_img, Set.ncard_image_of_injective _
      (mul_right_injective₀ (by exact_mod_cast hp.ne_zero :
        ((p : ℕ) : GaussianInt) ≠ 0))] at hnc
    linear_combination hnc
  · rw [ite_eq_right h2]
    have hAB_empty : {z ∈ ftnGaussNormSet N | π ∣ z} ∩
        {z ∈ ftnGaussNormSet N | star π ∣ z} = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff]
      rintro ⟨⟨hzS, hpi_z⟩, ⟨-, hstar_z⟩⟩
      have hzmem : z ∈
          {z ∈ ftnGaussNormSet N | ((p : ℕ) : GaussianInt) ∣ z} :=
        hAB_sub ⟨⟨hzS, hpi_z⟩, ⟨hzS, hstar_z⟩⟩
      obtain ⟨-, hpz⟩ := hzmem
      obtain ⟨w₀, hw₀⟩ := hpz
      have hnormz : ((N : ℕ) : ℤ) = (p : ℤ) ^ 2 * w₀.norm := by
        have e := ftn_gauss_norm_mul p w₀
        rw [← hw₀] at e
        have hzN : z.norm = ((N : ℕ) : ℤ) := hzS
        rw [hzN] at e
        exact e
      have hdvdZ : (((p ^ 2 : ℕ)) : ℤ) ∣ ((N : ℕ) : ℤ) := by
        rw [Nat.cast_pow p 2]
        exact ⟨w₀.norm, hnormz⟩
      exact h2 (Int.natCast_dvd_natCast.mp hdvdZ)
    rw [hAB_empty, Set.ncard_empty] at hnc
    linear_combination hnc

/-- χ₄ as an `ArithmeticFunction ℤ`. -/
private def ftnChiFour : ArithmeticFunction ℤ :=
  ⟨fun n => ZMod.χ₄ ((n : ℕ) : ZMod 4), by decide⟩

private lemma ftnChiFour_apply (d : ℕ) :
    ftnChiFour d = ZMod.χ₄ ((d : ℕ) : ZMod 4) := rfl

private lemma ftnChiFour_isMul : ftnChiFour.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {m n} _ _ _ => ?_⟩
  · change ZMod.χ₄ (((1 : ℕ)) : ZMod 4) = 1
    rw [Nat.cast_one]
    exact map_one _
  · change ZMod.χ₄ (((m * n : ℕ)) : ZMod 4) =
      ZMod.χ₄ ((m : ℕ) : ZMod 4) * ZMod.χ₄ ((n : ℕ) : ZMod 4)
    rw [Nat.cast_mul, map_mul]

private lemma ftnChiFourDivisorSum_eq_conv (N : ℕ) :
    ftnChiFourDivisorSum N = (ftnChiFour * ↑ArithmeticFunction.zeta) N := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [ftnChiFourDivisorSum, ftnChiFour_apply]

private lemma ftn_chi_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    ftnChiFourDivisorSum (m * n) =
      ftnChiFourDivisorSum m * ftnChiFourDivisorSum n := by
  have hH : (ftnChiFour * ↑ArithmeticFunction.zeta).IsMultiplicative :=
    ftnChiFour_isMul.mul
      (ArithmeticFunction.IsMultiplicative.natCast
        ArithmeticFunction.isMultiplicative_zeta)
  rw [ftnChiFourDivisorSum_eq_conv m, ftnChiFourDivisorSum_eq_conv n,
    ftnChiFourDivisorSum_eq_conv (m * n)]
  exact hH.map_mul_of_coprime h

private lemma ftn_chi_prime_pow (p k : ℕ) (hp : Nat.Prime p) :
    ftnChiFourDivisorSum (p ^ k) =
      ∑ i ∈ Finset.range (k + 1), (ZMod.χ₄ ((p : ℕ) : ZMod 4)) ^ i := by
  have h1 : ftnChiFourDivisorSum (p ^ k) =
      ∑ d ∈ (p ^ k).divisors, ftnChiFour d := by
    simp only [ftnChiFourDivisorSum, ftnChiFour_apply]
  rw [h1, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ftnChiFour_apply, Nat.cast_pow, map_pow]

private lemma ftn_sum_neg_one_pow (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hk : Even k
    · have hodd : Odd (k + 1) := hk.add_one
      have hne : ¬ Even (k + 1) := fun h => Nat.even_add_one.mp h hk
      rw [ite_eq_left hk, hodd.neg_one_pow, ite_eq_right hne]
      ring
    · have heven : Even (k + 1) := Nat.even_add_one.mpr hk
      rw [ite_eq_right hk, heven.neg_one_pow, ite_eq_left heven]
      ring

private lemma ftn_sum_one_pow (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (1 : ℤ) ^ i = ((k : ℕ) : ℤ) + 1 := by
  simp

private lemma ftn_chi_one : ftnChiFourDivisorSum 1 = 1 := by
  change ∑ d ∈ Nat.divisors 1, ZMod.χ₄ ((d : ℕ) : ZMod 4) = 1
  rw [Nat.divisors_one, Finset.sum_singleton, Nat.cast_one]
  exact map_one _

private lemma ftn_sq_dvd_iff (p k m : ℕ) (hp : Nat.Prime p) (hpm : ¬ p ∣ m) :
    p ^ 2 ∣ p ^ k * m ↔ 2 ≤ k := by
  constructor
  · intro hd
    by_contra hlt
    push Not at hlt
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · simp only [pow_zero, one_mul] at hd
      exact hpm (dvd_trans (dvd_pow_self p two_ne_zero) hd)
    · simp only [pow_one] at hd
      obtain ⟨t, ht⟩ := hd
      have h1 : p * m = p * (p * t) := by rw [ht]; ring
      have h2 : m = p * t := mul_left_cancel₀ hp.ne_zero h1
      exact hpm ⟨t, h2⟩
  · intro hle
    exact (pow_dvd_pow p hle).trans (dvd_mul_right _ _)

private lemma ftn_div_pow_mul (p k m j : ℕ) (hle : j ≤ k) (hp0 : 0 < p)
    (N : ℕ) (hNk : N = p ^ k * m) :
    N / p ^ j = p ^ (k - j) * m := by
  rw [hNk]
  have hk : p ^ k = p ^ j * p ^ (k - j) := by
    conv_lhs => rw [← Nat.add_sub_cancel' hle]
    rw [pow_add]
  rw [hk, mul_assoc]
  exact Nat.mul_div_cancel_left _ (pow_pos hp0 j)

private lemma ftn_chi_three (p N : ℕ) (hp : Nat.Prime p)
    (hmod : p % 4 = 3) (hN : N ≠ 0) (hdvd : p ∣ N) :
    ftnChiFourDivisorSum N =
      if p ^ 2 ∣ N then ftnChiFourDivisorSum (N / p ^ 2) else 0 := by
  obtain ⟨k, m, hpm, hNk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exfalso
      rw [pow_zero, one_mul] at hNk
      rw [hNk] at hdvd
      exact hpm hdvd
    · exact hpos
  have hcop : (p ^ k).Coprime m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left k
  have hsplit : ftnChiFourDivisorSum N =
      ftnChiFourDivisorSum (p ^ k) * ftnChiFourDivisorSum m := by
    rw [hNk]
    exact ftn_chi_mul_of_coprime hcop
  have hchi : ZMod.χ₄ ((p : ℕ) : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four hmod
  have hpp : ftnChiFourDivisorSum (p ^ k) = if Even k then 1 else 0 := by
    rw [ftn_chi_prime_pow p k hp, hchi, ftn_sum_neg_one_pow]
  have h2iff : p ^ 2 ∣ N ↔ 2 ≤ k := by
    rw [hNk]
    exact ftn_sq_dvd_iff p k m hp hpm
  by_cases h2 : p ^ 2 ∣ N
  · rw [ite_eq_left h2]
    have hk2 : 2 ≤ k := h2iff.mp h2
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk2
    have hdiv : N / p ^ 2 = p ^ t * m := by
      have h := ftn_div_pow_mul p (2 + t) m 2 (Nat.le_add_right 2 t) hp.pos N hNk
      rwa [Nat.add_sub_cancel_left] at h
    have hsplit2 : ftnChiFourDivisorSum (N / p ^ 2) =
        ftnChiFourDivisorSum (p ^ t) * ftnChiFourDivisorSum m := by
      rw [hdiv]
      exact ftn_chi_mul_of_coprime ((hp.coprime_iff_not_dvd.mpr hpm).pow_left t)
    have hpp2 : ftnChiFourDivisorSum (p ^ t) = if Even t then 1 else 0 := by
      rw [ftn_chi_prime_pow p t hp, hchi, ftn_sum_neg_one_pow]
    have heven : Even (2 + t) ↔ Even t := by
      constructor
      · rintro ⟨s, hs⟩
        exact ⟨s - 1, by omega⟩
      · rintro ⟨s, hs⟩
        exact ⟨s + 1, by omega⟩
    rw [hsplit, hpp, hsplit2, hpp2]
    simp only [heven]
  · rw [ite_eq_right h2]
    have hk_lt : k < 2 := by
      by_contra hcon
      push Not at hcon
      exact h2 (h2iff.mpr hcon)
    have hk_eq : k = 1 := by omega
    subst hk_eq
    rw [hsplit, hpp]
    have hne : ¬ Even (1 : ℕ) := by decide
    rw [ite_eq_right hne, zero_mul]

private lemma ftn_chi_one_mod (p N : ℕ) (hp : Nat.Prime p)
    (hmod : p % 4 = 1) (hN : N ≠ 0) (hdvd : p ∣ N) :
    ftnChiFourDivisorSum N +
        (if p ^ 2 ∣ N then ftnChiFourDivisorSum (N / p ^ 2) else 0) =
      2 * ftnChiFourDivisorSum (N / p) := by
  obtain ⟨k, m, hpm, hNk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exfalso
      rw [pow_zero, one_mul] at hNk
      rw [hNk] at hdvd
      exact hpm hdvd
    · exact hpos
  have hcop : (p ^ k).Coprime m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left k
  have hsplit : ftnChiFourDivisorSum N =
      ftnChiFourDivisorSum (p ^ k) * ftnChiFourDivisorSum m := by
    rw [hNk]
    exact ftn_chi_mul_of_coprime hcop
  have hchi : ZMod.χ₄ ((p : ℕ) : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hmod
  have hpp : ∀ j, ftnChiFourDivisorSum (p ^ j) = ((j : ℕ) : ℤ) + 1 := by
    intro j
    rw [ftn_chi_prime_pow p j hp, hchi]
    simp
  have h2iff : p ^ 2 ∣ N ↔ 2 ≤ k := by
    rw [hNk]
    exact ftn_sq_dvd_iff p k m hp hpm
  have hdiv1 : N / p = p ^ (k - 1) * m := by
    have h := ftn_div_pow_mul p k m 1 hk1 hp.pos N hNk
    rwa [pow_one] at h
  have hsplit1 : ftnChiFourDivisorSum (N / p) =
      ftnChiFourDivisorSum (p ^ (k - 1)) * ftnChiFourDivisorSum m := by
    rw [hdiv1]
    exact ftn_chi_mul_of_coprime ((hp.coprime_iff_not_dvd.mpr hpm).pow_left (k - 1))
  have c1 : ((((k - 1 : ℕ))) : ℤ) = ((k : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub hk1]
    norm_num
  by_cases h2 : p ^ 2 ∣ N
  · rw [ite_eq_left h2]
    have hk2 : 2 ≤ k := h2iff.mp h2
    have hdiv2 : N / p ^ 2 = p ^ (k - 2) * m :=
      ftn_div_pow_mul p k m 2 hk2 hp.pos N hNk
    have hsplit2 : ftnChiFourDivisorSum (N / p ^ 2) =
        ftnChiFourDivisorSum (p ^ (k - 2)) * ftnChiFourDivisorSum m := by
      rw [hdiv2]
      exact ftn_chi_mul_of_coprime ((hp.coprime_iff_not_dvd.mpr hpm).pow_left (k - 2))
    have c2 : ((((k - 2 : ℕ))) : ℤ) = ((k : ℕ) : ℤ) - 2 := by
      rw [Nat.cast_sub hk2]
      norm_num
    rw [hsplit, hpp k, hsplit1, hpp (k - 1), hsplit2, hpp (k - 2), c1, c2]
    ring
  · rw [ite_eq_right h2]
    have hk_lt : k < 2 := by
      by_contra hcon
      push Not at hcon
      exact h2 (h2iff.mpr hcon)
    have hk_eq : k = 1 := by omega
    subst hk_eq
    rw [hsplit, hpp 1, hsplit1, hpp (1 - 1), c1, Nat.cast_one]
    ring

private lemma ftn_gaussNormRegion_one :
    ftnGaussNormRegion 1 = {(1 : GaussianInt)} := by
  ext z
  constructor
  · intro hz
    have hnorm2 : z.re * z.re + z.im * z.im = 1 := by
      have e := ftn_norm_eq_of_mem 1 z hz.2
      simpa using e
    obtain ⟨hlt, -⟩ := hz
    rw [abs_lt] at hlt
    obtain ⟨hlt1, hlt2⟩ := hlt
    have hre1 : 1 ≤ z.re := by omega
    have hre2 : z.re ≤ 1 := by
      have hsq : z.re * z.re ≤ 1 := by
        have him2 : 0 ≤ z.im * z.im := mul_self_nonneg _
        omega
      nlinarith
    have hre : z.re = 1 := by omega
    have him0 : z.im = 0 := by
      have h0 : z.im * z.im = 0 := by
        rw [hre] at hnorm2
        linear_combination hnorm2
      rcases mul_eq_zero.mp h0 with h | h <;> exact h
    rw [Set.mem_singleton_iff, Zsqrtd.ext_iff]
    constructor
    · rw [hre]
      exact Zsqrtd.re_one.symm
    · rw [him0]
      exact Zsqrtd.im_one.symm
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    refine ⟨?_, ?_⟩
    · rw [Zsqrtd.im_one, Zsqrtd.re_one]
      norm_num
    · simp

private lemma ftn_ncard_gaussNormSet_eq_four_mul_chi (N : ℕ) (hN : Odd N) :
    ((ftnGaussNormSet N).ncard : ℤ) = 4 * ftnChiFourDivisorSum N := by
  revert hN
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases hN1 : N = 1
    · subst hN1
      have h4 := ftn_ncard_gaussNormSet_eq_four_mul 1 ⟨0, by norm_num⟩
      have hR : (ftnGaussNormRegion 1).ncard = 1 := by
        rw [ftn_gaussNormRegion_one, Set.ncard_singleton]
      have h1 := ftn_chi_one
      rw [h4, hR, h1]
      norm_num
    · have hN0 : N ≠ 0 := by
        rintro rfl
        exact (by decide : ¬ Odd (0 : ℕ)) hN
      have hpos : 0 < N := Nat.pos_of_ne_zero hN0
      set p := N.minFac
      have hp : p.Prime := Nat.minFac_prime hN1
      have hdvd : p ∣ N := Nat.minFac_dvd N
      have hodd_p : Odd p := by
        rcases Nat.even_or_odd p with hev | hodd
        · exfalso
          obtain ⟨a, ha⟩ := hev
          obtain ⟨t, ht⟩ := hdvd
          have hevenN : Even N := ⟨a * t, by rw [ht, ha]; ring⟩
          exact (Nat.not_even_iff_odd.mpr hN) hevenN
        · exact hodd
      have hNdiv : p * (N / p) = N := Nat.mul_div_cancel' hdvd
      have hodd_div : Odd (N / p) := by
        have h : Odd (p * (N / p)) := hNdiv.symm ▸ hN
        exact (Nat.odd_mul.mp h).2
      have hlt_div : N / p < N := Nat.div_lt_self hpos hp.one_lt
      have hIH_div : ((ftnGaussNormSet (N / p)).ncard : ℤ) =
          4 * ftnChiFourDivisorSum (N / p) :=
        ih (N / p) hlt_div hodd_div
      have hm0 : p % 4 ≠ 0 := by
        intro h
        have hmod2 : p % 2 = 0 := by
          have e := Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)
          rw [h] at e
          simpa using e.symm
        rw [Nat.odd_iff] at hodd_p
        omega
      have hm2 : p % 4 ≠ 2 := by
        intro h
        have hmod2 : p % 2 = 0 := by
          have e := Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)
          rw [h] at e
          simpa using e.symm
        rw [Nat.odd_iff] at hodd_p
        omega
      have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
        have hlt4 : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
        omega
      have hp2 : 1 < p ^ 2 := by
        have h : (4 : ℕ) ≤ p ^ 2 := by
          have h2 := Nat.pow_le_pow_left hp.two_le 2
          simpa using h2
        omega
      rcases hmod with hmod1 | hmod3
      · have hGn := ftn_ncard_gaussNormSet_of_prime_one p N hp hmod1 hdvd
        have hCh := ftn_chi_one_mod p N hp hmod1 hN0 hdvd
        by_cases h2 : p ^ 2 ∣ N
        · rw [ite_eq_left h2] at hGn hCh
          have hNdiv2 : p ^ 2 * (N / p ^ 2) = N := by
            rw [mul_comm]
            exact Nat.div_mul_cancel h2
          have hodd_div2 : Odd (N / p ^ 2) := by
            have h : Odd (p ^ 2 * (N / p ^ 2)) := hNdiv2.symm ▸ hN
            exact (Nat.odd_mul.mp h).2
          have hlt_div2 : N / p ^ 2 < N := Nat.div_lt_self hpos hp2
          have hIH2 : ((ftnGaussNormSet (N / p ^ 2)).ncard : ℤ) =
              4 * ftnChiFourDivisorSum (N / p ^ 2) :=
            ih (N / p ^ 2) hlt_div2 hodd_div2
          have hG : ((ftnGaussNormSet N).ncard : ℤ) +
              ((ftnGaussNormSet (N / p ^ 2)).ncard : ℤ) =
              2 * ((ftnGaussNormSet (N / p)).ncard : ℤ) := by
            exact_mod_cast hGn
          linear_combination hG - hIH2 + 2 * hIH_div - 4 * hCh
        · rw [ite_eq_right h2] at hGn hCh
          have hG : ((ftnGaussNormSet N).ncard : ℤ) + 0 =
              2 * ((ftnGaussNormSet (N / p)).ncard : ℤ) := by
            exact_mod_cast hGn
          linear_combination hG + 2 * hIH_div - 4 * hCh
      · have hGn := ftn_ncard_gaussNormSet_of_prime_three p N hp hmod3 hdvd
        have hCh := ftn_chi_three p N hp hmod3 hN0 hdvd
        by_cases h2 : p ^ 2 ∣ N
        · rw [ite_eq_left h2] at hGn hCh
          have hNdiv2 : p ^ 2 * (N / p ^ 2) = N := by
            rw [mul_comm]
            exact Nat.div_mul_cancel h2
          have hodd_div2 : Odd (N / p ^ 2) := by
            have h : Odd (p ^ 2 * (N / p ^ 2)) := hNdiv2.symm ▸ hN
            exact (Nat.odd_mul.mp h).2
          have hlt_div2 : N / p ^ 2 < N := Nat.div_lt_self hpos hp2
          have hIH2 : ((ftnGaussNormSet (N / p ^ 2)).ncard : ℤ) =
              4 * ftnChiFourDivisorSum (N / p ^ 2) :=
            ih (N / p ^ 2) hlt_div2 hodd_div2
          rw [hGn, hCh]
          exact hIH2
        · rw [ite_eq_right h2] at hGn hCh
          rw [hGn, hCh]
          simp

private lemma ftn_chi_eq_divisorsAntidiagonal_sum (m : ℕ) :
    ftnChiFourDivisorSum m =
      ∑ p ∈ Nat.divisorsAntidiagonal m, ZMod.χ₄ ((p.1 : ℕ) : ZMod 4) := by
  simp only [ftnChiFourDivisorSum]
  exact (Nat.sum_divisorsAntidiagonal (fun d _ => ZMod.χ₄ ((d : ℕ) : ZMod 4))).symm

private lemma ftn_flat_eq_nested (n : ℕ) :
    (∑ t ∈ (Finset.antidiagonal n).sigma
      (fun p => (Nat.divisorsAntidiagonal (4 * p.1 + 1)).sigma
        (fun _ => Nat.divisorsAntidiagonal (4 * p.2 + 1))),
      ZMod.χ₄ ((((t.2.1).1 : ℕ)) : ZMod 4) * ZMod.χ₄ ((((t.2.2).1 : ℕ)) : ZMod 4)) =
    (∑ p ∈ Finset.antidiagonal n, ∑ d ∈ Nat.divisorsAntidiagonal (4 * p.1 + 1),
      ∑ e ∈ Nat.divisorsAntidiagonal (4 * p.2 + 1),
      ZMod.χ₄ ((d.1 : ℕ) : ZMod 4) * ZMod.χ₄ ((e.1 : ℕ) : ZMod 4)) := by
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Finset.sum_sigma]

private lemma ftn_flat_eq_quad (n : ℕ) :
    (∑ t ∈ (Finset.antidiagonal n).sigma
      (fun p => (Nat.divisorsAntidiagonal (4 * p.1 + 1)).sigma
        (fun _ => Nat.divisorsAntidiagonal (4 * p.2 + 1))),
      ZMod.χ₄ ((((t.2.1).1 : ℕ)) : ZMod 4) * ZMod.χ₄ ((((t.2.2).1 : ℕ)) : ZMod 4)) =
    (∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => q.1 * q.2.1 % 4 = 1),
      ZMod.χ₄ ((q.1 : ℕ) : ZMod 4) * ZMod.χ₄ ((q.2.2.1 : ℕ) : ZMod 4)) := by
  apply Finset.sum_nbij'
    (fun t => (t.2.1.1, (t.2.1.2, (t.2.2.1, t.2.2.2))))
    (fun w => (⟨((w.1 * w.2.1 - 1) / 4, (w.2.2.1 * w.2.2.2 - 1) / 4),
      ⟨(w.1, w.2.1), (w.2.2.1, w.2.2.2)⟩⟩ :
      Sigma (fun _ : ℕ × ℕ => Sigma (fun _ : ℕ × ℕ => ℕ × ℕ)))) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨⟨a, b⟩, ⟨⟨d, x⟩, ⟨e, y⟩⟩⟩ := t
    have hmem := Finset.mem_sigma.mp ht
    obtain ⟨hpA, hqA⟩ := hmem
    have hmem2 := Finset.mem_sigma.mp hqA
    obtain ⟨hdA, heA⟩ := hmem2
    have hpA' : a + b = n := Finset.mem_antidiagonal.mp hpA
    have hdx : d * x = 4 * a + 1 := (Nat.mem_divisorsAntidiagonal.mp hdA).1
    have hey : e * y = 4 * b + 1 := (Nat.mem_divisorsAntidiagonal.mp heA).1
    have heq : d * x + e * y = 4 * n + 2 := by omega
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (dvd_mul_right d x) (by omega)
    have hx1 : 1 ≤ x := Nat.pos_of_dvd_of_pos (dvd_mul_left x d) (by omega)
    have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos (dvd_mul_right e y) (by omega)
    have hy1 : 1 ≤ y := Nat.pos_of_dvd_of_pos (dvd_mul_left y e) (by omega)
    have hdxodd : Odd (d * x) := ⟨2 * a, by omega⟩
    have heyodd : Odd (e * y) := ⟨2 * b, by omega⟩
    have hxodd : Odd x := Nat.Odd.of_mul_right hdxodd
    have hyodd : Odd y := Nat.Odd.of_mul_right heyodd
    have hdN : d ≤ 4 * n + 2 := by
      have h1 : d ≤ d * x := Nat.le_mul_of_pos_right d (by omega)
      omega
    have hxN : x ≤ 4 * n + 2 := by
      have h1 : 1 * x ≤ d * x := mul_le_mul_left (by omega) x
      rw [one_mul] at h1
      omega
    have heN : e ≤ 4 * n + 2 := by
      have h1 : e ≤ e * y := Nat.le_mul_of_pos_right e (by omega)
      omega
    have hyN : y ≤ 4 * n + 2 := by
      have h1 : 1 * y ≤ e * y := mul_le_mul_left (by omega) y
      rw [one_mul] at h1
      omega
    have hmod : (d * x) % 4 = 1 := by omega
    rw [Finset.mem_filter]
    refine ⟨?_, hmod⟩
    exact (ftn_mem_oddQuad (4 * n + 2) d x e y).mpr
      ⟨hd1, hx1, he1, hy1, heq, hxodd, hyodd⟩
  · intro w hw
    obtain ⟨d, x, e, y⟩ := w
    obtain ⟨hwQ, hmod⟩ := Finset.mem_filter.mp hw
    have hmem := (ftn_mem_oddQuad (4 * n + 2) d x e y).mp hwQ
    obtain ⟨hd1, hx1, he1, hy1, heq, hxo, hyo⟩ := hmem
    have hmod' : (d * x) % 4 = 1 := hmod
    have hey' : (e * y) % 4 = 1 := by omega
    have hdxpos : 1 ≤ d * x := le_trans hd1 (Nat.le_mul_of_pos_right d hx1)
    have heypos : 1 ≤ e * y := le_trans he1 (Nat.le_mul_of_pos_right e hy1)
    have e1 : 4 * ((d * x - 1) / 4) + 1 = d * x := by omega
    have e2 : 4 * ((e * y - 1) / 4) + 1 = e * y := by omega
    have hab : (d * x - 1) / 4 + ((e * y - 1) / 4) = n := by omega
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_antidiagonal]
      exact hab
    · rw [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · rw [Nat.mem_divisorsAntidiagonal]
        exact ⟨e1.symm, by omega⟩
      · rw [Nat.mem_divisorsAntidiagonal]
        exact ⟨e2.symm, by omega⟩
  · intro t ht
    obtain ⟨⟨a, b⟩, ⟨⟨d, x⟩, ⟨e, y⟩⟩⟩ := t
    have hmem := Finset.mem_sigma.mp ht
    obtain ⟨hpA, hqA⟩ := hmem
    have hmem2 := Finset.mem_sigma.mp hqA
    obtain ⟨hdA, heA⟩ := hmem2
    have hdx : d * x = 4 * a + 1 := (Nat.mem_divisorsAntidiagonal.mp hdA).1
    have hey : e * y = 4 * b + 1 := (Nat.mem_divisorsAntidiagonal.mp heA).1
    have ea : (d * x - 1) / 4 = a := by omega
    have eb : (e * y - 1) / 4 = b := by omega
    change (⟨((d * x - 1) / 4, (e * y - 1) / 4), ⟨(d, x), (e, y)⟩⟩ :
      Sigma (fun _ : ℕ × ℕ => Sigma (fun _ : ℕ × ℕ => ℕ × ℕ))) =
      (⟨(a, b), ⟨(d, x), (e, y)⟩⟩ :
      Sigma (fun _ : ℕ × ℕ => Sigma (fun _ : ℕ × ℕ => ℕ × ℕ)))
    rw [ea, eb]
  · intro w hw
    obtain ⟨d, x, e, y⟩ := w
    rfl
  · intro t ht
    obtain ⟨⟨a, b⟩, ⟨⟨d, x⟩, ⟨e, y⟩⟩⟩ := t
    change ZMod.χ₄ ((d : ℕ) : ZMod 4) * ZMod.χ₄ ((e : ℕ) : ZMod 4) =
      ZMod.χ₄ ((d : ℕ) : ZMod 4) * ZMod.χ₄ ((e : ℕ) : ZMod 4)
    rfl

private lemma ftn_chiFour_even (d : ℕ) (h : Even d) :
    ZMod.χ₄ ((d : ℕ) : ZMod 4) = 0 := by
  obtain ⟨r, hr⟩ := h
  have h2 : d % 2 = 0 := by omega
  rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_left h2]

private lemma ftn_oddQuad_even_of_even (N d x e y : ℕ)
    (hmem : ((d, (x, (e, y))) : ℕ × ℕ × ℕ × ℕ) ∈ ftnOddQuad N)
    (hev : Even (d * x)) (hN : Even N) : Even e := by
  obtain ⟨-, -, -, -, heq, -, hyo⟩ := (ftn_mem_oddQuad N d x e y).mp hmem
  obtain ⟨r, hr⟩ := hev
  obtain ⟨sN, hsN⟩ := hN
  have hEy : Even (e * y) := by
    generalize d * x = A at heq hr
    generalize e * y = B at heq ⊢
    rw [Nat.even_iff]
    omega
  by_contra hne
  have hoe : Odd e := Nat.not_even_iff_odd.mp hne
  have hodd : Odd (e * y) := hoe.mul hyo
  obtain ⟨s, hs⟩ := hEy
  obtain ⟨t, ht⟩ := hodd
  omega

private lemma ftn_oddQuad_chi_add (n d x e y : ℕ)
    (hmem : ((d, (x, (e, y))) : ℕ × ℕ × ℕ × ℕ) ∈ ftnOddQuad (4 * n + 2)) :
    (ZMod.χ₄ ((d : ℕ) : ZMod 4) + ZMod.χ₄ ((x : ℕ) : ZMod 4)) *
      ZMod.χ₄ ((e : ℕ) : ZMod 4) =
      2 * (if d * x % 4 = 1 then
        ZMod.χ₄ ((d : ℕ) : ZMod 4) * ZMod.χ₄ ((e : ℕ) : ZMod 4) else 0) := by
  obtain ⟨-, -, -, -, heq, hxo, hyo⟩ := (ftn_mem_oddQuad (4 * n + 2) d x e y).mp hmem
  by_cases hevd : Even d
  · have hd0 : ZMod.χ₄ ((d : ℕ) : ZMod 4) = 0 := ftn_chiFour_even d hevd
    have he0 : ZMod.χ₄ ((e : ℕ) : ZMod 4) = 0 :=
      ftn_chiFour_even e (ftn_oddQuad_even_of_even (4 * n + 2) d x e y hmem
        (hevd.mul_right x) ⟨2 * n + 1, by ring⟩)
    rw [hd0, he0]
    split_ifs with h <;> ring
  · have hod : Odd d := Nat.not_even_iff_odd.mp hevd
    have hd4 : d % 4 = 1 ∨ d % 4 = 3 := by
      obtain ⟨k, hk⟩ := hod
      omega
    have hx4 : x % 4 = 1 ∨ x % 4 = 3 := by
      obtain ⟨k, hk⟩ := hxo
      omega
    rcases hd4 with h1 | h3 <;> rcases hx4 with g1 | g3
    · have hcond : 1 * 1 % 4 = 1 := by decide
      rw [ZMod.χ₄_nat_one_mod_four h1, ZMod.χ₄_nat_one_mod_four g1,
        Nat.mul_mod, h1, g1, ite_eq_left hcond]
      ring
    · have hcond : ¬ 1 * 3 % 4 = 1 := by decide
      rw [ZMod.χ₄_nat_one_mod_four h1, ZMod.χ₄_nat_three_mod_four g3,
        Nat.mul_mod, h1, g3, ite_eq_right hcond]
      ring
    · have hcond : ¬ 3 * 1 % 4 = 1 := by decide
      rw [ZMod.χ₄_nat_three_mod_four h3, ZMod.χ₄_nat_one_mod_four g1,
        Nat.mul_mod, h3, g1, ite_eq_right hcond]
      ring
    · have hcond : 3 * 3 % 4 = 1 := by decide
      rw [ZMod.χ₄_nat_three_mod_four h3, ZMod.χ₄_nat_three_mod_four g3,
        Nat.mul_mod, h3, g3, ite_eq_left hcond]
      ring

private lemma ftn_quad_chi_add_eq (n : ℕ) :
    ∑ q ∈ ftnOddQuad (4 * n + 2),
        (ZMod.χ₄ (q.1 : ZMod 4) + ZMod.χ₄ (q.2.1 : ZMod 4)) *
          ZMod.χ₄ (q.2.2.1 : ZMod 4) =
      2 * ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => q.1 * q.2.1 % 4 = 1),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) := by
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨d, x, e, y⟩ := q
  exact ftn_oddQuad_chi_add n d x e y hq

private lemma ftn_quad_chi_split (n : ℕ) :
    ∑ q ∈ ftnOddQuad (4 * n + 2),
        (ZMod.χ₄ (q.1 : ZMod 4) + ZMod.χ₄ (q.2.1 : ZMod 4)) *
          ZMod.χ₄ (q.2.2.1 : ZMod 4) =
      (∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4)) +
      (∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.2.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  exact add_mul _ _ _

private lemma ftn_quad_chi_swap_aux1 (n d x e y : ℕ)
    (hq : ((d, (x, (e, y))) : ℕ × ℕ × ℕ × ℕ) ∈ ftnOddQuad (4 * n + 2))
    (hqS : ((d, (x, (e, y))) : ℕ × ℕ × ℕ × ℕ) ∉
      (ftnOddQuad (4 * n + 2)).filter (fun q => Odd q.1)) :
    ZMod.χ₄ ((x : ℕ) : ZMod 4) * ZMod.χ₄ ((e : ℕ) : ZMod 4) = 0 := by
  have hnod : ¬ Odd d := fun h => hqS (Finset.mem_filter.mpr ⟨hq, h⟩)
  have hevd : Even d := Nat.not_odd_iff_even.mp hnod
  have he0 : ZMod.χ₄ ((e : ℕ) : ZMod 4) = 0 :=
    ftn_chiFour_even e (ftn_oddQuad_even_of_even (4 * n + 2) d x e y hq
      (hevd.mul_right x) ⟨2 * n + 1, by ring⟩)
  rw [he0, mul_zero]

private lemma ftn_quad_chi_swap_aux2 (n d x e y : ℕ)
    (hq : ((d, (x, (e, y))) : ℕ × ℕ × ℕ × ℕ) ∈ ftnOddQuad (4 * n + 2))
    (hqS : ((d, (x, (e, y))) : ℕ × ℕ × ℕ × ℕ) ∉
      (ftnOddQuad (4 * n + 2)).filter (fun q => Odd q.1)) :
    ZMod.χ₄ ((d : ℕ) : ZMod 4) * ZMod.χ₄ ((e : ℕ) : ZMod 4) = 0 := by
  have hnod : ¬ Odd d := fun h => hqS (Finset.mem_filter.mpr ⟨hq, h⟩)
  have hevd : Even d := Nat.not_odd_iff_even.mp hnod
  rw [ftn_chiFour_even d hevd, zero_mul]

private lemma ftn_quad_chi_swap (n : ℕ) :
    ∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.2.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) =
      ∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) := by
  have e1 : ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => Odd q.1),
        ZMod.χ₄ (q.2.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) =
      ∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.2.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun q hq hqS => by
      obtain ⟨d, x, e, y⟩ := q
      exact ftn_quad_chi_swap_aux1 n d x e y hq hqS)
  have e2 : ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => Odd q.1),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) =
      ∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun q hq hqS => by
      obtain ⟨d, x, e, y⟩ := q
      exact ftn_quad_chi_swap_aux2 n d x e y hq hqS)
  have e3 : ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => Odd q.1),
        ZMod.χ₄ (q.2.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) =
      ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => Odd q.1),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) := by
    apply Finset.sum_nbij'
      (fun q => (q.2.1, (q.1, (q.2.2.1, q.2.2.2))))
      (fun q => (q.2.1, (q.1, (q.2.2.1, q.2.2.2)))) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨d, x, e, y⟩ := q
      obtain ⟨hqQ, hod⟩ := Finset.mem_filter.mp hq
      have hmem := (ftn_mem_oddQuad (4 * n + 2) d x e y).mp hqQ
      obtain ⟨hd1, hx1, he1, hy1, heq, hxo, hyo⟩ := hmem
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_oddQuad (4 * n + 2) x d e y).mpr
          ⟨hx1, hd1, he1, hy1, by rw [mul_comm x d]; exact heq, hod, hyo⟩
      · exact hxo
    · intro q hq
      obtain ⟨d, x, e, y⟩ := q
      obtain ⟨hqQ, hod⟩ := Finset.mem_filter.mp hq
      have hmem := (ftn_mem_oddQuad (4 * n + 2) d x e y).mp hqQ
      obtain ⟨hd1, hx1, he1, hy1, heq, hxo, hyo⟩ := hmem
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_oddQuad (4 * n + 2) x d e y).mpr
          ⟨hx1, hd1, he1, hy1, by rw [mul_comm x d]; exact heq, hod, hyo⟩
      · exact hxo
    · intro q hq
      obtain ⟨d, x, e, y⟩ := q
      rfl
    · intro q hq
      obtain ⟨d, x, e, y⟩ := q
      rfl
    · intro q hq
      obtain ⟨d, x, e, y⟩ := q
      rfl
  calc ∑ q ∈ ftnOddQuad (4 * n + 2),
          ZMod.χ₄ (q.2.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4)
      = ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => Odd q.1),
          ZMod.χ₄ (q.2.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) := e1.symm
    _ = ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => Odd q.1),
          ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) := e3
    _ = ∑ q ∈ ftnOddQuad (4 * n + 2),
          ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) := e2

private lemma ftn_sum_antidiagonal_chi_eq_oddQuad_sum (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
        ftnChiFourDivisorSum (4 * p.1 + 1) * ftnChiFourDivisorSum (4 * p.2 + 1) =
      ∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) := by
  have step1 : ∀ p ∈ Finset.antidiagonal n,
      ftnChiFourDivisorSum (4 * p.1 + 1) * ftnChiFourDivisorSum (4 * p.2 + 1) =
        ∑ d ∈ Nat.divisorsAntidiagonal (4 * p.1 + 1),
          ∑ e ∈ Nat.divisorsAntidiagonal (4 * p.2 + 1),
            ZMod.χ₄ ((d.1 : ℕ) : ZMod 4) * ZMod.χ₄ ((e.1 : ℕ) : ZMod 4) := by
    intro p _
    rw [ftn_chi_eq_divisorsAntidiagonal_sum, ftn_chi_eq_divisorsAntidiagonal_sum,
      Finset.sum_mul_sum]
  have hadd := ftn_quad_chi_add_eq n
  have hsplit := ftn_quad_chi_split n
  have hswap := ftn_quad_chi_swap n
  have hW : ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => q.1 * q.2.1 % 4 = 1),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) =
      ∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) := by
    linarith
  calc ∑ p ∈ Finset.antidiagonal n,
          ftnChiFourDivisorSum (4 * p.1 + 1) * ftnChiFourDivisorSum (4 * p.2 + 1)
      = ∑ p ∈ Finset.antidiagonal n, ∑ d ∈ Nat.divisorsAntidiagonal (4 * p.1 + 1),
          ∑ e ∈ Nat.divisorsAntidiagonal (4 * p.2 + 1),
            ZMod.χ₄ ((d.1 : ℕ) : ZMod 4) * ZMod.χ₄ ((e.1 : ℕ) : ZMod 4) :=
        Finset.sum_congr rfl step1
    _ = ∑ t ∈ (Finset.antidiagonal n).sigma
          (fun p => (Nat.divisorsAntidiagonal (4 * p.1 + 1)).sigma
            (fun _ => Nat.divisorsAntidiagonal (4 * p.2 + 1))),
          ZMod.χ₄ ((((t.2.1).1 : ℕ)) : ZMod 4) *
            ZMod.χ₄ ((((t.2.2).1 : ℕ)) : ZMod 4) := (ftn_flat_eq_nested n).symm
    _ = ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter (fun q => q.1 * q.2.1 % 4 = 1),
          ZMod.χ₄ ((q.1 : ℕ) : ZMod 4) * ZMod.χ₄ ((q.2.2.1 : ℕ) : ZMod 4) :=
        ftn_flat_eq_quad n
    _ = ∑ q ∈ ftnOddQuad (4 * n + 2),
          ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) := hW

private lemma ftn_oddQuad_sum_sub_decomp (N : ℕ) (f : ℤ → ℤ) (hf : ∀ k, f (-k) = f k) :
    ∑ q ∈ ftnOddQuad N, f ((q.1 : ℤ) - (q.2.2.1 : ℤ)) =
      f 0 * ((((ftnOddQuad N).filter (fun q => q.1 = q.2.2.1)).card : ℕ) : ℤ) +
        2 * ∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => q.2.1 < q.2.2.2),
          f ((q.1 : ℕ) : ℤ) := by
  have Hsplit1 : (∑ q ∈ (ftnOddQuad N).filter (fun q => q.1 < q.2.2.1),
        f ((q.1 : ℤ) - (q.2.2.1 : ℤ))) +
      (∑ q ∈ (ftnOddQuad N).filter (fun q => ¬ q.1 < q.2.2.1),
        f ((q.1 : ℤ) - (q.2.2.1 : ℤ))) =
      ∑ q ∈ ftnOddQuad N, f ((q.1 : ℤ) - (q.2.2.1 : ℤ)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have Hsplit2 : (∑ q ∈ ((ftnOddQuad N).filter fun q => ¬ q.1 < q.2.2.1).filter
        (fun q => q.2.2.1 < q.1), f ((q.1 : ℤ) - (q.2.2.1 : ℤ))) +
      (∑ q ∈ ((ftnOddQuad N).filter fun q => ¬ q.1 < q.2.2.1).filter
        (fun q => ¬ q.2.2.1 < q.1), f ((q.1 : ℤ) - (q.2.2.1 : ℤ))) =
      (∑ q ∈ (ftnOddQuad N).filter (fun q => ¬ q.1 < q.2.2.1),
        f ((q.1 : ℤ) - (q.2.2.1 : ℤ))) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have E1 : (((ftnOddQuad N).filter fun q => ¬ q.1 < q.2.2.1).filter
      fun q => q.2.2.1 < q.1) = (ftnOddQuad N).filter fun q => q.2.2.1 < q.1 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : q.2.2.1 < q.1 := h2
      exact h2'
    · intro h2
      have h2' : q.2.2.1 < q.1 := h2
      refine ⟨?_, h2'⟩
      omega
  have E2 : (((ftnOddQuad N).filter fun q => ¬ q.1 < q.2.2.1).filter
      fun q => ¬ q.2.2.1 < q.1) =
      (ftnOddQuad N).filter fun q => q.1 = q.2.2.1 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ¬ q.1 < q.2.2.1 := h1
      have h2' : ¬ q.2.2.1 < q.1 := h2
      change q.1 = q.2.2.1
      omega
    · intro h
      have h' : q.1 = q.2.2.1 := h
      refine ⟨?_, ?_⟩
      · omega
      · omega
  rw [E1, E2] at Hsplit2
  have Hswap : (∑ q ∈ (ftnOddQuad N).filter (fun q => q.1 < q.2.2.1),
        f ((q.1 : ℤ) - (q.2.2.1 : ℤ))) =
      (∑ q ∈ (ftnOddQuad N).filter (fun q => q.2.2.1 < q.1),
        f ((q.1 : ℤ) - (q.2.2.1 : ℤ))) := by
    apply Finset.sum_nbij' (fun q => (q.2.2.1, (q.2.2.2, (q.1, q.2.1))))
      (fun q => (q.2.2.1, (q.2.2.2, (q.1, q.2.1)))) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      obtain ⟨hqQ, hlt⟩ := Finset.mem_filter.mp hq
      have hmem := (ftn_mem_oddQuad N a x b y).mp hqQ
      obtain ⟨ha1, hx1, hb1, hy1, heq, hxo, hyo⟩ := hmem
      have hlt' : a < b := hlt
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_oddQuad N b y a x).mpr ⟨hb1, hy1, ha1, hx1, by omega, hyo, hxo⟩
      · change a < b
        omega
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      obtain ⟨hqQ, hlt⟩ := Finset.mem_filter.mp hq
      have hmem := (ftn_mem_oddQuad N a x b y).mp hqQ
      obtain ⟨ha1, hx1, hb1, hy1, heq, hxo, hyo⟩ := hmem
      have hlt' : b < a := hlt
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_oddQuad N b y a x).mpr ⟨hb1, hy1, ha1, hx1, by omega, hyo, hxo⟩
      · change b < a
        omega
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      rfl
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      rfl
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      change f ((a : ℤ) - (b : ℤ)) = f ((b : ℤ) - (a : ℤ))
      have hneg : (b : ℤ) - (a : ℤ) = -(((a : ℤ) - (b : ℤ))) := by ring
      rw [hneg]
      exact (hf _).symm
  have Hbij : (∑ q ∈ (ftnOddQuad N).filter (fun q => q.2.2.1 < q.1),
        f ((q.1 : ℤ) - (q.2.2.1 : ℤ))) =
      (∑ r ∈ (ftnLiouvilleTriples N).filter (fun r => r.2.1 < r.2.2.2),
        f ((r.1 : ℕ) : ℤ)) := by
    apply Finset.sum_nbij'
      (fun q => (q.1 - q.2.2.1, (q.2.1, (q.2.2.1, q.2.1 + q.2.2.2))))
      (fun r => (r.2.2.1 + r.1, (r.2.1, (r.2.2.1, r.2.2.2 - r.2.1)))) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      obtain ⟨hqQ, hlt⟩ := Finset.mem_filter.mp hq
      have hmem := (ftn_mem_oddQuad N a x b y).mp hqQ
      obtain ⟨ha1, hx1, hb1, hy1, heq, hxo, hyo⟩ := hmem
      have hba' : b < a := hlt
      have hba_le : b ≤ a := le_of_lt hba'
      have key : (a - b) * x + b * x = a * x := by
        have h := congrArg (· * x) (Nat.sub_add_cancel hba_le)
        rwa [add_mul] at h
      have heqV : (a - b) * x + b * (x + y) = N := by
        have hmul2 : b * (x + y) = b * x + b * y := mul_add _ _ _
        omega
      have hYeven : Even (x + y) := hxo.add_odd hyo
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_liouvilleTriples N (a - b) x b (x + y)).mpr
          ⟨by omega, hx1, hb1, by omega, heqV, hxo, hYeven⟩
      · change x < x + y
        omega
    · intro r hr
      obtain ⟨c, X, b, Y⟩ := r
      obtain ⟨hrV, hlt⟩ := Finset.mem_filter.mp hr
      have hmem := (ftn_mem_liouvilleTriples N c X b Y).mp hrV
      obtain ⟨hc1, hX1, hb1, hY1, heq, hXo, hYe⟩ := hmem
      have hlt' : X < Y := hlt
      have hXYle : X ≤ Y := le_of_lt hlt'
      have hsplit : X + (Y - X) = Y := Nat.add_sub_cancel' hXYle
      have hbY : b * Y = b * X + b * (Y - X) := by
        calc b * Y = b * (X + (Y - X)) := by rw [hsplit]
        _ = b * X + b * (Y - X) := mul_add _ _ _
      have heqQ : (b + c) * X + b * (Y - X) = N := by
        have hadd : (b + c) * X = b * X + c * X := add_mul _ _ _
        omega
      have hyodd : Odd (Y - X) := by
        obtain ⟨k, hk⟩ := hXo
        obtain ⟨l, hl⟩ := hYe
        have hsub : Y - X = 2 * (l - k - 1) + 1 := by omega
        exact ⟨l - k - 1, hsub⟩
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_oddQuad N (b + c) X b (Y - X)).mpr
          ⟨by omega, hX1, hb1, by omega, heqQ, hXo, hyodd⟩
      · change b < b + c
        omega
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      have hba' : b < a := (Finset.mem_filter.mp hq).2
      have g1 : b + (a - b) = a := by omega
      have g4 : (x + y) - x = y := by omega
      change ((b + (a - b), (x, (b, (x + y) - x)))) = ((a, (x, (b, y))))
      rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨g1, rfl, rfl, g4⟩
    · intro r hr
      obtain ⟨c, X, b, Y⟩ := r
      have hlt' : X < Y := (Finset.mem_filter.mp hr).2
      have g1 : (b + c) - b = c := by omega
      have g4 : X + (Y - X) = Y := by omega
      change ((((b + c) - b, (X, (b, X + (Y - X)))))) = ((c, (X, (b, Y))))
      rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨g1, rfl, rfl, g4⟩
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      obtain ⟨hqQ, hlt⟩ := Finset.mem_filter.mp hq
      have hba' : b < a := hlt
      have hcast : (((a - b : ℕ)) : ℤ) = (a : ℤ) - (b : ℤ) :=
        Nat.cast_sub (le_of_lt hba')
      change f ((a : ℤ) - (b : ℤ)) = f (((a - b : ℕ)) : ℤ)
      rw [hcast]
  have Hdiag : (∑ q ∈ (ftnOddQuad N).filter (fun q => q.1 = q.2.2.1),
        f ((q.1 : ℤ) - (q.2.2.1 : ℤ))) =
      f 0 * ((((ftnOddQuad N).filter (fun q => q.1 = q.2.2.1)).card : ℕ) : ℤ) := by
    have hterm : ∀ q ∈ (ftnOddQuad N).filter (fun q => q.1 = q.2.2.1),
        f ((q.1 : ℤ) - (q.2.2.1 : ℤ)) = f 0 := by
      intro q hq
      have heq : q.1 = q.2.2.1 := (Finset.mem_filter.mp hq).2
      have h0 : ((q.1 : ℤ) - (q.2.2.1 : ℤ)) = 0 := by
        rw [heq, sub_self]
      rw [h0]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    ring
  linear_combination Hswap + Hdiag + 2 * Hbij - Hsplit1 - Hsplit2

private lemma ftn_oddQuad_sum_add_decomp (N : ℕ) (f : ℤ → ℤ) :
    ∑ q ∈ ftnOddQuad N, f (((q.1 + q.2.2.1 : ℕ)) : ℤ) =
      ∑ q ∈ (ftnOddQuad N).filter (fun q => q.2.1 = q.2.2.2),
          f (((q.1 + q.2.2.1 : ℕ)) : ℤ) +
        2 * ∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => q.2.2.1 < q.1),
          f ((q.1 : ℕ) : ℤ) := by
  have Hsplit1 : (∑ q ∈ (ftnOddQuad N).filter (fun q => q.2.2.2 < q.2.1),
        f (((q.1 + q.2.2.1 : ℕ)) : ℤ)) +
      (∑ q ∈ (ftnOddQuad N).filter (fun q => ¬ q.2.2.2 < q.2.1),
        f (((q.1 + q.2.2.1 : ℕ)) : ℤ)) =
      ∑ q ∈ ftnOddQuad N, f (((q.1 + q.2.2.1 : ℕ)) : ℤ) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have Hsplit2 : (∑ q ∈ ((ftnOddQuad N).filter fun q => ¬ q.2.2.2 < q.2.1).filter
        (fun q => q.2.1 < q.2.2.2), f (((q.1 + q.2.2.1 : ℕ)) : ℤ)) +
      (∑ q ∈ ((ftnOddQuad N).filter fun q => ¬ q.2.2.2 < q.2.1).filter
        (fun q => ¬ q.2.1 < q.2.2.2), f (((q.1 + q.2.2.1 : ℕ)) : ℤ)) =
      (∑ q ∈ (ftnOddQuad N).filter (fun q => ¬ q.2.2.2 < q.2.1),
        f (((q.1 + q.2.2.1 : ℕ)) : ℤ)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have E1 : (((ftnOddQuad N).filter fun q => ¬ q.2.2.2 < q.2.1).filter
      fun q => q.2.1 < q.2.2.2) = (ftnOddQuad N).filter fun q => q.2.1 < q.2.2.2 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : q.2.1 < q.2.2.2 := h2
      exact h2'
    · intro h2
      have h2' : q.2.1 < q.2.2.2 := h2
      refine ⟨?_, h2'⟩
      omega
  have E2 : (((ftnOddQuad N).filter fun q => ¬ q.2.2.2 < q.2.1).filter
      fun q => ¬ q.2.1 < q.2.2.2) =
      (ftnOddQuad N).filter fun q => q.2.1 = q.2.2.2 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ¬ q.2.2.2 < q.2.1 := h1
      have h2' : ¬ q.2.1 < q.2.2.2 := h2
      change q.2.1 = q.2.2.2
      omega
    · intro h
      have h' : q.2.1 = q.2.2.2 := h
      refine ⟨?_, ?_⟩
      · omega
      · omega
  rw [E1, E2] at Hsplit2
  have Hswap2 : (∑ q ∈ (ftnOddQuad N).filter (fun q => q.2.1 < q.2.2.2),
        f (((q.1 + q.2.2.1 : ℕ)) : ℤ)) =
      (∑ q ∈ (ftnOddQuad N).filter (fun q => q.2.2.2 < q.2.1),
        f (((q.1 + q.2.2.1 : ℕ)) : ℤ)) := by
    apply Finset.sum_nbij' (fun q => (q.2.2.1, (q.2.2.2, (q.1, q.2.1))))
      (fun q => (q.2.2.1, (q.2.2.2, (q.1, q.2.1)))) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      obtain ⟨hqQ, hlt⟩ := Finset.mem_filter.mp hq
      have hmem := (ftn_mem_oddQuad N a x b y).mp hqQ
      obtain ⟨ha1, hx1, hb1, hy1, heq, hxo, hyo⟩ := hmem
      have hlt' : x < y := hlt
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_oddQuad N b y a x).mpr ⟨hb1, hy1, ha1, hx1, by omega, hyo, hxo⟩
      · change x < y
        omega
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      obtain ⟨hqQ, hlt⟩ := Finset.mem_filter.mp hq
      have hmem := (ftn_mem_oddQuad N a x b y).mp hqQ
      obtain ⟨ha1, hx1, hb1, hy1, heq, hxo, hyo⟩ := hmem
      have hlt' : y < x := hlt
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_oddQuad N b y a x).mpr ⟨hb1, hy1, ha1, hx1, by omega, hyo, hxo⟩
      · change y < x
        omega
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      rfl
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      rfl
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      have hab : a + b = b + a := Nat.add_comm a b
      change f (((a + b : ℕ)) : ℤ) = f (((b + a : ℕ)) : ℤ)
      rw [hab]
  have Hbij2 : (∑ q ∈ (ftnOddQuad N).filter (fun q => q.2.2.2 < q.2.1),
        f (((q.1 + q.2.2.1 : ℕ)) : ℤ)) =
      (∑ r ∈ (ftnLiouvilleTriples N).filter (fun r => r.2.2.1 < r.1),
        f ((r.1 : ℕ) : ℤ)) := by
    apply Finset.sum_nbij'
      (fun q => (q.1 + q.2.2.1, (q.2.2.2, (q.1, q.2.1 - q.2.2.2))))
      (fun r => (r.2.2.1, (r.2.1 + r.2.2.2, (r.1 - r.2.2.1, r.2.1)))) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      obtain ⟨hqQ, hlt⟩ := Finset.mem_filter.mp hq
      have hmem := (ftn_mem_oddQuad N a x b y).mp hqQ
      obtain ⟨ha1, hx1, hb1, hy1, heq, hxo, hyo⟩ := hmem
      have hlt' : y < x := hlt
      have hkey : a * (x - y) + a * y = a * x := by
        have h := congrArg (a * ·) (Nat.sub_add_cancel (le_of_lt hlt'))
        rwa [mul_add] at h
      have heqV : (a + b) * y + a * (x - y) = N := by
        have hadd : (a + b) * y = a * y + b * y := add_mul _ _ _
        omega
      have hYeven : Even (x - y) := by
        obtain ⟨k, hk⟩ := hxo
        obtain ⟨l, hl⟩ := hyo
        have hsub : x - y = (k - l) + (k - l) := by omega
        exact ⟨k - l, hsub⟩
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_liouvilleTriples N (a + b) y a (x - y)).mpr
          ⟨by omega, hy1, ha1, by omega, heqV, hyo, hYeven⟩
      · change a < a + b
        omega
    · intro r hr
      obtain ⟨c, X, b, Y⟩ := r
      obtain ⟨hrV, hlt⟩ := Finset.mem_filter.mp hr
      have hmem := (ftn_mem_liouvilleTriples N c X b Y).mp hrV
      obtain ⟨hc1, hX1, hb1, hY1, heq, hXo, hYe⟩ := hmem
      have hlt' : b < c := hlt
      have hkey : (c - b) * X + b * X = c * X := by
        have h := congrArg (· * X) (Nat.sub_add_cancel (le_of_lt hlt'))
        rwa [add_mul] at h
      have heqQ : b * (X + Y) + (c - b) * X = N := by
        have hmul : b * (X + Y) = b * X + b * Y := mul_add _ _ _
        omega
      have hxodd : Odd (X + Y) := hXo.add_even hYe
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_oddQuad N b (X + Y) (c - b) X).mpr
          ⟨hb1, by omega, by omega, hX1, heqQ, hxodd, hXo⟩
      · change X < X + Y
        omega
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      have hlt' : y < x := (Finset.mem_filter.mp hq).2
      have g2 : y + (x - y) = x := by omega
      have g3 : (a + b) - a = b := by omega
      change ((a, (y + (x - y), ((a + b) - a, y)))) = ((a, (x, (b, y))))
      rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨rfl, g2, g3, rfl⟩
    · intro r hr
      obtain ⟨c, X, b, Y⟩ := r
      have hlt' : b < c := (Finset.mem_filter.mp hr).2
      have g1 : b + (c - b) = c := by omega
      have g4 : (X + Y) - X = Y := by omega
      change ((b + (c - b), (X, (b, (X + Y) - X)))) = ((c, (X, (b, Y))))
      rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨g1, rfl, rfl, g4⟩
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      change f (((a + b : ℕ)) : ℤ) = f (((a + b : ℕ)) : ℤ)
      rfl
  linear_combination Hswap2 + 2 * Hbij2 - Hsplit1 - Hsplit2

private lemma ftn_liouvilleTriples_shift (N : ℕ) (f : ℤ → ℤ) :
    ∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => q.2.1 < q.2.2.2), f ((q.1 : ℕ) : ℤ) =
      ∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => q.2.2.1 < q.1), f ((q.1 : ℕ) : ℤ) +
        ∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => q.2.2.1 = q.1),
          f ((q.1 : ℕ) : ℤ) := by
  have Hempty : ((ftnLiouvilleTriples N).filter fun q => q.2.1 = q.2.2.2) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨hqV, heq⟩ := Finset.mem_filter.mp hq
    obtain ⟨c, X, b, Y⟩ := q
    have hmem := (ftn_mem_liouvilleTriples N c X b Y).mp hqV
    obtain ⟨-, -, -, -, -, hXo, hYe⟩ := hmem
    have hXY : X = Y := heq
    rw [hXY] at hXo
    obtain ⟨k, hk⟩ := hXo
    obtain ⟨l, hl⟩ := hYe
    omega
  have HsplitX : (∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => q.2.1 < q.2.2.2),
        f ((q.1 : ℕ) : ℤ)) +
      (∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => ¬ q.2.1 < q.2.2.2),
        f ((q.1 : ℕ) : ℤ)) =
      ∑ q ∈ ftnLiouvilleTriples N, f ((q.1 : ℕ) : ℤ) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have HsplitX2 : (∑ q ∈ ((ftnLiouvilleTriples N).filter fun q => ¬ q.2.1 < q.2.2.2).filter
        (fun q => q.2.2.2 < q.2.1), f ((q.1 : ℕ) : ℤ)) +
      (∑ q ∈ ((ftnLiouvilleTriples N).filter fun q => ¬ q.2.1 < q.2.2.2).filter
        (fun q => ¬ q.2.2.2 < q.2.1), f ((q.1 : ℕ) : ℤ)) =
      (∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => ¬ q.2.1 < q.2.2.2),
        f ((q.1 : ℕ) : ℤ)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have F1 : (((ftnLiouvilleTriples N).filter fun q => ¬ q.2.1 < q.2.2.2).filter
      fun q => q.2.2.2 < q.2.1) =
      (ftnLiouvilleTriples N).filter fun q => q.2.2.2 < q.2.1 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : q.2.2.2 < q.2.1 := h2
      exact h2'
    · intro h2
      have h2' : q.2.2.2 < q.2.1 := h2
      refine ⟨?_, h2'⟩
      omega
  have F2 : (((ftnLiouvilleTriples N).filter fun q => ¬ q.2.1 < q.2.2.2).filter
      fun q => ¬ q.2.2.2 < q.2.1) =
      (ftnLiouvilleTriples N).filter fun q => q.2.1 = q.2.2.2 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ¬ q.2.1 < q.2.2.2 := h1
      have h2' : ¬ q.2.2.2 < q.2.1 := h2
      change q.2.1 = q.2.2.2
      omega
    · intro h
      have h' : q.2.1 = q.2.2.2 := h
      refine ⟨?_, ?_⟩
      · omega
      · omega
  rw [F1, F2, Hempty, Finset.sum_empty] at HsplitX2
  have HsplitBC : (∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => q.2.2.1 < q.1),
        f ((q.1 : ℕ) : ℤ)) +
      (∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => ¬ q.2.2.1 < q.1),
        f ((q.1 : ℕ) : ℤ)) =
      ∑ q ∈ ftnLiouvilleTriples N, f ((q.1 : ℕ) : ℤ) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have HsplitBC2 : (∑ q ∈ ((ftnLiouvilleTriples N).filter fun q => ¬ q.2.2.1 < q.1).filter
        (fun q => q.1 < q.2.2.1), f ((q.1 : ℕ) : ℤ)) +
      (∑ q ∈ ((ftnLiouvilleTriples N).filter fun q => ¬ q.2.2.1 < q.1).filter
        (fun q => ¬ q.1 < q.2.2.1), f ((q.1 : ℕ) : ℤ)) =
      (∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => ¬ q.2.2.1 < q.1),
        f ((q.1 : ℕ) : ℤ)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have G1 : (((ftnLiouvilleTriples N).filter fun q => ¬ q.2.2.1 < q.1).filter
      fun q => q.1 < q.2.2.1) =
      (ftnLiouvilleTriples N).filter fun q => q.1 < q.2.2.1 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : q.1 < q.2.2.1 := h2
      exact h2'
    · intro h2
      have h2' : q.1 < q.2.2.1 := h2
      refine ⟨?_, h2'⟩
      omega
  have G2 : (((ftnLiouvilleTriples N).filter fun q => ¬ q.2.2.1 < q.1).filter
      fun q => ¬ q.1 < q.2.2.1) =
      (ftnLiouvilleTriples N).filter fun q => q.2.2.1 = q.1 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ¬ q.2.2.1 < q.1 := h1
      have h2' : ¬ q.1 < q.2.2.1 := h2
      change q.2.2.1 = q.1
      omega
    · intro h
      have h' : q.2.2.1 = q.1 := h
      refine ⟨?_, ?_⟩
      · omega
      · omega
  rw [G1, G2] at HsplitBC2
  have Hshift : (∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => q.1 < q.2.2.1),
        f ((q.1 : ℕ) : ℤ)) =
      (∑ q ∈ (ftnLiouvilleTriples N).filter (fun q => q.2.2.2 < q.2.1),
        f ((q.1 : ℕ) : ℤ)) := by
    apply Finset.sum_nbij'
      (fun q => (q.1, (q.2.1 + q.2.2.2, (q.2.2.1 - q.1, q.2.2.2))))
      (fun r => (r.1, (r.2.1 - r.2.2.2, (r.2.2.1 + r.1, r.2.2.2)))) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨c, X, b, Y⟩ := q
      obtain ⟨hqV, hlt⟩ := Finset.mem_filter.mp hq
      have hmem := (ftn_mem_liouvilleTriples N c X b Y).mp hqV
      obtain ⟨hc1, hX1, hb1, hY1, heq, hXo, hYe⟩ := hmem
      have hlt' : c < b := hlt
      have hcb_le : c ≤ b := le_of_lt hlt'
      have key : (b - c) * Y + c * Y = b * Y := by
        have h := congrArg (· * Y) (Nat.sub_add_cancel hcb_le)
        rwa [add_mul] at h
      have heqV : c * (X + Y) + (b - c) * Y = N := by
        have hmul : c * (X + Y) = c * X + c * Y := mul_add _ _ _
        omega
      have hXodd : Odd (X + Y) := hXo.add_even hYe
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_liouvilleTriples N c (X + Y) (b - c) Y).mpr
          ⟨hc1, by omega, by omega, hY1, heqV, hXodd, hYe⟩
      · change Y < X + Y
        omega
    · intro r hr
      obtain ⟨c, X, b, Y⟩ := r
      obtain ⟨hrV, hlt⟩ := Finset.mem_filter.mp hr
      have hmem := (ftn_mem_liouvilleTriples N c X b Y).mp hrV
      obtain ⟨hc1, hX1, hb1, hY1, heq, hXo, hYe⟩ := hmem
      have hlt' : Y < X := hlt
      have hYXle : Y ≤ X := le_of_lt hlt'
      have key : c * (X - Y) + c * Y = c * X := by
        have h := congrArg (c * ·) (Nat.sub_add_cancel hYXle)
        rwa [mul_add] at h
      have heqQ : c * (X - Y) + (b + c) * Y = N := by
        have hadd : (b + c) * Y = b * Y + c * Y := add_mul _ _ _
        omega
      have hxodd : Odd (X - Y) := by
        obtain ⟨k, hk⟩ := hXo
        obtain ⟨l, hl⟩ := hYe
        have hsub : X - Y = 2 * (k - l) + 1 := by omega
        exact ⟨k - l, hsub⟩
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (ftn_mem_liouvilleTriples N c (X - Y) (b + c) Y).mpr
          ⟨hc1, by omega, by omega, hY1, heqQ, hxodd, hYe⟩
      · change c < b + c
        omega
    · intro q hq
      obtain ⟨c, X, b, Y⟩ := q
      have hlt' : c < b := (Finset.mem_filter.mp hq).2
      have g2 : (X + Y) - Y = X := by omega
      have g3 : (b - c) + c = b := by omega
      change ((c, ((X + Y) - Y, ((b - c) + c, Y)))) = ((c, (X, (b, Y))))
      rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨rfl, g2, g3, rfl⟩
    · intro r hr
      obtain ⟨c, X, b, Y⟩ := r
      have hlt' : Y < X := (Finset.mem_filter.mp hr).2
      have g2 : (X - Y) + Y = X := by omega
      have g3 : (b + c) - c = b := by omega
      change ((c, ((X - Y) + Y, ((b + c) - c, Y)))) = ((c, (X, (b, Y))))
      rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
      exact ⟨rfl, g2, g3, rfl⟩
    · intro q hq
      obtain ⟨c, X, b, Y⟩ := q
      change f (((c : ℕ)) : ℤ) = f (((c : ℕ)) : ℤ)
      rfl
  linear_combination HsplitX + HsplitX2 - HsplitBC - HsplitBC2 + Hshift

private lemma ftn_diag_mul {n a x y s t : ℕ} (heq : a * x + a * y = 4 * n + 2)
    (hs : x = 2 * s + 1) (ht : y = 2 * t + 1) :
    a * (s + t + 1) = 2 * n + 1 := by
  have h2m : x + y = 2 * (s + t + 1) := by omega
  have heq2 : a * (x + y) = 2 * (2 * n + 1) := by
    have h1 : a * x + a * y = a * (x + y) := (mul_add _ _ _).symm
    omega
  have hmul : a * (2 * (s + t + 1)) = 2 * (2 * n + 1) := by rw [← h2m]; exact heq2
  have h3 : (a * (s + t + 1)) * 2 = (2 * n + 1) * 2 := by
    have e1 : (a * (s + t + 1)) * 2 = a * (2 * (s + t + 1)) := by ring
    have e2 : (2 * n + 1) * 2 = 2 * (2 * n + 1) := by ring
    rw [e1, hmul, e2]
  exact mul_right_cancel₀ (by norm_num) h3

private lemma ftn_diag_div (a m N : ℕ) (hane : a ≠ 0) (h : a * m = N) :
    N / a = m := by
  rw [← h]
  exact mul_div_cancel_left₀ _ hane

private lemma ftn_card_oddQuad_diag (n : ℕ) :
    ((ftnOddQuad (4 * n + 2)).filter (fun q => q.1 = q.2.2.1)).card =
      ∑ d ∈ Nat.divisors (2 * n + 1), d := by
  have Hbij : ((ftnOddQuad (4 * n + 2)).filter (fun q => q.1 = q.2.2.1)).card =
      ((Nat.divisors (2 * n + 1)).sigma fun a => Finset.range ((2 * n + 1) / a)).card := by
    apply Finset.card_bij'
      (fun q _ => (⟨q.1, (q.2.1 - 1) / 2⟩ : Σ _ : ℕ, ℕ))
      (fun p _ => (p.1, (2 * p.2 + 1, (p.1, 2 * ((2 * n + 1) / p.1) - 2 * p.2 - 1)))) ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      obtain ⟨hqQ, hdiag⟩ := Finset.mem_filter.mp hq
      have hdiag' : a = b := hdiag
      have hmem := (ftn_mem_oddQuad (4 * n + 2) a x b y).mp hqQ
      obtain ⟨-, -, -, -, heq, hxo, hyo⟩ := hmem
      rw [← hdiag'] at heq
      obtain ⟨s, hs⟩ := hxo
      obtain ⟨t, ht⟩ := hyo
      have hdvd : a * (s + t + 1) = 2 * n + 1 := ftn_diag_mul heq hs ht
      have hane : a ≠ 0 := by
        intro hzero
        rw [hzero, Nat.zero_mul] at hdvd
        omega
      have hadvd : a ∣ 2 * n + 1 := ⟨s + t + 1, hdvd.symm⟩
      have hamem : a ∈ Nat.divisors (2 * n + 1) :=
        Nat.mem_divisors.mpr ⟨hadvd, by omega⟩
      have hdiv : (2 * n + 1) / a = s + t + 1 :=
        ftn_diag_div a (s + t + 1) (2 * n + 1) hane hdvd
      have hhalf : (x - 1) / 2 = s := by omega
      have hkrange : (x - 1) / 2 < (2 * n + 1) / a := by
        rw [hhalf, hdiv]
        omega
      rw [Finset.mem_sigma]
      exact ⟨hamem, Finset.mem_range.mpr hkrange⟩
    · intro p hp
      obtain ⟨a, k⟩ := p
      have hmem := Finset.mem_sigma.mp hp
      obtain ⟨hamem, hkrange⟩ := hmem
      have hkrange' : k < (2 * n + 1) / a := Finset.mem_range.mp hkrange
      have hadvd : a ∣ 2 * n + 1 := (Nat.mem_divisors.mp hamem).1
      have hapos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (by omega)
      have ha1 : 1 ≤ a := hapos
      have hM : a * ((2 * n + 1) / a) = 2 * n + 1 := Nat.mul_div_cancel' hadvd
      have hxy : (2 * k + 1) + (2 * ((2 * n + 1) / a) - 2 * k - 1) = 2 * ((2 * n + 1) / a) := by
        omega
      have h2M : a * (2 * ((2 * n + 1) / a)) = 2 * (a * ((2 * n + 1) / a)) := by ring
      have heqQ : a * (2 * k + 1) + a * (2 * ((2 * n + 1) / a) - 2 * k - 1) = 4 * n + 2 := by
        have h1 : a * (2 * k + 1) + a * (2 * ((2 * n + 1) / a) - 2 * k - 1) =
            a * ((2 * k + 1) + (2 * ((2 * n + 1) / a) - 2 * k - 1)) := (mul_add _ _ _).symm
        rw [h1, hxy, h2M, hM]
        ring
      have hyodd : Odd (2 * ((2 * n + 1) / a) - 2 * k - 1) := by
        have hsub : 2 * ((2 * n + 1) / a) - 2 * k - 1 = 2 * (((2 * n + 1) / a) - k - 1) + 1 := by
          omega
        exact ⟨(2 * n + 1) / a - k - 1, hsub⟩
      have hy1 : 1 ≤ 2 * ((2 * n + 1) / a) - 2 * k - 1 := by omega
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      exact (ftn_mem_oddQuad (4 * n + 2) a (2 * k + 1) a
        (2 * ((2 * n + 1) / a) - 2 * k - 1)).mpr
        ⟨ha1, by omega, ha1, hy1, heqQ, ⟨k, rfl⟩, hyodd⟩
    · intro q hq
      obtain ⟨a, x, b, y⟩ := q
      obtain ⟨hqQ, hdiag⟩ := Finset.mem_filter.mp hq
      have hdiag' : a = b := hdiag
      have hmem := (ftn_mem_oddQuad (4 * n + 2) a x b y).mp hqQ
      obtain ⟨-, -, -, -, heq, hxo, hyo⟩ := hmem
      rw [← hdiag'] at heq
      obtain ⟨s, hs⟩ := hxo
      obtain ⟨t, ht⟩ := hyo
      have hdvd : a * (s + t + 1) = 2 * n + 1 := ftn_diag_mul heq hs ht
      have hane : a ≠ 0 := by
        intro hzero
        rw [hzero, Nat.zero_mul] at hdvd
        omega
      have hdiv : (2 * n + 1) / a = s + t + 1 :=
        ftn_diag_div a (s + t + 1) (2 * n + 1) hane hdvd
      have hhalf : (x - 1) / 2 = s := by omega
      change ((a, (2 * ((x - 1) / 2) + 1, (a, 2 * ((2 * n + 1) / a) - 2 * ((x - 1) / 2) - 1)))) =
        ((a, (x, (b, y))))
      rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
      refine ⟨rfl, ?_, hdiag', ?_⟩
      · rw [hhalf]
        exact hs.symm
      · rw [hhalf, hdiv]
        omega
    · intro p hp
      obtain ⟨a, k⟩ := p
      have hkk : ((2 * k + 1) - 1) / 2 = k := by omega
      change (⟨a, ((2 * k + 1) - 1) / 2⟩ : Σ _ : ℕ, ℕ) = ⟨a, k⟩
      rw [hkk]
  rw [Hbij, Finset.card_sigma]
  simp only [Finset.card_range]
  exact Nat.sum_div_divisors (2 * n + 1) (fun d => d)

private def ftnFourInd (k : ℤ) : ℤ := if (4 : ℤ) ∣ k then 1 else 0

private lemma ftnFourInd_neg (k : ℤ) : ftnFourInd (-k) = ftnFourInd k := by
  simp only [ftnFourInd, dvd_neg]

private lemma ftnFourInd_pos (X w : ℤ) (h : X = 4 * w) : ftnFourInd X = 1 := by
  simp only [ftnFourInd]
  rw [ite_eq_left ⟨w, h⟩]

private lemma ftnFourInd_neg_zero (X : ℤ) (h : X % 4 ≠ 0) : ftnFourInd X = 0 := by
  simp only [ftnFourInd]
  rw [ite_eq_right (fun hd => h (Int.emod_eq_zero_of_dvd hd))]

private lemma ftn_chi_mul_eq_fourInd (a b : ℕ) :
    ZMod.χ₄ ((a : ℕ) : ZMod 4) * ZMod.χ₄ ((b : ℕ) : ZMod 4) =
      ftnFourInd ((a : ℤ) - (b : ℤ)) - ftnFourInd ((a : ℤ) + (b : ℤ)) := by
  have ha4 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have hb4 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  have e1 : ∀ m : ℕ, m % 4 = 1 → ZMod.χ₄ ((m : ℕ) : ZMod 4) = 1 :=
    fun m hm => ZMod.χ₄_nat_one_mod_four hm
  have e3 : ∀ m : ℕ, m % 4 = 3 → ZMod.χ₄ ((m : ℕ) : ZMod 4) = -1 :=
    fun m hm => ZMod.χ₄_nat_three_mod_four hm
  have e0 : ∀ m : ℕ, m % 4 = 0 ∨ m % 4 = 2 → ZMod.χ₄ ((m : ℕ) : ZMod 4) = 0 := by
    intro m hm
    have hev : Even m := by
      rw [Nat.even_iff]
      omega
    exact ftn_chiFour_even m hev
  rcases ha4 with ha0 | ha1 | ha2 | ha3 <;> rcases hb4 with hb0 | hb1 | hb2 | hb3
  · rw [e0 a (Or.inl ha0), e0 b (Or.inl hb0),
      ftnFourInd_pos ((a : ℤ) - (b : ℤ)) ((a / 4 : ℤ) - (b / 4 : ℤ)) (by omega),
      ftnFourInd_pos ((a : ℤ) + (b : ℤ)) ((a / 4 : ℤ) + (b / 4 : ℤ)) (by omega)]
    ring
  · rw [e0 a (Or.inl ha0), e1 b hb1,
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e0 a (Or.inl ha0), e0 b (Or.inr hb2),
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e0 a (Or.inl ha0), e3 b hb3,
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e1 a ha1, e0 b (Or.inl hb0),
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e1 a ha1, e1 b hb1,
      ftnFourInd_pos ((a : ℤ) - (b : ℤ)) ((a / 4 : ℤ) - (b / 4 : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e1 a ha1, e0 b (Or.inr hb2),
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e1 a ha1, e3 b hb3,
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_pos ((a : ℤ) + (b : ℤ)) ((a / 4 : ℤ) + (b / 4 : ℤ) + 1) (by omega)]
    ring
  · rw [e0 a (Or.inr ha2), e0 b (Or.inl hb0),
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e0 a (Or.inr ha2), e1 b hb1,
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e0 a (Or.inr ha2), e0 b (Or.inr hb2),
      ftnFourInd_pos ((a : ℤ) - (b : ℤ)) ((a / 4 : ℤ) - (b / 4 : ℤ)) (by omega),
      ftnFourInd_pos ((a : ℤ) + (b : ℤ)) ((a / 4 : ℤ) + (b / 4 : ℤ) + 1) (by omega)]
    ring
  · rw [e0 a (Or.inr ha2), e3 b hb3,
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e3 a ha3, e0 b (Or.inl hb0),
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e3 a ha3, e1 b hb1,
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_pos ((a : ℤ) + (b : ℤ)) ((a / 4 : ℤ) + (b / 4 : ℤ) + 1) (by omega)]
    ring
  · rw [e3 a ha3, e0 b (Or.inr hb2),
      ftnFourInd_neg_zero ((a : ℤ) - (b : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring
  · rw [e3 a ha3, e3 b hb3,
      ftnFourInd_pos ((a : ℤ) - (b : ℤ)) ((a / 4 : ℤ) - (b / 4 : ℤ)) (by omega),
      ftnFourInd_neg_zero ((a : ℤ) + (b : ℤ)) (by omega)]
    ring

private lemma ftn_four_not_dvd (m K : ℕ) (hdiv : m ∣ K) (hmod : K % 4 = 2) :
    ¬ (4 : ℤ) ∣ ((m : ℕ) : ℤ) := by
  intro hd
  have hdN : 4 ∣ m := Int.natCast_dvd_natCast.mp (by exact_mod_cast hd)
  obtain ⟨t, ht⟩ := hdiv
  obtain ⟨s, hs⟩ := dvd_trans hdN ⟨t, ht⟩
  omega

private lemma ftn_oddQuad_chi_sum_eq_sigma (n : ℕ) :
    ∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) =
      (((∑ d ∈ Nat.divisors (2 * n + 1), d : ℕ)) : ℤ) := by
  have hterm : ∀ q ∈ ftnOddQuad (4 * n + 2),
      ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4) =
        ftnFourInd ((q.1 : ℤ) - (q.2.2.1 : ℤ)) -
          ftnFourInd (((q.1 + q.2.2.1 : ℕ)) : ℤ) := by
    intro q hq
    obtain ⟨d, x, e, y⟩ := q
    exact ftn_chi_mul_eq_fourInd d e
  have hsplit : (∑ q ∈ ftnOddQuad (4 * n + 2),
        ZMod.χ₄ (q.1 : ZMod 4) * ZMod.χ₄ (q.2.2.1 : ZMod 4)) =
      (∑ q ∈ ftnOddQuad (4 * n + 2),
        ftnFourInd ((q.1 : ℤ) - (q.2.2.1 : ℤ))) -
      (∑ q ∈ ftnOddQuad (4 * n + 2),
        ftnFourInd (((q.1 + q.2.2.1 : ℕ)) : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  have h10 := ftn_oddQuad_sum_sub_decomp (4 * n + 2) ftnFourInd
    (fun k => ftnFourInd_neg k)
  have h11 := ftn_oddQuad_sum_add_decomp (4 * n + 2) ftnFourInd
  have h12 := ftn_liouvilleTriples_shift (4 * n + 2) ftnFourInd
  have hvanV : ∑ q ∈ (ftnLiouvilleTriples (4 * n + 2)).filter
        (fun q => q.2.2.1 = q.1),
      ftnFourInd ((q.1 : ℕ) : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨c, X, b, Y⟩ := q
    obtain ⟨hqV, hbc⟩ := Finset.mem_filter.mp hq
    have hmem := (ftn_mem_liouvilleTriples (4 * n + 2) c X b Y).mp hqV
    obtain ⟨-, -, -, -, heq, -, -⟩ := hmem
    have hcb : b = c := hbc
    rw [hcb] at heq
    have heq' : c * (X + Y) = 4 * n + 2 := by
      rw [mul_add]
      exact heq
    have hnd : ¬ (4 : ℤ) ∣ ((c : ℕ) : ℤ) :=
      ftn_four_not_dvd c (4 * n + 2) ⟨X + Y, heq'.symm⟩ (by omega)
    have h0 : ftnFourInd ((c : ℕ) : ℤ) = 0 := by
      simp only [ftnFourInd]
      rw [ite_eq_right hnd]
    exact h0
  have hvanQ : ∑ q ∈ (ftnOddQuad (4 * n + 2)).filter
        (fun q => q.2.1 = q.2.2.2),
      ftnFourInd (((q.1 + q.2.2.1 : ℕ)) : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨a, x, b, y⟩ := q
    obtain ⟨hqQ, hxy⟩ := Finset.mem_filter.mp hq
    have hmem := (ftn_mem_oddQuad (4 * n + 2) a x b y).mp hqQ
    obtain ⟨-, -, -, -, heq, -, -⟩ := hmem
    have hxy' : x = y := hxy
    rw [hxy'] at heq
    have heq' : (a + b) * x = 4 * n + 2 := by
      rw [hxy', add_mul]
      exact heq
    have hnd : ¬ (4 : ℤ) ∣ ((((a + b : ℕ))) : ℤ) :=
      ftn_four_not_dvd (a + b) (4 * n + 2) ⟨x, heq'.symm⟩ (by omega)
    have h0 : ftnFourInd ((((a + b : ℕ))) : ℤ) = 0 := by
      simp only [ftnFourInd]
      rw [ite_eq_right hnd]
    exact h0
  have hf0 : ftnFourInd 0 = 1 := by simp [ftnFourInd]
  rw [hf0, one_mul] at h10
  have hdiagZ : ((((ftnOddQuad (4 * n + 2)).filter
        (fun q => q.1 = q.2.2.1)).card : ℕ) : ℤ) =
      (((∑ d ∈ Nat.divisors (2 * n + 1), d : ℕ)) : ℤ) := by
    exact_mod_cast ftn_card_oddQuad_diag n
  linarith

end MetaMathlibExt.FourTriangular

@[expose] public section

namespace MetaMathlibExt

/-! # Legendre's four-triangular-numbers identity
-/

/--
**Legendre's four-triangular-numbers theorem.** For $k \ge 0$ let $T_k = k(k+1)/2$ be the
$k$-th triangular number. For every natural number $j$, the number of ordered quadruples
$(k_1, k_2, k_3, k_4)$ of integers with $0 \le k_i \le j$ and
$T_{k_1} + T_{k_2} + T_{k_3} + T_{k_4} = j$ equals $\sigma(2j+1)$, the sum of the positive
divisors of $2j+1$.

The bound $k_i \le j$ is automatic, since $T_k \ge k$. Representations using $T_0 = 0$ are
counted, and quadruples that differ only in the order of their entries are counted separately.

Proves `Wanted` entry `four_triangular_numbers_eq_divisor_sum`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, "Glaisher's Divisors and
Infinite Products," Journal of Integer Sequences 27 (2024), Article 24.1.6,
Proposition [Legendre] (equation nttriangle-b), lines 738–740,
https://cs.uwaterloo.ca/journals/JIS/VOL27/Bhatnagar/bhat4.tex
-/
public theorem four_triangular_numbers_eq_divisor_sum
    (j : ℕ) :
    Fintype.card { t : Fin 4 → Fin (j + 1) //
      (∑ i, ((t i).val * ((t i).val + 1) / 2)) = j } =
      ∑ d ∈ Nat.divisors (2 * j + 1), d := by
  rw [FourTriangular.ftn_wanted_card_eq_quadruple_card,
    FourTriangular.ftn_quadruple_card_eq_sum_antidiagonal]
  have hcast : ∀ a : ℕ, (FourTriangular.ftnTriPairCount a : ℤ) =
      FourTriangular.ftnChiFourDivisorSum (4 * a + 1) := by
    intro a
    have hodd : Odd (4 * a + 1) := ⟨2 * a, by ring⟩
    have h3 := FourTriangular.ftn_triPairCount_eq_ncard_region a
    have h4 := FourTriangular.ftn_ncard_gaussNormSet_eq_four_mul (4 * a + 1) hodd
    have h8 := FourTriangular.ftn_ncard_gaussNormSet_eq_four_mul_chi (4 * a + 1) hodd
    have h4z : ((FourTriangular.ftnGaussNormSet (4 * a + 1)).ncard : ℤ) =
        4 * ((FourTriangular.ftnGaussNormRegion (4 * a + 1)).ncard : ℤ) := by
      exact_mod_cast h4
    have h3z : (FourTriangular.ftnTriPairCount a : ℤ) =
        ((FourTriangular.ftnGaussNormRegion (4 * a + 1)).ncard : ℤ) := by
      exact_mod_cast h3
    linarith
  have hterm : ∀ p ∈ Finset.antidiagonal j,
      ((FourTriangular.ftnTriPairCount p.1 * FourTriangular.ftnTriPairCount p.2 : ℕ) : ℤ) =
        FourTriangular.ftnChiFourDivisorSum (4 * p.1 + 1) *
          FourTriangular.ftnChiFourDivisorSum (4 * p.2 + 1) := by
    intro p _
    rw [Nat.cast_mul, hcast p.1, hcast p.2]
  have hZ : ((∑ p ∈ Finset.antidiagonal j,
      FourTriangular.ftnTriPairCount p.1 * FourTriangular.ftnTriPairCount p.2 : ℕ) : ℤ) =
      (((∑ d ∈ Nat.divisors (2 * j + 1), d : ℕ)) : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl hterm,
      FourTriangular.ftn_sum_antidiagonal_chi_eq_oddQuad_sum]
    exact FourTriangular.ftn_oddQuad_chi_sum_eq_sigma j
  exact_mod_cast hZ

end MetaMathlibExt
