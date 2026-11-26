/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.NumberTheory.SquareRepresentationCongruences
public import MathlibExt.NumberTheory.TriangularRepresentationWindow

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Representability criterion from a window of counts

This file proves `repCount_ne_zero_of_window`: for `n ≥ 1`, an odd prime `p` with
`p - 1 ≥ n + 1` and any integer `s`, if `p` does not divide the window sum of the square
representation counts at the `p - 1` exponents below `s`, then the count at `s` is nonzero,
and likewise for triangular representation counts. The proof goes through a window
congruence for `p` consecutive powers at every integer shift, proved by reducing the theta
series modulo `p`.

Statements from Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS 26 (2026),
Article A93, Theorem 7.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
private theorem dvd_sum_range_squares_window {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) (s : ℤ) :
    (p : ℤ) ∣ ∑ i ∈ Finset.range p, sumOfSquaresRepCount (s - i) n := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod p)) p
  let reduce := PowerSeries.map (Int.castRingHom (ZMod p))
  let f := reduce squareThetaSeries
  have h0 : PowerSeries.constantCoeff f = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change PowerSeries.coeff 0 (reduce squareThetaSeries) = _
    rw [PowerSeries.coeff_map, coeff_squareThetaSeries_small.1, map_one]
  have hX : PowerSeries.X ∣ f - 1 := by
    rw [PowerSeries.X_dvd_iff, map_sub, map_one, h0, sub_self]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hcon
    have h2cast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hcon
    rw [ZMod.natCast_eq_zero_iff] at h2cast
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2cast
    have hge : 2 ≤ p := hp.two_le
    omega
  have hf : f - 1 ≠ 0 := by
    intro h
    have h₁ := congrArg (PowerSeries.coeff 1) (sub_eq_zero.mp h)
    change PowerSeries.coeff 1 (reduce squareThetaSeries) = _ at h₁
    rw [PowerSeries.coeff_map, coeff_squareThetaSeries_small.2.1] at h₁
    exact h2 (by simpa using h₁)
  have hgeom : ∑ i ∈ Finset.range p, f ^ i = (f - 1) ^ (p - 1) := by
    apply mul_right_cancel₀ hf
    rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel hp.pos, sub_pow_char, one_pow]
  let u := isUnit_squareThetaSeries.unit
  let w := Units.map reduce.toMonoidHom u
  have hw : (w.val : PowerSeries (ZMod p)) = f := by
    simp only [w, Units.coe_map, u, IsUnit.unit_spec, f]
    rfl
  have hmap_pow : ∀ z : ℤ, ((w ^ z).val : PowerSeries (ZMod p)) = reduce ((u ^ z).val) := by
    intro z
    simp only [w, ← map_zpow, Units.coe_map]
    rfl
  let W : PowerSeries (ZMod p) := (w ^ (s - ((p - 1 : ℕ) : ℤ))).val
  have hexp : ∀ i : ℕ, i < p →
      s - (i : ℤ) = (s - ((p - 1 : ℕ) : ℤ)) + (((p - 1 - i : ℕ)) : ℤ) := by
    intro i hi
    have hi' : i ≤ p - 1 := by omega
    rw [Nat.cast_sub hi']
    ring
  have hterm : ∀ i : ℕ, i ∈ Finset.range p →
      ((w ^ (s - (i : ℤ))).val : PowerSeries (ZMod p)) = W * f ^ (p - 1 - i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hexp i hi', zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, hw]
  have hcast : ∀ i : ℕ, ((sumOfSquaresRepCount (s - (i : ℤ)) n : ℤ) : ZMod p) =
      PowerSeries.coeff n ((w ^ (s - (i : ℤ))).val) := by
    intro i
    rw [hmap_pow]
    simp only [sumOfSquaresRepCount]
    change Int.castRingHom (ZMod p) (PowerSeries.coeff n _) = _
    rw [← PowerSeries.coeff_map]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  calc ((∑ i ∈ Finset.range p, sumOfSquaresRepCount (s - i) n : ℤ) : ZMod p)
      = ∑ i ∈ Finset.range p, PowerSeries.coeff n ((w ^ (s - (i : ℤ))).val) := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl (fun i _ => hcast i)
    _ = ∑ i ∈ Finset.range p, PowerSeries.coeff n (W * f ^ (p - 1 - i)) := by
        exact Finset.sum_congr rfl (fun i hi => by rw [hterm i hi])
    _ = PowerSeries.coeff n (W * ∑ i ∈ Finset.range p, f ^ i) := by
        simp only [Finset.mul_sum, map_sum]
        exact Finset.sum_range_reflect (fun i => PowerSeries.coeff n (W * f ^ i)) p
    _ = 0 := by
        rw [hgeom]
        exact PowerSeries.X_pow_dvd_iff.mp
          (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hX (p - 1)) _) n (Nat.lt_of_succ_le hpn)

set_option linter.unusedVariables false in
private theorem dvd_sum_range_triangular_window {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) (s : ℤ) :
    (p : ℤ) ∣ ∑ i ∈ Finset.range p, sumOfTriangularRepCount (s - i) n := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod p)) p
  let reduce := PowerSeries.map (Int.castRingHom (ZMod p))
  let f := reduce triangularThetaSeries
  have h0 : PowerSeries.constantCoeff f = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change PowerSeries.coeff 0 (reduce triangularThetaSeries) = _
    rw [PowerSeries.coeff_map, coeff_triangularThetaSeries_small.1, map_one]
  have hX : PowerSeries.X ∣ f - 1 := by
    rw [PowerSeries.X_dvd_iff, map_sub, map_one, h0, sub_self]
  have hf : f - 1 ≠ 0 := by
    intro h
    have h₁ := congrArg (PowerSeries.coeff 1) (sub_eq_zero.mp h)
    change PowerSeries.coeff 1 (reduce triangularThetaSeries) = _ at h₁
    rw [PowerSeries.coeff_map, coeff_triangularThetaSeries_small.2.1, map_one] at h₁
    simp at h₁
  have hgeom : ∑ i ∈ Finset.range p, f ^ i = (f - 1) ^ (p - 1) := by
    apply mul_right_cancel₀ hf
    rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel hp.pos, sub_pow_char, one_pow]
  let u := isUnit_triangularThetaSeries.unit
  let w := Units.map reduce.toMonoidHom u
  have hw : (w.val : PowerSeries (ZMod p)) = f := by
    simp only [w, Units.coe_map, u, IsUnit.unit_spec, f]
    rfl
  have hmap_pow : ∀ z : ℤ, ((w ^ z).val : PowerSeries (ZMod p)) = reduce ((u ^ z).val) := by
    intro z
    simp only [w, ← map_zpow, Units.coe_map]
    rfl
  let W : PowerSeries (ZMod p) := (w ^ (s - ((p - 1 : ℕ) : ℤ))).val
  have hexp : ∀ i : ℕ, i < p →
      s - (i : ℤ) = (s - ((p - 1 : ℕ) : ℤ)) + (((p - 1 - i : ℕ)) : ℤ) := by
    intro i hi
    have hi' : i ≤ p - 1 := by omega
    rw [Nat.cast_sub hi']
    ring
  have hterm : ∀ i : ℕ, i ∈ Finset.range p →
      ((w ^ (s - (i : ℤ))).val : PowerSeries (ZMod p)) = W * f ^ (p - 1 - i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hexp i hi', zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, hw]
  have hcast : ∀ i : ℕ, ((sumOfTriangularRepCount (s - (i : ℤ)) n : ℤ) : ZMod p) =
      PowerSeries.coeff n ((w ^ (s - (i : ℤ))).val) := by
    intro i
    rw [hmap_pow]
    simp only [sumOfTriangularRepCount]
    change Int.castRingHom (ZMod p) (PowerSeries.coeff n _) = _
    rw [← PowerSeries.coeff_map]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  calc ((∑ i ∈ Finset.range p, sumOfTriangularRepCount (s - i) n : ℤ) : ZMod p)
      = ∑ i ∈ Finset.range p, PowerSeries.coeff n ((w ^ (s - (i : ℤ))).val) := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl (fun i _ => hcast i)
    _ = ∑ i ∈ Finset.range p, PowerSeries.coeff n (W * f ^ (p - 1 - i)) := by
        exact Finset.sum_congr rfl (fun i hi => by rw [hterm i hi])
    _ = PowerSeries.coeff n (W * ∑ i ∈ Finset.range p, f ^ i) := by
        simp only [Finset.mul_sum, map_sum]
        exact Finset.sum_range_reflect (fun i => PowerSeries.coeff n (W * f ^ i)) p
    _ = 0 := by
        rw [hgeom]
        exact PowerSeries.X_pow_dvd_iff.mp
          (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hX (p - 1)) _) n (Nat.lt_of_succ_le hpn)

private theorem sum_range_eq_add_Icc (G : ℤ → ℕ → ℤ) (n p : ℕ) (s : ℤ) (hp1 : 0 < p) :
    ∑ i ∈ Finset.range p, G (s - i) n = G s n + ∑ i ∈ Finset.Icc 1 (p - 1), G (s - i) n := by
  have hset : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp), Nat.cast_zero, sub_zero]

@[expose] public section

/-- **Representability criterion from a window of counts.** For an integer $k$ and $n \ge 0$, let
$r_k(n)$ and $t_k(n)$ be the coefficients of $q^n$ in $\theta(q)^k$ and $\psi(q)^k$, where $\theta$
and $\psi$ are the square and triangular theta series (units of $\mathbb{Z}[[q]]$). Let $n \ge 1$,
let $p$ be an odd prime with $p - 1 \ge n + 1$, and let $s$ be an integer. If $p$ does not divide
$r_{s-1}(n) + r_{s-2}(n) + \cdots + r_{s-(p-1)}(n)$, then $r_s(n) \ne 0$. Likewise, if $p$ does not
divide $t_{s-1}(n) + t_{s-2}(n) + \cdots + t_{s-(p-1)}(n)$, then $t_s(n) \ne 0$.

The source places no condition on $s$, so the statement is made for every integer $s$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 7 (`integers-2026-A93-thm-7`). -/
public theorem repCount_ne_zero_of_window {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) (s : ℤ) :
    (¬ (p : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (p - 1), sumOfSquaresRepCount (s - i) n →
      sumOfSquaresRepCount s n ≠ 0) ∧
    (¬ (p : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (p - 1), sumOfTriangularRepCount (s - i) n →
      sumOfTriangularRepCount s n ≠ 0) := by
  refine ⟨?_, ?_⟩
  · intro hdiv h0
    apply hdiv
    have hwin := dvd_sum_range_squares_window hn hp hp2 hpn s
    have hsplit := sum_range_eq_add_Icc sumOfSquaresRepCount n p s hp.pos
    rw [hsplit, h0, zero_add] at hwin
    exact hwin
  · intro hdiv h0
    apply hdiv
    have hwin := dvd_sum_range_triangular_window hn hp hp2 hpn s
    have hsplit := sum_range_eq_add_Icc sumOfTriangularRepCount n p s hp.pos
    rw [hsplit, h0, zero_add] at hwin
    exact hwin

end

end MetaMathlibExt
