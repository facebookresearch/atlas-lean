/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QAnalogCollatz
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.RingTheory.PowerSeries.Inverse
import MathlibExt.NumberTheory.QCollatzParityFlip

/-!
# Polynomial orbits of $T_{1,1+q^2}$

Every polynomial orbit of the $q$-analog $3x+1$ map with $A = 1$ and $B = 1 + q^2$ reaches
$\{0, 1 + q, 1, q\}$, and $T(x)$ is a polynomial if and only if $x$ is.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 5 (`jis-2025-25.6.8-thm-5`).
-/

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

private theorem X_mul_qShift_of_even {x : PowerSeries (ZMod 2)} (h : constantCoeff x = 0) :
    X * qShift x = x := by
  have hsub := PowerSeries.sub_const_eq_X_mul_shift x
  simp only [qShift] at *
  rw [h] at hsub
  simpa using hsub.symm

private theorem qShift_coe_eq_coe_divX (r : Polynomial (ZMod 2)) (h : r.coeff 0 = 0) :
    qShift (r : PowerSeries (ZMod 2)) = (r.divX : PowerSeries (ZMod 2)) := by
  have hX : Polynomial.X * r.divX = r := by
    have hadd := Polynomial.X_mul_divX_add r
    rw [h] at hadd
    simpa using hadd
  have hcoe : X * (r.divX : PowerSeries (ZMod 2)) = (r : PowerSeries (ZMod 2)) := by
    rw [← Polynomial.coe_X, ← Polynomial.coe_mul, hX]
  rw [← hcoe, qShift_X_mul]

private theorem zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  have hall : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  rcases hall a with rfl | rfl
  · exact absurd rfl h
  · rfl

private theorem coeff_Bpoly_zero : (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)).coeff 0 = 1 := by
  simp

private theorem natDegree_one_add_Xsq_le :
    (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)).natDegree ≤ 2 := by
  calc (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)).natDegree
      ≤ max (1 : Polynomial (ZMod 2)).natDegree
        (Polynomial.X ^ 2 : Polynomial (ZMod 2)).natDegree :=
        Polynomial.natDegree_add_le _ _
    _ ≤ 2 := by simp [Polynomial.natDegree_one]

private theorem exists_poly_qCollatz_coe (p : Polynomial (ZMod 2)) :
    ∃ q : Polynomial (ZMod 2),
      qCollatz 1 (1 + X ^ 2) (p : PowerSeries (ZMod 2)) = (q : PowerSeries (ZMod 2)) := by
  by_cases hp : p.coeff 0 = 0
  · have hconst : constantCoeff (p : PowerSeries (ZMod 2)) = 0 := by
      rw [Polynomial.constantCoeff_coe, hp]
    simp only [qCollatz, hconst, ↓reduceIte]
    exact ⟨p.divX, qShift_coe_eq_coe_divX p hp⟩
  · have hconst : constantCoeff (p : PowerSeries (ZMod 2)) ≠ 0 := by
      rw [Polynomial.constantCoeff_coe]
      exact hp
    simp only [qCollatz, hconst, ↓reduceIte]
    have hB : (1 + X ^ 2 : PowerSeries (ZMod 2))
        = ((1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by
      simp
    have hnum : (1 : PowerSeries (ZMod 2)) * (p : PowerSeries (ZMod 2)) + (1 + X ^ 2)
        = ((p + (1 + Polynomial.X ^ 2) : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by
      rw [hB, one_mul, ← Polynomial.coe_add]
    rw [hnum]
    have hcoeff : (p + (1 + Polynomial.X ^ 2) : Polynomial (ZMod 2)).coeff 0 = 0 := by
      have hp1 : p.coeff 0 = 1 := zmod2_eq_one_of_ne_zero hp
      rw [Polynomial.coeff_add, hp1, coeff_Bpoly_zero]
      decide
    exact ⟨(p + (1 + Polynomial.X ^ 2)).divX, qShift_coe_eq_coe_divX _ hcoeff⟩

private theorem exists_poly_of_exists_poly_qCollatz (x : PowerSeries (ZMod 2))
    (h : ∃ p : Polynomial (ZMod 2), qCollatz 1 (1 + X ^ 2) x = p) :
    ∃ q : Polynomial (ZMod 2), x = q := by
  obtain ⟨p, hp⟩ := h
  by_cases hx : constantCoeff x = 0
  · have hT : qShift x = (p : PowerSeries (ZMod 2)) := by
      simpa [qCollatz, hx] using hp
    have hx_eq : x = X * (p : PowerSeries (ZMod 2)) := by
      rw [← hT, X_mul_qShift_of_even hx]
    have hcoe : X * (p : PowerSeries (ZMod 2))
        = ((Polynomial.X * p : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by
      rw [Polynomial.coe_mul, Polynomial.coe_X]
    rw [hx_eq, hcoe]
    exact ⟨Polynomial.X * p, rfl⟩
  · have hT : qShift ((1 : PowerSeries (ZMod 2)) * x + (1 + X ^ 2))
        = (p : PowerSeries (ZMod 2)) := by
      simpa [qCollatz, hx] using hp
    have hx1 : constantCoeff x = 1 := zmod2_eq_one_of_ne_zero hx
    have hB1 : constantCoeff (1 + X ^ 2 : PowerSeries (ZMod 2)) = 1 := by simp
    have hy0 : constantCoeff ((1 : PowerSeries (ZMod 2)) * x + (1 + X ^ 2)) = 0 := by
      rw [map_add, map_mul, map_one, one_mul, hx1, hB1]
      decide
    have hy_eq : (1 : PowerSeries (ZMod 2)) * x + (1 + X ^ 2)
        = X * (p : PowerSeries (ZMod 2)) := by
      rw [← hT, X_mul_qShift_of_even hy0]
    have hx_eq : x = X * (p : PowerSeries (ZMod 2)) - (1 + X ^ 2 : PowerSeries (ZMod 2)) := by
      have h1 : (1 : PowerSeries (ZMod 2)) * x = x := one_mul x
      have h2 : x + (1 + X ^ 2 : PowerSeries (ZMod 2)) = X * (p : PowerSeries (ZMod 2)) := by
        simpa [h1] using hy_eq
      calc x = (x + (1 + X ^ 2 : PowerSeries (ZMod 2))) - (1 + X ^ 2) := by ring
        _ = X * (p : PowerSeries (ZMod 2)) - (1 + X ^ 2) := by rw [h2]
    have hB : (1 + X ^ 2 : PowerSeries (ZMod 2))
        = ((1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by
      simp
    have hX : X * (p : PowerSeries (ZMod 2))
        = ((Polynomial.X * p : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by
      rw [Polynomial.coe_mul, Polynomial.coe_X]
    rw [hx_eq, hX, hB, ← Polynomial.coe_sub]
    exact ⟨Polynomial.X * p - (1 + Polynomial.X ^ 2), rfl⟩

private theorem exists_poly_qCollatz_coe_decr (p : Polynomial (ZMod 2)) (hdeg : 2 ≤ p.natDegree) :
    ∃ q : Polynomial (ZMod 2),
      qCollatz 1 (1 + X ^ 2) (p : PowerSeries (ZMod 2)) = (q : PowerSeries (ZMod 2)) ∧
        q.natDegree < p.natDegree := by
  by_cases hp : p.coeff 0 = 0
  · have hconst : constantCoeff (p : PowerSeries (ZMod 2)) = 0 := by
      rw [Polynomial.constantCoeff_coe, hp]
    have hT : qCollatz 1 (1 + X ^ 2) (p : PowerSeries (ZMod 2))
        = (p.divX : PowerSeries (ZMod 2)) := by
      simp only [qCollatz, hconst, ↓reduceIte]
      exact qShift_coe_eq_coe_divX p hp
    refine ⟨p.divX, hT, ?_⟩
    have hdiv : p.divX.natDegree = p.natDegree - 1 :=
      Polynomial.natDegree_divX_eq_natDegree_tsub_one
    omega
  · have hconst : constantCoeff (p : PowerSeries (ZMod 2)) ≠ 0 := by
      rw [Polynomial.constantCoeff_coe]
      exact hp
    have hB : (1 + X ^ 2 : PowerSeries (ZMod 2))
        = ((1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by
      simp
    have hnum : (1 : PowerSeries (ZMod 2)) * (p : PowerSeries (ZMod 2)) + (1 + X ^ 2)
        = ((p + (1 + Polynomial.X ^ 2) : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by
      rw [hB, one_mul, ← Polynomial.coe_add]
    have hcoeff : (p + (1 + Polynomial.X ^ 2) : Polynomial (ZMod 2)).coeff 0 = 0 := by
      have hp1 : p.coeff 0 = 1 := zmod2_eq_one_of_ne_zero hp
      rw [Polynomial.coeff_add, hp1, coeff_Bpoly_zero]
      decide
    have hT : qCollatz 1 (1 + X ^ 2) (p : PowerSeries (ZMod 2))
        = (((p + (1 + Polynomial.X ^ 2)).divX : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by
      simp only [qCollatz, hconst, ↓reduceIte]
      rw [hnum]
      exact qShift_coe_eq_coe_divX _ hcoeff
    refine ⟨(p + (1 + Polynomial.X ^ 2)).divX, hT, ?_⟩
    have hle1 : (p + (1 + Polynomial.X ^ 2) : Polynomial (ZMod 2)).natDegree
        ≤ max p.natDegree (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)).natDegree :=
      Polynomial.natDegree_add_le _ _
    have hleB : (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)).natDegree ≤ p.natDegree :=
      le_trans natDegree_one_add_Xsq_le hdeg
    have hmax : max p.natDegree (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)).natDegree
        = p.natDegree := Nat.max_eq_left hleB
    have hle : (p + (1 + Polynomial.X ^ 2) : Polynomial (ZMod 2)).natDegree ≤ p.natDegree := by
      rw [hmax] at hle1
      exact hle1
    have hdiv : (p + (1 + Polynomial.X ^ 2) : Polynomial (ZMod 2)).divX.natDegree
        = (p + (1 + Polynomial.X ^ 2) : Polynomial (ZMod 2)).natDegree - 1 :=
      Polynomial.natDegree_divX_eq_natDegree_tsub_one
    omega

private theorem coe_mem_of_natDegree_le_one (p : Polynomial (ZMod 2)) (hdeg : p.natDegree ≤ 1) :
    (p : PowerSeries (ZMod 2)) ∈ ({0, 1 + X, 1, X} : Set (PowerSeries (ZMod 2))) := by
  have hform := Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
  have ha : p.coeff 1 = 0 ∨ p.coeff 1 = 1 := by
    have hall : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact hall _
  have hb : p.coeff 0 = 0 ∨ p.coeff 0 = 1 := by
    have hall : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact hall _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · have hp0 : p = 0 := by
      rw [hform, ha0, hb0]
      simp
    left
    rw [hp0]
    simp
  · have hp1 : p = 1 := by
      rw [hform, ha0, hb1]
      simp
    right; right; left
    rw [hp1]
    simp
  · have hpX : p = Polynomial.X := by
      rw [hform, ha1, hb0]
      simp
    right; right; right
    rw [hpX]
    simp
  · have hp : p = Polynomial.X + 1 := by
      rw [hform, ha1, hb1]
      simp [add_comm]
    right; left
    rw [hp]
    simp [add_comm]

private theorem orbit_exists (p : Polynomial (ZMod 2)) :
    ∃ k : ℕ, (qCollatz 1 (1 + X ^ 2))^[k] (p : PowerSeries (ZMod 2)) ∈
      ({0, 1 + X, 1, X} : Set (PowerSeries (ZMod 2))) := by
  suffices h : ∀ n : ℕ, ∀ q : Polynomial (ZMod 2), q.natDegree ≤ n →
      ∃ k : ℕ, (qCollatz 1 (1 + X ^ 2))^[k] (q : PowerSeries (ZMod 2)) ∈
        ({0, 1 + X, 1, X} : Set (PowerSeries (ZMod 2))) from h _ p le_rfl
  intro n
  induction n with
  | zero =>
    intro q hq
    have hle : q.natDegree ≤ 1 := le_trans hq (Nat.zero_le 1)
    exact ⟨0, by simpa using coe_mem_of_natDegree_le_one q hle⟩
  | succ n ih =>
    intro q hq
    by_cases hle1 : q.natDegree ≤ 1
    · exact ⟨0, by simpa using coe_mem_of_natDegree_le_one q hle1⟩
    · have hge : 2 ≤ q.natDegree := by omega
      obtain ⟨r, hrT, hrdeg⟩ := exists_poly_qCollatz_coe_decr q hge
      have hrle : r.natDegree ≤ n := by omega
      obtain ⟨k, hk⟩ := ih r hrle
      refine ⟨k.succ, ?_⟩
      rw [Function.iterate_succ_apply, hrT]
      exact hk

/-- **Polynomial orbits of $T_{1,1+q^2}$.** Let $T = T_{1,1+q^2}$ be the $q$-analog of the $3x+1$
map with $A = 1$ and $B = 1 + q^2$. For every polynomial $p$ over $\mathbb{F}_2$, some iterate
$T^k(p)$ with $k \ge 0$ lies in $\{0, 1 + q, 1, q\}$, the set formed by the fixed points $0$ and
$1 + q$ of $T$ and its $2$-cycle $\{1, q\}$. Moreover, for every $x \in \mathbb{F}_2[[q]]$, $T(x)$
is a polynomial if and only if $x$ is a polynomial.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 5 (`jis-2025-25.6.8-thm-5`). -/
public theorem qCollatz_one_one_add_X_sq_polynomial :
    (∀ p : Polynomial (ZMod 2), ∃ k : ℕ,
      (qCollatz 1 (1 + X ^ 2))^[k] (p : PowerSeries (ZMod 2)) ∈
        ({0, 1 + X, 1, X} : Set (PowerSeries (ZMod 2)))) ∧
    ∀ x : PowerSeries (ZMod 2),
      (∃ p : Polynomial (ZMod 2), qCollatz 1 (1 + X ^ 2) x = p) ↔
        ∃ p : Polynomial (ZMod 2), x = p := by
  refine ⟨orbit_exists, fun x => ⟨?_, ?_⟩⟩
  · intro h
    exact exists_poly_of_exists_poly_qCollatz x h
  · intro h
    obtain ⟨p0, rfl⟩ := h
    exact exists_poly_qCollatz_coe p0

end

end MetaMathlibExt
