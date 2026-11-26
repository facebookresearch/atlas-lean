/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.NumberTheory.QAnalogCollatz
public import MathlibExt.NumberTheory.QCollatzParityFlip
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.LinearCombination

/-!
# Fixed points and the two-cycle of the q-Collatz map

Classifies the fixed points and the nontrivial two-cycle of the q-Collatz map.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Lemma 13 (`jis-2025-25.6.8-lem-13`).
-/

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

private instance : CharP (PowerSeries (ZMod 2)) 2 :=
  charP_of_injective_ringHom (f := C (R := ZMod 2)) C_injective 2

private theorem shift_even (x : PowerSeries (ZMod 2)) (hx : constantCoeff x = 0) :
    X * qShift x = x := by
  simpa [qShift, hx] using (sub_const_eq_X_mul_shift x).symm

private theorem branch_even (A B x : PowerSeries (ZMod 2)) (hx : constantCoeff x = 0) :
    X * qCollatz A B x = x := by
  simpa [qCollatz, hx] using shift_even x hx

private theorem branch_odd (A B x : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (hx : constantCoeff x ≠ 0) :
    X * qCollatz A B x = A * x + B := by
  have key : ∀ a b c : ZMod 2, a ≠ 0 → b ≠ 0 → c ≠ 0 → a * c + b = 0 := by decide
  have hzero : constantCoeff (A * x + B) = 0 := by
    simpa only [map_add, map_mul] using key _ _ _ hA hB hx
  simpa [qCollatz, hx] using shift_even (A * x + B) hzero

private theorem solve (A B x : PowerSeries (ZMod 2)) (hA : constantCoeff A ≠ 0)
    (h : A * x = B) : x = B * A⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq hA).mpr
  simpa only [mul_comm] using h

private theorem same_branch (A B x y : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hx : X * y = A * x + B)
    (hy : X * x = A * y + B) : x = y := by
  have hnonzero : A + X ≠ 0 := by
    intro h
    apply hA
    simpa using congrArg constantCoeff h
  have h : (A + X) * (x - y) = 0 := by
    linear_combination hy - hx
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hnonzero)

private theorem odd_solution (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    constantCoeff (B * A⁻¹) ≠ 0 := by
  simpa using mul_ne_zero hB (inv_ne_zero hA)

private theorem equation_to_branch (A B x y : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (hx : constantCoeff x ≠ 0)
    (h : X * y = A * x + B) : qCollatz A B x = y := by
  apply X_mul_cancel
  exact (branch_odd A B x hA hB hx).trans h.symm

private theorem fixed (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (x : PowerSeries (ZMod 2)) :
    qCollatz A B x = x ↔ x = 0 ∨ x = B * (A + X)⁻¹ := by
  have hden : constantCoeff (A + X) ≠ 0 := by simpa using hA
  constructor
  · intro h
    by_cases hx : constantCoeff x = 0
    · left
      have he := branch_even A B x hx
      rw [h] at he
      have hz : (X - 1) * x = 0 := by linear_combination he
      have hn : (X - 1 : PowerSeries (ZMod 2)) ≠ 0 := by
        intro hn
        have hc := congrArg constantCoeff hn
        simp at hc
      exact (mul_eq_zero.mp hz).resolve_left hn
    · right
      have ho := branch_odd A B x hA hB hx
      rw [h] at ho
      apply solve (A + X) B x hden
      rw [add_mul, ho, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · rintro (rfl | rfl)
    · exact qCollatz_zero A B
    · have hu := odd_solution (A + X) B hden hB
      apply equation_to_branch A B _ _ hA hB hu
      have he : (A + X) * (B * (A + X)⁻¹) = B := by
        rw [mul_left_comm, PowerSeries.mul_inv_cancel _ hden, mul_one]
      rw [add_mul] at he
      have hs : X * (B * (A + X)⁻¹) + A * (B * (A + X)⁻¹) = B := by
        simpa only [add_comm] using he
      exact (CharTwo.add_eq_iff_eq_add.mp hs).trans (add_comm _ _)

private theorem cycle_step (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    qCollatz A B (B * (A + X ^ 2)⁻¹) = X * (B * (A + X ^ 2)⁻¹) ∧
      qCollatz A B (X * (B * (A + X ^ 2)⁻¹)) = B * (A + X ^ 2)⁻¹ ∧
      X * (B * (A + X ^ 2)⁻¹) ≠ B * (A + X ^ 2)⁻¹ := by
  have hden : constantCoeff (A + X ^ 2) ≠ 0 := by simpa using hA
  have hu := odd_solution (A + X ^ 2) B hden hB
  refine ⟨?_, qCollatz_X_mul A B _, ?_⟩
  · apply equation_to_branch A B _ _ hA hB hu
    have he : (A + X ^ 2) * (B * (A + X ^ 2)⁻¹) = B := by
      rw [mul_left_comm, PowerSeries.mul_inv_cancel _ hden, mul_one]
    have hs : X * (X * (B * (A + X ^ 2)⁻¹)) +
        A * (B * (A + X ^ 2)⁻¹) = B := by
      simpa only [add_mul, pow_two, mul_assoc, add_comm] using he
    exact (CharTwo.add_eq_iff_eq_add.mp hs).trans (add_comm _ _)
  · intro h
    apply hu
    have hc := congrArg constantCoeff h
    simpa using hc.symm

private theorem two_cycle (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (x : PowerSeries (ZMod 2)) :
    (qCollatz A B (qCollatz A B x) = x ∧ qCollatz A B x ≠ x) ↔
      x = B * (A + X ^ 2)⁻¹ ∨ x = X * (B * (A + X ^ 2)⁻¹) := by
  have hden : constantCoeff (A + X ^ 2) ≠ 0 := by simpa using hA
  constructor
  · rintro ⟨hperiod, hnotfixed⟩
    let y := qCollatz A B x
    have hy : qCollatz A B y = x := hperiod
    by_cases hx : constantCoeff x = 0
    · have ex : X * y = x := branch_even A B x hx
      by_cases hy0 : constantCoeff y = 0
      · have ey := branch_even A B y hy0
        rw [hy] at ey
        exact (hnotfixed (same_branch 1 0 x y (by simp)
          (by simpa using ex) (by simpa using ey)).symm).elim
      · have ey := branch_odd A B y hA hB hy0
        rw [hy, ← ex, ← mul_assoc, ← pow_two] at ey
        have he : (A + X ^ 2) * y = B := by
          rw [add_mul, ey, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        have hs := solve (A + X ^ 2) B y hden he
        exact Or.inr (ex.symm.trans (congrArg (X * ·) hs))
    · have ex : X * y = A * x + B := branch_odd A B x hA hB hx
      by_cases hy0 : constantCoeff y = 0
      · have ey := branch_even A B y hy0
        rw [hy] at ey
        rw [← ey, ← mul_assoc, ← pow_two] at ex
        have he : (A + X ^ 2) * x = B := by
          rw [add_mul, ex, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        exact Or.inl (solve (A + X ^ 2) B x hden he)
      · have ey := branch_odd A B y hA hB hy0
        rw [hy] at ey
        exact (hnotfixed (same_branch A B x y hA ex ey).symm).elim
  · obtain ⟨hodd, heven, hne⟩ := cycle_step A B hA hB
    rintro (rfl | rfl)
    · exact ⟨by rw [hodd, heven], by rwa [hodd]⟩
    · exact ⟨by rw [heven, hodd], by rw [heven]; exact hne.symm⟩

/-- **Fixed points and the $2$-cycle of the $q$-Collatz map.** Let $A, B \in \mathbb{F}_2[[q]]$ be
odd (constant term $1$) and let $T_{A,B}$ be the $q$-analog of the $3x+1$ map. For every
$x \in \mathbb{F}_2[[q]]$, $T_{A,B}(x) = x$ holds exactly when $x = 0$ or $x = B/(A+q)$. Moreover,
for every $x \in \mathbb{F}_2[[q]]$, $T_{A,B}(T_{A,B}(x)) = x$ and $T_{A,B}(x) \ne x$ hold together
exactly when $x = B/(A+q^2)$ or $x = qB/(A+q^2)$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Lemma 13 (`jis-2025-25.6.8-lem-13`). -/
public theorem qCollatz_fixedPoints_and_twoCycle (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    (∀ x, qCollatz A B x = x ↔ x = 0 ∨ x = B * (A + X)⁻¹) ∧
    ∀ x, (qCollatz A B (qCollatz A B x) = x ∧ qCollatz A B x ≠ x) ↔
      x = B * (A + X ^ 2)⁻¹ ∨ x = X * (B * (A + X ^ 2)⁻¹) := by
  exact ⟨fixed A B hA hB, two_cycle A B hA hB⟩

end

end MetaMathlibExt
