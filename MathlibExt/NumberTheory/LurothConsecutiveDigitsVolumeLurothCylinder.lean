/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LurothBorelBernstein

/-!
# Measure of Lüroth cylinders

The theorem `MetaMathlibExt.volume_lurothCylinder` gives the Lebesgue measure of the set of
points in `(0, 1]` with prescribed first `n` Lüroth digits as the product of the digit
weights. It follows from the joint distribution of the digits,
`volume_lurothConsecutiveDigits_zero_one_integral.measurePreserving_digitSeq`, by evaluating
the product measure on a finite box.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67.
-/

open MeasureTheory

namespace MetaMathlibExt

/-- **Measure of Lüroth cylinders.** Write $d_k(x)$ for the $k$-th Lüroth digit of $x$. For every
$n \in \mathbb{N}$ and all natural numbers $c_1, \dots, c_n$, the set
$\{x \in (0, 1] : d_j(x) = c_j \text{ for } 1 \le j \le n\}$ has Lebesgue measure
$\prod_{j=1}^{n} \frac{1}{c_j (c_j - 1)}$, with the convention $1/0 = 0$; in particular both
sides vanish when some $c_j < 2$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Proposition 1,
(10) (`integers-2024-A67-prop-1`). -/
public theorem volume_lurothCylinder {n : ℕ} (c : Fin n → ℕ) :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      ∏ j, ENNReal.ofReal (1 / ((c j : ℝ) * ((c j : ℝ) - 1))) := by
  obtain ⟨ν, _, hν, hmp⟩ :=
    volume_lurothConsecutiveDigits_zero_one_integral.measurePreserving_digitSeq
  let d : ℕ → ℕ := fun i => if h : i < n then c ⟨i, h⟩ else 0
  have hd (j : Fin n) : d j = c j := by simp [d, j.isLt]
  have hset : {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      lurothDigitSeq ⁻¹' (Set.pi (Finset.range n : Set ℕ) fun i => {d i}) ∩ Set.Ioc 0 1 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi,
      Finset.coe_range, Set.mem_Iio, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨fun i hi => by simpa [d, hi] using h ⟨i, hi⟩, hx⟩
    · rintro ⟨h, hx⟩
      exact ⟨hx, fun j => (h j j.isLt).trans (hd j)⟩
  rw [hset, ← Measure.restrict_apply' measurableSet_Ioc,
    hmp.measure_preimage
      (MeasurableSet.pi (Set.to_countable _) fun _ _ => .of_discrete).nullMeasurableSet,
    Measure.infinitePi_pi (X := fun _ : ℕ => ℕ) (μ := fun _ => ν) fun _ _ => .of_discrete,
    ← Fin.prod_univ_eq_prod_range (fun i => ν {d i}) n]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hν, hd]
  split_ifs with h
  · rfl
  · obtain h0 | h1 : c j = 0 ∨ c j = 1 := by omega
    · simp [h0]
    · simp [h1]

end MetaMathlibExt
