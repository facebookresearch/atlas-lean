/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import MathlibExt.NumberTheory.DivisibilityRuns

/-!
# Divisor-sum formula for the length-four run count

The length-four run count `divRunCount B 4` is expressed as a divisor sum over
the pairs $(x, y)$ with $x$, $y$, $x + y$ and $x + 2y$ all nonzero, in the
unscaled form counting triples $(a, b, c)$ and in the scaled form counting
triples $(\alpha, \beta, \gamma)$ with $a = x\alpha$, $b = y\beta$ and
$c = (x + y)\gamma$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 7
(`integers-2026-A122-prop-7`).
-/

@[expose] public section

namespace MetaMathlibExt

namespace divRunCount_four

private theorem isDivRunUpTo_four (x y a b c : ℤ) :
    IsDivRunUpTo x y a b c 4 ↔
      (x ≠ 0 ∧ x ∣ a) ∧ (y ≠ 0 ∧ y ∣ b) ∧ (x + y ≠ 0 ∧ x + y ∣ c) ∧
        (x + 2 * y ≠ 0 ∧ x + 2 * y ∣ a + b + c) := by
  have g2 : gibonacciNumber x y 2 = x + y := by
    change y + x = x + y; ring
  have g3 : gibonacciNumber x y 3 = x + 2 * y := by
    change (y + x) + y = x + 2 * y; ring
  have t3 : generalizedTribonacci a b c 3 = a + b + c := by
    change c + b + a = a + b + c; ring
  constructor
  · intro h
    have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    simp only [gibonacciNumber, generalizedTribonacci] at h0 h1 h2 h3
    obtain ⟨h2ne, h2dvd⟩ := h2
    obtain ⟨h3ne, h3dvd⟩ := h3
    refine ⟨h0, h1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [add_comm x y]; exact h2ne
    · rw [add_comm x y]; exact h2dvd
    · rw [show x + 2 * y = y + x + y by ring]; exact h3ne
    · rw [show x + 2 * y = y + x + y by ring, show a + b + c = c + b + a by ring]
      exact h3dvd
  · rintro ⟨h0, h1, h2, h3⟩ i hi
    have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi4 with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · rw [g2]; exact h2
    · rw [g3, t3]; exact h3

private theorem sum_triple (B : ℕ) (x y : ℤ) :
    (∑ t ∈ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B,
      if (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
          IsDivRunUpTo x y t.1 t.2.1 t.2.2 4 then (1 : ℤ) else 0) =
    if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0 then
      (((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
          Finset.Icc (-(B : ℤ)) B).filter fun t =>
            x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 ∧
              x + 2 * y ∣ t.1 + t.2.1 + t.2.2).card : ℤ) - 1
    else 0 := by
  by_cases hc : x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0
  · obtain ⟨hx, hy, hxy, hx2y⟩ := hc
    have hc' : x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0 := ⟨hx, hy, hxy, hx2y⟩
    rw [ite_eq_left hc']
    have hmem : (0, 0, 0) ∈ (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter fun t =>
          x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 ∧
            x + 2 * y ∣ t.1 + t.2.1 + t.2.2 := by
      simp [dvd_zero]
    have hfilter : (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter (fun t =>
          (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
            IsDivRunUpTo x y t.1 t.2.1 t.2.2 4) =
        ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
          Finset.Icc (-(B : ℤ)) B).filter fun t =>
            x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 ∧
              x + 2 * y ∣ t.1 + t.2.1 + t.2.2).erase (0, 0, 0) := by
      ext t
      obtain ⟨a, b, c⟩ := t
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨ht, -, htne, hrun⟩
        obtain ⟨⟨-, hqa⟩, ⟨-, hqb⟩, ⟨-, hqc⟩, ⟨-, hqd⟩⟩ :=
          (isDivRunUpTo_four x y a b c).mp hrun
        exact ⟨htne, ht, hqa, hqb, hqc, hqd⟩
      · rintro ⟨htne, ht, hq⟩
        exact ⟨ht, fun h => hx (Prod.ext_iff.mp h).1, htne,
          (isDivRunUpTo_four x y a b c).mpr
            ⟨⟨hx, hq.1⟩, ⟨hy, hq.2.1⟩, ⟨hxy, hq.2.2.1⟩, ⟨hx2y, hq.2.2.2⟩⟩⟩
    rw [← Finset.natCast_card_filter, hfilter, Finset.card_erase_of_mem hmem]
    have hpos : 1 ≤ ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter fun t =>
          x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 ∧
            x + 2 * y ∣ t.1 + t.2.1 + t.2.2).card :=
      Finset.card_pos.mpr ⟨(0, 0, 0), hmem⟩
    rw [Nat.cast_sub hpos]
    simp
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro t _
    rw [ite_eq_right]
    rintro ⟨-, -, hrun⟩
    obtain ⟨⟨hxa, -⟩, ⟨hyb, -⟩, ⟨hxc, -⟩, ⟨hxd, -⟩⟩ :=
      (isDivRunUpTo_four x y t.1 t.2.1 t.2.2).mp hrun
    exact hc ⟨hxa, hyb, hxc, hxd⟩

private theorem mem_Icc_iff_natAbs_le (a : ℤ) (B : ℕ) :
    a ∈ Finset.Icc (-(B : ℤ)) B ↔ a.natAbs ≤ B := by
  simp only [Finset.mem_Icc]
  omega

private theorem card_filter_scaled (B : ℕ) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) :
    (Finset.filter (fun t => x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 ∧
        x + 2 * y ∣ t.1 + t.2.1 + t.2.2)
      (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B)).card =
    (Finset.filter (fun t => x + 2 * y ∣ x * t.1 + y * t.2.1 + (x + y) * t.2.2)
      (Finset.Icc (-((B / x.natAbs : ℕ) : ℤ)) (B / x.natAbs : ℕ) ×ˢ
        Finset.Icc (-((B / y.natAbs : ℕ) : ℤ)) (B / y.natAbs : ℕ) ×ˢ
        Finset.Icc (-((B / (x + y).natAbs : ℕ) : ℤ)) (B / (x + y).natAbs : ℕ))).card := by
  apply Finset.card_bij'
    (fun t _ => (t.1 / x, t.2.1 / y, t.2.2 / (x + y)))
    (fun t _ => (x * t.1, y * t.2.1, (x + y) * t.2.2))
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    obtain ⟨haC, hq⟩ := ha
    simp only [Finset.mem_product] at haC
    obtain ⟨ha1, ha2, ha3⟩ := haC
    have hb1 : a.1.natAbs ≤ B := (mem_Icc_iff_natAbs_le a.1 B).mp ha1
    have hb2 : a.2.1.natAbs ≤ B := (mem_Icc_iff_natAbs_le a.2.1 B).mp ha2
    have hb3 : a.2.2.natAbs ≤ B := (mem_Icc_iff_natAbs_le a.2.2 B).mp ha3
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_product]
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_Icc_iff_natAbs_le (a.1 / x) (B / x.natAbs)).mpr
          (by rw [Int.natAbs_ediv_of_dvd hq.1]; exact Nat.div_le_div_right hb1)
      · exact (mem_Icc_iff_natAbs_le (a.2.1 / y) (B / y.natAbs)).mpr
          (by rw [Int.natAbs_ediv_of_dvd hq.2.1]; exact Nat.div_le_div_right hb2)
      · exact (mem_Icc_iff_natAbs_le (a.2.2 / (x + y)) (B / (x + y).natAbs)).mpr
          (by rw [Int.natAbs_ediv_of_dvd hq.2.2.1]; exact Nat.div_le_div_right hb3)
    · rw [Int.mul_ediv_cancel' hq.1, Int.mul_ediv_cancel' hq.2.1,
        Int.mul_ediv_cancel' hq.2.2.1]
      exact hq.2.2.2
  · intro b hb
    rw [Finset.mem_filter] at hb ⊢
    obtain ⟨hbC, hq⟩ := hb
    simp only [Finset.mem_product] at hbC
    obtain ⟨hb1, hb2, hb3⟩ := hbC
    have hc1 : b.1.natAbs ≤ B / x.natAbs :=
      (mem_Icc_iff_natAbs_le b.1 (B / x.natAbs)).mp hb1
    have hc2 : b.2.1.natAbs ≤ B / y.natAbs :=
      (mem_Icc_iff_natAbs_le b.2.1 (B / y.natAbs)).mp hb2
    have hc3 : b.2.2.natAbs ≤ B / (x + y).natAbs :=
      (mem_Icc_iff_natAbs_le b.2.2 (B / (x + y).natAbs)).mp hb3
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_product]
      refine ⟨?_, ?_, ?_⟩
      · exact (mem_Icc_iff_natAbs_le (x * b.1) B).mpr (by
          rw [Int.natAbs_mul]
          calc x.natAbs * b.1.natAbs ≤ x.natAbs * (B / x.natAbs) :=
                Nat.mul_le_mul le_rfl hc1
            _ = B / x.natAbs * x.natAbs := by rw [mul_comm]
            _ ≤ B := Nat.div_mul_le_self B x.natAbs)
      · exact (mem_Icc_iff_natAbs_le (y * b.2.1) B).mpr (by
          rw [Int.natAbs_mul]
          calc y.natAbs * b.2.1.natAbs ≤ y.natAbs * (B / y.natAbs) :=
                Nat.mul_le_mul le_rfl hc2
            _ = B / y.natAbs * y.natAbs := by rw [mul_comm]
            _ ≤ B := Nat.div_mul_le_self B y.natAbs)
      · exact (mem_Icc_iff_natAbs_le ((x + y) * b.2.2) B).mpr (by
          rw [Int.natAbs_mul]
          calc (x + y).natAbs * b.2.2.natAbs ≤ (x + y).natAbs * (B / (x + y).natAbs) :=
                Nat.mul_le_mul le_rfl hc3
            _ = B / (x + y).natAbs * (x + y).natAbs := by rw [mul_comm]
            _ ≤ B := Nat.div_mul_le_self B (x + y).natAbs)
    · exact ⟨dvd_mul_right x b.1, dvd_mul_right y b.2.1, dvd_mul_right (x + y) b.2.2, hq⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨-, hq⟩ := ha
    obtain ⟨a1, a2, a3⟩ := a
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · exact Int.mul_ediv_cancel' hq.1
    · exact Int.mul_ediv_cancel' hq.2.1
    · exact Int.mul_ediv_cancel' hq.2.2.1
  · intro b hb
    obtain ⟨b1, b2, b3⟩ := b
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · exact Int.mul_ediv_cancel_left b1 hx
    · exact Int.mul_ediv_cancel_left b2 hy
    · exact Int.mul_ediv_cancel_left b3 hxy
end divRunCount_four


/-- **Divisor-sum formula for the length-four run count.** For a natural number $B$, let $A_B(4)$
be the number of integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $4$. For integers $x, y$
let $T_B(x, y)$ be the number of integer triples $(a, b, c) \in [-B, B]^3$ with $x \mid a$,
$y \mid b$, $x + y \mid c$ and $x + 2y \mid a + b + c$, and let $T'_B(x, y)$ be the number of
integer triples $(\alpha, \beta, \gamma)$ with $|\alpha| \le \lfloor B/|x| \rfloor$,
$|\beta| \le \lfloor B/|y| \rfloor$, $|\gamma| \le \lfloor B/|x+y| \rfloor$ and
$x + 2y \mid x\alpha + y\beta + (x+y)\gamma$. Then
$$A_B(4) = \sum_{x, y} \left(T_B(x, y) - 1\right) = \sum_{x, y} \left(T'_B(x, y) - 1\right),$$
where both sums run over the integers $x, y \in [-B, B]$ with $x \ne 0$, $y \ne 0$, $x + y \ne 0$
and $x + 2y \ne 0$.

The second form comes from writing $a = x\alpha$, $b = y\beta$, $c = (x+y)\gamma$; it is the
paper's $\sum \chi_{x,y}(\alpha, \beta, \gamma)$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 7
(`integers-2026-A122-prop-7`). -/
theorem divRunCount_four (B : ℕ) :
    ((divRunCount B 4 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0 then
              (((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
                  Finset.Icc (-(B : ℤ)) B).filter fun t =>
                    x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 ∧
                      x + 2 * y ∣ t.1 + t.2.1 + t.2.2).card : ℤ) - 1
            else 0) ∧
    (divRunCount B 4 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0 then
              (((Finset.Icc (-((B / x.natAbs : ℕ) : ℤ)) (B / x.natAbs : ℕ) ×ˢ
                  Finset.Icc (-((B / y.natAbs : ℕ) : ℤ)) (B / y.natAbs : ℕ) ×ˢ
                  Finset.Icc (-((B / (x + y).natAbs : ℕ) : ℤ)) (B / (x + y).natAbs : ℕ)).filter
                    fun t => x + 2 * y ∣ x * t.1 + y * t.2.1 + (x + y) * t.2.2).card : ℤ) - 1
            else 0 := by
  have hfirst : (divRunCount B 4 : ℤ) =
      ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0 then
          (((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
              Finset.Icc (-(B : ℤ)) B).filter fun t =>
                x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 ∧
                  x + 2 * y ∣ t.1 + t.2.1 + t.2.2).card : ℤ) - 1
        else 0 := by
    have hdecomp : (divRunCount B 4 : ℤ) =
        ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          ∑ t ∈ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
              Finset.Icc (-(B : ℤ)) B,
            if (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
                IsDivRunUpTo x y t.1 t.2.1 t.2.2 4 then (1 : ℤ) else 0 := by
      unfold divRunCount
      rw [Finset.natCast_card_filter]
      simp only [Finset.sum_product]
    rw [hdecomp]
    exact Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => divRunCount_four.sum_triple B x y
  refine ⟨hfirst, ?_⟩
  rw [hfirst]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hc : x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0
  · rw [ite_eq_left hc, ite_eq_left hc,
      divRunCount_four.card_filter_scaled B x y hc.1 hc.2.1 hc.2.2.1]
  · rw [ite_eq_right hc, ite_eq_right hc]

end MetaMathlibExt
