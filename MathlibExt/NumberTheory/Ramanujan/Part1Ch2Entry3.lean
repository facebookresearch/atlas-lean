/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 3

Sum of arctan(1/(n+k)) equals π/4 plus an arctan sum in k.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry3

private lemma arctan_three_add {m : ℝ} (hm : 1 ≤ m) :
    Real.arctan (1 / (3 * m - 1)) + Real.arctan (1 / (3 * m)) +
      Real.arctan (1 / (3 * m + 1))
      = Real.arctan (1 / m) +
        Real.arctan ((10 * m) / ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1))) := by
  have hm0 : (0:ℝ) < m := by linarith
  have h1 : (0:ℝ) < 3 * m - 1 := by linarith
  have h2 : (0:ℝ) < 3 * m + 1 := by linarith
  have h3 : (0:ℝ) < 3 * m := by linarith
  have h4 : (0:ℝ) < 9 * m ^ 2 - 2 := by nlinarith [hm, sq_nonneg m]
  have h5 : (0:ℝ) < 9 * m ^ 2 - 1 := by nlinarith [hm, sq_nonneg m]
  have h7 : (0:ℝ) < 27 * m ^ 3 - 12 * m := by nlinarith [hm, sq_nonneg m]
  have h8 : (1:ℝ) < (3 * m - 1) * (3 * m + 1) := by nlinarith [hm, sq_nonneg m]
  have h9 : (2:ℝ) < 9 * m ^ 2 - 2 := by nlinarith [hm, sq_nonneg m]
  have h10 : (10:ℝ) < (3 * m ^ 2 + 2) * (9 * m ^ 2 - 1) := by
    nlinarith [hm, sq_nonneg m, sq_nonneg (m ^ 2)]
  have hGpos : (0:ℝ) < (3 * m ^ 2 + 2) * (9 * m ^ 2 - 1) :=
    mul_pos (by positivity) h5
  have nm : m ≠ 0 := ne_of_gt hm0
  have n1 : (3:ℝ) * m - 1 ≠ 0 := ne_of_gt h1
  have n2 : (3:ℝ) * m + 1 ≠ 0 := ne_of_gt h2
  have n3 : (3:ℝ) * m ≠ 0 := ne_of_gt h3
  have n4 : (9:ℝ) * m ^ 2 - 2 ≠ 0 := ne_of_gt h4
  have n7 : (27:ℝ) * m ^ 3 - 12 * m ≠ 0 := ne_of_gt h7
  have hG : (3 * m ^ 2 + 2) * (9 * m ^ 2 - 1) ≠ 0 := ne_of_gt hGpos
  have hDA : (3 * m - 1) * (3 * m + 1) ≠ 0 := mul_ne_zero n1 n2
  have hD3 : (9 * m ^ 2 - 2) * (3 * m) ≠ 0 := mul_ne_zero n4 n3
  have hDG : m * ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1)) ≠ 0 := mul_ne_zero nm hG
  have cancel : ∀ (N M D : ℝ), D ≠ 0 → M ≠ 0 → (N / D) / (M / D) = N / M := by
    intro N M D hD hM
    have hMD : M / D ≠ 0 := div_ne_zero hM hD
    rw [div_eq_iff hMD, div_mul_div_comm, div_eq_div_iff hD (mul_ne_zero hM hD)]
    ring
  have hA : (1 / (3 * m - 1)) * (1 / (3 * m + 1)) < 1 := by
    have hpos : (0:ℝ) < (3 * m - 1) * (3 * m + 1) := mul_pos h1 h2
    rw [one_div_mul_one_div, div_lt_one hpos]
    linarith
  have hMA : (3 * m - 1) * (3 * m + 1) - 1 ≠ 0 :=
    ne_of_gt (by linarith)
  have eA : Real.arctan (1 / (3 * m - 1)) + Real.arctan (1 / (3 * m + 1))
      = Real.arctan (6 * m / (9 * m ^ 2 - 2)) := by
    have eAnum : 1 / (3 * m - 1) + 1 / (3 * m + 1)
        = (1 * (3 * m + 1) + (3 * m - 1) * 1) / ((3 * m - 1) * (3 * m + 1)) := by
      rw [div_add_div _ _ n1 n2]
    have eAden : 1 - 1 / (3 * m - 1) * (1 / (3 * m + 1))
        = ((3 * m - 1) * (3 * m + 1) - 1) / ((3 * m - 1) * (3 * m + 1)) := by
      rw [one_div_mul_one_div, eq_div_iff hDA, sub_mul, div_mul_cancel₀ _ hDA,
        one_mul]
    rw [Real.arctan_add hA, eAnum, eAden, cancel _ _ _ hDA hMA]
    congr 1
    rw [div_eq_div_iff hMA n4]
    ring
  have hB : (6 * m / (9 * m ^ 2 - 2)) * (1 / (3 * m)) < 1 := by
    have heqB2 : (6 * m / (9 * m ^ 2 - 2)) * (1 / (3 * m))
        = 2 / (9 * m ^ 2 - 2) := by
      rw [div_mul_div_comm, div_eq_div_iff hD3 n4]
      ring
    rw [heqB2, div_lt_one h4]
    linarith
  have hMB : (9 * m ^ 2 - 2) * (3 * m) - 6 * m * 1 ≠ 0 :=
    ne_of_gt (by nlinarith [h7])
  have eB : Real.arctan (6 * m / (9 * m ^ 2 - 2)) + Real.arctan (1 / (3 * m))
      = Real.arctan ((27 * m ^ 2 - 2) / (27 * m ^ 3 - 12 * m)) := by
    have eBnum : 6 * m / (9 * m ^ 2 - 2) + 1 / (3 * m)
        = (6 * m * (3 * m) + (9 * m ^ 2 - 2) * 1) / ((9 * m ^ 2 - 2) * (3 * m)) := by
      rw [div_add_div _ _ n4 n3]
    have eBden : 1 - 6 * m / (9 * m ^ 2 - 2) * (1 / (3 * m))
        = ((9 * m ^ 2 - 2) * (3 * m) - 6 * m * 1) / ((9 * m ^ 2 - 2) * (3 * m)) := by
      rw [div_mul_div_comm, eq_div_iff hD3, sub_mul, div_mul_cancel₀ _ hD3,
        one_mul]
    rw [Real.arctan_add hB, eBnum, eBden, cancel _ _ _ hD3 hMB]
    congr 1
    rw [div_eq_div_iff hMB n7]
    ring
  have heqC : (1 / m) * ((10 * m) / ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1)))
      = 10 / ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1)) := by
    rw [div_mul_div_comm, div_eq_div_iff hDG hG]
    ring
  have hC : (1 / m) * ((10 * m) / ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1))) < 1 := by
    rw [heqC, div_lt_one hGpos]
    linarith
  have hMC : m * ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1)) - 1 * (10 * m) ≠ 0 := by
    have h1' : (0:ℝ) < ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1)) - 10 := by linarith
    have h2' := mul_pos hm0 h1'
    apply ne_of_gt
    linarith
  have eC : Real.arctan (1 / m) +
        Real.arctan ((10 * m) / ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1)))
      = Real.arctan ((27 * m ^ 2 - 2) / (27 * m ^ 3 - 12 * m)) := by
    have eCnum : 1 / m + (10 * m) / ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1))
        = (1 * ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1)) + m * (10 * m)) /
          (m * ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1))) := by
      rw [div_add_div _ _ nm hG]
    have eCden : 1 - (1 / m) * ((10 * m) / ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1)))
        = (m * ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1)) - 1 * (10 * m)) /
          (m * ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1))) := by
      rw [div_mul_div_comm, eq_div_iff hDG, sub_mul, div_mul_cancel₀ _ hDG,
        one_mul]
    rw [Real.arctan_add hC, eCnum, eCden, cancel _ _ _ hDG hMC]
    congr 1
    rw [div_eq_div_iff hMC n7]
    ring
  calc Real.arctan (1 / (3 * m - 1)) + Real.arctan (1 / (3 * m)) +
        Real.arctan (1 / (3 * m + 1))
      = (Real.arctan (1 / (3 * m - 1)) + Real.arctan (1 / (3 * m + 1))) +
        Real.arctan (1 / (3 * m)) := by ring
    _ = Real.arctan (6 * m / (9 * m ^ 2 - 2)) + Real.arctan (1 / (3 * m)) := by
        rw [eA]
    _ = Real.arctan ((27 * m ^ 2 - 2) / (27 * m ^ 3 - 12 * m)) := eB
    _ = Real.arctan (1 / m) +
        Real.arctan ((10 * m) / ((3 * m ^ 2 + 2) * (9 * m ^ 2 - 1))) := eC.symm

private lemma reindex_sum (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (2 * n + 1), Real.arctan (1 / ((↑n + ↑k : ℝ))))
      = ∑ j ∈ Finset.Icc (n + 1) (3 * n + 1), Real.arctan (1 / ((↑j : ℝ))) := by
  have eimg : n + (2 * n + 1) = 3 * n + 1 := by omega
  have himg : Finset.image (fun k => n + k) (Finset.Icc 1 (2 * n + 1))
      = Finset.Icc (n + 1) (3 * n + 1) := by
    have h := Finset.image_add_left_Icc 1 (2 * n + 1) n
    rw [eimg] at h
    exact h
  have hinj : Set.InjOn (fun k => n + k) ↑(Finset.Icc 1 (2 * n + 1)) := by
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  calc (∑ k ∈ Finset.Icc 1 (2 * n + 1), Real.arctan (1 / ((↑n + ↑k : ℝ))))
      = ∑ k ∈ Finset.Icc 1 (2 * n + 1),
          Real.arctan (1 / (((n + k : ℕ)) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.cast_add]
    _ = ∑ j ∈ Finset.Icc (n + 1) (3 * n + 1), Real.arctan (1 / ((↑j : ℝ))) := by
        rw [← himg, Finset.sum_image hinj]

private lemma window_step (n : ℕ) :
    (∑ j ∈ Finset.Icc (n + 2) (3 * n + 4), Real.arctan (1 / ((↑j : ℝ))))
      = (∑ j ∈ Finset.Icc (n + 1) (3 * n + 1), Real.arctan (1 / ((↑j : ℝ))))
        - Real.arctan (1 / (((n + 1 : ℕ)) : ℝ))
        + (Real.arctan (1 / (((3 * n + 2 : ℕ)) : ℝ))
          + Real.arctan (1 / (((3 * n + 3 : ℕ)) : ℝ))
          + Real.arctan (1 / (((3 * n + 4 : ℕ)) : ℝ))) := by
  have hsplit : Finset.Icc (n + 1) (3 * n + 1)
      = insert (n + 1) (Finset.Icc (n + 2) (3 * n + 1)) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnot : (n + 1) ∉ Finset.Icc (n + 2) (3 * n + 1) := by
    rw [Finset.mem_Icc]
    omega
  have q1 : (∑ j ∈ Finset.Icc (n + 2) (3 * n + 3), Real.arctan (1 / ((↑j : ℝ))))
        + Real.arctan (1 / (((3 * n + 4 : ℕ)) : ℝ))
      = ∑ j ∈ Finset.Icc (n + 2) (3 * n + 4), Real.arctan (1 / ((↑j : ℝ))) :=
    (Finset.sum_Icc_succ_top (a := n + 2) (b := 3 * n + 3)
      (show n + 2 ≤ (3 * n + 3) + 1 from by omega) _).symm
  have q2 : (∑ j ∈ Finset.Icc (n + 2) (3 * n + 2), Real.arctan (1 / ((↑j : ℝ))))
        + Real.arctan (1 / (((3 * n + 3 : ℕ)) : ℝ))
      = ∑ j ∈ Finset.Icc (n + 2) (3 * n + 3), Real.arctan (1 / ((↑j : ℝ))) :=
    (Finset.sum_Icc_succ_top (a := n + 2) (b := 3 * n + 2)
      (show n + 2 ≤ (3 * n + 2) + 1 from by omega) _).symm
  have q3 : (∑ j ∈ Finset.Icc (n + 2) (3 * n + 1), Real.arctan (1 / ((↑j : ℝ))))
        + Real.arctan (1 / (((3 * n + 2 : ℕ)) : ℝ))
      = ∑ j ∈ Finset.Icc (n + 2) (3 * n + 2), Real.arctan (1 / ((↑j : ℝ))) :=
    (Finset.sum_Icc_succ_top (a := n + 2) (b := 3 * n + 1)
      (show n + 2 ≤ (3 * n + 1) + 1 from by omega) _).symm
  rw [hsplit, Finset.sum_insert hnot]
  linarith

private lemma window_sum : ∀ n : ℕ,
    (∑ j ∈ Finset.Icc (n + 1) (3 * n + 1), Real.arctan (1 / ((↑j : ℝ))))
      = Real.pi / 4 + ∑ k ∈ Finset.Icc 1 n,
        Real.arctan ((10 * (↑k : ℝ)) / ((3 * (↑k : ℝ) ^ 2 + 2) * (9 * (↑k : ℝ) ^ 2 - 1))) := by
  intro n
  induction n with
  | zero =>
      have eI : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      have eJ : Finset.Icc (0 + 1) (3 * 0 + 1) = {1} := by decide
      rw [eI, eJ, Finset.sum_empty, Finset.sum_singleton, add_zero]
      have c1 : ((1 : ℕ):ℝ) = 1 := Nat.cast_one
      rw [c1, div_one]
      exact Real.arctan_one
  | succ n ih =>
      have hR : (∑ k ∈ Finset.Icc 1 (n + 1),
            Real.arctan ((10 * (↑k : ℝ)) / ((3 * (↑k : ℝ) ^ 2 + 2) * (9 * (↑k : ℝ) ^ 2 - 1))))
          = (∑ k ∈ Finset.Icc 1 n,
            Real.arctan ((10 * (↑k : ℝ)) / ((3 * (↑k : ℝ) ^ 2 + 2) * (9 * (↑k : ℝ) ^ 2 - 1))))
            + Real.arctan ((10 * (↑(n + 1) : ℝ)) / ((3 * (↑(n + 1) : ℝ) ^ 2 + 2) * (9 * (↑(n + 1) : ℝ) ^ 2 - 1))) :=
        Finset.sum_Icc_succ_top (a := 1) (b := n) (show (1:ℕ) ≤ n + 1 from by omega) _
      have eT : Finset.Icc ((n + 1) + 1) (3 * (n + 1) + 1)
          = Finset.Icc (n + 2) (3 * n + 4) := by
        ext x
        simp only [Finset.mem_Icc]
        omega
      rw [eT, hR]
      have hs := window_step n
      have hm1 : (1:ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := by
        have hle : 1 ≤ n + 1 := by omega
        exact_mod_cast hle
      have keyapp := arctan_three_add (m := (((n + 1 : ℕ)) : ℝ)) hm1
      have e1 : (((3 * n + 2 : ℕ)) : ℝ) = 3 * (((n + 1 : ℕ)) : ℝ) - 1 := by
        push_cast
        ring
      have e2 : (((3 * n + 3 : ℕ)) : ℝ) = 3 * (((n + 1 : ℕ)) : ℝ) := by
        push_cast
        ring
      have e3 : (((3 * n + 4 : ℕ)) : ℝ) = 3 * (((n + 1 : ℕ)) : ℝ) + 1 := by
        push_cast
        ring
      rw [← e1, ← e3, ← e2] at keyapp
      linarith

/-- **Ramanujan's arctangent identity for $\sum_{k=1}^{2n+1} \arctan(1/(n+k))$, $n \ge 0$.**
For every natural number $n$,
$$\sum_{k=1}^{2n+1} \arctan \frac{1}{n+k} = \frac{\pi}{4} +
\sum_{k=1}^{n} \arctan \frac{10k}{(3k^2 + 2)(9k^2 - 1)}.$$

This is Ramanujan's Entry 3 of Chapter 2 without the hypothesis $n \ge 1$; at $n = 0$ both sides
are $\pi/4$. -/
theorem ramanujan_part1_ch2_entry3_general (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * n + 1), Real.arctan (1 / ((↑n + ↑k : ℝ))) =
      Real.pi / 4 + ∑ k ∈ Finset.Icc 1 n,
          Real.arctan ((10 * (↑k : ℝ)) / ((3 * (↑k : ℝ) ^ 2 + 2) * (9 * (↑k : ℝ) ^ 2 - 1))) := by
  rw [reindex_sum n]
  exact window_sum n

set_option linter.unusedVariables false in
/-- **Ramanujan's arctangent identity for $\sum_{k=1}^{2n+1} \arctan(1/(n+k))$.** For every
positive integer $n$,
$$\sum_{k=1}^{2n+1} \arctan \frac{1}{n+k} = \frac{\pi}{4} +
\sum_{k=1}^{n} \arctan \frac{10k}{(3k^2 + 2)(9k^2 - 1)}.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    3, formula (3.1), printed p. 27 / PDF p. 37.
Proves `Wanted` entry `ramanujan_part1_ch2_entry3`.
-/
theorem ramanujan_part1_ch2_entry3 (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 (2 * n + 1), Real.arctan (1 / ((↑n + ↑k : ℝ))) =
      Real.pi / 4 + ∑ k ∈ Finset.Icc 1 n,
          Real.arctan ((10 * (↑k : ℝ)) / ((3 * (↑k : ℝ) ^ 2 + 2) * (9 * (↑k : ℝ) ^ 2 - 1))) :=
  by apply ramanujan_part1_ch2_entry3_general <;> assumption

end Entry3

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
