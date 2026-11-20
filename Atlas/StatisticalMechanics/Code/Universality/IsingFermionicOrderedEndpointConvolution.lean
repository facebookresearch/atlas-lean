/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointEscape










namespace StatMech.Universality

open Finset

noncomputable section

private theorem reversed_one_div_sqrt_sum_le (k : Nat) :
    (∑ j ∈ Finset.range k,
        1 / Real.sqrt ((k - j + 1 : Nat) : Real)) <=
      2 * Real.sqrt (k + 1 : Real) := by
  have hreflect :
      (∑ j ∈ Finset.range k,
          1 / Real.sqrt ((k - 1 - j + 2 : Nat) : Real)) =
        ∑ j ∈ Finset.range k,
          1 / Real.sqrt ((j + 2 : Nat) : Real) :=
    Finset.sum_range_reflect
      (fun j => 1 / Real.sqrt ((j + 2 : Nat) : Real)) k
  have heq :
      (∑ j ∈ Finset.range k,
          1 / Real.sqrt ((k - j + 1 : Nat) : Real)) =
        ∑ j ∈ Finset.range k,
          1 / Real.sqrt ((j + 2 : Nat) : Real) := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hindex : k - j + 1 = k - 1 - j + 2 := by omega
    rw [hindex]
  rw [heq]
  calc
    (∑ j ∈ Finset.range k,
        1 / Real.sqrt ((j + 2 : Nat) : Real)) <=
        ∑ j ∈ Finset.range k,
          1 / Real.sqrt ((j + 1 : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le
      · exact Real.sqrt_pos.2 (by positivity)
      · exact Real.sqrt_le_sqrt (by norm_num)
    _ <= ∑ j ∈ Finset.range (k + 1),
          1 / Real.sqrt ((j + 1 : Nat) : Real) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.le_succ k)
      · intro j hj hj'
        positivity
    _ <= 2 * Real.sqrt (k + 1 : Real) := by
      simpa [Nat.cast_add, Nat.cast_one] using sum_one_div_sqrt_succ_le k

private theorem one_div_mul_sqrt_succ_le_three_diff (l : Nat) :
    1 / (((l + 1 : Nat) : Real) *
        Real.sqrt ((l + 2 : Nat) : Real)) <=
      3 * (1 / Real.sqrt ((l + 1 : Nat) : Real) -
        1 / Real.sqrt ((l + 2 : Nat) : Real)) := by
  let x := Real.sqrt ((l + 1 : Nat) : Real)
  let y := Real.sqrt ((l + 2 : Nat) : Real)
  have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
  have hy : 0 < y := Real.sqrt_pos.2 (by positivity)
  have hx2 : x ^ 2 = ((l + 1 : Nat) : Real) := by
    dsimp [x]
    rw [Real.sq_sqrt]
    positivity
  have hy2 : y ^ 2 = ((l + 2 : Nat) : Real) := by
    dsimp [y]
    rw [Real.sq_sqrt]
    positivity
  norm_num [Nat.cast_add, Nat.cast_one] at hx2 hy2
  have hxone : 1 <= x ^ 2 := by
    rw [hx2]
    have hl0 : (0 : Real) <= l := by positivity
    linarith
  have hyx : y <= 2 * x := by
    nlinarith
  have hxy : x <= y := by nlinarith
  have hsum : y + x <= 3 * x := by linarith
  have hid : (y - x) * (y + x) = 1 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hxy)
  have hone : 1 <= 3 * x * (y - x) := by nlinarith
  change 1 / (((l + 1 : Nat) : Real) * y) <=
    3 * (1 / x - 1 / y)
  have hcast : (((l + 1 : Nat) : Real)) = x ^ 2 := by
    norm_num [Nat.cast_add, Nat.cast_one]
    exact hx2.symm
  rw [hcast]
  field_simp [hx.ne', hy.ne']
  nlinarith



theorem laterEndpointVerticalKernel_tail_le (j N : Nat) :
    (∑ l ∈ Finset.range N,
      (2 / ((j + l + 1 : Nat) : Real)) *
        (2 / Real.sqrt ((l + 2 : Nat) : Real))) <=
      32 / Real.sqrt ((j + 1 : Nat) : Real) := by
  let f : Nat -> Real := fun l =>
    (2 / ((j + l + 1 : Nat) : Real)) *
      (2 / Real.sqrt ((l + 2 : Nat) : Real))
  have hjpos : 0 < ((j + 1 : Nat) : Real) := by positivity
  have hhead (M : Nat) (hM : M <= j + 1) :
      (∑ l ∈ Finset.range M, f l) <=
        16 / Real.sqrt ((j + 1 : Nat) : Real) := by
    have hsum :
        (∑ l ∈ Finset.range M,
          1 / Real.sqrt ((l + 1 : Nat) : Real)) <=
          2 * Real.sqrt ((M + 1 : Nat) : Real) := by
      calc
        _ <= ∑ l ∈ Finset.range (M + 1),
            1 / Real.sqrt ((l + 1 : Nat) : Real) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_mono (Nat.le_succ M)
          · intro l hl hl'
            positivity
        _ <= 2 * Real.sqrt ((M + 1 : Nat) : Real) := by
          simpa [Nat.cast_add, Nat.cast_one] using
            sum_one_div_sqrt_succ_le M
    have hsqrt : Real.sqrt ((M + 1 : Nat) : Real) <=
        2 * Real.sqrt ((j + 1 : Nat) : Real) := by
      have hsqM : Real.sqrt ((M + 1 : Nat) : Real) ^ 2 =
          ((M + 1 : Nat) : Real) := Real.sq_sqrt (by positivity)
      have hsqj : Real.sqrt ((j + 1 : Nat) : Real) ^ 2 =
          ((j + 1 : Nat) : Real) := Real.sq_sqrt (by positivity)
      have hcast : ((M + 1 : Nat) : Real) <=
          2 * ((j + 1 : Nat) : Real) := by exact_mod_cast (by omega :
            M + 1 <= 2 * (j + 1))
      nlinarith [Real.sqrt_nonneg ((M + 1 : Nat) : Real),
        Real.sqrt_nonneg ((j + 1 : Nat) : Real)]
    calc
      (∑ l ∈ Finset.range M, f l) <=
          ∑ l ∈ Finset.range M,
            (4 / ((j + 1 : Nat) : Real)) *
              (1 / Real.sqrt ((l + 1 : Nat) : Real)) := by
        apply Finset.sum_le_sum
        intro l hl
        dsimp [f]
        have hjl : ((j + 1 : Nat) : Real) <=
            ((j + l + 1 : Nat) : Real) := by exact_mod_cast (by omega :
              j + 1 <= j + l + 1)
        have hs : Real.sqrt ((l + 1 : Nat) : Real) <=
            Real.sqrt ((l + 2 : Nat) : Real) :=
          Real.sqrt_le_sqrt (by norm_num)
        have hspos := Real.sqrt_pos.2 (by positivity :
          (0 : Real) < ((l + 1 : Nat) : Real))
        have hspos' := Real.sqrt_pos.2 (by positivity :
          (0 : Real) < ((l + 2 : Nat) : Real))
        rw [show (2 / ((j + l + 1 : Nat) : Real)) *
              (2 / Real.sqrt ((l + 2 : Nat) : Real)) =
            4 / (((j + l + 1 : Nat) : Real) *
              Real.sqrt ((l + 2 : Nat) : Real)) by ring,
          show (4 / ((j + 1 : Nat) : Real)) *
              (1 / Real.sqrt ((l + 1 : Nat) : Real)) =
            4 / (((j + 1 : Nat) : Real) *
              Real.sqrt ((l + 1 : Nat) : Real)) by ring]
        apply div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hjpos hspos)
        exact mul_le_mul hjl hs hspos.le (by positivity)
      _ = (4 / ((j + 1 : Nat) : Real)) *
          (∑ l ∈ Finset.range M,
            1 / Real.sqrt ((l + 1 : Nat) : Real)) := by
        rw [Finset.mul_sum]
      _ <= (4 / ((j + 1 : Nat) : Real)) *
          (2 * Real.sqrt ((M + 1 : Nat) : Real)) := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity
      _ <= 16 / Real.sqrt ((j + 1 : Nat) : Real) := by
        have hmul := mul_le_mul_of_nonneg_left hsqrt
          (by positivity : 0 <= 8 / ((j + 1 : Nat) : Real))
        calc
          (4 / ((j + 1 : Nat) : Real)) *
              (2 * Real.sqrt ((M + 1 : Nat) : Real)) =
              (8 / ((j + 1 : Nat) : Real)) *
                Real.sqrt ((M + 1 : Nat) : Real) := by ring
          _ <= (8 / ((j + 1 : Nat) : Real)) *
              (2 * Real.sqrt ((j + 1 : Nat) : Real)) := hmul
          _ = 16 / Real.sqrt ((j + 1 : Nat) : Real) := by
            have hsjne : Real.sqrt ((j + 1 : Nat) : Real) ≠ 0 :=
              (Real.sqrt_pos.2 (by positivity)).ne'
            have hsq : Real.sqrt ((j + 1 : Nat) : Real) ^ 2 =
                (((j + 1 : Nat) : Real)) :=
              Real.sq_sqrt (by positivity)
            field_simp [hsjne]
            nlinarith
  by_cases hN : N <= j + 1
  · exact (hhead N hN).trans (by
      apply mul_le_mul_of_nonneg_right (show (16 : Real) <= 32 by norm_num)
      positivity)
  · have hjN : j + 1 <= N := by omega
    have hsplit := Finset.sum_range_add_sum_Ico f hjN
    have htail : (∑ l ∈ Finset.Ico (j + 1) N, f l) <=
        12 / Real.sqrt ((j + 1 : Nat) : Real) := by
      let g : Nat -> Real := fun l =>
        1 / Real.sqrt ((l + 1 : Nat) : Real)
      have hterm (l : Nat) (hl : l ∈ Finset.Ico (j + 1) N) :
          f l <= 12 * (g l - g (l + 1)) := by
        have hjl : ((l + 1 : Nat) : Real) <=
            ((j + l + 1 : Nat) : Real) := by exact_mod_cast (by omega :
              l + 1 <= j + l + 1)
        have hbase := one_div_mul_sqrt_succ_le_three_diff l
        dsimp [f, g]
        have hden : 0 < ((l + 1 : Nat) : Real) *
            Real.sqrt ((l + 2 : Nat) : Real) := by positivity
        calc
          (2 / ((j + l + 1 : Nat) : Real)) *
                (2 / Real.sqrt ((l + 2 : Nat) : Real)) <=
              4 / (((l + 1 : Nat) : Real) *
                Real.sqrt ((l + 2 : Nat) : Real)) := by
            rw [show (2 / ((j + l + 1 : Nat) : Real)) *
                (2 / Real.sqrt ((l + 2 : Nat) : Real)) =
              4 / (((j + l + 1 : Nat) : Real) *
                Real.sqrt ((l + 2 : Nat) : Real)) by ring]
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (mul_le_mul_of_nonneg_right hjl (by positivity))
          _ = 4 * (1 / (((l + 1 : Nat) : Real) *
                Real.sqrt ((l + 2 : Nat) : Real))) := by ring
          _ <= 4 * (3 *
              (1 / Real.sqrt ((l + 1 : Nat) : Real) -
                1 / Real.sqrt ((l + 2 : Nat) : Real))) :=
            mul_le_mul_of_nonneg_left hbase (by norm_num)
          _ = _ := by
            rw [show l + 1 + 1 = l + 2 by omega]
            ring
      calc
        (∑ l ∈ Finset.Ico (j + 1) N, f l) <=
            ∑ l ∈ Finset.Ico (j + 1) N,
              12 * (g l - g (l + 1)) :=
          Finset.sum_le_sum hterm
        _ = 12 * (g (j + 1) - g N) := by
          have htelOpp := Finset.sum_Ico_sub g hjN
          have htel :
              (∑ l ∈ Finset.Ico (j + 1) N,
                (g l - g (l + 1))) = g (j + 1) - g N := by
            calc
              _ = -(∑ l ∈ Finset.Ico (j + 1) N,
                    (g (l + 1) - g l)) := by
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro l hl
                ring
              _ = -(g N - g (j + 1)) := by rw [htelOpp]
              _ = g (j + 1) - g N := by ring
          calc
            (∑ l ∈ Finset.Ico (j + 1) N,
                12 * (g l - g (l + 1))) =
                12 * (∑ l ∈ Finset.Ico (j + 1) N,
                  (g l - g (l + 1))) := by rw [Finset.mul_sum]
            _ = 12 * (g (j + 1) - g N) := by rw [htel]
        _ <= 12 * g (j + 1) := by
          have hgN : 0 <= g N := by
            dsimp [g]
            positivity
          nlinarith
        _ <= 12 / Real.sqrt ((j + 1 : Nat) : Real) := by
          dsimp [g]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa only [one_div] using
            (one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
              (Real.sqrt_le_sqrt (by norm_num :
                (((j + 1 : Nat) : Real) <= (j + 1 + 1 : Nat)))))
    rw [← hsplit]
    calc
      (∑ l ∈ Finset.range (j + 1), f l) +
          ∑ l ∈ Finset.Ico (j + 1) N, f l <=
        16 / Real.sqrt ((j + 1 : Nat) : Real) +
          12 / Real.sqrt ((j + 1 : Nat) : Real) :=
        add_le_add (hhead (j + 1) le_rfl) htail
      _ <= 32 / Real.sqrt ((j + 1 : Nat) : Real) := by
        ring_nf
        apply mul_le_mul_of_nonneg_left (show (28 : Real) <= 32 by norm_num)
        positivity





theorem orderedFarFirstEndpoint_swapped_convolution_le
    (T : Nat) (b : Nat -> Real) (hb0 : forall j, 0 <= b j) :
    (∑ j ∈ Finset.range (T + 1), b j *
      (∑ l ∈ Finset.range (T - j),
        (2 / ((j + l + 1 : Nat) : Real)) *
          (2 / Real.sqrt ((l + 2 : Nat) : Real)))) <=
      16 * (∑ j ∈ Finset.range (T + 1),
        (2 / Real.sqrt ((j + 1 : Nat) : Real)) * b j) := by
  calc
    _ <= ∑ j ∈ Finset.range (T + 1),
        b j * (32 / Real.sqrt ((j + 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (laterEndpointVerticalKernel_tail_le j (T - j)) (hb0 j)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring




theorem orderedFarFirstEndpoint_convolution_le
    (rho m T : Nat) (C : Real) (b v : Nat -> Real)
    (hρ : 0 < rho) (hρm : rho <= m) (hT : T <= rho * rho)
    (hC : 0 <= C) (hv0 : forall k, 0 <= v k)
    (hb : forall j, j <= T ->
      b j <= C * (j + 1 : Real) / (m : Real) ^ 5)
    (hvMass : (∑ k ∈ Finset.range (T + 1), v k) <= 1) :
    (∑ k ∈ Finset.range (T + 1),
      v k * (∑ j ∈ Finset.range k,
        b j * (2 / Real.sqrt ((k - j + 1 : Nat) : Real)))) <=
      32 * C / (rho : Real) ^ 2 := by
  have hm : 0 < m := lt_of_lt_of_le hρ hρm
  have hm2 : 0 < (m : Real) ^ 2 := by positivity
  have hm5 : 0 < (m : Real) ^ 5 := by positivity
  have hTReal : (T : Real) <= (rho : Real) ^ 2 := by
    exact_mod_cast (show T <= rho ^ 2 by simpa [pow_two] using hT)
  have hρmReal : (rho : Real) ^ 2 <= (m : Real) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left hρm 2
  have hinner (k : Nat) (hk : k <= T) :
      (∑ j ∈ Finset.range k,
        b j * (2 / Real.sqrt ((k - j + 1 : Nat) : Real))) <=
        32 * C / (m : Real) ^ 2 := by
    have hkFour : (k + 1 : Real) <= 4 * (m : Real) ^ 2 := by
      have hkReal : (k : Real) <= (m : Real) ^ 2 :=
        le_trans (by exact_mod_cast hk) (hTReal.trans hρmReal)
      have hmOne : (1 : Real) <= (m : Real) ^ 2 := by
        have : (1 : Nat) <= m := hm
        nlinarith [show (1 : Real) <= m by exact_mod_cast this]
      nlinarith
    have hsqrt : Real.sqrt (k + 1 : Real) <= 2 * (m : Real) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith
    have hsum := reversed_one_div_sqrt_sum_le k
    calc
      (∑ j ∈ Finset.range k,
          b j * (2 / Real.sqrt ((k - j + 1 : Nat) : Real))) <=
          ∑ j ∈ Finset.range k,
            (C * (k + 1 : Real) / (m : Real) ^ 5) *
              (2 / Real.sqrt ((k - j + 1 : Nat) : Real)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        apply mul_le_mul_of_nonneg_right
        · exact (hb j (hjk.le.trans hk)).trans (by
            apply div_le_div_of_nonneg_right _ hm5.le
            apply mul_le_mul_of_nonneg_left _ hC
            norm_num
            exact_mod_cast hjk.le)
        · positivity
      _ = (2 * C * (k + 1 : Real) / (m : Real) ^ 5) *
          (∑ j ∈ Finset.range k,
            1 / Real.sqrt ((k - j + 1 : Nat) : Real)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ <= (2 * C * (k + 1 : Real) / (m : Real) ^ 5) *
          (2 * Real.sqrt (k + 1 : Real)) := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity
      _ <= 32 * C / (m : Real) ^ 2 := by
        have hprod := mul_le_mul hkFour hsqrt (by positivity) (by positivity)
        have hprodC := mul_le_mul_of_nonneg_left hprod hC
        have hfourprod :
            4 * C * ((k + 1 : Real) * Real.sqrt (k + 1 : Real)) <=
              32 * C * (m : Real) ^ 3 := by
          nlinarith
        calc
          (2 * C * (k + 1 : Real) / (m : Real) ^ 5) *
              (2 * Real.sqrt (k + 1 : Real)) =
              (4 * C * ((k + 1 : Real) *
                Real.sqrt (k + 1 : Real))) / (m : Real) ^ 5 := by ring
          _ <= (32 * C * (m : Real) ^ 3) / (m : Real) ^ 5 :=
            div_le_div_of_nonneg_right hfourprod hm5.le
          _ = 32 * C / (m : Real) ^ 2 := by field_simp
  calc
    (∑ k ∈ Finset.range (T + 1),
        v k * (∑ j ∈ Finset.range k,
          b j * (2 / Real.sqrt ((k - j + 1 : Nat) : Real)))) <=
        ∑ k ∈ Finset.range (T + 1),
          v k * (32 * C / (m : Real) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left
      · have hks : k < Nat.succ T := by
          simpa [Nat.succ_eq_add_one] using Finset.mem_range.mp hk
        exact hinner k (Nat.lt_succ_iff.mp hks)
      · exact hv0 k
    _ = (32 * C / (m : Real) ^ 2) *
        (∑ k ∈ Finset.range (T + 1), v k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ <= 32 * C / (m : Real) ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left hvMass (by positivity :
        0 <= 32 * C / (m : Real) ^ 2)
    _ <= 32 * C / (rho : Real) ^ 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hρmReal

end

end StatMech.Universality
