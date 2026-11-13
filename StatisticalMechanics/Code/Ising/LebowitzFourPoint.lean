/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Ising.GHSInhomogeneous
import Code.FrontierA.GrahamPinnedVBGCore
import Code.FrontierA.GrahamCorrections

open scoped BigOperators
open Finset Filter Set

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.FrontierA

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def lebowitzPointField (l : V) (t : Real) : V -> Real :=
  fun x => if x = l then t else 0



theorem wJ_pointField_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (l : V) (t : Real)
    (s : ConfigSpace V) :
    wJ E J (lebowitzPointField l t) s =
      wJ E J (fun _ => 0) s *
        (Real.cosh t + spin s l * Real.sinh t) := by
  unfold wJ lebowitzPointField
  have hfield :
      (∑ x : V, (if x = l then t else 0) * spin s x) = t * spin s l := by
    simp
  rw [hfield]
  simp only [zero_mul, Finset.sum_const_zero, add_zero, Real.exp_add]
  rw [exp_mul_pm t (spin s l) (spin_eq_pm s l)]



theorem ZJ_pointField_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (l : V) (t : Real) :
    ZJ E J (lebowitzPointField l t) =
      Real.cosh t * ZJ E J (fun _ => 0) := by
  unfold ZJ
  simp_rw [wJ_pointField_eq E J l t]
  have hodd :
      (∑ s : ConfigSpace V, spin s l * wJ E J (fun _ => 0) s) = 0 := by
    have h := expJ_zero_spin_eq_zero E J l
    unfold expJ at h
    exact (div_eq_zero_iff.mp h).resolve_right (ZJ_pos E J (fun _ => 0)).ne'
  calc
    (∑ s : ConfigSpace V,
        wJ E J (fun _ => 0) s *
          (Real.cosh t + spin s l * Real.sinh t)) =
        ∑ s : ConfigSpace V,
          (Real.cosh t * wJ E J (fun _ => 0) s +
            Real.sinh t * (spin s l * wJ E J (fun _ => 0) s)) := by
              apply Finset.sum_congr rfl
              intro s _
              ring
    _ =
        Real.cosh t * (∑ s : ConfigSpace V, wJ E J (fun _ => 0) s) +
          Real.sinh t *
            (∑ s : ConfigSpace V, spin s l * wJ E J (fun _ => 0) s) := by
              rw [Finset.mul_sum, Finset.mul_sum,
                Finset.sum_add_distrib]
    _ = Real.cosh t *
        (∑ s : ConfigSpace V, wJ E J (fun _ => 0) s) := by
      rw [hodd, mul_zero, add_zero]


theorem expJ_pointField_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (l : V) (t : Real)
    (f : ConfigSpace V -> Real) :
    expJ E J (lebowitzPointField l t) f =
      expJ E J (fun _ => 0) f +
        Real.tanh t * expJ E J (fun _ => 0)
          (fun s => f s * spin s l) := by
  unfold expJ
  rw [ZJ_pointField_eq]
  simp_rw [wJ_pointField_eq E J l t]
  have hcosh : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  have hZ : ZJ E J (fun _ => 0) ≠ 0 := (ZJ_pos E J (fun _ => 0)).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  have hnum :
      (∑ s : ConfigSpace V,
          f s *
            (wJ E J (fun _ => 0) s *
              (Real.cosh t + spin s l * Real.sinh t))) =
        Real.cosh t *
            (∑ s : ConfigSpace V, f s * wJ E J (fun _ => 0) s) +
          Real.sinh t *
            (∑ s : ConfigSpace V,
              (f s * spin s l) * wJ E J (fun _ => 0) s) := by
    calc
      _ = ∑ s : ConfigSpace V,
          (Real.cosh t * (f s * wJ E J (fun _ => 0) s) +
            Real.sinh t *
              ((f s * spin s l) * wJ E J (fun _ => 0) s)) := by
                apply Finset.sum_congr rfl
                intro s _
                ring
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
  rw [hnum]
  field_simp



theorem expJ_zero_three_spin_eq_zero
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    expJ E J (fun _ => 0)
      (fun s => spin s x * (spin s y * spin s z)) = 0 := by
  have hodd : Odd ({x, y, z} : Finset V).card := by
    simp [hxy, hxz, hyz, Odd]
  have h := expJ_zero_spinProd_odd_eq_zero E J {x, y, z} hodd
  have hfun :
      (fun s : ConfigSpace V => spin s x * (spin s y * spin s z)) =
        spinProd {x, y, z} := by
    funext s
    simp [spinProd, hxy, hxz, hyz]
  rw [hfun, h]


theorem expJ_pointField_two_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (x y l : V) (hxl : x ≠ l) (hyl : y ≠ l) (hxy : x ≠ y)
    (t : Real) :
    expJ E J (lebowitzPointField l t)
        (fun s => spin s x * spin s y) =
      expJ E J (fun _ => 0) (fun s => spin s x * spin s y) := by
  rw [expJ_pointField_eq]
  have hodd := expJ_zero_three_spin_eq_zero E J x y l hxy hxl hyl
  rw [show (fun s : ConfigSpace V =>
      (spin s x * spin s y) * spin s l) =
      (fun s => spin s x * (spin s y * spin s l)) by funext s; ring,
    hodd, mul_zero, add_zero]



theorem expJ_pointField_one_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (x l : V) (t : Real) :
    expJ E J (lebowitzPointField l t) (fun s => spin s x) =
      Real.tanh t *
        expJ E J (fun _ => 0) (fun s => spin s x * spin s l) := by
  rw [expJ_pointField_eq, expJ_zero_spin_eq_zero, zero_add]



theorem expJ_pointField_three_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (i j k l : V)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : Real) :
    expJ E J (lebowitzPointField l t)
        (fun s => spin s i * (spin s j * spin s k)) =
      Real.tanh t * expJ E J (fun _ => 0)
        (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
  rw [expJ_pointField_eq,
    expJ_zero_three_spin_eq_zero E J i j k hij hik hjk, zero_add]
  have hfun :
      (fun s : ConfigSpace V =>
        (spin s i * (spin s j * spin s k)) * spin s l) =
      (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
    funext s
    ring
  rw [hfun]



theorem lebowitz_four_point_with_parameter
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hK : ∀ e, 0 ≤ K e)
    (i j k l : V)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) :
    grahamUrsell4 G.edgeFinset K i j k l +
        2 * q ^ 2 *
          (grahamTwoPoint G.edgeFinset K i l *
            grahamTwoPoint G.edgeFinset K j l *
            grahamTwoPoint G.edgeFinset K k l) ≤ 0 := by
  let t := Real.artanh q
  have hqmem : q ∈ Ioo (-1 : Real) 1 := ⟨by linarith, hq1⟩
  have ht : Real.tanh t = q := Real.tanh_artanh hqmem
  have hfield : ∀ x, 0 ≤ lebowitzPointField l t x := by
    intro x
    by_cases hx : x = l
    · simp [lebowitzPointField, hx, t, Real.artanh_nonneg, hq0.le]
    · simp [lebowitzPointField, hx]
  have hghs := ghsi_ursell_nonpos G K (lebowitzPointField l t)
    hK hfield i j k hij
  rw [expJ_pointField_three_eq G.edgeFinset K i j k l hij hik hjk,
    expJ_pointField_one_eq G.edgeFinset K i l,
    expJ_pointField_two_eq G.edgeFinset K j k l hjl hkl hjk,
    expJ_pointField_two_eq G.edgeFinset K i j l hil hjl hij,
    expJ_pointField_one_eq G.edgeFinset K k l,
    expJ_pointField_two_eq G.edgeFinset K i k l hil hkl hik,
    expJ_pointField_one_eq G.edgeFinset K j l,
    ht] at hghs
  rw [grahamUrsell4_eq_expJ,
    grahamTwoPoint_eq_expJ, grahamTwoPoint_eq_expJ,
    grahamTwoPoint_eq_expJ]
  nlinarith





theorem lebowitz_four_point_le_leading
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hK : ∀ e, 0 ≤ K e)
    (i j k l : V)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    grahamUrsell4 G.edgeFinset K i j k l ≤
      -2 * (grahamTwoPoint G.edgeFinset K i l *
        grahamTwoPoint G.edgeFinset K j l *
        grahamTwoPoint G.edgeFinset K k l) := by
  let P := grahamTwoPoint G.edgeFinset K i l *
    grahamTwoPoint G.edgeFinset K j l *
    grahamTwoPoint G.edgeFinset K k l
  let q : Nat -> Real := fun n => 1 - 1 / (n + 1 : Real)
  have hq0 : ∀ n : Nat, 0 < q (n + 1) := by
    intro n
    dsimp [q]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hden : (0 : Real) < ((n : Real) + 1) + 1 := by positivity
    have hlt : (1 : Real) / (((n : Real) + 1) + 1) < 1 :=
      (div_lt_one hden).2 (by
        nlinarith [show (0 : Real) ≤ n from Nat.cast_nonneg n])
    linarith
  have hq1 : ∀ n : Nat, q (n + 1) < 1 := by
    intro n
    dsimp [q]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hden : (0 : Real) < ((n : Real) + 1) + 1 := by positivity
    have hpos : (0 : Real) < 1 / (((n : Real) + 1) + 1) :=
      div_pos zero_lt_one hden
    linarith
  have hineq : ∀ n : Nat,
      grahamUrsell4 G.edgeFinset K i j k l +
        2 * (q (n + 1)) ^ 2 * P ≤ 0 := by
    intro n
    exact lebowitz_four_point_with_parameter G K hK i j k l
      hij hik hil hjk hjl hkl (q (n + 1)) (hq0 n) (hq1 n)
  have hq_tendsto : Tendsto (fun n : Nat => q (n + 1)) atTop (nhds 1) := by
    have hzero' := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    have hzero : Tendsto (fun n : Nat => (1 : Real) / (n + 1 + 1 : Real))
        atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hzero'
    simpa [q, Nat.cast_add, Nat.cast_one] using tendsto_const_nhds.sub hzero
  have hlim : Tendsto (fun n : Nat =>
      grahamUrsell4 G.edgeFinset K i j k l +
        2 * (q (n + 1)) ^ 2 * P) atTop
      (nhds (grahamUrsell4 G.edgeFinset K i j k l + 2 * 1 ^ 2 * P)) := by
    simpa [pow_two] using tendsto_const_nhds.add
      ((tendsto_const_nhds.mul (hq_tendsto.mul hq_tendsto)).mul
        tendsto_const_nhds)
  have := le_of_tendsto' hlim hineq
  dsimp [P] at this ⊢
  linarith



theorem lebowitz_four_point_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hK : ∀ e, 0 ≤ K e)
    (i j k l : V)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    grahamUrsell4 G.edgeFinset K i j k l ≤ 0 := by
  have hlead := lebowitz_four_point_le_leading G K hK i j k l
    hij hik hil hjk hjl hkl
  have hi := ghsvp_expJ_zero_nonneg G.edgeFinset K
    (fun e he => hK e) (grahamPairSupport i l)
  have hj := ghsvp_expJ_zero_nonneg G.edgeFinset K
    (fun e he => hK e) (grahamPairSupport j l)
  have hk := ghsvp_expJ_zero_nonneg G.edgeFinset K
    (fun e he => hK e) (grahamPairSupport k l)
  change 0 ≤ grahamTwoPoint G.edgeFinset K i l at hi
  change 0 ≤ grahamTwoPoint G.edgeFinset K j l at hj
  change 0 ≤ grahamTwoPoint G.edgeFinset K k l at hk
  nlinarith [mul_nonneg (mul_nonneg hi hj) hk]

end

end StatMech.Ising
