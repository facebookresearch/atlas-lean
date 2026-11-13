/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeInfinityWave

open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

theorem strictMono_sixVertexFixedChargeAlternantExponent_of_noAdjacent
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    StrictMono (sixVertexFixedChargeAlternantExponent r k x) := by
  intro i j hij
  let d := j.val - i.val
  have hd : 0 < d := by dsimp [d]; omega
  have hid : i.val + d = j.val := by dsimp [d]; omega
  have hindex : (⟨i.val + d, by omega⟩ :
      Fin (sixVertexFixedChargeBetheParticleCount r k)) = j := by
    apply Fin.ext
    exact hid
  have hpos := sixVertexSectorNoAdjacent_position_add_lower x hx i.val d
    (by omega)
  have hiindex : (⟨i.val, by omega⟩ :
      Fin (sixVertexFixedChargeBetheParticleCount r k)) = i := Fin.ext rfl
  rw [hiindex] at hpos
  rw [hindex] at hpos
  have hpair :
      sixVertexFixedChargeBetheParticleCount r k - 1 - i.val =
        (sixVertexFixedChargeBetheParticleCount r k - 1 - j.val) + d := by
    dsimp [d]
    omega
  unfold sixVertexFixedChargeAlternantExponent
  rw [hpair]
  omega

private theorem sixVertexFixedChargeAlternantExponent_span_lt_complement
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    sixVertexFixedChargeAlternantExponent r k x
          ⟨sixVertexFixedChargeBetheParticleCount r k - 1, by
            exact Nat.sub_lt (sixVertexFixedChargeBetheParticleCount_pos r k)
              (by omega)⟩ <
      sixVertexFixedChargeAlternantExponent r k x
          ⟨0, sixVertexFixedChargeBetheParticleCount_pos r k⟩ +
        sixVertexFixedChargeBetheComplementCount r k := by
  have hwrap := hx.2 (sixVertexFixedChargeBetheParticleCount_pos r k)
  have hNm : sixVertexFourWidth r k =
      sixVertexFixedChargeBetheParticleCount r k +
        sixVertexFixedChargeBetheComplementCount r k := by
    rw [sixVertexFixedChargeBetheParticleCount_eq,
      sixVertexFixedChargeBetheComplementCount_eq]
    unfold sixVertexFourWidth
    omega
  unfold sixVertexFixedChargeAlternantExponent
  simp only [Nat.sub_self, Nat.sub_zero, add_zero]
  change (sixVertexSectorPosition x
      ⟨sixVertexFixedChargeBetheParticleCount r k - 1,
        Nat.sub_lt (sixVertexFixedChargeBetheParticleCount_pos r k) (by omega)⟩).val + 1 <
    sixVertexFourWidth r k +
      (sixVertexSectorPosition x
        ⟨0, sixVertexFixedChargeBetheParticleCount_pos r k⟩).val at hwrap
  have hn := sixVertexFixedChargeBetheParticleCount_pos r k
  omega

theorem sixVertexFixedChargeAlternantExponent_sub_abs_lt_complement
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x)
    (i j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    abs ((sixVertexFixedChargeAlternantExponent r k x i : Real) -
      sixVertexFixedChargeAlternantExponent r k x j) <
        sixVertexFixedChargeBetheComplementCount r k := by
  let first : Fin (sixVertexFixedChargeBetheParticleCount r k) :=
    ⟨0, sixVertexFixedChargeBetheParticleCount_pos r k⟩
  let last : Fin (sixVertexFixedChargeBetheParticleCount r k) :=
    ⟨sixVertexFixedChargeBetheParticleCount r k - 1, by
      exact Nat.sub_lt (sixVertexFixedChargeBetheParticleCount_pos r k)
        (by omega)⟩
  let e := sixVertexFixedChargeAlternantExponent r k x
  have he :=
    (strictMono_sixVertexFixedChargeAlternantExponent_of_noAdjacent r k x hx).monotone
  have hfirsti : e first <= e i := he (by
    change 0 <= i.val
    omega)
  have hfirstj : e first <= e j := he (by
    change 0 <= j.val
    omega)
  have hilast : e i <= e last := he (by
    change i.val <= sixVertexFixedChargeBetheParticleCount r k - 1
    omega)
  have hjlast : e j <= e last := he (by
    change j.val <= sixVertexFixedChargeBetheParticleCount r k - 1
    omega)
  have hspan := sixVertexFixedChargeAlternantExponent_span_lt_complement
    r k x hx
  dsimp only [e, first, last] at hfirsti hfirstj hilast hjlast hspan ⊢
  rw [abs_lt]
  constructor
  · have hint : -(sixVertexFixedChargeBetheComplementCount r k : Int) <
        (sixVertexFixedChargeAlternantExponent r k x i : Int) -
          sixVertexFixedChargeAlternantExponent r k x j := by omega
    exact_mod_cast hint
  · have hint :
        (sixVertexFixedChargeAlternantExponent r k x i : Int) -
            sixVertexFixedChargeAlternantExponent r k x j <
          sixVertexFixedChargeBetheComplementCount r k := by omega
    exact_mod_cast hint

theorem sixVertexFixedChargeAlternantPoint_injective_of_noAdjacent
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    Function.Injective (sixVertexFixedChargeAlternantPoint r k x) := by
  intro i j hij
  unfold sixVertexFixedChargeAlternantPoint
    sixVertexFixedChargeLimitingPhaseStep at hij
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul] at hij
  rcases Complex.exp_eq_exp_iff_exists_int.mp hij with ⟨z, hz⟩
  have him := congrArg Complex.im hz
  norm_num at him
  have hratio :
      ((2 * (Real.pi : Complex) /
        (3 * (r : Complex) + 2 * ((k : Complex) + 1)))).re =
        2 * Real.pi / (3 * (r : Real) + 2 * ((k : Real) + 1)) := by
    have hden : 3 * (r : Complex) + 2 * ((k : Complex) + 1) =
        ((3 * (r : Real) + 2 * ((k : Real) + 1) : Real) : Complex) := by
      push_cast
      rfl
    rw [hden]
    conv_lhs =>
      rw [← Complex.ofReal_ofNat]
      rw [← Complex.ofReal_mul]
      rw [← Complex.ofReal_div]
    rfl
  rw [hratio] at him
  have hm : (0 : Real) <
      (sixVertexFixedChargeBetheComplementCount r k : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheComplementCount_pos r k
  have hdiff := sixVertexFixedChargeAlternantExponent_sub_abs_lt_complement
    r k x hx i j
  have hzformula :
      (sixVertexFixedChargeAlternantExponent r k x i : Real) -
          sixVertexFixedChargeAlternantExponent r k x j =
        (z : Real) * sixVertexFixedChargeBetheComplementCount r k := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [sixVertexFixedChargeBetheComplementCount_eq]
    push_cast
    have hden : (3 * (r : Real) + 2 * ((k : Real) + 1)) ≠ 0 := by
      positivity
    field_simp [hden] at him
    nlinarith [Real.pi_pos]
  rw [hzformula, abs_mul, abs_of_pos hm] at hdiff
  have hzabs : abs (z : Real) < 1 := by
    apply lt_of_mul_lt_mul_right (a :=
      (sixVertexFixedChargeBetheComplementCount r k : Real))
    · simpa [mul_comm] using hdiff
    · exact hm.le
  have hzlo : (-1 : Int) < z := by
    exact_mod_cast (neg_lt_of_abs_lt hzabs)
  have hzhi : z < (1 : Int) := by
    exact_mod_cast (lt_of_abs_lt hzabs)
  have hz0 : z = 0 := by omega
  rw [hz0, Int.cast_zero, zero_mul] at hzformula
  have heq : sixVertexFixedChargeAlternantExponent r k x i =
      sixVertexFixedChargeAlternantExponent r k x j := by
    exact_mod_cast sub_eq_zero.mp hzformula
  exact (strictMono_sixVertexFixedChargeAlternantExponent_of_noAdjacent
    r k x hx).injective heq

theorem sixVertexFixedChargeLimitingWave_ne_zero_of_noAdjacent
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    sixVertexFixedChargeLimitingWave r k x ≠ 0 := by
  rw [sixVertexFixedChargeLimitingWave_eq_center_mul_vandermonde]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (Complex.exp_ne_zero _)
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (sixVertexFixedChargeAlternantPoint_injective_of_noAdjacent r k x hx)

end

end StatMech.FrontierD
