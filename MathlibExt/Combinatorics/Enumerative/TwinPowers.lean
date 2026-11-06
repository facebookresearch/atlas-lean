/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

private theorem subst_neg_apply (a f : PowerSeries ℝ) (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (-f) = -PowerSeries.subst a f := by
  simpa [PowerSeries.coe_substAlgHom] using map_neg (PowerSeries.substAlgHom (R := ℝ) ha) f

private theorem constantCoeff_subst_id (a f : PowerSeries ℝ)
    (ha0 : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst a f)
      = PowerSeries.constantCoeff f := by
  have h := PowerSeries.constantCoeff_subst_of_constantCoeff_zero (R := ℝ) (a := a) ha0 f
  simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at h
  exact h

private theorem constantCoeff_subst_zero (a f : PowerSeries ℝ)
    (ha0 : PowerSeries.constantCoeff a = 0)
    (hf0 : PowerSeries.constantCoeff f = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  have h := PowerSeries.constantCoeff_subst_of_constantCoeff_zero (R := ℝ) (a := a) ha0 f
  simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at h
  rw [hf0] at h
  exact h

private theorem constantCoeff_X_pow_ne_zero (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℝ) ^ n) = 0 := by
  rw [map_pow, PowerSeries.constantCoeff_X, zero_pow hn]

private theorem subst_inj_of_ne_zero (a : PowerSeries ℝ)
    (hane : a ≠ 0)
    (ha : PowerSeries.HasSubst a) :
    Function.Injective (PowerSeries.subst a : PowerSeries ℝ → PowerSeries ℝ) := by
  intro p q hpq
  by_contra hne
  have hsub_sub : PowerSeries.subst a (p - q) = 0 := by
    rw [PowerSeries.subst_sub ha]
    exact sub_eq_zero.mpr hpq
  have hd_ne : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hdiv_unit : IsUnit (p - q).divXPowOrder :=
    PowerSeries.isUnit_divided_by_X_pow_order hd_ne
  obtain ⟨u, hu⟩ := hdiv_unit
  have hmul : PowerSeries.subst a ((p - q).divXPowOrder * (↑u⁻¹ : PowerSeries ℝ)) = 1 := by
    have h1 : (p - q).divXPowOrder * (↑u⁻¹ : PowerSeries ℝ) = 1 := by
      rw [← hu]
      simp [Units.mul_inv]
    rw [h1]
    have hmap : PowerSeries.substAlgHom (R := ℝ) ha (1 : PowerSeries ℝ) = 1 :=
      map_one _
    rw [PowerSeries.coe_substAlgHom] at hmap
    simpa using hmap
  rw [PowerSeries.subst_mul ha] at hmul
  have hdiv_ne : PowerSeries.subst a (p - q).divXPowOrder ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmul
    exact one_ne_zero hmul.symm
  have hfactor : p - q = (PowerSeries.X : PowerSeries ℝ) ^ (p - q).order.toNat *
      (p - q).divXPowOrder :=
    (PowerSeries.X_pow_order_mul_divXPowOrder).symm
  have hzero : PowerSeries.subst a (p - q) =
      (PowerSeries.subst a ((PowerSeries.X : PowerSeries ℝ) ^ (p - q).order.toNat)) *
        PowerSeries.subst a (p - q).divXPowOrder := by
    conv_lhs => rw [hfactor]
    rw [PowerSeries.subst_mul ha]
  rw [PowerSeries.subst_pow ha] at hzero
  rw [PowerSeries.subst_X ha] at hzero
  have hpow_ne : a ^ (p - q).order.toNat ≠ 0 := pow_ne_zero _ hane
  have hprod_ne : a ^ (p - q).order.toNat * PowerSeries.subst a (p - q).divXPowOrder ≠ 0 :=
    mul_ne_zero hpow_ne hdiv_ne
  rw [hsub_sub] at hzero
  exact hprod_ne hzero.symm

private theorem coeff_one_X_mul (q : PowerSeries ℝ) :
    PowerSeries.coeff 1 ((PowerSeries.X : PowerSeries ℝ) * q) =
      PowerSeries.constantCoeff q := by
  simp only [PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff]

private theorem coeff1_of_BFunction (p B : PowerSeries ℝ)
    (hB : p - (PowerSeries.X : PowerSeries ℝ) =
      ((PowerSeries.X : PowerSeries ℝ) * B).subst
        ((PowerSeries.X : PowerSeries ℝ) * p)) :
    PowerSeries.constantCoeff p = 0 ∧ PowerSeries.coeff 1 p = 1 := by
  have hXp0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℝ) * p) = 0 := by
    simp
  have hXp : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries ℝ) * p) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXp0
  have hRHS : ((PowerSeries.X : PowerSeries ℝ) * B).subst
        ((PowerSeries.X : PowerSeries ℝ) * p) =
      ((PowerSeries.X : PowerSeries ℝ) * p) *
        (B.subst ((PowerSeries.X : PowerSeries ℝ) * p)) := by
    rw [PowerSeries.subst_mul hXp, PowerSeries.subst_X hXp]
  rw [hRHS] at hB
  have hcc : PowerSeries.constantCoeff p = 0 := by
    have hcc2 := congrArg PowerSeries.constantCoeff hB
    simp at hcc2
    simpa [hXp0] using hcc2
  have hpeq : p = (PowerSeries.X : PowerSeries ℝ) +
      (PowerSeries.X : PowerSeries ℝ) * (p * B.subst ((PowerSeries.X : PowerSeries ℝ) * p)) := by
    linear_combination hB
  have hcoeff : PowerSeries.coeff 1 p = 1 := by
    rw [hpeq]
    rw [map_add]
    rw [PowerSeries.coeff_one_X]
    rw [coeff_one_X_mul]
    have h0 : PowerSeries.constantCoeff
        (p * B.subst ((PowerSeries.X : PowerSeries ℝ) * p)) = 0 := by
      simp [hcc]
    rw [h0]
    simp
  exact ⟨hcc, hcoeff⟩

private theorem pseudo_iff_neg (p : PowerSeries ℝ)
    (h0 : PowerSeries.constantCoeff p = 0)
    (hu : IsUnit (PowerSeries.coeff 1 p)) :
    (p.substInvOfIsUnit hu = -(p.subst (-(PowerSeries.X : PowerSeries ℝ)))) ↔
      p.subst (-p) = -(PowerSeries.X : PowerSeries ℝ) := by
  have hp : PowerSeries.HasSubst p := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hnegX0 : PowerSeries.constantCoeff (-(PowerSeries.X : PowerSeries ℝ)) = 0 := by simp
  have hnegX : PowerSeries.HasSubst (-(PowerSeries.X : PowerSeries ℝ)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hnegX0
  have hnegp0 : PowerSeries.constantCoeff (-p) = 0 := by simp [h0]
  have hnegp : PowerSeries.HasSubst (-p) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hnegp0
  have hneg_neg : PowerSeries.subst (-(PowerSeries.X : PowerSeries ℝ))
      (-(PowerSeries.X : PowerSeries ℝ)) = (PowerSeries.X : PowerSeries ℝ) := by
    rw [subst_neg_apply _ _ hnegX, PowerSeries.subst_X hnegX, neg_neg]
  constructor
  · intro hInv
    have hP : PowerSeries.subst (p.substInvOfIsUnit hu) p =
        (PowerSeries.X : PowerSeries ℝ) :=
      PowerSeries.subst_substInvOfIsUnit_right p h0 hu
    rw [hInv] at hP
    have hEq : (-(p.subst (-(PowerSeries.X : PowerSeries ℝ)))) =
        PowerSeries.subst (-(PowerSeries.X : PowerSeries ℝ)) (-p) := by
      rw [subst_neg_apply _ _ hnegX]
    rw [hEq] at hP
    have hcomp := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
      (a := -p) (b := -(PowerSeries.X : PowerSeries ℝ)) hnegp hnegX p
    rw [← hcomp] at hP
    have hQ : PowerSeries.subst (-(PowerSeries.X : PowerSeries ℝ))
        (PowerSeries.subst (-p) p) = (PowerSeries.X : PowerSeries ℝ) := hP
    have hQQ := congrArg (PowerSeries.subst (-(PowerSeries.X : PowerSeries ℝ))) hQ
    have hcomp2 := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
      (a := -(PowerSeries.X : PowerSeries ℝ))
      (b := -(PowerSeries.X : PowerSeries ℝ)) hnegX hnegX (PowerSeries.subst (-p) p)
    rw [hneg_neg] at hcomp2
    rw [PowerSeries.X_subst] at hcomp2
    rw [hcomp2] at hQQ
    have hnegX_X : PowerSeries.subst (-(PowerSeries.X : PowerSeries ℝ))
        (PowerSeries.X : PowerSeries ℝ) = -(PowerSeries.X : PowerSeries ℝ) :=
      PowerSeries.subst_X hnegX
    rw [hnegX_X] at hQQ
    exact hQQ
  · intro hqq
    have hQ0 : PowerSeries.constantCoeff
        (p.subst (-(PowerSeries.X : PowerSeries ℝ))) = 0 :=
      constantCoeff_subst_zero _ _ hnegX0 h0
    have hQneg0 : PowerSeries.constantCoeff
        (-(p.subst (-(PowerSeries.X : PowerSeries ℝ)))) = 0 := by
      simp [hQ0]
    have hQneg : PowerSeries.HasSubst (-(p.subst (-(PowerSeries.X : PowerSeries ℝ)))) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hQneg0
    have hEq2 : (-(p.subst (-(PowerSeries.X : PowerSeries ℝ)))) =
        PowerSeries.subst (-(PowerSeries.X : PowerSeries ℝ)) (-p) := by
      rw [subst_neg_apply _ _ hnegX]
    have hgoal : PowerSeries.subst (-(p.subst (-(PowerSeries.X : PowerSeries ℝ)))) p =
        (PowerSeries.X : PowerSeries ℝ) := by
      rw [hEq2]
      have hcomp := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
        (a := -p) (b := -(PowerSeries.X : PowerSeries ℝ)) hnegp hnegX p
      rw [← hcomp, hqq, hneg_neg]
    have hEqInv := PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X p h0 hu hQneg hgoal
    exact hEqInv.symm

private theorem odd_neg_pow_aux (a : PowerSeries ℝ) (l : ℕ) :
    (-a) ^ (2 * l + 1) = -(a ^ (2 * l + 1)) := by
  have hodd : Odd (2 * l + 1) := ⟨l, by ring⟩
  exact hodd.neg_pow a

private theorem transfer_fwd_aux (l : ℕ)
    (f h : PowerSeries ℝ)
    (hfn : f ^ (2 * l + 1) = h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)))
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hh0 : PowerSeries.constantCoeff h = 0)
    (hff : PowerSeries.subst (-f) f = -(PowerSeries.X : PowerSeries ℝ)) :
    PowerSeries.subst (-h) h = -(PowerSeries.X : PowerSeries ℝ) := by
  have hn_ne : (2 * l + 1 : ℕ) ≠ 0 := by omega
  have hXn0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) = 0 :=
    constantCoeff_X_pow_ne_zero _ hn_ne
  have hXn : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXn0
  have hnegf0 : PowerSeries.constantCoeff (-f) = 0 := by simp [hf0]
  have hnegf : PowerSeries.HasSubst (-f) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hnegf0
  have hnegh0 : PowerSeries.constantCoeff (-h) = 0 := by simp [hh0]
  have hnegh : PowerSeries.HasSubst (-h) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hnegh0
  have hXn_ne : ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) ≠ 0 :=
    pow_ne_zero _ PowerSeries.X_ne_zero
  have hLHS : PowerSeries.subst (-f) (f ^ (2 * l + 1)) =
      -(((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) := by
    rw [PowerSeries.subst_pow hnegf, hff]
    have hodd : Odd (2 * l + 1 : ℕ) := ⟨l, by ring⟩
    exact hodd.neg_pow _
  have hcomp1 := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
    (a := ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) (b := -f) hXn hnegf h
  have hXn_f : PowerSeries.subst (-f) ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) =
      (-f) ^ (2 * l + 1) := by
    rw [PowerSeries.subst_pow hnegf, PowerSeries.subst_X hnegf]
  have hnegfn : (-f) ^ (2 * l + 1) = -(f ^ (2 * l + 1)) := odd_neg_pow_aux f l
  have hfn2 : -(f ^ (2 * l + 1)) = -(h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) := by
    rw [hfn]
  have hsubXn_h : PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) (-h) =
      -(h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) := by
    rw [subst_neg_apply _ _ hXn]
  have hcomp2 := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
    (a := -h) (b := ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) hnegh hXn h
  have hRHS_eq : PowerSeries.subst (-f) (h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
        (PowerSeries.subst (-h) h) := by
    rw [hcomp1, hXn_f, hnegfn, hfn2, ← hsubXn_h, ← hcomp2]
  have happly := congrArg (PowerSeries.subst (-f)) hfn
  rw [hLHS] at happly
  have hsubXn_negX : PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
      (-(PowerSeries.X : PowerSeries ℝ)) = -(((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) := by
    rw [subst_neg_apply _ _ hXn, PowerSeries.subst_X hXn]
  have hfinal : PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
      (-(PowerSeries.X : PowerSeries ℝ)) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
        (PowerSeries.subst (-h) h) := by
    rw [hsubXn_negX, ← hRHS_eq, ← happly]
  have hinj := subst_inj_of_ne_zero _ hXn_ne hXn
  exact (hinj hfinal).symm

private theorem transfer_bwd_aux (l : ℕ) (Bf : PowerSeries ℝ)
    (f h : PowerSeries ℝ)
    (hfn : f ^ (2 * l + 1) = h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)))
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hh0 : PowerSeries.constantCoeff h = 0)
    (hBf : f - (PowerSeries.X : PowerSeries ℝ) =
      ((PowerSeries.X : PowerSeries ℝ) * Bf).subst
        ((PowerSeries.X : PowerSeries ℝ) * f))
    (hhh : PowerSeries.subst (-h) h = -(PowerSeries.X : PowerSeries ℝ)) :
    PowerSeries.subst (-f) f = -(PowerSeries.X : PowerSeries ℝ) := by
  have hn_ne : (2 * l + 1 : ℕ) ≠ 0 := by omega
  have hXn0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) = 0 :=
    constantCoeff_X_pow_ne_zero _ hn_ne
  have hXn : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXn0
  have hnegf0 : PowerSeries.constantCoeff (-f) = 0 := by simp [hf0]
  have hnegf : PowerSeries.HasSubst (-f) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hnegf0
  have hnegh0 : PowerSeries.constantCoeff (-h) = 0 := by simp [hh0]
  have hnegh : PowerSeries.HasSubst (-h) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hnegh0
  have hXf0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℝ) * f) = 0 := by simp
  have hXf : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries ℝ) * f) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXf0
  have hRHS : ((PowerSeries.X : PowerSeries ℝ) * Bf).subst
        ((PowerSeries.X : PowerSeries ℝ) * f) =
      ((PowerSeries.X : PowerSeries ℝ) * f) *
        (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)) := by
    rw [PowerSeries.subst_mul hXf, PowerSeries.subst_X hXf]
  have hfv : f = (PowerSeries.X : PowerSeries ℝ) *
      (1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f))) := by
    linear_combination (hBf.trans hRHS)
  have hv0 : PowerSeries.constantCoeff
      (1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f))) = 1 := by
    rw [map_add, map_one, map_mul, hf0, zero_mul, add_zero]
  have hw0 : PowerSeries.constantCoeff
      ((1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f))).subst (-f)) = 1 := by
    rw [constantCoeff_subst_id _ _ hnegf0, hv0]
  have hqeq : PowerSeries.subst (-f) f =
      (-f) * ((1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f))).subst (-f)) := by
    nth_rewrite 2 [hfv]
    rw [PowerSeries.subst_mul hnegf, PowerSeries.subst_X hnegf]
  have hu0 : PowerSeries.constantCoeff
      ((-(1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)))) *
        ((1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f))).subst (-f))) = -1 := by
    rw [map_mul, map_neg, hv0, hw0]
    simp
  have hqXu : PowerSeries.subst (-f) f = (PowerSeries.X : PowerSeries ℝ) *
      ((-(1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)))) *
        ((1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f))).subst (-f))) := by
    rw [hqeq]
    have hnegf_eq : (-f) = (PowerSeries.X : PowerSeries ℝ) *
        (-(1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)))) := by
      conv_lhs => rw [hfv]
      ring
    rw [hnegf_eq, ← mul_assoc]
  have hcomp1 := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
    (a := ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) (b := -f) hXn hnegf h
  have hXn_f : PowerSeries.subst (-f) ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) =
      (-f) ^ (2 * l + 1) := by
    rw [PowerSeries.subst_pow hnegf, PowerSeries.subst_X hnegf]
  have hnegfn : (-f) ^ (2 * l + 1) = -(f ^ (2 * l + 1)) := odd_neg_pow_aux f l
  have hfn2 : -(f ^ (2 * l + 1)) = -(h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) := by
    rw [hfn]
  have hsubXn_h : PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) (-h) =
      -(h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) := by
    rw [subst_neg_apply _ _ hXn]
  have hcomp2 := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
    (a := -h) (b := ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) hnegh hXn h
  have hRHS_eq : PowerSeries.subst (-f) (h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
        (PowerSeries.subst (-h) h) := by
    rw [hcomp1, hXn_f, hnegfn, hfn2, ← hsubXn_h, ← hcomp2]
  have hqn : (PowerSeries.subst (-f) f) ^ (2 * l + 1) =
      -(((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) := by
    have h1 : (PowerSeries.subst (-f) f) ^ (2 * l + 1) =
        PowerSeries.subst (-f) (f ^ (2 * l + 1)) := by
      rw [PowerSeries.subst_pow hnegf]
    rw [h1, hfn, hRHS_eq, hhh]
    rw [subst_neg_apply _ _ hXn, PowerSeries.subst_X hXn]
  have hun : ((-(1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)))) *
        ((1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f))).subst (-f))) ^ (2 * l + 1)
      = (-1 : PowerSeries ℝ) := by
    have hXu_pow : ((PowerSeries.X : PowerSeries ℝ) *
        ((-(1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)))) *
          ((1 + f * (Bf.subst
            ((PowerSeries.X : PowerSeries ℝ) * f))).subst (-f)))) ^ (2 * l + 1) =
        (PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1) *
          ((-(1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)))) *
            ((1 + f * (Bf.subst
              ((PowerSeries.X : PowerSeries ℝ) * f))).subst (-f))) ^ (2 * l + 1) := by
      rw [mul_pow]
    have hnegXn : -(((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) =
        (PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1) * (-1) := by
      rw [mul_neg, mul_one]
    rw [← hqXu] at hXu_pow
    rw [hqn, hnegXn] at hXu_pow
    exact PowerSeries.X_pow_mul_cancel hXu_pow.symm
  set u : PowerSeries ℝ := (-(1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)))) *
        ((1 + f * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f))).subst (-f)) with hu_def
  have hun' : u ^ (2 * l + 1) = (-1 : PowerSeries ℝ) := hun
  have hu0' : PowerSeries.constantCoeff u = -1 := hu0
  have hnegu : (-u) ^ (2 * l + 1) = (1 : PowerSeries ℝ) := by
    have hodd : Odd (2 * l + 1 : ℕ) := ⟨l, by ring⟩
    rw [hodd.neg_pow, hun', neg_neg]
  have hgeom := geom_sum_mul (-u) (2 * l + 1)
  rw [hnegu, sub_self] at hgeom
  have hsum_unit : IsUnit (Finset.sum (Finset.range (2 * l + 1)) (fun i => (-u) ^ i)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hcc : PowerSeries.constantCoeff (Finset.sum (Finset.range (2 * l + 1))
        (fun i => (-u) ^ i)) = ((2 * l + 1 : ℕ) : ℝ) := by
      rw [map_sum]
      have h1 : ∀ i : ℕ, PowerSeries.constantCoeff ((-u) ^ i) = 1 := by
        intro i
        rw [map_pow]
        have hcu : PowerSeries.constantCoeff (-u) = 1 := by simp [hu0']
        rw [hcu, one_pow]
      simp only [h1]
      rw [Finset.sum_const, Finset.card_range]
      simp [nsmul_eq_mul]
    rw [hcc]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hn_ne)
  have hzero : (-u) - 1 = 0 := by
    have hmp := mul_eq_zero.mp hgeom
    cases hmp with
    | inl hl =>
      have hne : Finset.sum (Finset.range (2 * l + 1)) (fun i => (-u) ^ i) ≠ 0 :=
        hsum_unit.ne_zero
      exact False.elim (absurd hl hne)
    | inr hr => exact hr
  have hu_eq : u = -1 := by
    have : -u = 1 := sub_eq_zero.mp hzero
    simpa using congrArg Neg.neg this
  have hq_final : PowerSeries.subst (-f) f = -(PowerSeries.X : PowerSeries ℝ) := by
    rw [hqXu, hu_eq]
    simp
  exact hq_final

private theorem coeff_eq_aux (l j : ℕ) (hj : j ≤ l) :
    ((((2 * l + 1 : ℕ) : ℝ) / (((2 * j + 1 : ℕ) : ℝ))) *
      ((Nat.choose (l + j) (2 * j) : ℕ) : ℝ)) =
    ((Nat.choose (l + j) (2 * j) : ℕ) : ℝ) +
      2 * ((Nat.choose (l + j) (2 * j + 1) : ℕ) : ℝ) := by
  have hj1 : (((2 * j + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (by omega : (2 * j + 1 : ℕ) ≠ 0)
  have hchoose : (Nat.choose (l + j) (2 * j + 1) : ℕ) * (2 * j + 1) =
      (Nat.choose (l + j) (2 * j) : ℕ) * (l - j) := by
    have h := Nat.choose_succ_right_eq (l + j) (2 * j)
    have hsub : (l + j) - 2 * j = l - j := by omega
    rw [hsub] at h
    linarith [h]
  have hreal : (((Nat.choose (l + j) (2 * j + 1) : ℕ)) : ℝ)
      * (((2 * j + 1 : ℕ)) : ℝ) =
      (((Nat.choose (l + j) (2 * j) : ℕ)) : ℝ) * (((l - j : ℕ)) : ℝ) := by
    exact_mod_cast hchoose
  have hlj : ((l : ℝ) - (j : ℝ)) = (((l - j : ℕ)) : ℝ) := by
    rw [Nat.cast_sub hj]
  have h2lj : (((2 * l + 1 : ℕ)) : ℝ) - (((2 * j + 1 : ℕ)) : ℝ)
      = 2 * ((l : ℝ) - (j : ℝ)) := by
    push_cast; ring
  have hC : (((Nat.choose (l + j) (2 * j) : ℕ)) : ℝ)
      * ((((2 * l + 1 : ℕ)) : ℝ) - (((2 * j + 1 : ℕ)) : ℝ)) =
      2 * (((Nat.choose (l + j) (2 * j) : ℕ)) : ℝ)
        * (((l - j : ℕ)) : ℝ) := by
    rw [h2lj, hlj]; ring
  field_simp
  linear_combination hC - 2 * hreal

private theorem f_pow_eq (l : ℕ) (g : PowerSeries ℝ) :
    ((PowerSeries.X : PowerSeries ℝ)
        * g.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)))
        ^ (2 * l + 1)
      = ((PowerSeries.X : PowerSeries ℝ) * g ^ (2 * l + 1)).subst
        ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) := by
  have hn : 2 * l + 1 ≠ 0 := by omega
  have hXn : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) :=
    PowerSeries.HasSubst.X_pow hn
  rw [mul_pow, PowerSeries.subst_mul hXn, PowerSeries.subst_X hXn,
    PowerSeries.subst_pow hXn]

private theorem pascal_twice (m k : ℕ) :
    Nat.choose (m + 2) (k + 2)
      = Nat.choose m k + 2 * Nat.choose m (k + 1)
        + Nat.choose m (k + 2) := by
  have h1 := Nat.choose_succ_succ' (m + 1) (k + 1)
  have h2 := Nat.choose_succ_succ' m k
  have h3 := Nat.choose_succ_succ' m (k + 1)
  have hm : m + 2 = (m + 1) + 1 := by omega
  have hk : k + 2 = (k + 1) + 1 := by omega
  rw [hm, hk, h1, h2, h3]
  omega

private def dCoeffNat (l j : ℕ) : ℕ :=
  Nat.choose (l + j) (2 * j) + 2 * Nat.choose (l + j) (2 * j + 1)

private theorem dNat_zero (n : ℕ) :
    dCoeffNat (n + 2) 0 + dCoeffNat n 0
      = 2 * dCoeffNat (n + 1) 0 := by
  simp only [dCoeffNat, Nat.add_zero, Nat.mul_zero, Nat.zero_add,
    Nat.choose_zero_right, Nat.choose_one_right]
  omega

private theorem dNat_succ (n k : ℕ) :
    dCoeffNat (n + 2) (k + 1) + dCoeffNat n (k + 1)
      = dCoeffNat (n + 1) k + 2 * dCoeffNat (n + 1) (k + 1) := by
  simp only [dCoeffNat]
  have e1 : (n + 2) + (k + 1) = (n + k + 1) + 2 := by omega
  have e2 : n + (k + 1) = n + k + 1 := by omega
  have e3 : (n + 1) + k = n + k + 1 := by omega
  have e4 : (n + 1) + (k + 1) = (n + k + 1) + 1 := by omega
  have f2 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
  have f1 : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [e1, e2, e3, e4, f2, f1]
  have hP1 := pascal_twice (n + k + 1) (2 * k)
  have hP2 := pascal_twice (n + k + 1) (2 * k + 1)
  have hQ1 := Nat.choose_succ_succ' (n + k + 1) (2 * k + 1)
  have g1 : (2 * k + 1) + 1 = 2 * k + 2 := by omega
  rw [g1] at hQ1 hP2
  have hQ2 := Nat.choose_succ_succ' (n + k + 1) (2 * k + 2)
  have g2 : (2 * k + 2) + 1 = (2 * k + 1) + 2 := by omega
  rw [g2] at hQ2
  omega

private theorem dNat_eq_zero_of_lt {l j : ℕ} (h : l < j) :
    dCoeffNat l j = 0 := by
  simp only [dCoeffNat]
  have h1 : l + j < 2 * j := by omega
  have h2 : l + j < 2 * j + 1 := by omega
  rw [Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2]

private theorem odd_pow_rec {R : Type*} [CommRing R]
    (u v : R) (n : ℕ) :
    (u ^ (2 * (n + 2) + 1) - v ^ (2 * (n + 2) + 1))
      = ((u - v) ^ 2 + 2 * (u * v))
        * (u ^ (2 * (n + 1) + 1) - v ^ (2 * (n + 1) + 1))
        - (u * v) ^ 2 * (u ^ (2 * n + 1) - v ^ (2 * n + 1)) := by
  have hu1 : u ^ (2 * (n + 2) + 1)
      = u ^ (2 * (n + 1) + 1) * u ^ 2 := by
    rw [show 2 * (n + 2) + 1 = (2 * (n + 1) + 1) + 2 from by omega,
      pow_add]
  have hu2 : u ^ (2 * (n + 1) + 1) = u ^ (2 * n + 1) * u ^ 2 := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by omega, pow_add]
  have hv1 : v ^ (2 * (n + 2) + 1)
      = v ^ (2 * (n + 1) + 1) * v ^ 2 := by
    rw [show 2 * (n + 2) + 1 = (2 * (n + 1) + 1) + 2 from by omega,
      pow_add]
  have hv2 : v ^ (2 * (n + 1) + 1) = v ^ (2 * n + 1) * v ^ 2 := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by omega, pow_add]
  rw [hu1, hu2, hv1, hv2]
  ring

private theorem Spow_2p {R : Type*} [CommRing R]
    (p w : R) (n : ℕ) :
    2 * p * (∑ j ∈ Finset.range (n + 2),
        (dCoeffNat (n + 1) j : R) * (p ^ (n + 1 - j) * w ^ j))
      = ∑ k ∈ Finset.range (n + 3),
        (2 * (dCoeffNat (n + 1) k : R)) * (p ^ (n + 2 - k) * w ^ k) := by
  rw [Finset.mul_sum]
  have hcongr : (∑ j ∈ Finset.range (n + 2),
        2 * p * ((dCoeffNat (n + 1) j : R) * (p ^ (n + 1 - j) * w ^ j)))
      = ∑ j ∈ Finset.range (n + 2),
        (2 * (dCoeffNat (n + 1) j : R)) * (p ^ (n + 2 - j) * w ^ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hk : n + 2 - j = (n + 1 - j) + 1 := by omega
    rw [hk, pow_succ]
    ring
  rw [hcongr]
  have hsub : Finset.range (n + 2) ⊆ Finset.range (n + 3) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  apply Finset.sum_subset hsub
  intro x hx hnx
  simp only [Finset.mem_range] at hx hnx
  have hxeq : x = n + 2 := by omega
  rw [hxeq]
  have hd0 : dCoeffNat (n + 1) (n + 2) = 0 :=
    dNat_eq_zero_of_lt (by omega)
  simp [hd0]

private theorem Spow_p2 {R : Type*} [CommRing R]
    (p w : R) (n : ℕ) :
    p ^ 2 * (∑ j ∈ Finset.range (n + 1),
        (dCoeffNat n j : R) * (p ^ (n - j) * w ^ j))
      = ∑ k ∈ Finset.range (n + 3),
        (dCoeffNat n k : R) * (p ^ (n + 2 - k) * w ^ k) := by
  rw [Finset.mul_sum]
  have hcongr : (∑ j ∈ Finset.range (n + 1),
        p ^ 2 * ((dCoeffNat n j : R) * (p ^ (n - j) * w ^ j)))
      = ∑ j ∈ Finset.range (n + 1),
        (dCoeffNat n j : R) * (p ^ (n + 2 - j) * w ^ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hk : n + 2 - j = (n - j) + 2 := by omega
    rw [hk, pow_add]
    ring
  rw [hcongr]
  have hsub : Finset.range (n + 1) ⊆ Finset.range (n + 3) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  apply Finset.sum_subset hsub
  intro x hx hnx
  simp only [Finset.mem_range] at hx hnx
  have hd0 : dCoeffNat n x = 0 := dNat_eq_zero_of_lt (by omega)
  simp [hd0]

private theorem Spow_w {R : Type*} [CommRing R]
    (p w : R) (n : ℕ) :
    w * (∑ j ∈ Finset.range (n + 2),
        (dCoeffNat (n + 1) j : R) * (p ^ (n + 1 - j) * w ^ j))
      = ∑ k ∈ Finset.range (n + 3),
        (if k = 0 then (0 : R)
          else (dCoeffNat (n + 1) (k - 1) : R) * (p ^ (n + 2 - k) * w ^ k)) := by
  rw [Finset.mul_sum]
  have hexpand : (∑ j ∈ Finset.range (n + 2),
        w * ((dCoeffNat (n + 1) j : R) * (p ^ (n + 1 - j) * w ^ j)))
      = ∑ j ∈ Finset.range (n + 2),
        (dCoeffNat (n + 1) j : R) * (p ^ (n + 1 - j) * w ^ (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    ring
  rw [hexpand]
  have hshift : (∑ k ∈ Finset.range (n + 3),
        (if k = 0 then (0 : R)
          else (dCoeffNat (n + 1) (k - 1) : R) * (p ^ (n + 2 - k) * w ^ k)))
      = ∑ j ∈ Finset.range (n + 2),
        (dCoeffNat (n + 1) j : R) * (p ^ (n + 1 - j) * w ^ (j + 1)) := by
    have hsucc := Finset.sum_range_succ' (fun k =>
      (if k = 0 then (0 : R)
        else (dCoeffNat (n + 1) (k - 1) : R) * (p ^ (n + 2 - k) * w ^ k))) (n + 2)
    have hn3 : n + 3 = (n + 2) + 1 := by omega
    rw [hn3, hsucc]
    have h0 : (if (0 : ℕ) = 0 then (0 : R)
        else (dCoeffNat (n + 1) (0 - 1) : R) * (p ^ (n + 2 - 0) * w ^ 0)) = 0 := by
      simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hne : j + 1 ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    have hsub1 : j + 1 - 1 = j := by omega
    have hsub2 : n + 2 - (j + 1) = n + 1 - j := by omega
    rw [hsub1, hsub2]
  rw [hshift]

private theorem Spow_rec {R : Type*} [CommRing R]
    (p w : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 3),
        (dCoeffNat (n + 2) k : R) * (p ^ (n + 2 - k) * w ^ k))
      = (w + 2 * p) * (∑ j ∈ Finset.range (n + 2),
          (dCoeffNat (n + 1) j : R) * (p ^ (n + 1 - j) * w ^ j))
        - p ^ 2 * (∑ j ∈ Finset.range (n + 1),
          (dCoeffNat n j : R) * (p ^ (n - j) * w ^ j)) := by
  have hw := Spow_w (R := R) p w n
  have h2p := Spow_2p (R := R) p w n
  have hp2 := Spow_p2 (R := R) p w n
  have hRHS : (w + 2 * p) * (∑ j ∈ Finset.range (n + 2),
          (dCoeffNat (n + 1) j : R) * (p ^ (n + 1 - j) * w ^ j))
        - p ^ 2 * (∑ j ∈ Finset.range (n + 1),
          (dCoeffNat n j : R) * (p ^ (n - j) * w ^ j))
      = ∑ k ∈ Finset.range (n + 3),
        ((if k = 0 then (0 : R)
            else (dCoeffNat (n + 1) (k - 1) : R) * (p ^ (n + 2 - k) * w ^ k))
          + (2 * (dCoeffNat (n + 1) k : R)) * (p ^ (n + 2 - k) * w ^ k)
          - (dCoeffNat n k : R) * (p ^ (n + 2 - k) * w ^ k)) := by
    rw [add_mul, hw, h2p, hp2]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [hRHS]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte]
    have h0 := congrArg (Nat.cast : ℕ → R) (dNat_zero n)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h0
    linear_combination h0 * (p ^ (n + 2 - 0) * w ^ 0)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk0
    have hne2 : j + 1 ≠ 0 := by omega
    simp only [hne2, ↓reduceIte]
    have hsub1 : j + 1 - 1 = j := by omega
    rw [hsub1]
    have hs := congrArg (Nat.cast : ℕ → R) (dNat_succ n j)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hs
    linear_combination hs * (p ^ (n + 2 - (j + 1)) * w ^ (j + 1))

private theorem Sfactor {R : Type*} [CommRing R]
    (u v : R) (l : ℕ) :
    (∑ j ∈ Finset.range (l + 1),
        (dCoeffNat l j : R) * ((u * v) ^ (l - j) * (u - v) ^ (2 * j + 1)))
      = (u - v) * (∑ j ∈ Finset.range (l + 1),
        (dCoeffNat l j : R) * ((u * v) ^ (l - j) * ((u - v) ^ 2) ^ j)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h1 : (u - v) ^ (2 * j + 1) = (u - v) ^ (2 * j) * (u - v) := by
    rw [show 2 * j + 1 = (2 * j) + 1 from by omega, pow_add, pow_one]
  have h2 : (u - v) ^ (2 * j) = (((u - v) ^ 2) ^ j) := by
    rw [pow_mul]
  rw [h1, h2]
  ring

private theorem girard_zero {R : Type*} [CommRing R] (u v : R) :
    u ^ (2 * 0 + 1) - v ^ (2 * 0 + 1)
      = ∑ j ∈ Finset.range (0 + 1),
        (dCoeffNat 0 j : R) * ((u * v) ^ (0 - j) * (u - v) ^ (2 * j + 1)) := by
  have hd0 : dCoeffNat 0 0 = 1 := rfl
  rw [Finset.sum_range_one]
  have h10 : (2 * 0 + 1 : ℕ) = 1 := rfl
  rw [h10, pow_one, pow_one]
  have h0 : (0 : ℕ) - 0 = 0 := rfl
  simp only [hd0, Nat.cast_one, h0, pow_zero]
  simp

private theorem girard_one {R : Type*} [CommRing R] (u v : R) :
    u ^ (2 * 1 + 1) - v ^ (2 * 1 + 1)
      = ∑ j ∈ Finset.range (1 + 1),
        (dCoeffNat 1 j : R) * ((u * v) ^ (1 - j) * (u - v) ^ (2 * j + 1)) := by
  have hd10 : dCoeffNat 1 0 = 3 := rfl
  have hd11 : dCoeffNat 1 1 = 1 := rfl
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h31 : (2 * 1 + 1 : ℕ) = 3 := rfl
  rw [h31]
  simp only [hd10, hd11, Nat.cast_ofNat, Nat.cast_one, one_mul]
  ring

private theorem girard {R : Type*} [CommRing R]
    (u v : R) (l : ℕ) :
    u ^ (2 * l + 1) - v ^ (2 * l + 1)
      = ∑ j ∈ Finset.range (l + 1),
        (dCoeffNat l j : R) * ((u * v) ^ (l - j) * (u - v) ^ (2 * j + 1)) := by
  induction l using Nat.twoStepInduction with
  | zero => exact girard_zero u v
  | one => exact girard_one u v
  | more n ih0 ih1 =>
    have hT := odd_pow_rec (R := R) u v n
    have hSp := Spow_rec (R := R) (u * v) ((u - v) ^ 2) n
    have e1 : (n + 2) + 1 = n + 3 := by omega
    have e2 : (n + 1) + 1 = n + 2 := by omega
    have hSf2 := Sfactor (R := R) u v (n + 2)
    have hSf1 := Sfactor (R := R) u v (n + 1)
    have hSf0 := Sfactor (R := R) u v n
    rw [e1] at hSf2
    rw [e2] at hSf1
    rw [e1]
    have hS : (∑ j ∈ Finset.range (n + 3),
          (dCoeffNat (n + 2) j : R) * ((u * v) ^ (n + 2 - j) * (u - v) ^ (2 * j + 1)))
        = (((u - v) ^ 2 + 2 * (u * v))
            * (∑ j ∈ Finset.range (n + 2),
              (dCoeffNat (n + 1) j : R)
                * ((u * v) ^ (n + 1 - j) * (u - v) ^ (2 * j + 1)))
            - (u * v) ^ 2 * (∑ j ∈ Finset.range (n + 1),
              (dCoeffNat n j : R) * ((u * v) ^ (n - j) * (u - v) ^ (2 * j + 1)))) := by
      rw [hSf2, hSp, hSf1, hSf0]
      ring
    rw [hT]
    rw [e2] at ih1
    rw [ih1, ih0]
    exact hS.symm

private theorem f_ne_of_hg (l : ℕ) (g f : PowerSeries ℝ)
    (hg : PowerSeries.constantCoeff g ≠ 0)
    (hf : f = (PowerSeries.X : PowerSeries ℝ)
      * g.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) :
    f ≠ 0 := by
  have hn : 2 * l + 1 ≠ 0 := by omega
  have hXn0 : PowerSeries.constantCoeff
      ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) = 0 :=
    constantCoeff_X_pow_ne_zero _ hn
  have hGc : PowerSeries.constantCoeff
      (g.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)))
      = PowerSeries.constantCoeff g :=
    constantCoeff_subst_id _ _ hXn0
  have hGne : g.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hGc
    exact hg hGc.symm
  rw [hf]
  exact mul_ne_zero PowerSeries.X_ne_zero hGne

private theorem A_has (f : PowerSeries ℝ) :
    PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℝ) * f) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  simp only [map_mul, PowerSeries.constantCoeff_X, zero_mul]

private theorem A_ne_of_hg (l : ℕ) (g f : PowerSeries ℝ)
    (hg : PowerSeries.constantCoeff g ≠ 0)
    (hf : f = (PowerSeries.X : PowerSeries ℝ)
      * g.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) :
    (PowerSeries.X : PowerSeries ℝ) * f ≠ 0 := by
  have hfne := f_ne_of_hg l g f hg hf
  exact mul_ne_zero PowerSeries.X_ne_zero hfne

private theorem Bf_eq (f Bf : PowerSeries ℝ)
    (hBf : f - (PowerSeries.X : PowerSeries ℝ)
      = ((PowerSeries.X : PowerSeries ℝ) * Bf).subst
        ((PowerSeries.X : PowerSeries ℝ) * f)) :
    f - (PowerSeries.X : PowerSeries ℝ)
      = ((PowerSeries.X : PowerSeries ℝ) * f)
        * Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f) := by
  have hA := A_has f
  have h : ((PowerSeries.X : PowerSeries ℝ) * Bf).subst
        ((PowerSeries.X : PowerSeries ℝ) * f)
      = ((PowerSeries.X : PowerSeries ℝ) * f)
        * Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f) := by
    rw [PowerSeries.subst_mul hA, PowerSeries.subst_X hA]
  exact hBf.trans h

private theorem Bh_subst (l : ℕ) (f h Bh : PowerSeries ℝ)
    (hfn : f ^ (2 * l + 1)
      = h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)))
    (hBh : h - (PowerSeries.X : PowerSeries ℝ)
      = ((PowerSeries.X : PowerSeries ℝ) * Bh).subst
        ((PowerSeries.X : PowerSeries ℝ) * h)) :
    f ^ (2 * l + 1) - (PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)
      = ((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)
        * Bh.subst (((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)) := by
  have hn : 2 * l + 1 ≠ 0 := by omega
  have hXn : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) :=
    PowerSeries.HasSubst.X_pow hn
  have hXh := A_has h
  have hA0 : PowerSeries.constantCoeff
      ((PowerSeries.X : PowerSeries ℝ) * f) = 0 := by
    simp only [map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hAn0 : PowerSeries.constantCoeff
      (((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)) = 0 := by
    rw [map_pow, hA0, zero_pow hn]
  have hAn : PowerSeries.HasSubst
      (((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hAn0
  have hcomp := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
    (a := (PowerSeries.X : PowerSeries ℝ) * h)
    (b := (PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) hXh hXn
    ((PowerSeries.X : PowerSeries ℝ) * Bh)
  have hXh_sub : ((PowerSeries.X : PowerSeries ℝ) * h).subst
        ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
      = ((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1) := by
    rw [PowerSeries.subst_mul hXn, PowerSeries.subst_X hXn, ← hfn, ← mul_pow]
  have hRHS : PowerSeries.subst
        ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
        (((PowerSeries.X : PowerSeries ℝ) * Bh).subst
          ((PowerSeries.X : PowerSeries ℝ) * h))
      = ((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)
        * Bh.subst (((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)) := by
    rw [hcomp, hXh_sub, PowerSeries.subst_mul hAn, PowerSeries.subst_X hAn]
  have hLHS : PowerSeries.subst
        ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
        (h - (PowerSeries.X : PowerSeries ℝ))
      = f ^ (2 * l + 1) - (PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1) := by
    rw [PowerSeries.subst_sub hXn, ← hfn, PowerSeries.subst_X hXn]
  have happ := congrArg
    (PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))) hBh
  rw [hLHS, hRHS] at happ
  exact happ

private theorem C_coeff_eq (l j : ℕ) (hj : j ≤ l) :
    PowerSeries.C
        ((((2 * l + 1 : ℕ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ))
          * (Nat.choose (l + j) (2 * j) : ℝ))
      = (dCoeffNat l j : PowerSeries ℝ) := by
  have hreal : ((dCoeffNat l j : ℕ) : ℝ)
      = ((Nat.choose (l + j) (2 * j) : ℕ) : ℝ)
        + 2 * ((Nat.choose (l + j) (2 * j + 1) : ℕ) : ℝ) := by
    simp only [dCoeffNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hc : ((((2 * l + 1 : ℕ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ))
        * (Nat.choose (l + j) (2 * j) : ℝ))
      = ((dCoeffNat l j : ℕ) : ℝ) :=
    (coeff_eq_aux l j hj).trans hreal.symm
  rw [hc]
  exact map_natCast PowerSeries.C (dCoeffNat l j)

private noncomputable def Pd (l : ℕ) : PowerSeries ℝ :=
  Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
    ((dCoeffNat l j : ℕ) : PowerSeries ℝ)
      * (PowerSeries.X : PowerSeries ℝ) ^ j)

private theorem subst_natCast (t : PowerSeries ℝ)
    (ha : PowerSeries.HasSubst t) (d : ℕ) :
    PowerSeries.subst t ((d : ℕ) : PowerSeries ℝ)
      = ((d : ℕ) : PowerSeries ℝ) := by
  have h := map_natCast (PowerSeries.substAlgHom (R := ℝ) ha) d
  simp only [PowerSeries.coe_substAlgHom] at h
  exact h

private theorem Pd_subst (l : ℕ) (t : PowerSeries ℝ)
    (ha : PowerSeries.HasSubst t) :
    (Pd l).subst t
      = Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
        ((dCoeffNat l j : ℕ) : PowerSeries ℝ) * t ^ j) := by
  simp only [Pd]
  have hsum : PowerSeries.subst t
        (Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
          ((dCoeffNat l j : ℕ) : PowerSeries ℝ)
            * (PowerSeries.X : PowerSeries ℝ) ^ j))
      = Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
        PowerSeries.subst t (((dCoeffNat l j : ℕ) : PowerSeries ℝ)
          * (PowerSeries.X : PowerSeries ℝ) ^ j)) := by
    have h := map_sum (PowerSeries.substAlgHom (R := ℝ) ha)
      (fun j : ℕ => ((dCoeffNat l j : ℕ) : PowerSeries ℝ)
        * (PowerSeries.X : PowerSeries ℝ) ^ j) (Finset.range (l + 1))
    simp only [PowerSeries.coe_substAlgHom] at h
    exact h
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [PowerSeries.subst_mul ha, subst_natCast t ha,
    PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

private theorem term_factor (A bf : PowerSeries ℝ)
    (l j : ℕ) (hj : j ≤ l) (d : PowerSeries ℝ) :
    d * (A ^ (l - j) * (A * bf) ^ (2 * j + 1))
      = A ^ (l + 1) * (d * (A ^ j * bf ^ (2 * j + 1))) := by
  rw [mul_pow]
  have hexp : (l - j) + (2 * j + 1) = (l + 1) + j := by omega
  have hpow : A ^ (l - j) * A ^ (2 * j + 1) = A ^ (l + 1) * A ^ j := by
    rw [← pow_add, ← pow_add, hexp]
  linear_combination hpow * (d * bf ^ (2 * j + 1))

private theorem term_bf (A bf : PowerSeries ℝ)
    (j : ℕ) (d : PowerSeries ℝ) :
    d * (A ^ j * bf ^ (2 * j + 1))
      = bf * (d * (A * bf ^ 2) ^ j) := by
  have h1 : (A * bf ^ 2) ^ j = A ^ j * (bf ^ 2) ^ j := by rw [mul_pow]
  have h2 : (bf ^ 2) ^ j = bf ^ (2 * j) := by rw [← pow_mul]
  have h3 : bf ^ (2 * j + 1) = bf ^ (2 * j) * bf := by
    rw [show 2 * j + 1 = (2 * j) + 1 from by omega, pow_add, pow_one]
  rw [h1, h2, h3]
  ring

private theorem girard_to_Pd (l : ℕ) (f Bf : PowerSeries ℝ)
    (hBf : f - (PowerSeries.X : PowerSeries ℝ)
      = ((PowerSeries.X : PowerSeries ℝ) * f)
        * Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)) :
    f ^ (2 * l + 1) - (PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)
      = ((PowerSeries.X : PowerSeries ℝ) * f) ^ (l + 1)
        * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)
          * (Pd l).subst (((PowerSeries.X : PowerSeries ℝ) * f)
            * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)) ^ 2)) := by
  set A : PowerSeries ℝ := (PowerSeries.X : PowerSeries ℝ) * f with hA
  set bf : PowerSeries ℝ := Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f) with hbf
  set t : PowerSeries ℝ := A * bf ^ 2 with ht
  have hg := girard (R := PowerSeries ℝ) f (PowerSeries.X : PowerSeries ℝ) l
  have hAX : f * (PowerSeries.X : PowerSeries ℝ) = A := by
    rw [hA, mul_comm]
  have hBfA : f - (PowerSeries.X : PowerSeries ℝ) = A * bf := hBf
  rw [hAX, hBfA] at hg
  have hsum1 : (Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
        ((dCoeffNat l j : ℕ) : PowerSeries ℝ)
          * (A ^ (l - j) * (A * bf) ^ (2 * j + 1))))
      = Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
        A ^ (l + 1) * (((dCoeffNat l j : ℕ) : PowerSeries ℝ)
          * (A ^ j * bf ^ (2 * j + 1)))) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjle : j ≤ l := by omega
    exact term_factor A bf l j hjle ((dCoeffNat l j : ℕ) : PowerSeries ℝ)
  rw [hsum1, ← Finset.mul_sum] at hg
  have ht0 : PowerSeries.constantCoeff t = 0 := by
    rw [ht, hA]
    simp only [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_mul]
  have hth : PowerSeries.HasSubst t :=
    PowerSeries.HasSubst.of_constantCoeff_zero' ht0
  have hPd := Pd_subst l t hth
  have hsum2 : (Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
        ((dCoeffNat l j : ℕ) : PowerSeries ℝ) * (A ^ j * bf ^ (2 * j + 1))))
      = bf * (Pd l).subst t := by
    rw [hPd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have htb : t = A * bf ^ 2 := rfl
    rw [htb]
    exact term_bf A bf j ((dCoeffNat l j : ℕ) : PowerSeries ℝ)
  rw [hsum2] at hg
  exact hg

private theorem Pd_eq_P (l : ℕ) :
    Pd l
      = Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
        (PowerSeries.C
            ((((2 * l + 1 : ℕ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ))
              * (Nat.choose (l + j) (2 * j) : ℝ)) : PowerSeries ℝ)
          * (PowerSeries.X : PowerSeries ℝ) ^ j) := by
  simp only [Pd]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjle : j ≤ l := by omega
  rw [← C_coeff_eq l j hjle]

private theorem cancel_pow (l : ℕ) (A bf bh Psub : PowerSeries ℝ)
    (h : A ^ (2 * l + 1) * bh = A ^ (l + 1) * (bf * Psub))
    (hA : A ≠ 0) :
    A ^ l * bh = bf * Psub := by
  have hexp : 2 * l + 1 = (l + 1) + l := by omega
  have hpow : A ^ (2 * l + 1) = A ^ (l + 1) * A ^ l := by
    rw [hexp, pow_add]
  rw [hpow] at h
  have h2 : A ^ (l + 1) * (A ^ l * bh) = A ^ (l + 1) * (bf * Psub) := by
    rw [← mul_assoc]
    exact h
  have hne : A ^ (l + 1) ≠ 0 := pow_ne_zero _ hA
  exact mul_left_cancel₀ hne h2

private theorem square_mul (l : ℕ) (A bf bh Psub : PowerSeries ℝ)
    (h : A ^ l * bh = bf * Psub) :
    A ^ (2 * l + 1) * bh ^ 2 = (A * bf ^ 2) * Psub ^ 2 := by
  have hsq : (A ^ l * bh) ^ 2 = (bf * Psub) ^ 2 := by rw [h]
  have hA : A * ((A ^ l) ^ 2) = A ^ (2 * l + 1) := by
    have h1 : ((A ^ l) ^ 2 : PowerSeries ℝ) = A ^ (l * 2) := by
      rw [← pow_mul]
    have h2 : l * 2 = 2 * l := by omega
    rw [h1, h2]
    have h3 : (2 * l + 1 : ℕ) = (2 * l) + 1 := by omega
    rw [h3, pow_succ]
    ring
  have hL : A ^ (2 * l + 1) * bh ^ 2 = A * ((A ^ l * bh) ^ 2) := by
    rw [mul_pow, ← mul_assoc, hA]
  have hR : (A * bf ^ 2) * Psub ^ 2 = A * ((bf * Psub) ^ 2) := by
    rw [mul_pow]
    ring
  rw [hL, hR, hsq]

private theorem subst_LHS (l : ℕ) (f Bh : PowerSeries ℝ) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) * f)
        (((PowerSeries.X : PowerSeries ℝ) * Bh ^ 2).subst
          ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)))
      = ((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)
        * (Bh.subst (((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1))) ^ 2 := by
  have hn : 2 * l + 1 ≠ 0 := by omega
  have hXn : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) :=
    PowerSeries.HasSubst.X_pow hn
  have hA := A_has f
  have hA0 : PowerSeries.constantCoeff
      ((PowerSeries.X : PowerSeries ℝ) * f) = 0 := by
    simp only [map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hAn0 : PowerSeries.constantCoeff
      (((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)) = 0 := by
    rw [map_pow, hA0, zero_pow hn]
  have hAn : PowerSeries.HasSubst
      (((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hAn0
  have hcomp := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
    (a := (PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
    (b := (PowerSeries.X : PowerSeries ℝ) * f) hXn hA
    ((PowerSeries.X : PowerSeries ℝ) * Bh ^ 2)
  have hXnA : PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) * f)
        ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
      = ((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1) := by
    rw [PowerSeries.subst_pow hA, PowerSeries.subst_X hA]
  rw [hcomp, hXnA, PowerSeries.subst_mul hAn, PowerSeries.subst_X hAn,
    PowerSeries.subst_pow hAn]

private theorem subst_RHS (f Bf P : PowerSeries ℝ) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) * f)
        (((PowerSeries.X : PowerSeries ℝ) * P ^ 2).subst
          ((PowerSeries.X : PowerSeries ℝ) * Bf ^ 2))
      = (((PowerSeries.X : PowerSeries ℝ) * f)
          * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)) ^ 2)
        * (P.subst (((PowerSeries.X : PowerSeries ℝ) * f)
          * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)) ^ 2)) ^ 2 := by
  have hA := A_has f
  have hXB0 : PowerSeries.constantCoeff
      ((PowerSeries.X : PowerSeries ℝ) * Bf ^ 2) = 0 := by
    simp only [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_mul]
  have hXB : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℝ) * Bf ^ 2) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXB0
  have ht0 : PowerSeries.constantCoeff
      (((PowerSeries.X : PowerSeries ℝ) * f)
        * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)) ^ 2) = 0 := by
    have hA0 : PowerSeries.constantCoeff
        ((PowerSeries.X : PowerSeries ℝ) * f) = 0 := by
      simp only [map_mul, PowerSeries.constantCoeff_X, zero_mul]
    rw [map_mul, map_pow, hA0, zero_mul]
  have ht : PowerSeries.HasSubst
      (((PowerSeries.X : PowerSeries ℝ) * f)
        * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)) ^ 2) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' ht0
  have hcomp := PowerSeries.subst_comp_subst_apply (R := ℝ) (S := ℝ) (T := ℝ)
    (a := (PowerSeries.X : PowerSeries ℝ) * Bf ^ 2)
    (b := (PowerSeries.X : PowerSeries ℝ) * f) hXB hA
    ((PowerSeries.X : PowerSeries ℝ) * P ^ 2)
  have hsub : PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) * f)
        ((PowerSeries.X : PowerSeries ℝ) * Bf ^ 2)
      = ((PowerSeries.X : PowerSeries ℝ) * f)
        * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)) ^ 2 := by
    rw [PowerSeries.subst_mul hA, PowerSeries.subst_X hA,
      PowerSeries.subst_pow hA]
  rw [hcomp, hsub, PowerSeries.subst_mul ht, PowerSeries.subst_X ht,
    PowerSeries.subst_pow ht]

private theorem B_identity (l : ℕ)
    (g f h Bf Bh P : PowerSeries ℝ)
    (hg : PowerSeries.constantCoeff g ≠ 0)
    (hf : f = (PowerSeries.X : PowerSeries ℝ)
      * g.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)))
    (hfn : f ^ (2 * l + 1)
      = h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)))
    (hBf : f - (PowerSeries.X : PowerSeries ℝ)
      = ((PowerSeries.X : PowerSeries ℝ) * Bf).subst
        ((PowerSeries.X : PowerSeries ℝ) * f))
    (hBh : h - (PowerSeries.X : PowerSeries ℝ)
      = ((PowerSeries.X : PowerSeries ℝ) * Bh).subst
        ((PowerSeries.X : PowerSeries ℝ) * h))
    (hP : P = Pd l) :
    ((PowerSeries.X : PowerSeries ℝ) * Bh ^ 2).subst
        ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
      = ((PowerSeries.X : PowerSeries ℝ) * P ^ 2).subst
        ((PowerSeries.X : PowerSeries ℝ) * Bf ^ 2) := by
  have hBf' := Bf_eq f Bf hBf
  have hBh' := Bh_subst l f h Bh hfn hBh
  have hG := girard_to_Pd l f Bf hBf'
  rw [← hP] at hG
  have h_eq : ((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1)
        * Bh.subst (((PowerSeries.X : PowerSeries ℝ) * f) ^ (2 * l + 1))
      = ((PowerSeries.X : PowerSeries ℝ) * f) ^ (l + 1)
        * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)
          * P.subst (((PowerSeries.X : PowerSeries ℝ) * f)
            * (Bf.subst ((PowerSeries.X : PowerSeries ℝ) * f)) ^ 2)) :=
    hBh'.symm.trans hG
  have hAne := A_ne_of_hg l g f hg hf
  have hcancel := cancel_pow _ _ _ _ _ h_eq hAne
  have hsq := square_mul _ _ _ _ _ hcancel
  have hLHS := subst_LHS l f Bh
  have hRHS := subst_RHS f Bf P
  have hsub : PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) * f)
        (((PowerSeries.X : PowerSeries ℝ) * Bh ^ 2).subst
          ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)))
      = PowerSeries.subst ((PowerSeries.X : PowerSeries ℝ) * f)
        (((PowerSeries.X : PowerSeries ℝ) * P ^ 2).subst
          ((PowerSeries.X : PowerSeries ℝ) * Bf ^ 2)) :=
    (hLHS.trans hsq).trans (hRHS.symm)
  have hinj := subst_inj_of_ne_zero
    ((PowerSeries.X : PowerSeries ℝ) * f) hAne (A_has f)
  exact hinj hsub

private theorem pseudo_to_subst (p : PowerSeries ℝ)
    (h : PowerSeries.constantCoeff p = 0
      ∧ ∃ hp : IsUnit (PowerSeries.coeff 1 p),
        p.substInvOfIsUnit hp
          = -(p.subst (-(PowerSeries.X : PowerSeries ℝ)))) :
    p.subst (-p) = -(PowerSeries.X : PowerSeries ℝ) := by
  obtain ⟨h0, hp, hInv⟩ := h
  exact (pseudo_iff_neg p h0 hp).mp hInv

private theorem subst_to_pseudo (p : PowerSeries ℝ)
    (h0 : PowerSeries.constantCoeff p = 0)
    (h1 : PowerSeries.coeff 1 p = 1)
    (hqq : p.subst (-p) = -(PowerSeries.X : PowerSeries ℝ)) :
    PowerSeries.constantCoeff p = 0
      ∧ ∃ hp : IsUnit (PowerSeries.coeff 1 p),
        p.substInvOfIsUnit hp
          = -(p.subst (-(PowerSeries.X : PowerSeries ℝ))) := by
  have hu : IsUnit (PowerSeries.coeff 1 p) := by
    rw [h1]
    exact isUnit_one
  have hInv := (pseudo_iff_neg p h0 hu).mpr hqq
  exact ⟨h0, hu, hInv⟩

/-! # Twin Powers theorem for pseudo-involutory Riordan arrays -/

/-- **Twin Powers Theorem for pseudo-involutions.** Let $l$ be a natural number, let
$n = 2l + 1$, and let $g$ be a formal power series over $\mathbb{R}$ with $g(0) \ne 0$. Put
$f(x) = x\, g(x^n)$ and $h(x) = x\, g(x)^n$. Call a power series $p$ pseudo-involutory if
$p(0) = 0$, the coefficient of $x$ in $p$ is nonzero, and the compositional inverse $\bar p$ of
$p$ satisfies $\bar p(x) = -p(-x)$; call $B$ a B-function of $p$ if
$p(x) - x = x\, p(x)\, B(x\, p(x))$. Let

$$P(x) = \sum_{j=0}^{l} \frac{2l+1}{2j+1} \binom{l+j}{2j} x^j.$$

Suppose that $B_f$ is a B-function of $f$, that $B_h$ is a B-function of $h$, and that $f$ or $h$
is pseudo-involutory. Then $f$ and $h$ are both pseudo-involutory, and

$$x^n B_h(x^n)^2 = x B_f(x)^2 \, P\bigl(x B_f(x)^2\bigr)^2.$$

Proves `Wanted` entry `twin_powers`.

Source: Alexander Burstein and Louis W. Shapiro, "Pseudo-Involutions in the
Riordan Group," Journal of Integer Sequences 25 (2022), Article 22.3.6,
The Twin Powers Theorem (label thm:aeration), lines 1129–1146,
https://cs.uwaterloo.ca/journals/JIS/VOL25/Burstein/burstein14.tex
-/
theorem twin_powers
    (l : ℕ)
    (g : PowerSeries ℝ)
    (Bf : PowerSeries ℝ)
    (Bh : PowerSeries ℝ)
    (hg : PowerSeries.constantCoeff g ≠ 0) :
    let Xr : PowerSeries ℝ := PowerSeries.X
    let n := 2 * l + 1
    let f := Xr * g.subst (Xr ^ n)
    let h := Xr * g ^ n
    let IsPseudoInvolutory := fun p : PowerSeries ℝ =>
      PowerSeries.constantCoeff p = 0 ∧
        ∃ hp : IsUnit (PowerSeries.coeff 1 p),
          p.substInvOfIsUnit hp = -(p.subst (-Xr))
    let IsBFunction := fun p B : PowerSeries ℝ =>
      p - Xr = (Xr * B).subst (Xr * p)
    let P : PowerSeries ℝ :=
      Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
        (PowerSeries.C
            ((((2 * l + 1 : ℕ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ)) *
              (Nat.choose (l + j) (2 * j) : ℝ)) : PowerSeries ℝ) *
          Xr ^ j)
    (IsPseudoInvolutory f ∨ IsPseudoInvolutory h) →
      IsBFunction f Bf →
      IsBFunction h Bh →
      IsPseudoInvolutory f ∧ IsPseudoInvolutory h ∧
        (Xr * Bh ^ 2).subst (Xr ^ n) =
          (Xr * P ^ 2).subst (Xr * Bf ^ 2) := by
  intro Xr n f h IsPseudoInvolutory IsBFunction P hOr hBf hBh
  have _hXr : Xr = (PowerSeries.X : PowerSeries ℝ) := rfl
  have _hn : n = 2 * l + 1 := rfl
  have _hI : IsPseudoInvolutory f = IsPseudoInvolutory f := rfl
  have _hB : IsBFunction f Bf = IsBFunction f Bf := rfl
  have hf : f = (PowerSeries.X : PowerSeries ℝ)
      * g.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) := rfl
  have hBf' : f - (PowerSeries.X : PowerSeries ℝ)
      = ((PowerSeries.X : PowerSeries ℝ) * Bf).subst
        ((PowerSeries.X : PowerSeries ℝ) * f) := hBf
  have hBh' : h - (PowerSeries.X : PowerSeries ℝ)
      = ((PowerSeries.X : PowerSeries ℝ) * Bh).subst
        ((PowerSeries.X : PowerSeries ℝ) * h) := hBh
  have hfn : f ^ (2 * l + 1)
      = h.subst ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1)) :=
    f_pow_eq l g
  have hcf := coeff1_of_BFunction f Bf hBf'
  have hch := coeff1_of_BFunction h Bh hBh'
  obtain ⟨hf0, hf1⟩ := hcf
  obtain ⟨hh0, hh1⟩ := hch
  have hP : P = Pd l := by
    rw [Pd_eq_P]
  have hBeq : ((PowerSeries.X : PowerSeries ℝ) * Bh ^ 2).subst
        ((PowerSeries.X : PowerSeries ℝ) ^ (2 * l + 1))
      = ((PowerSeries.X : PowerSeries ℝ) * P ^ 2).subst
        ((PowerSeries.X : PowerSeries ℝ) * Bf ^ 2) :=
    B_identity l g f h Bf Bh P hg hf hfn hBf' hBh' hP
  cases hOr with
  | inl hPf =>
    have hPf' : PowerSeries.constantCoeff f = 0
        ∧ ∃ hp : IsUnit (PowerSeries.coeff 1 f),
          f.substInvOfIsUnit hp
            = -(f.subst (-(PowerSeries.X : PowerSeries ℝ))) := hPf
    have hff := pseudo_to_subst f hPf'
    have hhh := transfer_fwd_aux l f h hfn hf0 hh0 hff
    have hPh' := subst_to_pseudo h hh0 hh1 hhh
    exact ⟨hPf, hPh', hBeq⟩
  | inr hPh =>
    have hPh' : PowerSeries.constantCoeff h = 0
        ∧ ∃ hp : IsUnit (PowerSeries.coeff 1 h),
          h.substInvOfIsUnit hp
            = -(h.subst (-(PowerSeries.X : PowerSeries ℝ))) := hPh
    have hhh := pseudo_to_subst h hPh'
    have hff := transfer_bwd_aux l Bf f h hfn hf0 hh0 hBf' hhh
    have hPf' := subst_to_pseudo f hf0 hf1 hff
    exact ⟨hPf', hPh, hBeq⟩

end MetaMathlibExt
end
