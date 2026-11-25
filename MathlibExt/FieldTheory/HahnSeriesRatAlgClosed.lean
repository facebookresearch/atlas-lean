/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HahnSeries_isAlgClosed_rat.lean`
and
`P2M/Sol/S_HahnSeries_isAlgClosed_rat.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.HahnSeries.Basic
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Zorn

@[expose] public section

/-!
# Hahn series with rational exponents are algebraically closed

Hahn series with rational exponents over an algebraically closed field form
an algebraically closed field, in any characteristic. The proof adapts the
Newton–Kaplansky argument: a Newton polygon step improves an approximate
root, and a maximal pseudo-convergent approximation is an exact root.
-/

set_option autoImplicit false

open Polynomial HahnSeries
open scoped Classical

noncomputable section

namespace HahnSeriesAlgClosedAux

variable {K : Type*} [Field K]

private theorem coeff_eval_single (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (c : K) (g : ℚ) :
    (f.eval (HahnSeries.single γ c)).coeff g =
      ∑ i ∈ Finset.range (f.natDegree + 1), (f.coeff i).coeff (g - i • γ) * c ^ i := by
  rw [Polynomial.eval_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [HahnSeries.single_pow, HahnSeries.coeff_mul_single]

end HahnSeriesAlgClosedAux

end

open Polynomial HahnSeries
open scoped Classical

noncomputable section

namespace HahnSeriesAlgClosedAux

variable {K : Type*} [Field K]

private def evalSlopeSupport (f : (HahnSeries ℚ K)[X]) : Finset ℕ :=
  (Finset.range (f.natDegree + 1)).filter (fun j => 1 ≤ j ∧ f.coeff j ≠ 0)

private theorem evalSlopeSupport_nonempty {f : (HahnSeries ℚ K)[X]} (hf : f.Monic)
    (hdeg : 1 ≤ f.natDegree) : (evalSlopeSupport f).Nonempty :=
  ⟨f.natDegree, Finset.mem_filter.mpr
    ⟨Finset.self_mem_range_succ _, hdeg, by rw [hf.coeff_natDegree]; exact one_ne_zero⟩⟩

private theorem mem_evalSlopeSupport {f : (HahnSeries ℚ K)[X]} {j : ℕ} :
    j ∈ evalSlopeSupport f ↔ j ≤ f.natDegree ∧ 1 ≤ j ∧ f.coeff j ≠ 0 := by
  simp only [evalSlopeSupport, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

private theorem exists_evalNewtonSlope {f : (HahnSeries ℚ K)[X]} (hf : f.Monic)
    (hdeg : 1 ≤ f.natDegree) :
    ∃ γ : ℚ,
      (∀ j, 1 ≤ j → j ≤ f.natDegree → f.coeff j ≠ 0 →
        (f.coeff 0).order ≤ (f.coeff j).order + j • γ) ∧
      ∃ j₀, 1 ≤ j₀ ∧ j₀ ≤ f.natDegree ∧ f.coeff j₀ ≠ 0 ∧
        (f.coeff 0).order = (f.coeff j₀).order + j₀ • γ := by
  classical
  set δ : ℚ := (f.coeff 0).order

  set ψ : ℕ → ℚ := fun j => (δ - (f.coeff j).order) / (j : ℚ)
  obtain ⟨j₀, hj₀mem, hj₀max⟩ :=
    Finset.exists_max_image (evalSlopeSupport f) ψ (evalSlopeSupport_nonempty hf hdeg)
  obtain ⟨hj₀le, hj₀1, hj₀ne⟩ := mem_evalSlopeSupport.mp hj₀mem
  set γ : ℚ := ψ j₀
  have hj₀pos : (0 : ℚ) < (j₀ : ℚ) := by exact_mod_cast hj₀1
  refine ⟨γ, ?_, j₀, hj₀1, hj₀le, hj₀ne, ?_⟩
  ·
    intro j hj1 hjle hjne
    have hjpos : (0 : ℚ) < (j : ℚ) := by exact_mod_cast hj1
    have hmem : j ∈ evalSlopeSupport f := mem_evalSlopeSupport.mpr ⟨hjle, hj1, hjne⟩
    have hle : ψ j ≤ γ := hj₀max j hmem

    rw [nsmul_eq_mul]
    have hmul : δ - (f.coeff j).order ≤ (j : ℚ) * γ := by
      rw [div_le_iff₀ hjpos] at hle; linarith [hle]
    linarith
  ·
    rw [nsmul_eq_mul]
    have heq : (j₀ : ℚ) * γ = δ - (f.coeff j₀).order := by
      simp only [γ, ψ]; field_simp
    linarith

private def evalEdgeForm (f : (HahnSeries ℚ K)[X]) (γ : ℚ) : K[X] :=
  ∑ j ∈ Finset.range (f.natDegree + 1),
    Polynomial.C ((f.coeff j).coeff ((f.coeff 0).order - j • γ)) * Polynomial.X ^ j

private theorem evalEdgeForm_coeff (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (k : ℕ)
    (hk : k ≤ f.natDegree) :
    (evalEdgeForm f γ).coeff k = (f.coeff k).coeff ((f.coeff 0).order - k • γ) := by
  unfold evalEdgeForm
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hj), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) h

private theorem evalEdgeForm_coeff_zero (f : (HahnSeries ℚ K)[X]) (γ : ℚ) :
    (evalEdgeForm f γ).coeff 0 = (f.coeff 0).leadingCoeff := by
  rw [evalEdgeForm_coeff f γ 0 (Nat.zero_le _), zero_smul, sub_zero,
    ← HahnSeries.leadingCoeff_eq]

private theorem evalEdgeForm_coeff_of_eq {f : (HahnSeries ℚ K)[X]} {γ : ℚ} {j₀ : ℕ}
    (hj₀le : j₀ ≤ f.natDegree) (heq : (f.coeff 0).order = (f.coeff j₀).order + j₀ • γ) :
    (evalEdgeForm f γ).coeff j₀ = (f.coeff j₀).leadingCoeff := by
  rw [evalEdgeForm_coeff f γ j₀ hj₀le, heq, add_sub_cancel_right, ← HahnSeries.leadingCoeff_eq]

private theorem coeff_eval_single_order_zero (f : (HahnSeries ℚ K)[X]) (γ : ℚ) (c : K) :
    (f.eval (HahnSeries.single γ c)).coeff (f.coeff 0).order =
      (evalEdgeForm f γ).eval c := by
  rw [coeff_eval_single, evalEdgeForm, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem coeff_eval_single_of_lt_order_zero {f : (HahnSeries ℚ K)[X]} {γ : ℚ}
    (hslope : ∀ j, 1 ≤ j → j ≤ f.natDegree → f.coeff j ≠ 0 →
      (f.coeff 0).order ≤ (f.coeff j).order + j • γ)
    (c : K) {g : ℚ} (hg : g < (f.coeff 0).order) :
    (f.eval (HahnSeries.single γ c)).coeff g = 0 := by
  rw [coeff_eval_single]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjle : j ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rcases Nat.eq_zero_or_pos j with hzero | hpos
  ·
    subst hzero
    rw [zero_smul, sub_zero, HahnSeries.coeff_eq_zero_of_lt_order hg, zero_mul]
  ·
    rcases eq_or_ne (f.coeff j) 0 with hcoeff | hcoeff
    · simp [hcoeff]
    · have hbound : (f.coeff 0).order ≤ (f.coeff j).order + j • γ := hslope j hpos hjle hcoeff
      have hlt : g - j • γ < (f.coeff j).order := by linarith
      rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, zero_mul]

variable {Γ : Type*} [LinearOrder Γ]

private theorem monic_taylor {f : (HahnSeries ℚ K)[X]} (hf : f.Monic) (r : HahnSeries ℚ K) :
    (Polynomial.taylor r f).Monic := by
  rw [Polynomial.taylor_apply]
  exact hf.comp (Polynomial.monic_X_add_C r)
    (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero)

end HahnSeriesAlgClosedAux

end

open Polynomial HahnSeries
open scoped Classical

noncomputable section

namespace HahnSeriesAlgClosedAux

variable {K : Type*} [Field K]

private theorem nsmul_top_withTop {j : ℕ} (hj : 1 ≤ j) : j • (⊤ : WithTop ℚ) = ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [add_comm, succ_nsmul, add_top]

private theorem nsmul_coe_withTop (j : ℕ) (q : ℚ) :
    j • (q : WithTop ℚ) = ((j • q : ℚ) : WithTop ℚ) := by
  induction j with
  | zero => simp
  | succ k ih => rw [succ_nsmul, succ_nsmul, ih]; push_cast; ring_nf

private theorem nsmul_le_nsmul_iff_withTop {j : ℕ} (hj : 1 ≤ j) {a b : WithTop ℚ} :
    j • a ≤ j • b ↔ a ≤ b := by
  cases a with
  | top =>
    rw [nsmul_top_withTop hj]
    simp only [top_le_iff]
    cases b with
    | top => simp [nsmul_top_withTop hj]
    | coe q =>
      rw [nsmul_coe_withTop]
      exact ⟨fun h => absurd h WithTop.coe_ne_top, fun h => absurd h WithTop.coe_ne_top⟩
  | coe p =>
    cases b with
    | top => simp [nsmul_top_withTop hj, nsmul_coe_withTop]
    | coe q =>
      rw [nsmul_coe_withTop, nsmul_coe_withTop, WithTop.coe_le_coe, WithTop.coe_le_coe,
        nsmul_eq_mul, nsmul_eq_mul]
      exact mul_le_mul_iff_of_pos_left (by exact_mod_cast hj)

private theorem withTop_add_lt_add_left {a : WithTop ℚ} (ha : a ≠ ⊤) {b c : WithTop ℚ}
    (h : a + b < a + c) : b < c := by
  cases a with
  | top => exact absurd rfl ha
  | coe p =>
    cases b with
    | top => simp only [add_top, ← not_le, le_top, not_true] at h
    | coe q =>
      cases c with
      | top => exact WithTop.coe_lt_top _
      | coe s =>
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_lt_coe] at h
        exact WithTop.coe_lt_coe.mpr (lt_of_add_lt_add_left h)

private theorem eval_sub_eval_eq_sum_taylor (f : (HahnSeries ℚ K)[X]) (r h : HahnSeries ℚ K) :
    f.eval (r + h) - f.eval r =
      ∑ j ∈ Finset.range (f.natDegree + 1),
        (if j = 0 then 0 else (Polynomial.taylor r f).coeff j * h ^ j) := by
  have hnat : (Polynomial.taylor r f).natDegree = f.natDegree := Polynomial.natDegree_taylor f r
  rw [show r + h = h + r from add_comm r h, ← Polynomial.taylor_eval,
    Polynomial.eval_eq_sum_range, hnat]
  rw [show f.eval r = (Polynomial.taylor r f).coeff 0 from (Polynomial.taylor_coeff_zero ..).symm]
  have h0mem : 0 ∈ Finset.range (f.natDegree + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
  rw [← Finset.add_sum_erase _ (fun j => (Polynomial.taylor r f).coeff j * h ^ j) h0mem,
    ← Finset.add_sum_erase _
      (fun j => if j = 0 then 0 else (Polynomial.taylor r f).coeff j * h ^ j) h0mem]
  rw [pow_zero, mul_one, add_sub_cancel_left, if_pos rfl, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_neg (Finset.ne_of_mem_erase hj)]

private def KaplanskySlope (f : (HahnSeries ℚ K)[X]) (r r' : HahnSeries ℚ K) : Prop :=
  ∀ j, 1 ≤ j → j ≤ f.natDegree →
    HahnSeries.addVal ℚ K (f.eval r) ≤
      HahnSeries.addVal ℚ K ((Polynomial.taylor r f).coeff j) +
        j • HahnSeries.addVal ℚ K (r' - r)

private theorem KaplanskySlope.refl (f : (HahnSeries ℚ K)[X]) (r : HahnSeries ℚ K) :
    KaplanskySlope f r r := by
  intro j hj _
  rw [sub_self, AddValuation.map_zero, nsmul_top_withTop hj, add_top]
  exact le_top

private theorem KaplanskySlope.addVal_eval_le {f : (HahnSeries ℚ K)[X]} {r r' : HahnSeries ℚ K}
    (h : KaplanskySlope f r r') :
    HahnSeries.addVal ℚ K (f.eval r) ≤ HahnSeries.addVal ℚ K (f.eval r') := by
  have hsum : HahnSeries.addVal ℚ K (f.eval r) ≤
      HahnSeries.addVal ℚ K (f.eval r' - f.eval r) := by
    rw [show f.eval r' - f.eval r = f.eval (r + (r' - r)) - f.eval r by ring_nf,
      eval_sub_eval_eq_sum_taylor]
    refine (HahnSeries.addVal ℚ K).map_le_sum fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp
    · rw [if_neg hpos.ne', (HahnSeries.addVal ℚ K).map_mul, (HahnSeries.addVal ℚ K).map_pow]
      exact h j hpos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  calc HahnSeries.addVal ℚ K (f.eval r)
      ≤ min (HahnSeries.addVal ℚ K (f.eval r)) (HahnSeries.addVal ℚ K (f.eval r' - f.eval r)) :=
        le_min le_rfl hsum
    _ ≤ HahnSeries.addVal ℚ K (f.eval r + (f.eval r' - f.eval r)) :=
        (HahnSeries.addVal ℚ K).map_add _ _
    _ = HahnSeries.addVal ℚ K (f.eval r') := by ring_nf

private theorem KaplanskySlope.mono {f : (HahnSeries ℚ K)[X]} {r r' r'' : HahnSeries ℚ K}
    (h : KaplanskySlope f r r')
    (hle : HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (r'' - r)) :
    KaplanskySlope f r r'' := by
  intro j hj hjle
  exact (h j hj hjle).trans
    (add_le_add le_rfl ((nsmul_le_nsmul_iff_withTop hj).mpr hle))

private theorem exists_addVal_taylor_coeff_of_addVal_eval_lt {f : (HahnSeries ℚ K)[X]}
    {r r' : HahnSeries ℚ K}
    (hlt : HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r')) :
    ∃ j, 1 ≤ j ∧ j ≤ f.natDegree ∧
      HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j) +
        j • HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (f.eval r) := by

  by_contra habs
  push Not at habs

  have hsum : HahnSeries.addVal ℚ K (f.eval r) <
      HahnSeries.addVal ℚ K (f.eval (r' + (r - r'))) := by
    rw [show f.eval (r' + (r - r')) = f.eval r' + (f.eval (r' + (r - r')) - f.eval r') by ring,
      eval_sub_eval_eq_sum_taylor]
    refine (HahnSeries.addVal ℚ K).map_lt_add hlt ?_
    refine (HahnSeries.addVal ℚ K).map_lt_sum (ne_of_lt (lt_of_lt_of_le hlt le_top)) fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simpa using lt_of_lt_of_le hlt le_top
    · rw [if_neg hpos.ne', (HahnSeries.addVal ℚ K).map_mul, (HahnSeries.addVal ℚ K).map_pow,
        show r - r' = -(r' - r) by ring, (HahnSeries.addVal ℚ K).map_neg]
      exact habs j hpos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [show r' + (r - r') = r by ring] at hsum
  exact lt_irrefl _ hsum

private def KaplanskyLE (f : (HahnSeries ℚ K)[X]) (r r' : HahnSeries ℚ K) : Prop :=
  r = r' ∨ (HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r') ∧
    KaplanskySlope f r r')

private theorem KaplanskyLE.refl (f : (HahnSeries ℚ K)[X]) (r : HahnSeries ℚ K) :
    KaplanskyLE f r r := Or.inl rfl

private instance (f : (HahnSeries ℚ K)[X]) : Std.Refl (KaplanskyLE f) :=
  ⟨KaplanskyLE.refl f⟩

private theorem KaplanskyLE.addVal_eval_le {f : (HahnSeries ℚ K)[X]} {r r' : HahnSeries ℚ K}
    (h : KaplanskyLE f r r') :
    HahnSeries.addVal ℚ K (f.eval r) ≤ HahnSeries.addVal ℚ K (f.eval r') := by
  rcases h with rfl | ⟨hlt, _⟩
  · exact le_rfl
  · exact hlt.le

private theorem KaplanskySlope.of_kaplanskyLE_of_lt {f : (HahnSeries ℚ K)[X]}
    {r r' r'' : HahnSeries ℚ K}
    (hlt : HahnSeries.addVal ℚ K (f.eval r) < HahnSeries.addVal ℚ K (f.eval r'))
    (hslope : KaplanskySlope f r r') (h' : KaplanskyLE f r' r'') :
    KaplanskySlope f r r'' := by
  rcases h' with rfl | ⟨_, hslope'⟩
  · exact hslope
  obtain ⟨j₀, hj₀1, hj₀le, hj₀⟩ := exists_addVal_taylor_coeff_of_addVal_eval_lt hlt
  have hj₀' := hslope' j₀ hj₀1 hj₀le
  have hlt'' : HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) +
        j₀ • HahnSeries.addVal ℚ K (r' - r) <
      HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) +
        j₀ • HahnSeries.addVal ℚ K (r'' - r') :=
    lt_of_le_of_lt hj₀ (lt_of_lt_of_le hlt hj₀')
  have hbne : HahnSeries.addVal ℚ K ((Polynomial.taylor r' f).coeff j₀) ≠ ⊤ := by
    intro htop; rw [htop, top_add, top_add] at hlt''; exact lt_irrefl _ hlt''
  have hηle : HahnSeries.addVal ℚ K (r' - r) ≤ HahnSeries.addVal ℚ K (r'' - r') :=
    (nsmul_le_nsmul_iff_withTop hj₀1).mp (withTop_add_lt_add_left hbne hlt'').le
  refine hslope.mono ?_
  calc HahnSeries.addVal ℚ K (r' - r)
      = min (HahnSeries.addVal ℚ K (r' - r)) (HahnSeries.addVal ℚ K (r'' - r')) :=
        (min_eq_left hηle).symm
    _ ≤ HahnSeries.addVal ℚ K ((r' - r) + (r'' - r')) := (HahnSeries.addVal ℚ K).map_add _ _
    _ = HahnSeries.addVal ℚ K (r'' - r) := by ring_nf

private theorem KaplanskyLE.trans {f : (HahnSeries ℚ K)[X]} {r r' r'' : HahnSeries ℚ K}
    (h : KaplanskyLE f r r') (h' : KaplanskyLE f r' r'') : KaplanskyLE f r r'' := by
  rcases h with rfl | ⟨hlt, hslope⟩
  · exact h'
  exact Or.inr ⟨lt_of_lt_of_le hlt h'.addVal_eval_le, hslope.of_kaplanskyLE_of_lt hlt h'⟩

private theorem KaplanskyLE.antisymm {f : (HahnSeries ℚ K)[X]} {r r' : HahnSeries ℚ K}
    (h : KaplanskyLE f r r') (h' : KaplanskyLE f r' r) : r = r' := by
  rcases h with rfl | ⟨hlt, _⟩
  · rfl
  rcases h' with rfl | ⟨hlt', _⟩
  · rfl
  exact absurd hlt (not_lt.mpr hlt'.le)

private theorem exists_kaplanskyLE_of_eval_ne_zero [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    {r : HahnSeries ℚ K} (hr : f.eval r ≠ 0) :
    ∃ r', r ≠ r' ∧ KaplanskyLE f r r' := by
  set g := Polynomial.taylor r f with hg
  have hgmonic : g.Monic := monic_taylor hf r
  have hgdeg : 1 ≤ g.natDegree := by rw [hg, Polynomial.natDegree_taylor]; exact hdeg
  have hg0 : g.coeff 0 ≠ 0 := by rw [hg, Polynomial.taylor_coeff_zero]; exact hr
  obtain ⟨γ, hslope, j₀, hj₀1, hj₀le, hj₀ne, hj₀eq⟩ := exists_evalNewtonSlope hgmonic hgdeg

  have hconst : (evalEdgeForm g γ).coeff 0 ≠ 0 := by
    rw [evalEdgeForm_coeff_zero]; exact HahnSeries.leadingCoeff_ne_zero.mpr hg0
  have hj₀coeff : (evalEdgeForm g γ).coeff j₀ ≠ 0 := by
    rw [evalEdgeForm_coeff_of_eq hj₀le hj₀eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr hj₀ne
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root (evalEdgeForm g γ)
    ((Polynomial.natDegree_pos_iff_degree_pos.mp
      (le_trans hj₀1 (Polynomial.le_natDegree_of_ne_zero hj₀coeff))).ne')
  have hcne : c ≠ 0 := fun hc0 => by
    rw [Polynomial.IsRoot, hc0, ← Polynomial.coeff_zero_eq_eval_zero] at hc; exact hconst hc

  have hvanish : ∀ q ≤ (g.coeff 0).order, (g.eval (HahnSeries.single γ c)).coeff q = 0 := by
    intro q hq
    rcases lt_or_eq_of_le hq with hlt' | heq
    · exact coeff_eval_single_of_lt_order_zero hslope c hlt'
    · subst heq; rw [coeff_eval_single_order_zero]; exact hc
  have heval0 : f.eval r = g.coeff 0 := by
    rw [hg, Polynomial.taylor_coeff_zero]
  have hltγ : HahnSeries.addVal ℚ K (f.eval r) <
      HahnSeries.addVal ℚ K (g.eval (HahnSeries.single γ c)) := by
    rw [heval0, HahnSeries.addVal_apply_of_ne hg0, HahnSeries.addVal_apply]
    rcases eq_or_ne (g.eval (HahnSeries.single γ c)) 0 with heq | hne
    · rw [heq, HahnSeries.orderTop_zero]; exact WithTop.coe_lt_top _
    · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne, WithTop.coe_lt_coe]
      by_contra hle
      have hkey := hvanish (g.eval (HahnSeries.single γ c)).order (not_lt.mp hle)
      rw [← HahnSeries.leadingCoeff_eq] at hkey
      exact (HahnSeries.leadingCoeff_ne_zero.mpr hne) hkey
  have hevals : g.eval (HahnSeries.single γ c) = f.eval (r + HahnSeries.single γ c) := by
    rw [hg, Polynomial.taylor_eval, add_comm]
  refine ⟨r + HahnSeries.single γ c, fun heq => hcne ?_, Or.inr ⟨hevals ▸ hltγ, ?_⟩⟩
  · have h0 : (HahnSeries.single γ c : HahnSeries ℚ K) = 0 := by
      have heq' : r + HahnSeries.single γ c = r + (0 : HahnSeries ℚ K) := by
        rw [add_zero]; exact heq.symm
      exact add_left_cancel heq'
    exact HahnSeries.single_eq_zero_iff.mp h0
  ·
    intro j hj hjle
    rw [add_sub_cancel_left, heval0, HahnSeries.addVal_apply_of_ne hg0]
    rcases eq_or_ne ((Polynomial.taylor r f).coeff j) 0 with hzero | hne
    · rw [hzero, AddValuation.map_zero, top_add]; exact le_top
    · have hjle' : j ≤ g.natDegree := by rw [hg, Polynomial.natDegree_taylor]; exact hjle
      rw [HahnSeries.addVal_apply_of_ne hne, HahnSeries.addVal_apply,
        HahnSeries.orderTop_single hcne, ← hg, nsmul_coe_withTop]
      exact_mod_cast hslope j hj hjle' hne

private theorem eval_eq_zero_of_kaplanskyLE_max [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    {m : HahnSeries ℚ K} (hmax : ∀ r, KaplanskyLE f m r → KaplanskyLE f r m) :
    f.eval m = 0 := by
  by_contra hm
  obtain ⟨r', hne, hle⟩ := exists_kaplanskyLE_of_eval_ne_zero hf hdeg hm
  exact hne (KaplanskyLE.antisymm hle (hmax r' hle))

section ChainUpperBound

variable {f : (HahnSeries ℚ K)[X]}

private def KaplanskyBelowSlope (f : (HahnSeries ℚ K)[X]) (a : HahnSeries ℚ K) (g : ℚ) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ f.natDegree ∧
    HahnSeries.addVal ℚ K ((Polynomial.taylor a f).coeff j) + ((j • g : ℚ) : WithTop ℚ) <
      HahnSeries.addVal ℚ K (f.eval a)

private theorem nsmul_lt_nsmul_iff_withTop {j : ℕ} (hj : 1 ≤ j) {a b : WithTop ℚ} :
    j • a < j • b ↔ a < b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, nsmul_le_nsmul_iff_withTop hj,
    nsmul_le_nsmul_iff_withTop hj]

private theorem KaplanskyBelowSlope.lt_addVal_sub {a b : HahnSeries ℚ K} {g : ℚ}
    (hbelow : KaplanskyBelowSlope f a g) (hslope : KaplanskySlope f a b) :
    (g : WithTop ℚ) < HahnSeries.addVal ℚ K (b - a) := by
  obtain ⟨j, hj1, hjle, hjlt⟩ := hbelow
  have hj := hslope j hj1 hjle
  have hbne : HahnSeries.addVal ℚ K ((Polynomial.taylor a f).coeff j) ≠ ⊤ := by
    intro htop; rw [htop, top_add] at hjlt; exact not_top_lt hjlt
  have hlt : ((j • g : ℚ) : WithTop ℚ) < j • HahnSeries.addVal ℚ K (b - a) :=
    withTop_add_lt_add_left hbne (lt_of_lt_of_le hjlt hj)
  rw [← nsmul_coe_withTop] at hlt
  exact (nsmul_lt_nsmul_iff_withTop hj1).mp hlt

private theorem kaplanskyChain_coeff_eq {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) {a b : HahnSeries ℚ K} (ha : a ∈ C) (hb : b ∈ C)
    {g : ℚ} (hga : KaplanskyBelowSlope f a g) (hgb : KaplanskyBelowSlope f b g) :
    a.coeff g = b.coeff g := by
  rcases hC.total ha hb with hab | hab
  · rcases hab with rfl | ⟨_, hslope⟩
    · rfl
    have hlt := hga.lt_addVal_sub hslope
    rw [HahnSeries.addVal_apply] at hlt
    have hdiff := HahnSeries.coeff_eq_zero_of_lt_orderTop hlt
    rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
    exact hdiff.symm
  · rcases hab with rfl | ⟨_, hslope⟩
    · rfl
    have hlt := hgb.lt_addVal_sub hslope
    rw [HahnSeries.addVal_apply] at hlt
    have hdiff := HahnSeries.coeff_eq_zero_of_lt_orderTop hlt
    rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
    exact hdiff

private def kaplanskyLimitCoeff (C : Set (HahnSeries ℚ K)) (g : ℚ) : K :=
  if h : ∃ a ∈ C, KaplanskyBelowSlope f a g then h.choose.coeff g else 0

private theorem kaplanskyLimitCoeff_eq {C : Set (HahnSeries ℚ K)} (hC : IsChain (KaplanskyLE f) C)
    {a : HahnSeries ℚ K} (ha : a ∈ C) {g : ℚ} (hga : KaplanskyBelowSlope f a g) :
    kaplanskyLimitCoeff (f := f) C g = a.coeff g := by
  unfold kaplanskyLimitCoeff
  rw [dif_pos ⟨a, ha, hga⟩]
  obtain ⟨hb, hgb⟩ := (⟨a, ha, hga⟩ : ∃ a ∈ C, KaplanskyBelowSlope f a g).choose_spec
  exact kaplanskyChain_coeff_eq hC hb ha hgb hga

private theorem kaplanskyLimitCoeff_isPWO_support {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    (Function.support (kaplanskyLimitCoeff (f := f) C)).IsPWO := by
  refine Set.IsWF.isPWO ?_
  rw [Set.isWF_iff_no_descending_seq]
  intro s hanti hs
  have hf0 : kaplanskyLimitCoeff (f := f) C (s 0) ≠ 0 := hs 0
  have hex : ∃ a ∈ C, KaplanskyBelowSlope f a (s 0) := by
    by_contra hnone; rw [kaplanskyLimitCoeff, dif_neg hnone] at hf0; exact hf0 rfl
  obtain ⟨a₀, ha₀, hga₀⟩ := hex

  have hsk : ∀ k, s k ∈ a₀.support := by
    intro k
    have hsk0 : s k ≤ s 0 := hanti.antitone (Nat.zero_le k)

    obtain ⟨j, hj1, hjle, hjlt⟩ := hga₀
    have hgak : KaplanskyBelowSlope f a₀ (s k) := ⟨j, hj1, hjle, by
      refine lt_of_le_of_lt ?_ hjlt
      gcongr⟩
    have heq := kaplanskyLimitCoeff_eq hC ha₀ hgak
    rw [HahnSeries.mem_support, ← heq]
    exact hs k
  have hWF := a₀.isWF_support
  rw [Set.isWF_iff_no_descending_seq] at hWF
  exact hWF s hanti hsk

private def kaplanskyLimit {C : Set (HahnSeries ℚ K)} (hC : IsChain (KaplanskyLE f) C) :
    HahnSeries ℚ K where
  coeff := kaplanskyLimitCoeff (f := f) C
  isPWO_support' := kaplanskyLimitCoeff_isPWO_support hC

private theorem kaplanskySlope_kaplanskyLimit {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) {a : HahnSeries ℚ K} (ha : a ∈ C) :
    KaplanskySlope f a (kaplanskyLimit hC) := by
  intro j hj hjle

  by_contra hlt
  push Not at hlt

  have hne : kaplanskyLimit hC - a ≠ 0 := by
    intro heq
    rw [heq, AddValuation.map_zero, nsmul_top_withTop hj, add_top] at hlt
    exact not_top_lt hlt
  set q : ℚ := (kaplanskyLimit hC - a).order with hq
  have hqval : HahnSeries.addVal ℚ K (kaplanskyLimit hC - a) = (q : WithTop ℚ) := by
    rw [HahnSeries.addVal_apply_of_ne hne, hq]
  rw [hqval, nsmul_coe_withTop] at hlt

  have hbelow : KaplanskyBelowSlope f a q := ⟨j, hj, hjle, hlt⟩

  have hcoeff : (kaplanskyLimit hC - a).coeff q = 0 := by
    rw [HahnSeries.coeff_sub]
    show kaplanskyLimitCoeff (f := f) C q - a.coeff q = 0
    rw [kaplanskyLimitCoeff_eq hC ha hbelow, sub_self]

  rw [hq, ← HahnSeries.leadingCoeff_eq] at hcoeff
  exact (HahnSeries.leadingCoeff_ne_zero.mpr hne) hcoeff

private theorem exists_kaplanskyLE_upperBound {C : Set (HahnSeries ℚ K)}
    (hC : IsChain (KaplanskyLE f) C) :
    ∃ ub, ∀ a ∈ C, KaplanskyLE f a ub := by

  by_cases hmax : ∃ m ∈ C, ∀ a ∈ C, KaplanskyLE f a m
  · obtain ⟨m, _, hm⟩ := hmax; exact ⟨m, hm⟩
  push Not at hmax

  have hnomax : ∀ a ∈ C, ∃ b ∈ C, KaplanskyLE f a b ∧ a ≠ b := by
    intro a ha
    obtain ⟨b, hb, hnle⟩ := hmax a ha
    rcases hC.total ha hb with hab | hab
    · exact ⟨b, hb, hab, fun heq => hnle (heq ▸ KaplanskyLE.refl f a)⟩
    · exact absurd hab hnle

  refine ⟨kaplanskyLimit hC, fun a ha => ?_⟩
  obtain ⟨b, hb, hab, hne⟩ := hnomax a ha
  have hltab : HahnSeries.addVal ℚ K (f.eval a) < HahnSeries.addVal ℚ K (f.eval b) := by
    rcases hab with rfl | ⟨hlt, _⟩
    · exact absurd rfl hne
    · exact hlt
  refine Or.inr ⟨?_, kaplanskySlope_kaplanskyLimit hC ha⟩
  exact lt_of_lt_of_le hltab (kaplanskySlope_kaplanskyLimit hC hb).addVal_eval_le

end ChainUpperBound

private theorem exists_isRoot_hahnSeries [IsAlgClosed K] {f : (HahnSeries ℚ K)[X]}
    (hf : f.Monic) (hdeg : 1 ≤ f.natDegree) :
    ∃ r : HahnSeries ℚ K, f.IsRoot r := by
  obtain ⟨m, hmax⟩ := exists_maximal_of_chains_bounded
    (r := KaplanskyLE f) (fun C hC => exists_kaplanskyLE_upperBound hC)
    (fun {a b c} => KaplanskyLE.trans)
  exact ⟨m, eval_eq_zero_of_kaplanskyLE_max hf hdeg hmax⟩

private theorem isAlgClosed_hahnSeries_rat [IsAlgClosed K] :
    IsAlgClosed (HahnSeries ℚ K) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  have hdeg : 1 ≤ f.natDegree := by
    by_contra hlt
    have h1 : f = 1 := hf.natDegree_eq_zero.mp (Nat.lt_one_iff.mp (not_le.mp hlt))
    exact hirr.not_isUnit (h1 ▸ isUnit_one)
  exact exists_isRoot_hahnSeries hf hdeg

end HahnSeriesAlgClosedAux

end

namespace HahnSeries

/-- Rational-exponent Hahn series over an algebraically closed field form
an algebraically closed field, in any characteristic. -/
theorem isAlgClosed_rat {K : Type*} [Field K] [IsAlgClosed K] :
    IsAlgClosed (HahnSeries ℚ K) :=
  HahnSeriesAlgClosedAux.isAlgClosed_hahnSeries_rat

end HahnSeries
