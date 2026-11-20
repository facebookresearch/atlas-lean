/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.ShermanLemma4Return










namespace StatMech.Onsager

open BigOperators

private theorem summable_mul_prod {K : Type*} [RCLike K]
    {alpha beta : Type*} {f : alpha → K} {g : beta → K}
    (hf : Summable f) (hg : Summable g) :
    Summable (fun z : alpha × beta => f z.1 * g z.2) := by
  apply Summable.of_norm
  have hfn := hf.norm
  have hgn := hg.norm
  simp_rw [norm_mul]
  rw [summable_prod_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  constructor
  · intro a
    exact hgn.mul_left ‖f a‖
  · simp_rw [tsum_mul_left]
    exact hfn.mul_right (∑' b, ‖g b‖)


theorem ons_summable_tupleProd {K : Type*} [RCLike K]
    {alpha : Type*} (wt : alpha → K)
    (hwt : Summable wt) (k : ℕ) :
    Summable (fun p : Fin k → alpha => ∏ i, wt (p i)) := by
  induction k with
  | zero =>
      letI : Finite (Fin 0 → alpha) := Finite.of_subsingleton
      letI : Fintype (Fin 0 → alpha) := Fintype.ofFinite _
      exact (hasSum_fintype _).summable
  | succ k ih =>
      let split : (Fin (k + 1) → alpha) ≃ alpha × (Fin k → alpha) :=
        (Fin.consEquiv (fun _ : Fin (k + 1) => alpha)).symm
      have hp := summable_mul_prod hwt ih
      have hs := (split.summable_iff).mpr hp
      simpa [split, Fin.prod_univ_succ] using hs



theorem ons_tsum_tupleProd_eq_pow {K : Type*} [RCLike K]
    {alpha : Type*} (wt : alpha → K)
    (hwt : Summable wt) (k : ℕ) :
    (∑' p : Fin k → alpha, ∏ i, wt (p i)) = (∑' a, wt a) ^ k := by
  induction k with
  | zero =>
      letI : Finite (Fin 0 → alpha) := Finite.of_subsingleton
      letI : Fintype (Fin 0 → alpha) := Fintype.ofFinite _
      simp [tsum_fintype]
  | succ k ih =>
      let split : (Fin (k + 1) → alpha) ≃ alpha × (Fin k → alpha) :=
        (Fin.consEquiv (fun _ : Fin (k + 1) => alpha)).symm
      let f : alpha × (Fin k → alpha) → K :=
        fun z => wt z.1 * ∏ i, wt (z.2 i)
      have hfun : (fun p : Fin (k + 1) → alpha => ∏ i, wt (p i)) = f ∘ split := by
        funext p
        simp only [f, split, Function.comp_apply, Fin.consEquiv_symm_apply,
          Fin.prod_univ_succ]
        congr 1
      rw [hfun]
      calc
        (∑' p : Fin (k + 1) → alpha, (f ∘ split) p) = ∑' z, f z :=
          split.tsum_eq f
        _ = (∑' a, wt a) * (∑' p : Fin k → alpha, ∏ i, wt (p i)) := by
          rw [(summable_mul_prod hwt (ons_summable_tupleProd wt hwt k)).tsum_prod]
          simp only [Prod.fst, Prod.snd]
          simp_rw [tsum_mul_left]
          rw [tsum_mul_right]
        _ = (∑' a, wt a) ^ (k + 1) := by rw [ih, pow_succ, mul_comm]

noncomputable def ons_listSeriesTerm {alpha : Type*} (wt : alpha → ℂ)
    (l : List alpha) : ℂ :=
  if h : l = [] then 0 else (l.map wt).prod / (l.length : ℂ)

private theorem list_norm_prod_nonneg {alpha : Type*} (wt : alpha → ℂ)
    (l : List alpha) : 0 ≤ (l.map fun a => ‖wt a‖).prod := by
  apply List.prod_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact norm_nonneg _

private theorem norm_listSeriesTerm_le {alpha : Type*} (wt : alpha → ℂ)
    (l : List alpha) :
    ‖ons_listSeriesTerm wt l‖ ≤ (l.map fun a => ‖wt a‖).prod := by
  unfold ons_listSeriesTerm
  split_ifs with h
  · subst l
    simp
  · calc
      ‖(l.map wt).prod / (l.length : ℂ)‖ =
          ‖(l.map wt).prod‖ / ‖(l.length : ℂ)‖ := norm_div _ _
      _ ≤ (l.map fun a => ‖wt a‖).prod / ‖(l.length : ℂ)‖ := by
        have hn := List.norm_prod_le (l.map wt)
        simpa [List.map_map, Function.comp_def] using
          div_le_div_of_nonneg_right hn (norm_nonneg (l.length : ℂ))
      _ ≤ (l.map fun a => ‖wt a‖).prod := by
        apply div_le_self
        · exact list_norm_prod_nonneg wt l
        · rw [norm_natCast]
          exact_mod_cast (List.length_pos_iff.mpr h)

private theorem summable_listNormProd {alpha : Type*} (wt : alpha → ℂ)
    (hwt : Summable fun a => ‖wt a‖) (hsmall : ∑' a, ‖wt a‖ < 1) :
    Summable (fun l : List alpha => (l.map fun a => ‖wt a‖).prod) := by
  let equiv : (Sigma fun n : ℕ => Fin n → alpha) ≃ List alpha :=
    (List.equivSigmaTuple : List alpha ≃ Sigma fun n : ℕ => Fin n → alpha).symm
  apply equiv.summable_iff.mp
  rw [summable_sigma_of_nonneg (fun x => by
    change 0 ≤ (List.map (fun a => ‖wt a‖) (equiv x)).prod
    exact list_norm_prod_nonneg wt (equiv x))]
  constructor
  · intro k
    simpa [equiv, List.equivSigmaTuple_symm_apply, List.map_ofFn, List.prod_ofFn,
      Function.comp_def] using ons_summable_tupleProd (fun a => ‖wt a‖) hwt k
  ·
    have hnonneg : 0 ≤ ∑' a : alpha, ‖wt a‖ :=
      tsum_nonneg (fun a : alpha => norm_nonneg (wt a))
    have hpow := summable_geometric_of_norm_lt_one
      (K := ℝ) (by
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact hsmall)
    convert hpow using 1
    funext k
    rw [← ons_tsum_tupleProd_eq_pow (fun a => ‖wt a‖) hwt k]
    apply tsum_congr
    intro p
    simp [equiv, List.equivSigmaTuple_symm_apply, List.map_ofFn, List.prod_ofFn,
      Function.comp_def]



theorem ons_summable_listSeriesTerm {alpha : Type*} (wt : alpha → ℂ)
    (hwt : Summable fun a => ‖wt a‖) (hsmall : ∑' a, ‖wt a‖ < 1) :
    Summable (ons_listSeriesTerm wt) :=
  Summable.of_norm_bounded (summable_listNormProd wt hwt hsmall)
    (norm_listSeriesTerm_le wt)






theorem ons_tsum_listSeriesTerm {alpha : Type*} (wt : alpha → ℂ)
    (hwt : Summable fun a => ‖wt a‖) (hsmall : ∑' a, ‖wt a‖ < 1) :
    (∑' l : List alpha, ons_listSeriesTerm wt l) =
      ∑' k : ℕ, (∑' a, wt a) ^ (k + 1) / (k + 1) := by
  have hwt' : Summable wt := Summable.of_norm hwt
  have hall := ons_summable_listSeriesTerm wt hwt hsmall
  let equiv : (Sigma fun n : ℕ => Fin n → alpha) ≃ List alpha :=
    (List.equivSigmaTuple : List alpha ≃ Sigma fun n : ℕ => Fin n → alpha).symm
  rw [← equiv.tsum_eq]
  have hsigma : Summable (ons_listSeriesTerm wt ∘ equiv) :=
    equiv.summable_iff.mpr hall
  change (∑' c, (ons_listSeriesTerm wt ∘ equiv) c) = _
  rw [hsigma.tsum_sigma]
  have houter := hsigma.sigma
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).2 houter)]
  have hzero : (∑' c : Fin 0 → alpha,
      (ons_listSeriesTerm wt ∘ equiv) ⟨0, c⟩) = 0 := by
    letI : Finite (Fin 0 → alpha) := Finite.of_subsingleton
    letI : Fintype (Fin 0 → alpha) := Fintype.ofFinite _
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro c _
    simp [equiv, ons_listSeriesTerm]
  rw [hzero, zero_add]
  apply tsum_congr
  intro k
  simp only [equiv, List.equivSigmaTuple_symm_apply, Function.comp_apply]
  have hne (p : Fin (k + 1) → alpha) : List.ofFn p ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  simp_rw [ons_listSeriesTerm, dif_neg (hne _)]
  simp only [List.map_ofFn, List.prod_ofFn, List.length_ofFn, Function.comp_def]
  rw [tsum_div_const]
  rw [ons_tsum_tupleProd_eq_pow wt hwt' (k + 1)]
  push_cast
  ring

end StatMech.Onsager
