/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.CompletelyRegular

/-!

# Series over lists of first-return loops

Summability and evaluation of the series `∑ₗ (∏ wt) / length l` over finite lists.

## i. Overview

For a weight `wt : α → ℂ` with `∑ ‖wt a‖ < 1`, the function on lists `l ↦ (∏_{a ∈ l} wt a) / |l|`
(and `0` on the empty list) is summable, and its sum equals
`∑ₖ (∑ₐ wt a) ^ (k + 1) / (k + 1) = -log (1 - ∑ₐ wt a)`. Lists of length `k` correspond to tuples
`Fin k → α`, whose product sums factor as `(∑ₐ wt a) ^ k`. In Sherman's argument `α` is the set of
first-return loops at a directed edge and a list is the factorization of a rooted closed walk.

## ii. Key results

- `ons_tsum_tupleProd_eq_pow` : `∑ over p : Fin k → α of ∏ wt (p i)` is `(∑ wt) ^ k`
- `ons_summable_listSeriesTerm` : summability of the list series
- `ons_tsum_listSeriesTerm` : the list series equals the logarithmic series in `∑ wt`

## iii. Table of contents

- A. Products of summable families
- B. The list series

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open BigOperators

/-! ## A. Products of summable families -/

private lemma summable_mul_prod {K : Type*} [RCLike K]
    {alpha beta : Type*} {f : alpha → K} {g : beta → K}
    (hf : Summable f) (hg : Summable g) :
    Summable (fun z : alpha × beta => f z.1 * g z.2) :=
  summable_mul_of_summable_norm hf.norm hg.norm

lemma ons_summable_tupleProd {K : Type*} [RCLike K]
    {alpha : Type*} (wt : alpha → K)
    (hwt : Summable wt) (k : ℕ) :
    Summable (fun p : Fin k → alpha => ∏ i, wt (p i)) := by
  induction k with
  | zero =>
      let : Finite (Fin 0 → alpha) := Finite.of_subsingleton
      let : Fintype (Fin 0 → alpha) := Fintype.ofFinite _
      exact (hasSum_fintype _).summable
  | succ k ih =>
      let split : (Fin (k + 1) → alpha) ≃ alpha × (Fin k → alpha) :=
        (Fin.consEquiv (fun _ : Fin (k + 1) => alpha)).symm
      have hp := summable_mul_prod hwt ih
      have hs := (split.summable_iff).mpr hp
      simpa [split, Fin.prod_univ_succ, Function.comp_def, Fin.tail] using hs

lemma ons_tsum_tupleProd_eq_pow {K : Type*} [RCLike K]
    {alpha : Type*} (wt : alpha → K)
    (hwt : Summable wt) (k : ℕ) :
    (∑' p : Fin k → alpha, ∏ i, wt (p i)) = (∑' a, wt a) ^ k := by
  induction k with
  | zero =>
      let : Finite (Fin 0 → alpha) := Finite.of_subsingleton
      let : Fintype (Fin 0 → alpha) := Fintype.ofFinite _
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
          simp only
          simp_rw [tsum_mul_left]
          rw [tsum_mul_right]
        _ = (∑' a, wt a) ^ (k + 1) := by rw [ih, pow_succ, mul_comm]

/-! ## B. The list series -/

/-- The term `(∏_{a ∈ l} wt a) / |l|` of the list series, set to `0` on the empty list. -/
noncomputable def ons_listSeriesTerm {alpha : Type*} (wt : alpha → ℂ)
    (l : List alpha) : ℂ :=
  if _h : l = [] then 0 else (l.map wt).prod / (l.length : ℂ)

private lemma list_norm_prod_nonneg {alpha : Type*} (wt : alpha → ℂ)
    (l : List alpha) : 0 ≤ (l.map fun a => ‖wt a‖).prod := by
  apply List.prod_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact norm_nonneg _

private lemma norm_listSeriesTerm_le {alpha : Type*} (wt : alpha → ℂ)
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

private lemma summable_listNormProd {alpha : Type*} (wt : alpha → ℂ)
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
  · have hnonneg : 0 ≤ ∑' a : alpha, ‖wt a‖ :=
      tsum_nonneg (fun a : alpha => norm_nonneg (wt a))
    have hpow := summable_geometric_of_norm_lt_one
      (R := ℝ) (by
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact hsmall)
    convert hpow using 1
    funext k
    rw [← ons_tsum_tupleProd_eq_pow (fun a => ‖wt a‖) hwt k]
    apply tsum_congr
    intro p
    simp [equiv, List.equivSigmaTuple_symm_apply, List.map_ofFn, List.prod_ofFn,
      Function.comp_def]

lemma ons_summable_listSeriesTerm {alpha : Type*} (wt : alpha → ℂ)
    (hwt : Summable fun a => ‖wt a‖) (hsmall : ∑' a, ‖wt a‖ < 1) :
    Summable (ons_listSeriesTerm wt) :=
  Summable.of_norm_bounded (summable_listNormProd wt hwt hsmall)
    (norm_listSeriesTerm_le wt)

lemma ons_tsum_listSeriesTerm {alpha : Type*} (wt : alpha → ℂ)
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
    let : Finite (Fin 0 → alpha) := Finite.of_subsingleton
    let : Fintype (Fin 0 → alpha) := Fintype.ofFinite _
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
  simp_rw [ons_listSeriesTerm, dite_eq_right (hne _)]
  simp only [List.map_ofFn, List.prod_ofFn, List.length_ofFn, Function.comp_def]
  rw [tsum_div_const]
  rw [ons_tsum_tupleProd_eq_pow wt hwt' (k + 1)]
  push_cast
  ring

end StatMech.Onsager
