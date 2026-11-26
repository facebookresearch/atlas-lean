/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Unit-weighted zero sums from valuation parity

## References

- Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants of `ℤ_n`*,
  INTEGERS 24 (2024), Article A38, pp. 1–16, Lemma 3.5.
- Simon Griffiths, *The Erdős–Ginzburg–Ziv theorem with units*, Discrete Mathematics 308 (2008),
  pp. 5473–5484, Lemma 2.4 and the remark following it.
-/

namespace MetaMathlibExt

-- Match up the units; each pair cancels using the other member as a weight, with opposite signs.
private theorem exists_unit_weights_of_even_card {ι R : Type*} [Fintype ι] [CommRing R]
    (u : ι → R) (hu : ∀ i, IsUnit (u i)) (h : Even (Fintype.card ι)) :
    ∃ a : ι → R, (∀ i, IsUnit (a i)) ∧ ∑ i, a i * u i = 0 := by
  classical
  obtain ⟨m, hm⟩ := h
  let e : ι ≃ Fin 2 × Fin m := Fintype.equivOfCardEq (by simpa [two_mul] using hm)
  let b (ij : Fin 2 × Fin m) : R :=
    if ij.1 = 0 then u (e.symm (1, ij.2)) else -u (e.symm (0, ij.2))
  refine ⟨b ∘ e, fun i => ?_, ?_⟩
  · dsimp [b, Function.comp]
    split
    · exact hu _
    · exact (hu _).neg
  calc
    _ = ∑ ij : Fin 2 × Fin m, b ij * u (e.symm ij) := by
      apply Fintype.sum_equiv e
      intro i
      simp [Function.comp]
    _ = 0 := by
      rw [Fintype.sum_prod_type_right]
      simp [Fin.sum_univ_two, b, mul_comm]

/-- **Griffiths' criterion for unit-weighted zero sums modulo a prime power.** Let $p$ be a prime,
let $r$ and $k$ be natural numbers, put $n = p^r$, and let
$x_1, \dots, x_k \in \mathbb{Z}/n\mathbb{Z}$. Suppose that for each $i \in [1, r]$ the set
$X_i = \{j : x_j \not\equiv 0 \pmod{p^i}\}$ has an even number of elements. Then there are units
$a_1, \dots, a_k$ of $\mathbb{Z}/n\mathbb{Z}$ with $a_1 x_1 + \dots + a_k x_k = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.5 (`integers-2024-A38-lem-3-5`). -/
public theorem unitWeightedZeroSum_of_even_nonDivisible {p r k : ℕ} (hp : p.Prime)
    (x : Fin k → ZMod (p ^ r))
    (h : ∀ i ∈ Finset.Icc 1 r, Even (Finset.univ.filter fun j => ¬ p ^ i ∣ (x j).val).card) :
    ∃ a : Fin k → ZMod (p ^ r), (∀ i, IsUnit (a i)) ∧ ∑ i, a i * x i = 0 := by
  classical
  let : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hlt (j : Fin k) (hj : x j ≠ 0) : multiplicity p (x j).val < r := by
    have hn : (x j).val ≠ 0 := (ZMod.val_eq_zero _).not.mpr hj
    exact lt_of_not_ge fun hr => (x j).val_lt.not_ge <|
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((Nat.pow_dvd_iff_le_multiplicity hp.ne_one hn).2 hr)
  -- Give the zero entries valuation `r`; every other entry has strictly smaller valuation.
  let v (j : Fin k) : Fin (r + 1) :=
    ⟨if x j = 0 then r else multiplicity p (x j).val, by
      split_ifs with hj
      · exact Nat.lt_succ_self r
      · exact (hlt j hj).trans (Nat.lt_succ_self r)⟩
  have hv (j : Fin k) (hj : x j ≠ 0) : (v j : ℕ) = multiplicity p (x j).val := ite_eq_right hj
  have hbelow (i : ℕ) (hi : i ≤ r) (j : Fin k) :
      ((v j : ℕ) < i) ↔ ¬ p ^ i ∣ (x j).val := by
    by_cases hj : x j = 0
    · simp [v, hj, Nat.not_lt.mpr hi]
    · rw [hv j hj, Nat.pow_dvd_iff_le_multiplicity hp.ne_one ((ZMod.val_eq_zero _).not.mpr hj),
        not_le]
  let below (i : ℕ) := Finset.univ.filter fun j : Fin k => (v j : ℕ) < i
  have heven (i : ℕ) (hi : i ≤ r) : Even (below i).card := by
    cases i with
    | zero => simp [below]
    | succ i =>
      simpa only [below, hbelow (i + 1) hi] using
        h (i + 1) (Finset.mem_Icc.mpr ⟨Nat.succ_pos i, hi⟩)
  have hfiber (i : Fin (r + 1)) (hi : (i : ℕ) < r) : Even (Fintype.card {j // v j = i}) := by
    have hsub : below i ⊆ below ((i : ℕ) + 1) := by
      intro j hj
      simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      omega
    have heq : (Finset.univ.filter fun j => v j = i) = below ((i : ℕ) + 1) \ below i := by
      ext j
      simp only [below, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Fin.ext_iff]
      omega
    rw [Fintype.card_subtype, heq, Finset.card_sdiff_of_subset hsub]
    exact (Nat.even_sub (Finset.card_le_card hsub)).2
      (iff_of_true (heven _ hi) (heven _ hi.le))
  have hweights (i : Fin (r + 1)) :
      ∃ a : {j // v j = i} → ZMod (p ^ r), (∀ j, IsUnit (a j)) ∧ ∑ j, a j * x j = 0 := by
    by_cases hi : (i : ℕ) < r
    · have hnz (j : {j // v j = i}) : x j ≠ 0 := by
        intro hz
        have hvi : (v j : ℕ) = (i : ℕ) := congrArg Fin.val j.property
        have : (i : ℕ) = r := hvi.symm.trans (ite_eq_left hz)
        omega
      let u (j : {j // v j = i}) := (x j).val / p ^ (i : ℕ)
      have hm (j : {j // v j = i}) : multiplicity p (x j).val = (i : ℕ) :=
        (hv j (hnz j)).symm.trans (congrArg Fin.val j.property)
      have hdiv (j : {j // v j = i}) (a : ℕ) : p ^ a ∣ (x j).val ↔ a ≤ (i : ℕ) := by
        rw [Nat.pow_dvd_iff_le_multiplicity hp.ne_one ((ZMod.val_eq_zero _).not.mpr (hnz j)), hm j]
      have hfactor (j : {j // v j = i}) : p ^ (i : ℕ) * u j = (x j).val :=
        Nat.mul_div_cancel' ((hdiv j i).2 le_rfl)
      have hunit (j : {j // v j = i}) : IsUnit (u j : ZMod (p ^ r)) := by
        apply (ZMod.isUnit_iff_coprime _ _).2
        refine ((hp.coprime_iff_not_dvd.mpr ?_).symm).pow_right r
        intro hd
        have hmul := Nat.mul_dvd_mul_left (p ^ (i : ℕ)) hd
        rw [← pow_succ, hfactor j, hdiv] at hmul
        omega
      obtain ⟨a, ha, hz⟩ := exists_unit_weights_of_even_card _ hunit (hfiber i hi)
      refine ⟨a, ha, ?_⟩
      calc
        ∑ j, a j * x j = (p : ZMod (p ^ r)) ^ (i : ℕ) * ∑ j, a j * u j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          calc
            a j * x j = a j * ((p : ZMod (p ^ r)) ^ (i : ℕ) * u j) := by
              rw [← Nat.cast_pow, ← Nat.cast_mul, hfactor, ZMod.natCast_zmod_val]
            _ = _ := mul_left_comm _ _ _
        _ = 0 := by rw [hz, mul_zero]
    · refine ⟨fun _ => 1, fun _ => isUnit_one, Finset.sum_eq_zero fun j _ => ?_⟩
      have hz : x j = 0 := by
        by_contra hn
        exact hi ((congrArg Fin.val j.property).symm.trans_lt ((hv j hn).trans_lt (hlt j hn)))
      simp [hz]
  choose a ha hsum using hweights
  let c (j : Fin k) : ZMod (p ^ r) := a (v j) ⟨j, rfl⟩
  refine ⟨c, fun j => ha (v j) ⟨j, rfl⟩, ?_⟩
  calc
    _ = ∑ ij : Σ i : Fin (r + 1), {j // v j = i}, a ij.1 ij.2 * x ij.2 := by
      symm
      apply Fintype.sum_equiv (Equiv.sigmaFiberEquiv v)
      rintro ⟨i, j, hj⟩
      subst i
      rfl
    _ = 0 := by rw [Fintype.sum_sigma]; simp [hsum]

end MetaMathlibExt
