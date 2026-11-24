/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MultipleZeta.Series
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Convergence of admissible strict multiple-zeta series
-/

section
namespace MetaMathlibExt.MultipleZeta

/-- Auxiliary: real `rpow` distributes over finset products of positive reals. -/
private theorem auxProdRpow (ι : Type*) (s : Finset ι) (x : ι → ℝ) (c : ℝ) :
    (∀ i ∈ s, 0 < x i) → ∏ i ∈ s, (x i) ^ c = (∏ i ∈ s, x i) ^ c := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.prod_empty, Real.one_rpow]
  · intro a t hat iht hx
    have ha0 : 0 ≤ x a := le_of_lt (hx a (Finset.mem_insert_self a t))
    have ht0 : 0 ≤ ∏ i ∈ t, x i :=
      le_of_lt (Finset.prod_pos (fun i hi => hx i (Finset.mem_insert_of_mem hi)))
    have iht' := iht (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert hat, Finset.prod_insert hat, Real.mul_rpow ha0 ht0, iht']

/-- Auxiliary: the `rpow` `p`-series over positive naturals. -/
private theorem auxSummablePnat (c : ℝ) (hc : 1 < c) :
    Summable (fun n : PNat => (((n : ℕ) : ℝ) ^ c)⁻¹) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ (-c))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have h2 : Summable (fun n : PNat => ((((n : ℕ)) : ℝ) ^ (-c))) :=
    (summable_pnat_iff_summable_nat (f := fun n : ℕ => ((n : ℝ) ^ (-c)))).mpr h1
  have h3 : (fun n : PNat => ((((n : ℕ)) : ℝ) ^ (-c)))
      = (fun n : PNat => ((((n : ℕ)) : ℝ) ^ c)⁻¹) := by
    funext n
    exact Real.rpow_neg (Nat.cast_nonneg _) c
  rw [h3] at h2
  exact h2

/-- Auxiliary: products of a summable positive family over `Fin r → PNat` are summable. -/
private theorem auxSummablePi (f : PNat → ℝ) (hf : Summable f) (hpos : ∀ n, 0 < f n)
    (r : ℕ) (hr : 0 < r) : Summable (fun m : Fin r → PNat => ∏ i, f (m i)) := by
  have hr1 : 1 ≤ r := hr
  refine Nat.le_induction ?base ?step r hr1
  · have hGe : (fun m : Fin 1 → PNat => ∏ i, f (m i))
          ∘ ⇑(Equiv.funUnique (Fin 1) PNat).symm = f := by
      funext n
      have h1 : ((Equiv.funUnique (Fin 1) PNat).symm n) = fun _ => n := rfl
      change ∏ i : Fin 1, f (((Equiv.funUnique (Fin 1) PNat).symm n) i) = f n
      rw [h1, Fin.prod_univ_one]
    have h2 : Summable ((fun m : Fin 1 → PNat => ∏ i, f (m i))
        ∘ ⇑(Equiv.funUnique (Fin 1) PNat).symm) := by
      rw [hGe]
      exact hf
    exact (Equiv.funUnique (Fin 1) PNat).symm.summable_iff.mp h2
  · intro n hn ih
    have hGe : (fun m : Fin (n + 1) → PNat => ∏ i, f (m i))
          ∘ ⇑(Fin.consEquiv fun _ => PNat)
        = fun p : PNat × (Fin n → PNat) => f p.1 * ∏ i, f (p.2 i) := by
      funext ⟨a, t⟩
      have h1 : (Fin.consEquiv (fun _ => PNat)) (a, t) = Fin.cons a t := rfl
      change ∏ i : Fin (n + 1), f (((Fin.consEquiv fun _ => PNat) (a, t)) i)
        = f a * ∏ i, f (t i)
      simp only [h1, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hSi : Summable (fun q : Σ _ : PNat, (Fin n → PNat) => f q.1 * ∏ i, f (q.2 i)) := by
      have hnn : ∀ q : Σ _ : PNat, (Fin n → PNat), 0 ≤ f q.1 * ∏ i, f (q.2 i) :=
        fun q => mul_nonneg (le_of_lt (hpos _))
          (le_of_lt (Finset.prod_pos (fun i _ => hpos _)))
      have hfib : ∀ a : PNat, Summable (fun t : Fin n → PNat => f a * ∏ i, f (t i)) :=
        fun a => ih.mul_left (f a)
      have htsum : Summable (fun a : PNat => ∑' t : Fin n → PNat, f a * ∏ i, f (t i)) := by
        have heq : (fun a : PNat => ∑' t : Fin n → PNat, f a * ∏ i, f (t i))
            = fun a => f a * ∑' t : Fin n → PNat, ∏ i, f (t i) := by
          funext a
          exact tsum_mul_left
        rw [heq]
        exact hf.mul_right _
      exact (summable_sigma_of_nonneg hnn).mpr ⟨hfib, htsum⟩
    have hS : Summable (fun p : PNat × (Fin n → PNat) => f p.1 * ∏ i, f (p.2 i)) := by
      have hEq : (fun p : PNat × (Fin n → PNat) => f p.1 * ∏ i, f (p.2 i))
            ∘ ⇑(Equiv.sigmaEquivProd PNat (Fin n → PNat))
          = fun q : Σ _ : PNat, (Fin n → PNat) => f q.1 * ∏ i, f (q.2 i) := by
        funext q
        rfl
      have h2 : Summable ((fun p : PNat × (Fin n → PNat) => f p.1 * ∏ i, f (p.2 i))
          ∘ ⇑(Equiv.sigmaEquivProd PNat (Fin n → PNat))) := by
        rw [hEq]
        exact hSi
      exact (Equiv.sigmaEquivProd PNat (Fin n → PNat)).summable_iff.mp h2
    have h2 : Summable ((fun m : Fin (n + 1) → PNat => ∏ i, f (m i))
        ∘ ⇑(Fin.consEquiv fun _ => PNat)) := by
      rw [hGe]
      exact hS
    exact (Fin.consEquiv (fun _ => PNat)).summable_iff.mp h2

/-- Auxiliary: the key finitary estimate, for minimal exponents. -/
private theorem auxKeyMin (r : ℕ) (n : Fin r → ℕ) (hr : 1 ≤ r) [NeZero r]
    (hdec : ∀ i : Fin r, i ≠ 0 → n i < n 0) :
    (∏ i, n i) ^ (r + 1) ≤ (∏ i, n i ^ (if i = 0 then 2 else 1)) ^ r := by
  have h0 : (0 : Fin r) ∈ Finset.univ := Finset.mem_univ _
  have e1 : ∏ i, n i = n 0 * ∏ i ∈ Finset.univ.erase 0, n i :=
    (Finset.mul_prod_erase _ _ h0).symm
  have e2t : ∏ i ∈ Finset.univ.erase (0 : Fin r), n i ^ (if i = 0 then 2 else 1)
      = ∏ i ∈ Finset.univ.erase (0 : Fin r), n i := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [ite_eq_right (Finset.ne_of_mem_erase hi), pow_one]
  have e2 : ∏ i, n i ^ (if i = 0 then 2 else 1)
      = n 0 ^ 2 * ∏ i ∈ Finset.univ.erase (0 : Fin r), n i := by
    have h := Finset.mul_prod_erase Finset.univ (fun i => n i ^ (if i = 0 then 2 else 1)) h0
    beta_reduce at h
    rw [e2t, ite_eq_left rfl] at h
    exact h.symm
  have hP : ∏ i ∈ Finset.univ.erase (0 : Fin r), n i ≤ n 0 ^ (r - 1) := by
    have h1 : ∏ i ∈ Finset.univ.erase (0 : Fin r), n i
        ≤ ∏ i ∈ Finset.univ.erase (0 : Fin r), n 0 :=
      Finset.prod_le_prod (fun i hi => le_of_lt (hdec i (Finset.ne_of_mem_erase hi)))
    have h2 : ∏ i ∈ Finset.univ.erase (0 : Fin r), n 0 = n 0 ^ (r - 1) := by
      rw [Finset.prod_const, Finset.card_erase_of_mem h0, Finset.card_univ, Fintype.card_fin]
    rwa [h2] at h1
  have hfin : n 0 ^ (r + 1) * (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ (r + 1)
      ≤ n 0 ^ (2 * r) * (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ r := by
    have h1 : (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ (r + 1)
        ≤ (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ r * n 0 ^ (r - 1) := by
      rw [pow_succ]
      gcongr
    calc n 0 ^ (r + 1) * (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ (r + 1)
        ≤ n 0 ^ (r + 1)
            * ((∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ r * n 0 ^ (r - 1)) := by
          gcongr
      _ = n 0 ^ (2 * r) * (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ r := by
          have hrr : r + 1 + (r - 1) = 2 * r := by omega
          calc n 0 ^ (r + 1)
                * ((∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ r * n 0 ^ (r - 1))
              = n 0 ^ (r + 1 + (r - 1))
                * (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ r := by
                conv_rhs => rw [pow_add]
                ring
            _ = n 0 ^ (2 * r) * (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ r := by
                rw [hrr]
  calc (∏ i, n i) ^ (r + 1)
      = n 0 ^ (r + 1) * (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ (r + 1) := by
        rw [e1, mul_pow]
    _ ≤ n 0 ^ (2 * r) * (∏ i ∈ Finset.univ.erase (0 : Fin r), n i) ^ r := hfin
    _ = (∏ i, n i ^ (if i = 0 then 2 else 1)) ^ r := by
        rw [e2, mul_pow, ← pow_mul]

/-- Auxiliary: the key finitary estimate, for general admissible exponents. -/
private theorem auxKey (r : ℕ) (n k : Fin r → ℕ) (hr : 1 ≤ r) [NeZero r]
    (h1n : ∀ i, 1 ≤ n i) (hdec : ∀ i, i ≠ 0 → n i < n 0)
    (hk0 : 2 ≤ k ⟨0, hr⟩) (hkk : ∀ i, 1 ≤ k i) :
    (∏ i, n i) ^ (r + 1) ≤ (∏ i, n i ^ k i) ^ r := by
  have e_le : ∀ i, (if i = 0 then 2 else 1) ≤ k i := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [ite_eq_left rfl]
      exact hk0
    · rw [ite_eq_right hi]
      exact hkk i
  have hmono : ∏ i, n i ^ (if i = 0 then 2 else 1) ≤ ∏ i, n i ^ k i :=
    Finset.prod_le_prod (fun i _ =>
      Nat.pow_le_pow_right (lt_of_lt_of_le Nat.zero_lt_one (h1n i)) (e_le i))
  calc (∏ i, n i) ^ (r + 1)
      ≤ (∏ i, n i ^ (if i = 0 then 2 else 1)) ^ r := auxKeyMin r n hr hdec
    _ ≤ (∏ i, n i ^ k i) ^ r := Nat.pow_le_pow_left hmono r

/-- Auxiliary: summability of the strict summand for abstracted exponents. -/
private theorem auxSummableStrict (r : ℕ) (k : Fin r → ℕ) (hr : 1 ≤ r) [NeZero r]
    (hk0 : 2 ≤ k ⟨0, hr⟩) (hkk : ∀ i, 1 ≤ k i) :
    Summable (fun m : StrictDecreasingTuple r =>
      (∏ i, (((m.1 i : ℕ) : ℝ) ^ (k i)))⁻¹) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have h : 0 < r := hr
    exact_mod_cast h
  set c : ℝ := ((r : ℝ) + 1) / (r : ℝ) with hcdef
  have hc1 : 1 < c := by
    rw [hcdef]
    exact (one_lt_div hr0).mpr (by linarith)
  have hfP : Summable (fun n : PNat => ((((n : ℕ)) : ℝ) ^ c)⁻¹) :=
    auxSummablePnat c hc1
  have hG : Summable (fun m : Fin r → PNat => ∏ i, ((((m i : ℕ)) : ℝ) ^ c)⁻¹) :=
    auxSummablePi (fun n : PNat => ((((n : ℕ)) : ℝ) ^ c)⁻¹) hfP
      (fun n => inv_pos.mpr (Real.rpow_pos_of_pos
        (show (0 : ℝ) < ((((n : ℕ)) : ℝ)) from by exact_mod_cast PNat.pos n) c)) r
      (by omega)
  have hsum : Summable (fun m : StrictDecreasingTuple r => ∏ i, ((((m.1 i : ℕ)) : ℝ) ^ c)⁻¹) :=
    hG.comp_injective Subtype.val_injective
  have h0 : ∀ m : StrictDecreasingTuple r,
      0 ≤ (∏ i, ((((m.1 i : ℕ)) : ℝ) ^ (k i)))⁻¹ := by
    intro m
    apply le_of_lt
    apply inv_pos.mpr
    apply Finset.prod_pos
    intro i _
    apply pow_pos
    have h : (0 : ℝ) < ((((m.1 i : ℕ)) : ℝ)) := by
      have h := PNat.pos (m.1 i)
      exact_mod_cast h
    exact h
  have hle : ∀ m : StrictDecreasingTuple r,
      (∏ i, ((((m.1 i : ℕ)) : ℝ) ^ (k i)))⁻¹ ≤ ∏ i, ((((m.1 i : ℕ)) : ℝ) ^ c)⁻¹ := by
    intro m
    have h1n : ∀ i, 1 ≤ ((m.1 i : ℕ)) := by
      intro i
      have h := PNat.pos (m.1 i)
      omega
    have hdec : ∀ i : Fin r, i ≠ 0 → ((m.1 i : ℕ)) < ((m.1 0 : ℕ)) := by
      intro i hi
      have h0i : (0 : Fin r) < i := (Fin.pos_iff_ne_zero).mpr hi
      exact (PNat.coe_lt_coe _ _).mpr (m.2 h0i)
    have hkey := auxKey r (fun i => ((m.1 i : ℕ))) k hr h1n hdec hk0 hkk
    have hAB : (∏ i, (((m.1 i : ℕ)) : ℝ)) ^ (r + 1)
        ≤ (∏ i, (((m.1 i : ℕ)) : ℝ) ^ (k i)) ^ r := by
      exact_mod_cast hkey
    have hBpos : 0 < ∏ i, (((m.1 i : ℕ)) : ℝ) := by
      apply Finset.prod_pos
      intro i _
      have h : (0 : ℝ) < ((((m.1 i : ℕ)) : ℝ)) := by
        have h := PNat.pos (m.1 i)
        exact_mod_cast h
      exact h
    have hApos : 0 < ∏ i, ((((m.1 i : ℕ)) : ℝ) ^ (k i)) := by
      apply Finset.prod_pos
      intro i _
      apply pow_pos
      have h : (0 : ℝ) < ((((m.1 i : ℕ)) : ℝ)) := by
        have h := PNat.pos (m.1 i)
        exact_mod_cast h
      exact h
    have hBc : (∏ i, (((m.1 i : ℕ)) : ℝ)) ^ c
        ≤ ∏ i, ((((m.1 i : ℕ)) : ℝ) ^ (k i)) := by
      have hR : (r : ℝ) ≠ 0 := ne_of_gt hr0
      have eR : ((r : ℝ) + 1) = (((r + 1 : ℕ)) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
      have e3 : (∏ i, (((m.1 i : ℕ)) : ℝ)) ^ c
          = ((∏ i, (((m.1 i : ℕ)) : ℝ)) ^ ((r : ℝ) + 1)) ^ (r : ℝ)⁻¹ := by
        rw [hcdef, div_eq_mul_inv, Real.rpow_mul (le_of_lt hBpos)]
      have e4 : ((∏ i, ((((m.1 i : ℕ)) : ℝ) ^ (k i))) ^ (r : ℝ)) ^ (r : ℝ)⁻¹
          = ∏ i, ((((m.1 i : ℕ)) : ℝ) ^ (k i)) := by
        rw [← Real.rpow_mul (le_of_lt hApos), mul_inv_cancel₀ hR, Real.rpow_one]
      have hle2 : (∏ i, (((m.1 i : ℕ)) : ℝ)) ^ ((r : ℝ) + 1)
          ≤ (∏ i, ((((m.1 i : ℕ)) : ℝ) ^ (k i))) ^ (r : ℝ) := by
        rw [eR, Real.rpow_natCast, Real.rpow_natCast]
        exact hAB
      calc (∏ i, (((m.1 i : ℕ)) : ℝ)) ^ c
          = ((∏ i, (((m.1 i : ℕ)) : ℝ)) ^ ((r : ℝ) + 1)) ^ (r : ℝ)⁻¹ := e3
        _ ≤ ((∏ i, ((((m.1 i : ℕ)) : ℝ) ^ (k i))) ^ (r : ℝ)) ^ (r : ℝ)⁻¹ :=
            Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hBpos) _) hle2
              (inv_nonneg.mpr (le_of_lt hr0))
        _ = ∏ i, ((((m.1 i : ℕ)) : ℝ) ^ (k i)) := e4
    have hposB : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 < ((((m.1 i : ℕ)) : ℝ)) := by
      intro i _
      have h : (0 : ℝ) < ((((m.1 i : ℕ)) : ℝ)) := by
        have h := PNat.pos (m.1 i)
        exact_mod_cast h
      exact h
    have hH : (∏ i, (((m.1 i : ℕ) : ℝ) ^ c)⁻¹)
        = ((∏ i, ((m.1 i : ℕ) : ℝ)) ^ c)⁻¹ := by
      have hprod : ∏ i, (((m.1 i : ℕ) : ℝ) ^ c) = (∏ i, ((m.1 i : ℕ) : ℝ)) ^ c :=
        auxProdRpow _ _ _ _ hposB
      rw [Finset.prod_inv_distrib, hprod]
    rw [hH]
    exact (inv_le_inv₀ hApos (Real.rpow_pos_of_pos hBpos c)).mpr hBc
  exact Summable.of_nonneg_of_le h0 hle hsum

/--
**Convergence of multiple zeta series.** Let $\mathbf{k} = (k_1, \dots, k_r)$ be an admissible
index, that is, a nonempty index of positive integers with $k_1 \ge 2$. Then the strict
multiple-zeta series of $\mathbf{k}$, the family of terms $(m_1^{k_1} \cdots m_r^{k_r})^{-1}$
indexed by the strictly decreasing tuples $m_1 > \cdots > m_r$ of positive integers, is summable.

Proves `Wanted` entry `summable_strictSummand`.

Source: arXiv:2307.09867, lines 60–63, and arXiv:2309.07569, lines 76–80; equivalent
increasing-variable formulations occur in arXiv:2304.08722, 2312.13525, 2608.10675,
2608.15480, and 2608.22280 after reversing both the variables and exponents.
-/
theorem summable_strictSummand (index : Index) (hindex : index.IsAdmissible) :
    Summable (strictSummand index) := by
  rcases index with ⟨N, comp⟩
  rcases comp with ⟨blocks, hsum, hpos⟩
  cases blocks with
  | nil =>
      simp [Index.IsAdmissible] at hindex
  | cons h t =>
      simp only [Index.IsAdmissible] at hindex
      have hdepth : Index.depth ⟨N, ⟨h :: t, hsum, hpos⟩⟩ = (h :: t).length :=
        (Composition.blocks_length _).symm
      have hr : 1 ≤ Index.depth ⟨N, ⟨h :: t, hsum, hpos⟩⟩ := by
        rw [hdepth, List.length_cons]
        omega
      have e0 : (Index.entry ⟨N, ⟨h :: t, hsum, hpos⟩⟩ ⟨0, hr⟩ : ℕ) = h := rfl
      have hkk : ∀ i : Fin (Index.depth ⟨N, ⟨h :: t, hsum, hpos⟩⟩),
          1 ≤ ((Index.entry ⟨N, ⟨h :: t, hsum, hpos⟩⟩ i : ℕ)) := by
        intro i
        have h := PNat.pos ((Index.entry ⟨N, ⟨h :: t, hsum, hpos⟩⟩ i))
        omega
      have hk0 : 2 ≤ ((Index.entry ⟨N, ⟨h :: t, hsum, hpos⟩⟩ ⟨0, hr⟩ : ℕ)) := by
        rw [e0]
        exact hindex
      have : NeZero (Index.depth ⟨N, ⟨h :: t, hsum, hpos⟩⟩) := ⟨by omega⟩
      exact auxSummableStrict _
        (fun i => ((Index.entry ⟨N, ⟨h :: t, hsum, hpos⟩⟩ i : ℕ))) hr hk0 hkk

end MetaMathlibExt.MultipleZeta
