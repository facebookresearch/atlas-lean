/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- Descent at 1-based adjacent position `i.val + 1` for a permutation of `Fin n`. -/
private def des (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) : Prop :=
  (σ ⟨i.val, by have := i.isLt; omega⟩).val >
    (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val

private instance desDec (n : ℕ) (σ : Equiv.Perm (Fin n)) : DecidablePred (des n σ) :=
  fun _ => Nat.decLt _ _

private lemma nat_toggle (X Y : ℕ) (h : X ≠ Y) : Y > X ↔ ¬ X > Y := by
  constructor
  · intro h1 h2
    omega
  · intro h1
    omega

private lemma toggle_des (n : ℕ) (a : Fin (n - 1)) (x y : Fin n) (hx : x.val = a.val)
    (hy : y.val = a.val + 1) (ha1 : a.val < n) (ha2 : a.val + 1 < n)
    (σ : Equiv.Perm (Fin n)) :
    des n ((Equiv.swap x y).trans σ) a ↔ ¬ des n σ a := by
  have hxy : x ≠ y := by
    intro h
    have h3 : x.val = y.val := congrArg Fin.val h
    omega
  have hxm : (⟨a.val, ha1⟩ : Fin n) = x := Fin.ext hx.symm
  have hym : (⟨a.val + 1, ha2⟩ : Fin n) = y := Fin.ext hy.symm
  have hne : (σ x).val ≠ (σ y).val := fun h => hxy (σ.injective (Fin.ext h))
  have e1 : ((Equiv.swap x y).trans σ) x = σ y := by
    rw [Equiv.trans_apply, Equiv.swap_apply_left]
  have e2 : ((Equiv.swap x y).trans σ) y = σ x := by
    rw [Equiv.trans_apply, Equiv.swap_apply_right]
  unfold des
  rw [hxm, hym, e1, e2]
  exact nat_toggle _ _ hne

private lemma pres_des (n : ℕ) (a j : Fin (n - 1)) (x y : Fin n) (hx : x.val = a.val)
    (hy : y.val = a.val + 1) (h0 : a ≠ j) (h1 : a.val + 1 ≠ j.val)
    (h2 : j.val + 1 ≠ a.val) (σ : Equiv.Perm (Fin n)) :
    des n ((Equiv.swap x y).trans σ) j ↔ des n σ j := by
  have h0v : a.val ≠ j.val := fun hcon => h0 (Fin.ext hcon)
  have hj1 : j.val < n := by have h := j.isLt; omega
  have hj2 : j.val + 1 < n := by have h := j.isLt; omega
  have hne1 : (⟨j.val, hj1⟩ : Fin n) ≠ x := by
    intro h
    have h3 : j.val = x.val := Fin.ext_iff.mp h
    omega
  have hne2 : (⟨j.val, hj1⟩ : Fin n) ≠ y := by
    intro h
    have h3 : j.val = y.val := Fin.ext_iff.mp h
    omega
  have hne3 : (⟨j.val + 1, hj2⟩ : Fin n) ≠ x := by
    intro h
    have h3 : j.val + 1 = x.val := Fin.ext_iff.mp h
    omega
  have hne4 : (⟨j.val + 1, hj2⟩ : Fin n) ≠ y := by
    intro h
    have h3 : j.val + 1 = y.val := Fin.ext_iff.mp h
    omega
  have e1 : ((Equiv.swap x y).trans σ) ⟨j.val, hj1⟩ = σ ⟨j.val, hj1⟩ := by
    rw [Equiv.trans_apply]
    exact congrArg σ (Equiv.swap_apply_of_ne_of_ne hne1 hne2)
  have e2 : ((Equiv.swap x y).trans σ) ⟨j.val + 1, hj2⟩ = σ ⟨j.val + 1, hj2⟩ := by
    rw [Equiv.trans_apply]
    exact congrArg σ (Equiv.swap_apply_of_ne_of_ne hne3 hne4)
  unfold des
  rw [e1, e2]

private lemma key (n : ℕ) (p : ℝ) : ∀ (S : Finset (Fin (n - 1))),
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → i.val + 1 ≠ j.val ∧ j.val + 1 ≠ i.val) →
    ∑ σ : Equiv.Perm (Fin n), ∏ i ∈ S, (if des n σ i then p else 1)
      = (Nat.factorial n : ℝ) / 2 ^ S.card * (1 + p) ^ S.card := by
  intro S
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp [Fintype.card_perm]
  · intro a s hnotmem ih hS
    have hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → i.val + 1 ≠ j.val ∧ j.val + 1 ≠ i.val := by
      intro i hi j hj hne
      exact hS i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hne
    have ih' := ih hsep
    have hdisj : ∀ j ∈ s, a ≠ j ∧ (a.val + 1 ≠ j.val ∧ j.val + 1 ≠ a.val) := by
      intro j hj
      have hne : a ≠ j := by
        intro hcon
        subst hcon
        exact hnotmem hj
      refine ⟨hne, ?_, ?_⟩
      · exact (hS a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) hne).1
      · exact (hS a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) hne).2
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact absurd a.isLt (Nat.not_lt_zero _)
      · exact hpos
    have ha1 : a.val < n := lt_of_lt_of_le a.isLt (Nat.sub_le n 1)
    have ha2 : a.val + 1 < n := by
      have h1 : a.val + 1 ≤ n - 1 := a.isLt
      have h2 : n - 1 < n := by omega
      exact lt_of_le_of_lt h1 h2
    set u : Fin n := ⟨a.val, ha1⟩ with hu_def
    set v : Fin n := ⟨a.val + 1, ha2⟩ with hv_def
    have hsw : (Equiv.swap u v).trans
        (Equiv.swap u v) = Equiv.refl _ := by
      ext z
      simp
    have hww : ∀ σ : Equiv.Perm (Fin n),
        ((Equiv.swap u v).trans
          ((Equiv.swap u v).trans σ)) = σ := by
      intro σ
      rw [← Equiv.trans_assoc, hsw, Equiv.refl_trans]
    have htoggle : ∀ σ : Equiv.Perm (Fin n),
        des n ((Equiv.swap u v).trans σ) a ↔
          ¬ des n σ a := by
      intro σ
      exact toggle_des n a u v (by rw [hu_def]) (by rw [hv_def]) ha1 ha2 σ
    have hpres : ∀ σ : Equiv.Perm (Fin n), ∀ j ∈ s,
        des n ((Equiv.swap u v).trans σ) j ↔
          des n σ j := by
      intro σ j hj
      obtain ⟨hnej, h1, h2⟩ := hdisj j hj
      exact pres_des n a j u v (by rw [hu_def]) (by rw [hv_def]) hnej h1 h2 σ
    have hAB : (∑ σ ∈ Finset.univ.filter (fun σ => des n σ a),
          ∏ i ∈ s, (if des n σ i then p else (1:ℝ))) =
        ∑ σ ∈ Finset.univ.filter (fun σ => ¬ des n σ a),
          ∏ i ∈ s, (if des n σ i then p else (1:ℝ)) := by
      apply Finset.sum_bij
        (fun σ _ => (Equiv.swap u v).trans σ)
      · intro σ hσ
        rw [Finset.mem_filter] at hσ ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [htoggle σ]
        exact not_not_intro hσ.2
      · intro σ₁ _ σ₂ _ h
        have h2 := congrArg
          (fun τ : Equiv.Perm (Fin n) =>
            (Equiv.swap u v).trans τ) h
        rwa [hww, hww] at h2
      · intro τ hτ
        rw [Finset.mem_filter] at hτ
        refine ⟨(Equiv.swap u v).trans τ, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [htoggle]
          exact hτ.2
        · exact hww τ
      · intro σ hσ
        rw [Finset.mem_filter] at hσ
        apply Finset.prod_congr rfl
        intro j hj
        simp only [hpres σ j hj]
    have hsum : (∑ σ : Equiv.Perm (Fin n),
          ∏ i ∈ s, (if des n σ i then p else (1:ℝ)))
        = (∑ σ ∈ Finset.univ.filter (fun σ => des n σ a),
          ∏ i ∈ s, (if des n σ i then p else (1:ℝ)))
          + (∑ σ ∈ Finset.univ.filter (fun σ => ¬ des n σ a),
          ∏ i ∈ s, (if des n σ i then p else (1:ℝ))) := by
      have h := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun σ : Equiv.Perm (Fin n) => des n σ a)
        (fun σ => ∏ i ∈ s, (if des n σ i then p else (1:ℝ)))
      exact h.symm
    have hprod : ∀ σ : Equiv.Perm (Fin n),
        (∏ i ∈ insert a s, (if des n σ i then p else (1:ℝ)))
          = (if des n σ a then p else 1) *
            ∏ i ∈ s, (if des n σ i then p else (1:ℝ)) :=
      fun σ => Finset.prod_insert (f := fun i => if des n σ i then p else (1:ℝ)) hnotmem
    have hmain : (∑ σ : Equiv.Perm (Fin n),
          (if des n σ a then p else (1:ℝ)) *
            ∏ i ∈ s, (if des n σ i then p else (1:ℝ)))
        = (1 + p) * (∑ σ ∈ Finset.univ.filter (fun σ => ¬ des n σ a),
          ∏ i ∈ s, (if des n σ i then p else (1:ℝ))) := by
      have e1 : (∑ σ : Equiv.Perm (Fin n),
            (if des n σ a then p else (1:ℝ)) *
              ∏ i ∈ s, (if des n σ i then p else (1:ℝ)))
          = p * (∑ σ ∈ Finset.univ.filter (fun σ => des n σ a),
            ∏ i ∈ s, (if des n σ i then p else (1:ℝ)))
            + (∑ σ ∈ Finset.univ.filter (fun σ => ¬ des n σ a),
            ∏ i ∈ s, (if des n σ i then p else (1:ℝ))) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun σ : Equiv.Perm (Fin n) => des n σ a)]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ hσ
          have h2 : des n σ a := (Finset.mem_filter.mp hσ).2
          change (if des n σ a then p else (1:ℝ)) * _ = p * _
          simp [h2]
        · apply Finset.sum_congr rfl
          intro σ hσ
          have h2 : ¬ des n σ a := (Finset.mem_filter.mp hσ).2
          change (if des n σ a then p else (1:ℝ)) * _ = _
          simp [h2]
      rw [e1, hAB]
      ring
    simp_rw [hprod]
    rw [hmain]
    have hB : (∑ σ ∈ Finset.univ.filter (fun σ => ¬ des n σ a),
        ∏ i ∈ s, (if des n σ i then p else (1:ℝ)))
        = (Nat.factorial n : ℝ) / 2 ^ s.card * (1 + p) ^ s.card / 2 := by
      rw [hAB] at hsum
      rw [ih'] at hsum
      linarith
    rw [hB, Finset.card_insert_of_notMem hnotmem, pow_succ, pow_succ]
    ring

private lemma card_even_range (m : ℕ) : ((Finset.range m).filter Even).card = (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_add_one]
    by_cases hm : Even m
    · have hfil : (insert m (Finset.range m)).filter Even
          = insert m ((Finset.range m).filter Even) := by
        simp [Finset.filter_insert, hm]
      rw [hfil, Finset.card_insert_of_notMem (by simp), ih]
      obtain ⟨k, rfl⟩ := hm
      omega
    · have hfil : (insert m (Finset.range m)).filter Even
          = (Finset.range m).filter Even := by
        simp [Finset.filter_insert, hm]
      rw [hfil, ih]
      have ho : Odd m := Nat.not_even_iff_odd.mp hm
      obtain ⟨k, rfl⟩ := ho
      omega

private lemma card_odd_range (m : ℕ) : ((Finset.range m).filter Odd).card = m / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_add_one]
    by_cases hm : Odd m
    · have hfil : (insert m (Finset.range m)).filter Odd
          = insert m ((Finset.range m).filter Odd) := by
        simp [Finset.filter_insert, hm]
      rw [hfil, Finset.card_insert_of_notMem (by simp), ih]
      obtain ⟨k, rfl⟩ := hm
      omega
    · have hfil : (insert m (Finset.range m)).filter Odd
          = (Finset.range m).filter Odd := by
        simp [Finset.filter_insert, hm]
      rw [hfil, ih]
      have he : Even m := Nat.not_odd_iff_even.mp hm
      obtain ⟨k, rfl⟩ := he
      omega

private lemma card_odd_positions (n : ℕ) :
    (Finset.univ.filter (fun i : Fin (n - 1) => Odd (i.val + 1))).card
      = n / 2 := by
  have hbij : (Finset.univ.filter (fun i : Fin (n - 1) => Odd (i.val + 1))).card
      = ((Finset.range (n - 1)).filter (fun k => Odd (k + 1))).card := by
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.isLt, ha'.2⟩
    · intro a₁ _ a₂ _ h
      exact Fin.ext h
    · intro b hb
      have hb' := Finset.mem_filter.mp hb
      have hblt : b < n - 1 := Finset.mem_range.mp hb'.1
      refine ⟨⟨b, hblt⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'.2⟩
  rw [hbij]
  have hiff : ∀ k ∈ Finset.range (n - 1), Odd (k + 1) ↔ Even k := by
    intro k _
    constructor
    · intro h
      obtain ⟨t, ht⟩ := h
      exact ⟨t, by omega⟩
    · intro h
      obtain ⟨t, ht⟩ := h
      exact ⟨t, by omega⟩
  rw [Finset.filter_congr hiff, card_even_range]
  omega

private lemma card_even_positions (n : ℕ) :
    (Finset.univ.filter (fun i : Fin (n - 1) => Even (i.val + 1))).card
      = (n - 1) / 2 := by
  have hbij : (Finset.univ.filter (fun i : Fin (n - 1) => Even (i.val + 1))).card
      = ((Finset.range (n - 1)).filter (fun k => Even (k + 1))).card := by
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.isLt, ha'.2⟩
    · intro a₁ _ a₂ _ h
      exact Fin.ext h
    · intro b hb
      have hb' := Finset.mem_filter.mp hb
      have hblt : b < n - 1 := Finset.mem_range.mp hb'.1
      refine ⟨⟨b, hblt⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'.2⟩
  rw [hbij]
  have hiff : ∀ k ∈ Finset.range (n - 1), Even (k + 1) ↔ Odd k := by
    intro k _
    constructor
    · intro h
      obtain ⟨t, ht⟩ := h
      exact ⟨t - 1, by omega⟩
    · intro h
      obtain ⟨t, ht⟩ := h
      exact ⟨t + 1, by omega⟩
  rw [Finset.filter_congr hiff, card_odd_range]

private lemma pow_card_eq_prod (n : ℕ) (p : ℝ) (O : Finset (Fin (n - 1)))
    (σ : Equiv.Perm (Fin n)) :
    p ^ (O.filter (des n σ)).card
      = ∏ i ∈ O, (if des n σ i then p else (1:ℝ)) := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_const p).symm

/-! # Refined Eulerian odd/even descent marginals -/

set_option backward.proofsInPublic true in
/--
**Marginals of the refined Eulerian polynomial.** Let $n \ge 1$. For a permutation $\sigma$
of $\{1, \dots, n\}$, let $\mathrm{odes}(\sigma)$ (resp. $\mathrm{edes}(\sigma)$) be the number
of odd (resp. even) positions $i \in \{1, \dots, n-1\}$ with $\sigma(i) > \sigma(i+1)$, and let
$A_n(p, q) = \sum_{\sigma} p^{\mathrm{odes}(\sigma)} q^{\mathrm{edes}(\sigma)}$, the sum over all
permutations $\sigma$ of $\{1, \dots, n\}$. Then for all real numbers $p$ and $q$,
$$A_n(p, 1) = \frac{n!}{2^{\lfloor n/2 \rfloor}} (1+p)^{\lfloor n/2 \rfloor}$$
and
$$A_n(1, q) = \frac{n!}{2^{\lfloor (n-1)/2 \rfloor}} (1+q)^{\lfloor (n-1)/2 \rfloor}.$$

Proves `Wanted` entry `sun_refined_eulerian_marginals`.

Source: Hua Sun, "A New Class of Refined Eulerian Polynomials", Journal of Integer
Sequences 21 (2018), Article 18.5.5, Proposition lines 248-254,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Sun/sun2.tex>.
-/
theorem sun_refined_eulerian_marginals (n : ℕ) (hn : 0 < n) (p q : ℝ) :
    let odes : Equiv.Perm (Fin n) → ℕ := fun σ =>
      (Finset.univ.filter (fun i : Fin (n - 1) =>
        Odd (i.val + 1) ∧
        (σ ⟨i.val, by have := i.isLt; omega⟩).val >
          (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val)).card;
    let edes : Equiv.Perm (Fin n) → ℕ := fun σ =>
      (Finset.univ.filter (fun i : Fin (n - 1) =>
        Even (i.val + 1) ∧
        (σ ⟨i.val, by have := i.isLt; omega⟩).val >
          (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val)).card;
    let genA : ℝ → ℝ → ℝ := fun p q =>
      ∑ σ : Equiv.Perm (Fin n), p ^ odes σ * q ^ edes σ;
    genA p 1 = (Nat.factorial n : ℝ) / 2 ^ (n / 2) * (1 + p) ^ (n / 2) ∧
      genA 1 q = (Nat.factorial n : ℝ) / 2 ^ ((n - 1) / 2) * (1 + q) ^ ((n - 1) / 2) := by
  refine ⟨?_, ?_⟩
  · simp only [one_pow, mul_one]
    have hsepO : ∀ i ∈ Finset.univ.filter (fun i : Fin (n - 1) => Odd (i.val + 1)),
        ∀ j ∈ Finset.univ.filter (fun i : Fin (n - 1) => Odd (i.val + 1)),
        i ≠ j → i.val + 1 ≠ j.val ∧ j.val + 1 ≠ i.val := by
      intro i hi j hj hne
      have hoi : Odd (i.val + 1) := (Finset.mem_filter.mp hi).2
      have hoj : Odd (j.val + 1) := (Finset.mem_filter.mp hj).2
      constructor
      · intro hcon
        obtain ⟨r, hr⟩ := hoi
        obtain ⟨t, ht⟩ := hoj
        omega
      · intro hcon
        obtain ⟨r, hr⟩ := hoi
        obtain ⟨t, ht⟩ := hoj
        omega
    have hfilO : ∀ σ : Equiv.Perm (Fin n),
        (Finset.univ.filter (fun i : Fin (n - 1) => Odd (i.val + 1))).filter (des n σ)
          = Finset.univ.filter (fun i : Fin (n - 1) =>
            Odd (i.val + 1) ∧ (σ ⟨i.val, by have := i.isLt; omega⟩).val >
              (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val) := by
      intro σ
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro i _
      rfl
    have h1 : ∀ σ : Equiv.Perm (Fin n),
        p ^ (Finset.univ.filter (fun i : Fin (n - 1) =>
          Odd (i.val + 1) ∧ (σ ⟨i.val, by have := i.isLt; omega⟩).val >
            (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val)).card
        = ∏ i ∈ Finset.univ.filter (fun i : Fin (n - 1) => Odd (i.val + 1)),
          (if des n σ i then p else (1:ℝ)) := by
      intro σ
      rw [← pow_card_eq_prod n p _ σ, hfilO σ]
    have hsum : (∑ σ : Equiv.Perm (Fin n),
          p ^ (Finset.univ.filter (fun i : Fin (n - 1) =>
            Odd (i.val + 1) ∧ (σ ⟨i.val, by have := i.isLt; omega⟩).val >
              (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val)).card)
        = ∑ σ : Equiv.Perm (Fin n),
          ∏ i ∈ Finset.univ.filter (fun i : Fin (n - 1) => Odd (i.val + 1)),
            (if des n σ i then p else (1:ℝ)) :=
      Finset.sum_congr rfl (fun σ _ => h1 σ)
    rw [hsum, key n p _ hsepO, card_odd_positions]
  · simp only [one_pow, one_mul]
    have hsepE : ∀ i ∈ Finset.univ.filter (fun i : Fin (n - 1) => Even (i.val + 1)),
        ∀ j ∈ Finset.univ.filter (fun i : Fin (n - 1) => Even (i.val + 1)),
        i ≠ j → i.val + 1 ≠ j.val ∧ j.val + 1 ≠ i.val := by
      intro i hi j hj hne
      have hei : Even (i.val + 1) := (Finset.mem_filter.mp hi).2
      have hej : Even (j.val + 1) := (Finset.mem_filter.mp hj).2
      constructor
      · intro hcon
        obtain ⟨r, hr⟩ := hei
        obtain ⟨t, ht⟩ := hej
        omega
      · intro hcon
        obtain ⟨r, hr⟩ := hei
        obtain ⟨t, ht⟩ := hej
        omega
    have hfilE : ∀ σ : Equiv.Perm (Fin n),
        (Finset.univ.filter (fun i : Fin (n - 1) => Even (i.val + 1))).filter (des n σ)
          = Finset.univ.filter (fun i : Fin (n - 1) =>
            Even (i.val + 1) ∧ (σ ⟨i.val, by have := i.isLt; omega⟩).val >
              (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val) := by
      intro σ
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro i _
      rfl
    have h1 : ∀ σ : Equiv.Perm (Fin n),
        q ^ (Finset.univ.filter (fun i : Fin (n - 1) =>
          Even (i.val + 1) ∧ (σ ⟨i.val, by have := i.isLt; omega⟩).val >
            (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val)).card
        = ∏ i ∈ Finset.univ.filter (fun i : Fin (n - 1) => Even (i.val + 1)),
          (if des n σ i then q else (1:ℝ)) := by
      intro σ
      rw [← pow_card_eq_prod n q _ σ, hfilE σ]
    have hsum : (∑ σ : Equiv.Perm (Fin n),
          q ^ (Finset.univ.filter (fun i : Fin (n - 1) =>
            Even (i.val + 1) ∧ (σ ⟨i.val, by have := i.isLt; omega⟩).val >
              (σ ⟨i.val + 1, by have := i.isLt; omega⟩).val)).card)
        = ∑ σ : Equiv.Perm (Fin n),
          ∏ i ∈ Finset.univ.filter (fun i : Fin (n - 1) => Even (i.val + 1)),
            (if des n σ i then q else (1:ℝ)) :=
      Finset.sum_congr rfl (fun σ _ => h1 σ)
    rw [hsum, key n q _ hsepE, card_even_positions]

end MetaMathlibExt
