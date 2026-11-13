/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

@[expose] public section

namespace MetaMathlibExt

/-! # regular drawing crossing count of `K_{n,n}` (Legendre) -/

/-- The point map sending a crossing pair to its interior intersection point. -/
private def phi : ((ℕ × ℕ) × (ℕ × ℕ)) → Rat × Rat := fun p => match p with
  | ((i, j), (i', j')) =>
    (((i' : Rat) - (i : Rat)) / (((i' : Rat) - (i : Rat)) + ((j : Rat) - (j' : Rat))),
      (i : Rat) + (((i' : Rat) - (i : Rat)) /
        (((i' : Rat) - (i : Rat)) + ((j : Rat) - (j' : Rat))) * ((j : Rat) - (i : Rat))))

/-- The primitive line data `(a, b, c)` attached to a crossing pair. -/
private def key : ((ℕ × ℕ) × (ℕ × ℕ)) → (ℕ × ℕ × ℕ) := fun p => match p with
  | ((i, j), (i', j')) =>
    let d := i' - i; let e := j - j'; let g := Nat.gcd d e
    (d / g, e / g, (e / g) * i + (d / g) * j)

/-- The reconstruction of the intersection point from `(a, b, c)`. -/
private def rho : (ℕ × ℕ × ℕ) → Rat × Rat := fun t => match t with
  | (a, b, c) => ((a : Rat) / ((a : Rat) + (b : Rat)), (c : Rat) / ((a : Rat) + (b : Rat)))

/-- The set of crossing pairs, `= C`. -/
private def box (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  Finset.filter
    (fun p => match p with | ((i, j), (i', j')) => i < i' ∧ j' < j)
    ((Finset.range n ×ˢ Finset.range n) ×ˢ (Finset.range n ×ˢ Finset.range n))

-- start points for direction (a,b): i in [0,n-a), j in [b,n).
private def strt (a b n : ℕ) : Finset (ℕ × ℕ) := (Finset.range (n - a)) ×ˢ (Finset.Ico b n)
private def predset (a b n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico a (n - a)) ×ˢ (Finset.Ico b (n - b))
private def cm (a b : ℕ) : ℕ × ℕ → ℕ := fun q => b * q.1 + a * q.2

private def dirs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter
    (fun ab => 1 ≤ ab.1 ∧ 1 ≤ ab.2 ∧ Nat.Coprime ab.1 ab.2)

-- ===== geometry =====

private lemma phi_eq_rho_key (i j i' j' : ℕ) (h1 : i < i') (h2 : j' < j) :
    phi ((i, j), (i', j')) = rho (key ((i, j), (i', j'))) := by
  set d := i' - i with hd_def
  set e := j - j' with he_def
  set g := Nat.gcd d e with hg_def
  have hd1 : 1 ≤ d := by omega
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hga : g * (d / g) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have hgb : g * (e / g) = e := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  have hcd : ((i' : Rat) - (i : Rat)) = (d : Rat) := by
    rw [hd_def]; push_cast [Nat.cast_sub (le_of_lt h1)]; ring
  have hce : ((j : Rat) - (j' : Rat)) = (e : Rat) := by
    rw [he_def]; push_cast [Nat.cast_sub (le_of_lt h2)]; ring
  simp only [phi, key, rho]
  have hgR : (0:Rat) < (g:Rat) := by exact_mod_cast hgpos
  set a := d / g with ha_def
  set b := e / g with hb_def
  have hdR : (d:Rat) = (g:Rat) * (a:Rat) := by rw [ha_def]; exact_mod_cast hga.symm
  have heR : (e:Rat) = (g:Rat) * (b:Rat) := by rw [hb_def]; exact_mod_cast hgb.symm
  have haR : (0:Rat) < (a:Rat) := by
    rw [ha_def]; have : 1 ≤ d / g := Nat.one_le_div_iff hgpos |>.mpr (Nat.gcd_le_left e hd1)
    exact_mod_cast this
  have hbR : (0:Rat) < (b:Rat) := by
    rw [hb_def]
    have : 1 ≤ e / g := Nat.one_le_div_iff hgpos |>.mpr (Nat.gcd_le_right d (by omega))
    exact_mod_cast this
  have hden2 : (a:Rat) + (b:Rat) ≠ 0 := by positivity
  rw [hcd, hce]
  have hcR : (((e / g) * i + (d / g) * j : ℕ) : Rat) = (b:Rat) * i + (a:Rat) * j := by
    push_cast; rw [← ha_def, ← hb_def]
  ext
  · change (d:Rat) / ((d:Rat)+(e:Rat)) = (a:Rat)/((a:Rat)+(b:Rat))
    rw [hdR, heR]; field_simp
  · change (i:Rat) + (d:Rat)/((d:Rat)+(e:Rat)) * ((j:Rat)-(i:Rat))
      = (((e / g) * i + (d / g) * j : ℕ):Rat)/((a:Rat)+(b:Rat))
    rw [hcR, hdR, heR]; field_simp; ring

private lemma rho_inj (a b c a' b' c' : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hcop : Nat.Coprime a b)
    (ha' : 1 ≤ a') (hb' : 1 ≤ b') (hcop' : Nat.Coprime a' b')
    (h : rho (a, b, c) = rho (a', b', c')) : (a, b, c) = (a', b', c') := by
  simp only [rho, Prod.mk.injEq] at h
  obtain ⟨hx, hy⟩ := h
  have hcross : (a:Rat) * ((a':Rat)+(b':Rat)) = (a':Rat) * ((a:Rat)+(b:Rat)) := by
    have hda : (0:Rat) < (a:Rat) + (b:Rat) := by
      have : (0:Rat) < (a:Rat) := by exact_mod_cast ha
      have : (0:Rat) < (b:Rat) := by exact_mod_cast hb
      positivity
    have hda' : (0:Rat) < (a':Rat) + (b':Rat) := by
      have : (0:Rat) < (a':Rat) := by exact_mod_cast ha'
      have : (0:Rat) < (b':Rat) := by exact_mod_cast hb'
      positivity
    field_simp at hx
    linarith [hx]
  have hab : a * b' = a' * b := by
    have : (a:Rat) * (b':Rat) = (a':Rat) *
        (b:Rat) := by ring_nf; ring_nf at hcross; linarith [hcross]
    exact_mod_cast this
  have hdvd1 : a ∣ a' := hcop.dvd_of_dvd_mul_right ⟨b', hab.symm⟩
  have hdvd2 : a' ∣ a := hcop'.dvd_of_dvd_mul_right ⟨b, hab⟩
  have haa : a = a' := Nat.dvd_antisymm hdvd1 hdvd2
  subst haa
  have hbb : b = b' := Nat.eq_of_mul_eq_mul_left (by omega) hab.symm
  subst hbb
  have hcc : (c:Rat) = (c':Rat) := by
    have hda : (0:Rat) < (a:Rat) + (b:Rat) := by
      have : (0:Rat) < (a:Rat) := by exact_mod_cast ha
      have : (0:Rat) < (b:Rat) := by exact_mod_cast hb
      positivity
    have hh : (c:Rat) / ((a:Rat)+(b:Rat)) = (c':Rat) / ((a:Rat)+(b:Rat)) := hy
    field_simp at hh
    exact hh
  have : c = c' := by exact_mod_cast hcc
  subst this; rfl

private lemma mem_box {n : ℕ} {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ box n) :
    p.1.1 < n ∧ p.1.2 < n ∧ p.2.1 < n ∧ p.2.2 < n ∧ p.1.1 < p.2.1 ∧ p.2.2 < p.1.2 := by
  obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := p
  simp only [box, Finset.mem_filter] at hp
  obtain ⟨hmem, hcond⟩ := hp
  simp only [Finset.mem_product, Finset.mem_range] at hmem
  exact ⟨hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2, hcond.1, hcond.2⟩

private lemma key_valid (i j i' j' : ℕ) (h1 : i < i') (h2 : j' < j) :
    1 ≤ (key ((i, j), (i', j'))).1 ∧ 1 ≤ (key ((i, j), (i', j'))).2.1 ∧
      Nat.Coprime (key ((i, j), (i', j'))).1 (key ((i, j), (i', j'))).2.1 := by
  simp only [key]
  set d := i' - i with hd
  set e := j - j' with he
  have hgpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left _ (by omega)
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.one_le_div_iff hgpos).mpr (Nat.gcd_le_left e (by omega))
  · exact (Nat.one_le_div_iff hgpos).mpr (Nat.gcd_le_right d (by omega))
  · exact Nat.coprime_div_gcd_div_gcd hgpos

private lemma reduction (n : ℕ) :
    (Finset.image phi (box n)).card = (Finset.image key (box n)).card := by
  have hcong : Finset.image phi (box n) = Finset.image rho (Finset.image key (box n)) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro p hp
    obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := p
    have hb := mem_box hp
    exact phi_eq_rho_key i j i' j' hb.2.2.2.2.1 hb.2.2.2.2.2
  rw [hcong, Finset.card_image_of_injOn]
  intro t1 h1 t2 h2 heq
  obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨p2, hp2, rfl⟩ := Finset.mem_image.mp h2
  obtain ⟨⟨i1, j1⟩, ⟨i1', j1'⟩⟩ := p1
  obtain ⟨⟨i2, j2⟩, ⟨i2', j2'⟩⟩ := p2
  have hb1 := mem_box hp1
  have hb2 := mem_box hp2
  have hv1 := key_valid i1 j1 i1' j1' hb1.2.2.2.2.1 hb1.2.2.2.2.2
  have hv2 := key_valid i2 j2 i2' j2' hb2.2.2.2.2.1 hb2.2.2.2.2.2
  set k1 := key ((i1, j1), (i1', j1')) with hk1
  set k2 := key ((i2, j2), (i2', j2')) with hk2
  have hEq : (k1.1, k1.2.1, k1.2.2) = (k2.1, k2.2.1, k2.2.2) :=
    rho_inj k1.1 k1.2.1 k1.2.2 k2.1 k2.2.1 k2.2.2 hv1.1 hv1.2.1 hv1.2.2 hv2.1 hv2.2.1 hv2.2.2 heq
  simpa using hEq

-- ===== per-direction counting =====

private lemma pred_sub (a b n : ℕ) : predset a b n ⊆ strt a b n := by
  intro q hq
  simp only [predset, strt, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hq ⊢
  exact ⟨hq.1.2, hq.2.1, by omega⟩

private lemma card_strt (a b n : ℕ) : (strt a b n).card = (n - a) * (n - b) := by
  simp [strt, Finset.card_product, Nat.card_Ico]

private lemma card_pred (a b n : ℕ) : (predset a b n).card = (n - 2 * a) * (n - 2 * b) := by
  simp only [predset, Finset.card_product, Nat.card_Ico]
  congr 1 <;> omega

private lemma mem_strt {a b n : ℕ} {q : ℕ × ℕ} :
    q ∈ strt a b n ↔ q.1 + a < n ∧ b ≤ q.2 ∧ q.2 < n := by
  obtain ⟨i, j⟩ := q
  simp only [strt, Finset.mem_product, Finset.mem_range, Finset.mem_Ico]
  omega

private lemma mem_pred {a b n : ℕ} {q : ℕ × ℕ} :
    q ∈ predset a b n ↔ a ≤ q.1 ∧ q.1 + a < n ∧ b ≤ q.2 ∧ q.2 + b < n := by
  obtain ⟨i, j⟩ := q
  simp only [predset, Finset.mem_product, Finset.mem_Ico]
  omega

private lemma predecessor_in (a b n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hcop : Nat.Coprime a b)
    (i1 j1 i2 j2 : ℕ) (hs2 : (i2, j2) ∈ strt a b n) (hj1n : j1 < n)
    (heq : b * i1 + a * j1 = b * i2 + a * j2) (hlt : i1 < i2) :
    (i2, j2) ∈ predset a b n := by
  rw [mem_strt] at hs2
  have keyZ : (b : ℤ) * i1 + a * j1 = b * i2 + a * j2 := by exact_mod_cast heq
  have hdvdmul : (a : ℤ) ∣ b * ((i2 : ℤ) - i1) :=
    ⟨(j1 : ℤ) - j2, by linear_combination -keyZ⟩
  have hcopZ : IsCoprime (a : ℤ) (b : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using hcop
  have hdvd : (a : ℤ) ∣ ((i2 : ℤ) - i1) := hcopZ.dvd_of_dvd_mul_left hdvdmul
  have hpos : (0 : ℤ) < (i2 : ℤ) - i1 := by
    have : (i1 : ℤ) < i2 := by exact_mod_cast hlt
    linarith
  have hale : (a : ℤ) ≤ (i2 : ℤ) - i1 := Int.le_of_dvd hpos hdvd
  have hai2 : a ≤ i2 := by
    have : (a : ℤ) ≤ i2 := by linarith
    exact_mod_cast this
  have hjrel : (b : ℤ) * ((i2 : ℤ) - i1) = a * ((j1 : ℤ) - j2) := by linarith [keyZ]
  have hbpos : (0 : ℤ) < b := by exact_mod_cast hb
  have hapos : (0 : ℤ) < a := by exact_mod_cast ha
  have hbge : (a : ℤ) * b ≤ a * ((j1 : ℤ) - j2) := by nlinarith [hale, hbpos, hjrel]
  have hjge : (b : ℤ) ≤ (j1 : ℤ) - j2 := le_of_mul_le_mul_left hbge hapos
  have hj2b : j2 + b ≤ j1 := by
    have : (j2 : ℤ) + b ≤ j1 := by linarith
    exact_mod_cast this
  rw [mem_pred]
  exact ⟨hai2, hs2.1, hs2.2.1, by omega⟩

private lemma f_eq (a b n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hcop : Nat.Coprime a b) :
    ((strt a b n).image (cm a b)).card = (n - a) * (n - b) - (n - 2 * a) * (n - 2 * b) := by
  set F := strt a b n \ predset a b n with hF
  have hsurj : (strt a b n).image (cm a b) = F.image (cm a b) := by
    apply Finset.Subset.antisymm
    · intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨q, hq, rfl⟩ := hc
      set C := (strt a b n).filter (fun r => cm a b r = cm a b q) with hC
      have hCne : C.Nonempty := ⟨q, by rw [hC, Finset.mem_filter]; exact ⟨hq, rfl⟩⟩
      obtain ⟨r, hrC, hrmin⟩ := C.exists_min_image Prod.fst hCne
      rw [hC, Finset.mem_filter] at hrC
      obtain ⟨hrs, hrc⟩ := hrC
      have hrF : r ∈ F := by
        rw [hF, Finset.mem_sdiff]
        refine ⟨hrs, ?_⟩
        intro hrp
        rw [mem_pred] at hrp
        have hps : (r.1 - a, r.2 + b) ∈ strt a b n := by
          rw [mem_strt]; exact ⟨by omega, by omega, by omega⟩
        have hpc : cm a b (r.1 - a, r.2 + b) = cm a b q := by
          simp only [cm] at hrc ⊢
          have h1 : a ≤ r.1 := hrp.1
          have : b * (r.1 - a) + a * (r.2 + b) = b * r.1 + a * r.2 := by zify [h1]; ring
          rw [this]; exact hrc
        have hpC : (r.1 - a, r.2 + b) ∈ C := by rw [hC, Finset.mem_filter]; exact ⟨hps, hpc⟩
        have := hrmin _ hpC
        simp only at this
        omega
      rw [Finset.mem_image]
      exact ⟨r, hrF, hrc⟩
    · exact Finset.image_subset_image (Finset.sdiff_subset)
  have hinj : Set.InjOn (cm a b) F := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, hF, Finset.mem_sdiff] at hp hq
    obtain ⟨hps, hpp⟩ := hp
    obtain ⟨hqs, hqp⟩ := hq
    obtain ⟨i1, j1⟩ := p
    obtain ⟨i2, j2⟩ := q
    simp only [cm] at hpq
    have hj1 : j1 < n := (mem_strt.mp hps).2.2
    have hj2 : j2 < n := (mem_strt.mp hqs).2.2
    rcases lt_trichotomy i1 i2 with h | h | h
    · exact absurd (predecessor_in a b n ha hb hcop i1 j1 i2 j2 hqs hj1 hpq h) hqp
    · subst h
      have hmul : a * j1 = a * j2 := by omega
      have : j1 = j2 := Nat.eq_of_mul_eq_mul_left (by omega) hmul
      subst this; rfl
    · exact absurd (predecessor_in a b n ha hb hcop i2 j2 i1 j1 hps hj2 hpq.symm h) hpp
  rw [hsurj, Finset.card_image_of_injOn hinj, hF, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (pred_sub a b n), card_strt, card_pred]

-- ===== bridge: image key box in terms of directions =====

private lemma mem_image_key {n a b c : ℕ} :
    (a, b, c) ∈ Finset.image key (box n) ↔
      (a, b) ∈ dirs n ∧ c ∈ (strt a b n).image (cm a b) := by
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨p, hp, hkey⟩ := h
    obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := p
    have hb := mem_box hp
    dsimp only at hb
    have hv := key_valid i j i' j' hb.2.2.2.2.1 hb.2.2.2.2.2
    have ha' : a = (key ((i, j), (i', j'))).1 := by rw [hkey]
    have hb' : b = (key ((i, j), (i', j'))).2.1 := by rw [hkey]
    have hc' : c = (key ((i, j), (i', j'))).2.2 := by rw [hkey]
    have hgpos : 0 < Nat.gcd (i' - i) (j - j') := Nat.gcd_pos_of_pos_left _ (by omega)
    have haval : (key ((i, j), (i', j'))).1 = (i' - i) / Nat.gcd (i' - i) (j - j') := rfl
    have hbval : (key ((i, j), (i', j'))).2.1 = (j - j') / Nat.gcd (i' - i) (j - j') := rfl
    have haux : (i' - i) / Nat.gcd (i' - i) (j - j') ≤ i' - i := Nat.div_le_self _ _
    have hbux : (j - j') / Nat.gcd (i' - i) (j - j') ≤ j - j' := Nat.div_le_self _ _
    have han : a ≤ i' - i := by rw [ha', haval]; exact haux
    have hbn : b ≤ j - j' := by rw [hb', hbval]; exact hbux
    refine ⟨?_, ?_⟩
    · simp only [dirs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨by omega, by omega⟩, ?_, ?_, ?_⟩
      · rw [ha']; exact hv.1
      · rw [hb']; exact hv.2.1
      · rw [ha', hb']; exact hv.2.2
    · rw [Finset.mem_image]
      refine ⟨(i, j), ?_, ?_⟩
      · rw [mem_strt]; exact ⟨by omega, by omega, by omega⟩
      · have hcval : (key ((i, j), (i', j'))).2.2
            = (j - j') / Nat.gcd (i' - i) (j - j') * i + (i' - i) / Nat.gcd (i' - i) (j - j') * j :=
          rfl
        simp only [cm]
        rw [ha', hb', hc', haval, hbval, hcval]
  · rintro ⟨hab, hc⟩
    simp only [dirs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
    obtain ⟨⟨han, hbn⟩, ha1, hb1, hcop⟩ := hab
    rw [Finset.mem_image] at hc
    obtain ⟨⟨I, J⟩, hIJ, hcm⟩ := hc
    rw [mem_strt] at hIJ
    dsimp only at hIJ
    rw [Finset.mem_image]
    refine ⟨((I, J), (I + a, J - b)), ?_, ?_⟩
    · simp only [box, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega, by omega⟩
    · have hd : (I + a) - I = a := by omega
      have he : J - (J - b) = b := by omega
      have hg1 : Nat.gcd a b = 1 := hcop
      simp only [key, hd, he, hg1, Nat.div_one]
      simp only [cm] at hcm
      rw [hcm]

private lemma image_key_card (n : ℕ) :
    (Finset.image key (box n)).card
      = ∑ ab ∈ dirs n, ((strt ab.1 ab.2 n).image (cm ab.1 ab.2)).card := by
  have hbu : Finset.image key (box n)
      = (dirs n).biUnion (fun ab =>
          ((strt ab.1 ab.2 n).image (cm ab.1 ab.2)).image (fun c => (ab.1, ab.2, c))) := by
    ext t
    obtain ⟨a, b, c⟩ := t
    rw [Finset.mem_biUnion, mem_image_key]
    constructor
    · rintro ⟨hab, hc⟩
      exact ⟨(a, b), hab, by rw [Finset.mem_image]; exact ⟨c, hc, rfl⟩⟩
    · rintro ⟨⟨a0, b0⟩, hab, ht⟩
      rw [Finset.mem_image] at ht
      obtain ⟨c', hc', heq⟩ := ht
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨hab, hc'⟩
  have hdisj : ∀ x ∈ dirs n, ∀ y ∈ dirs n, x ≠ y →
      Disjoint (((strt x.1 x.2 n).image (cm x.1 x.2)).image (fun c => (x.1, x.2, c)))
        (((strt y.1 y.2 n).image (cm y.1 y.2)).image (fun c => (y.1, y.2, c))) := by
    rintro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ hne
    apply Finset.disjoint_left.mpr
    intro t ht1 ht2
    rw [Finset.mem_image] at ht1 ht2
    obtain ⟨c1, _, he1⟩ := ht1
    obtain ⟨c2, _, he2⟩ := ht2
    rw [← he1] at he2
    simp only [Prod.mk.injEq] at he2
    exact hne (by simp [he2.1, he2.2.1])
  rw [hbu, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro ab _
  rw [Finset.card_image_of_injOn]
  intro x _ y _ hxy
  simpa using hxy

private lemma sum_match (n : ℕ) :
    (∑ ab ∈ dirs n, ((n - ab.1) * (n - ab.2) - (n - 2 * ab.1) * (n - 2 * ab.2)))
      = ((∑ a ∈ Finset.filter (fun a => 1 ≤ a) (Finset.range n),
            ∑ b ∈ Finset.filter (fun b => 1 ≤ b ∧ Nat.Coprime a b) (Finset.range n),
            (n - a) * (n - b)) -
          (∑ a ∈ Finset.filter (fun a => 1 ≤ 2 * a ∧ 2 * a < n) (Finset.range n),
            ∑ b ∈ Finset.filter (fun b => 1 ≤ 2 * b ∧ 2 * b < n ∧ Nat.Coprime a b)
              (Finset.range n),
            (n - 2 * a) * (n - 2 * b))) := by
  have hMain : (∑ ab ∈ dirs n, (n - ab.1) * (n - ab.2))
      = ∑ a ∈ Finset.filter (fun a => 1 ≤ a) (Finset.range n),
          ∑ b ∈ Finset.filter (fun b => 1 ≤ b ∧ Nat.Coprime a b) (Finset.range n),
          (n - a) * (n - b) := by
    rw [dirs, Finset.sum_filter, Finset.sum_product]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_filter]
    by_cases h1 : 1 ≤ a
    · simp only [h1, ite_true]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases h2 : 1 ≤ b <;> by_cases hc : Nat.Coprime a b <;> simp [h2, hc]
    · simp only [h1, ite_false]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      simp
  have hCorr : (∑ ab ∈ dirs n, (n - 2 * ab.1) * (n - 2 * ab.2))
      = ∑ a ∈ Finset.filter (fun a => 1 ≤ 2 * a ∧ 2 * a < n) (Finset.range n),
          ∑ b ∈ Finset.filter (fun b => 1 ≤ 2 * b ∧ 2 * b < n ∧ Nat.Coprime a b)
            (Finset.range n),
          (n - 2 * a) * (n - 2 * b) := by
    rw [dirs, Finset.sum_filter, Finset.sum_product]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_filter]
    by_cases h1 : 1 ≤ a
    · by_cases hA : 2 * a < n
      · have h2a : 1 ≤ 2 * a := by omega
        simp only [h2a, hA, and_self, ite_true]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        by_cases hL : 1 ≤ a ∧ 1 ≤ b ∧ Nat.Coprime a b
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hL)]
          by_cases hB : 2 * b < n
          · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hB, hL.2.2⟩)]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hB h.2.1)),
              show n - 2 * b = 0 from by omega, Nat.mul_zero]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hL),
            ite_eq_right_of_eq_false _ _ (eq_false (fun h => hL ⟨h1, by omega, h.2.2⟩))]
      · have : n - 2 * a = 0 := by omega
        simp only [hA, and_false, ite_false]
        refine Finset.sum_eq_zero (fun b _ => ?_)
        simp only [this, Nat.zero_mul, ite_self]
    · have h2a : ¬ (1 ≤ 2 * a) := by omega
      simp only [h2a, false_and, ite_false]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      simp [h1]
  have hle : ∀ ab ∈ dirs n, (n - 2 * ab.1) * (n - 2 * ab.2) ≤ (n - ab.1) * (n - ab.2) :=
    fun ab _ => Nat.mul_le_mul (Nat.sub_le_sub_left (by omega) n) (Nat.sub_le_sub_left (by omega) n)
  have hsum_le : (∑ ab ∈ dirs n, (n - 2 * ab.1) * (n - 2 * ab.2))
      ≤ ∑ ab ∈ dirs n, (n - ab.1) * (n - ab.2) := Finset.sum_le_sum hle
  have hsub : (∑ ab ∈ dirs n, ((n - ab.1) * (n - ab.2) - (n - 2 * ab.1) * (n - 2 * ab.2)))
      = (∑ ab ∈ dirs n, (n - ab.1) * (n - ab.2)) - ∑ ab ∈ dirs n, (n - 2 * ab.1) *
          (n - 2 * ab.2) := by
    symm
    rw [Nat.sub_eq_iff_eq_add hsum_le, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ab hab => (Nat.sub_add_cancel (hle ab hab)).symm)
  rw [hsub, hMain, hCorr]

/-- **Crossing points of the regular drawing of the complete bipartite graph.** Let $n$ be a
natural number. In the regular drawing of $K_{n,n}$ in $\mathbb{Q}^2$, the left vertices are the
points $(0, i)$ and the right vertices are the points $(1, j)$ for $0 \le i, j < n$, and each edge
is the straight segment from $(0, i)$ to $(1, j)$. For $i < i'$ and $j' < j$, the edges from
$(0, i)$ to $(1, j)$ and from $(0, i')$ to $(1, j')$ cross at the point $(x, i + x(j - i))$, where
$x = (i' - i)/((i' - i) + (j - j'))$. The number of distinct points obtained in this way, over all
$i, i', j, j' < n$ with $i < i'$ and $j' < j$, equals $S_1 - S_2$, where $S_1$ is the sum of
$(n - a)(n - b)$ over all ordered pairs $(a, b)$ of coprime integers with $1 \le a, b \le n - 1$,
and $S_2$ is the sum of $(n - 2a)(n - 2b)$ over all ordered pairs $(a, b)$ of coprime integers
with $1 \le 2a \le n - 1$ and $1 \le 2b \le n - 1$.

The difference is taken in $\mathbb{N}$; since $S_2 \le S_1$, it is the ordinary difference.

Proves `Wanted` entry `legendre_regular_crossing`.

Source: Stéphane Legendre, "The Number of Crossings in a Regular Drawing of the
Complete Bipartite Graph", Journal of Integer Sequences 12 (2009), Article 09.5.5,
Proposition `count_all`, line 263,
<https://cs.uwaterloo.ca/journals/JIS/VOL12/Legendre/legendre2.tex>.
-/
theorem legendre_regular_crossing :
    ∀ (n : ℕ),
      Finset.card
        (Finset.image
          (fun p => match p with
            | ((i, j), (i', j')) =>
              (((i' : Rat) - (i : Rat)) /
                (((i' : Rat) - (i : Rat)) + ((j : Rat) - (j' : Rat))),
                (i : Rat) +
                  (((i' : Rat) - (i : Rat)) /
                    (((i' : Rat) - (i : Rat)) +
                      ((j : Rat) - (j' : Rat))) *
                    ((j : Rat) - (i : Rat)))))
          (Finset.filter
            (fun p => match p with
              | ((i, j), (i', j')) => i < i' ∧ j' < j)
            (Finset.product
              (Finset.product (Finset.range n) (Finset.range n))
              (Finset.product (Finset.range n) (Finset.range n))))) =
        ((∑ a ∈ Finset.filter (fun a => 1 ≤ a) (Finset.range n),
            ∑ b ∈ Finset.filter (fun b => 1 ≤ b ∧ Nat.Coprime a b)
              (Finset.range n),
            (n - a) * (n - b)) -
          (∑ a ∈ Finset.filter (fun a => 1 ≤ 2 * a ∧ 2 * a < n)
              (Finset.range n),
            ∑ b ∈ Finset.filter
              (fun b => 1 ≤ 2 * b ∧ 2 * b < n ∧ Nat.Coprime a b)
              (Finset.range n),
            (n - 2 * a) * (n - 2 * b))) := by
  intro n
  change (Finset.image phi (box n)).card = _
  rw [reduction, image_key_card]
  rw [Finset.sum_congr rfl (fun ab hab => f_eq ab.1 ab.2 n
    ((Finset.mem_filter.mp hab).2.1) ((Finset.mem_filter.mp hab).2.2.1)
    ((Finset.mem_filter.mp hab).2.2.2))]
  exact sum_match n

end MetaMathlibExt
