/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.NumberTheory.QuadraticForms.ThreeSquares

import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

namespace MetaMathlibExt

/-! # Legendre-symbol recursion for sums of three squares

This file proves the prime-power recursion for `Nat.threeSquareRepresentationCount` in terms of a
Legendre symbol and a geometric sum.
-/

private abbrev r3legIntVec := (ℤ × ℤ) × ℤ

private abbrev r3legModVec (p : ℕ) := (ZMod p × ZMod p) × ZMod p

private def r3legQ {R : Type*} [Semiring R] (x : (R × R) × R) : R :=
  x.1.1 ^ 2 + x.1.2 ^ 2 + x.2 ^ 2

private def r3legB {R : Type*} [Semiring R] (x y : (R × R) × R) : R :=
  x.1.1 * y.1.1 + x.1.2 * y.1.2 + x.2 * y.2

private def r3legRed (p : ℕ) (x : r3legIntVec) : r3legModVec p :=
  (((x.1.1 : ZMod p), (x.1.2 : ZMod p)), (x.2 : ZMod p))

private def r3legScale (c : ℤ) (x : r3legIntVec) : r3legIntVec :=
  ((c * x.1.1, c * x.1.2), c * x.2)

private def r3legAdd {R : Type*} [Add R] (x y : (R × R) × R) : (R × R) × R :=
  ((x.1.1 + y.1.1, x.1.2 + y.1.2), x.2 + y.2)

private def r3legSub {R : Type*} [Sub R] (x y : (R × R) × R) : (R × R) × R :=
  ((x.1.1 - y.1.1, x.1.2 - y.1.2), x.2 - y.2)

private def r3legRep (n : ℕ) : Finset r3legIntVec :=
  ((((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ))) ×ˢ
      (Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
      (fun x => r3legQ x = (n : ℤ)))

private lemma r3leg_coord_mem (n : ℕ) (a b c : ℤ)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = (n : ℤ)) :
    a ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  rw [Finset.mem_Icc]
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  have ha : a ^ 2 ≤ (n : ℤ) := by omega
  have hpos := Int.le_self_sq a
  have hneg := Int.le_self_sq (-a)
  rw [show (-a) ^ 2 = a ^ 2 by ring] at hneg
  omega

private lemma r3leg_mem_rep {n : ℕ} {x : r3legIntVec} :
    x ∈ r3legRep n ↔ r3legQ x = (n : ℤ) := by
  rw [r3legRep, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_product, Finset.mem_product]
    have h₁ := r3leg_coord_mem n x.1.1 x.1.2 x.2 h
    have h₂ := r3leg_coord_mem n x.1.2 x.1.1 x.2 (by
      dsimp [r3legQ] at h ⊢
      linear_combination h)
    have h₃ := r3leg_coord_mem n x.2 x.1.1 x.1.2 (by
      dsimp [r3legQ] at h ⊢
      linear_combination h)
    exact ⟨⟨h₁, h₂⟩, h₃⟩

private lemma r3leg_rep_card (n : ℕ) :
    (r3legRep n).card = Nat.threeSquareRepresentationCount n := by
  rfl

private def r3legPure (x : r3legIntVec) : Quaternion ℤ :=
  { re := 0, imI := x.1.1, imJ := x.1.2, imK := x.2 }

private def r3legVec (q : Quaternion ℤ) : r3legIntVec :=
  ((q.imI, q.imJ), q.imK)

private def r3legPhi (q : Quaternion ℤ) (x : r3legIntVec) : r3legIntVec :=
  r3legVec (q * r3legPure x * star q)

private lemma r3leg_pure_injective : Function.Injective r3legPure := by
  intro x y h
  have hI := congrArg (fun q : Quaternion ℤ => q.imI) h
  have hJ := congrArg (fun q : Quaternion ℤ => q.imJ) h
  have hK := congrArg (fun q : Quaternion ℤ => q.imK) h
  exact Prod.ext (Prod.ext hI hJ) hK

private lemma r3leg_normSq_pure (x : r3legIntVec) :
    Quaternion.normSq (r3legPure x) = r3legQ x := by
  simp [Quaternion.normSq_def', r3legPure, r3legQ]

private lemma r3leg_sandwich_re (q : Quaternion ℤ) (x : r3legIntVec) :
    (q * r3legPure x * star q).re = 0 := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star, r3legPure]
  ring

private lemma r3leg_pure_phi (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legPure (r3legPhi q x) = q * r3legPure x * star q := by
  apply Quaternion.ext
  · exact (r3leg_sandwich_re q x).symm
  · rfl
  · rfl
  · rfl

private lemma r3leg_phi_comp (q r : Quaternion ℤ) (x : r3legIntVec) :
    r3legPhi q (r3legPhi r x) = r3legPhi (q * r) x := by
  apply r3leg_pure_injective
  calc
    r3legPure (r3legPhi q (r3legPhi r x)) =
        q * r3legPure (r3legPhi r x) * star q := r3leg_pure_phi q _
    _ = q * (r * r3legPure x * star r) * star q := by
      rw [r3leg_pure_phi]
    _ = (q * r) * r3legPure x * star (q * r) := by
      rw [star_mul]
      simp only [mul_assoc]
    _ = r3legPure (r3legPhi (q * r) x) := (r3leg_pure_phi _ _).symm

private lemma r3leg_q_phi (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legQ (r3legPhi q x) = Quaternion.normSq q ^ 2 * r3legQ x := by
  calc
    r3legQ (r3legPhi q x) =
        Quaternion.normSq (r3legPure (r3legPhi q x)) :=
      (r3leg_normSq_pure _).symm
    _ = Quaternion.normSq (q * r3legPure x * star q) := by
      rw [r3leg_pure_phi]
    _ = Quaternion.normSq q ^ 2 * r3legQ x := by
      rw [map_mul, map_mul, Quaternion.normSq_star, r3leg_normSq_pure]
      ring

private lemma r3leg_phi_fst_fst (q : Quaternion ℤ) (x : r3legIntVec) :
    (r3legPhi q x).1.1 =
      (q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2) * x.1.1 +
      2 * (q.imI * q.imJ - q.re * q.imK) * x.1.2 +
      2 * (q.imI * q.imK + q.re * q.imJ) * x.2 := by
  simp only [r3legPhi, r3legVec, r3legPure, Quaternion.imI_mul,
    Quaternion.re_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star]
  ring

private lemma r3leg_phi_fst_snd (q : Quaternion ℤ) (x : r3legIntVec) :
    (r3legPhi q x).1.2 =
      2 * (q.imI * q.imJ + q.re * q.imK) * x.1.1 +
      (q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2) * x.1.2 +
      2 * (q.imJ * q.imK - q.re * q.imI) * x.2 := by
  simp only [r3legPhi, r3legVec, r3legPure, Quaternion.imJ_mul,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star]
  ring

private lemma r3leg_phi_snd (q : Quaternion ℤ) (x : r3legIntVec) :
    (r3legPhi q x).2 =
      2 * (q.imI * q.imK - q.re * q.imJ) * x.1.1 +
      2 * (q.imJ * q.imK + q.re * q.imI) * x.1.2 +
      (q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2) * x.2 := by
  simp only [r3legPhi, r3legVec, r3legPure, Quaternion.imK_mul,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star]
  ring

private lemma r3leg_phi_smul (c : ℤ) (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legPhi (c • q) x = r3legScale (c ^ 2) (r3legPhi q x) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [r3legScale]
      rw [r3leg_phi_fst_fst, r3leg_phi_fst_fst]
      simp
      ring
    · simp only [r3legScale]
      rw [r3leg_phi_fst_snd, r3leg_phi_fst_snd]
      simp
      ring
  · simp only [r3legScale]
    rw [r3leg_phi_snd, r3leg_phi_snd]
    simp
    ring

private lemma r3leg_phi_intCast (c : ℤ) (x : r3legIntVec) :
    r3legPhi (c : Quaternion ℤ) x = r3legScale (c ^ 2) x := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [r3legScale]
      rw [r3leg_phi_fst_fst]
      simp
    · simp only [r3legScale]
      rw [r3leg_phi_fst_snd]
      simp
  · simp only [r3legScale]
    rw [r3leg_phi_snd]
    simp

private lemma r3leg_phi_star_phi (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legPhi q (r3legPhi (star q) x) =
      r3legScale (Quaternion.normSq q ^ 2) x := by
  rw [r3leg_phi_comp, Quaternion.self_mul_star]
  exact r3leg_phi_intCast _ _

private lemma r3leg_phi_phi_star (q : Quaternion ℤ) (x : r3legIntVec) :
    r3legPhi (star q) (r3legPhi q x) =
      r3legScale (Quaternion.normSq q ^ 2) x := by
  rw [r3leg_phi_comp, Quaternion.star_mul_self]
  exact r3leg_phi_intCast _ _

private lemma r3leg_phi_adjoint (q : Quaternion ℤ) (z u : r3legIntVec) :
    r3legB (r3legPhi (star q) z) u = r3legB z (r3legPhi q u) := by
  simp only [r3legB]
  rw [r3leg_phi_fst_fst, r3leg_phi_fst_snd, r3leg_phi_snd,
    r3leg_phi_fst_fst, r3leg_phi_fst_snd, r3leg_phi_snd]
  simp only [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star]
  ring

private def r3legAligned (p : ℕ) (q : Quaternion ℤ) (w : r3legModVec p) : Prop :=
  ∀ x, ∃ t : ZMod p, r3legRed p (r3legPhi q x) = t • w

private lemma r3leg_red_scale (p : ℕ) (c : ℤ) (x : r3legIntVec) :
    r3legRed p (r3legScale c x) = (c : ZMod p) • r3legRed p x := by
  apply Prod.ext
  · apply Prod.ext <;> simp [r3legRed, r3legScale]
  · simp [r3legRed, r3legScale]

private lemma r3leg_aligned_transfer {p : ℕ} [Fact (Nat.Prime p)]
    {q q' r : Quaternion ℤ}
    {w : r3legModVec p} {c : ℤ} (hc : (c : ZMod p) ≠ 0)
    (hqr : c • q' = q * r) (hq : r3legAligned p q w) :
    r3legAligned p q' w := by
  intro x
  obtain ⟨t, ht⟩ := hq (r3legPhi r x)
  have hs : ((c : ZMod p) ^ 2) • r3legRed p (r3legPhi q' x) = t • w := by
    calc
      ((c : ZMod p) ^ 2) • r3legRed p (r3legPhi q' x) =
          r3legRed p (r3legScale (c ^ 2) (r3legPhi q' x)) := by
        rw [← Int.cast_pow]
        exact (r3leg_red_scale p (c ^ 2) (r3legPhi q' x)).symm
      _ = r3legRed p (r3legPhi (c • q') x) := by
        rw [r3leg_phi_smul]
      _ = r3legRed p (r3legPhi (q * r) x) := by rw [hqr]
      _ = r3legRed p (r3legPhi q (r3legPhi r x)) := by
        rw [r3leg_phi_comp]
      _ = t • w := ht
  refine ⟨(((c : ZMod p) ^ 2)⁻¹ * t), ?_⟩
  have hi := congrArg (fun v : r3legModVec p => ((c : ZMod p) ^ 2)⁻¹ • v) hs
  have hc2 : (c : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  simpa [smul_smul, hc2] using hi

private def r3legEpsI : Quaternion ℤ :=
  { re := 1, imI := -1, imJ := 0, imK := 0 }

private def r3legEpsJ : Quaternion ℤ :=
  { re := 1, imI := 0, imJ := -1, imK := 0 }

private def r3legEpsK : Quaternion ℤ :=
  { re := 1, imI := 0, imJ := 0, imK := -1 }

private lemma r3leg_zmod_two_parity :
    ∀ a b c d : ZMod 2, a + b + c + d = 0 →
      (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  decide

private lemma r3leg_zmod_two_sq (a : ZMod 2) : a ^ 2 = a := by
  revert a
  decide

private lemma r3leg_zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

private lemma r3leg_eps_norm (e : Quaternion ℤ)
    (h : e = r3legEpsI ∨ e = r3legEpsJ ∨ e = r3legEpsK) :
    Quaternion.normSq e = 2 := by
  rcases h with rfl | rfl | rfl <;>
    simp [Quaternion.normSq_def', r3legEpsI, r3legEpsJ, r3legEpsK]

private lemma r3leg_two_dvd_of_cast_eq_zero (z : ℤ) (h : (z : ZMod 2) = 0) :
    (2 : ℤ) ∣ z := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp h

private lemma r3leg_even_right_factor (q : Quaternion ℤ)
    (h2 : (2 : ℤ) ∣ Quaternion.normSq q) :
    ∃ e : Quaternion ℤ,
      Quaternion.normSq e = 2 ∧
      (2 : ℤ) ∣ (q * e).re ∧ (2 : ℤ) ∣ (q * e).imI ∧
      (2 : ℤ) ∣ (q * e).imJ ∧ (2 : ℤ) ∣ (q * e).imK := by
  have hn : ((Quaternion.normSq q : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  have hsum : (q.re : ZMod 2) + q.imI + q.imJ + q.imK = 0 := by
    rw [Quaternion.normSq_def'] at hn
    push_cast at hn
    simpa only [r3leg_zmod_two_sq] using hn
  rcases r3leg_zmod_two_parity _ _ _ _ hsum with h | h | h
  · refine ⟨r3legEpsI, r3leg_eps_norm _ (Or.inl rfl), ?_⟩
    obtain ⟨h₁, h₂⟩ := h
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, r3legEpsI]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp [r3leg_zmod_two_add_self]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
  · refine ⟨r3legEpsJ, r3leg_eps_norm _ (Or.inr (Or.inl rfl)), ?_⟩
    obtain ⟨h₁, h₂⟩ := h
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, r3legEpsJ]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp [r3leg_zmod_two_add_self]
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
  · refine ⟨r3legEpsK, r3leg_eps_norm _ (Or.inr (Or.inr rfl)), ?_⟩
    obtain ⟨h₁, h₂⟩ := h
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, r3legEpsK]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
    constructor
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₂]
      simp [r3leg_zmod_two_add_self]
    · apply r3leg_two_dvd_of_cast_eq_zero
      push_cast
      rw [h₁]
      simp [r3leg_zmod_two_add_self]

private def r3legQuatDiv (q : Quaternion ℤ) (c : ℤ) : Quaternion ℤ :=
  { re := q.re / c, imI := q.imI / c, imJ := q.imJ / c, imK := q.imK / c }

private lemma r3leg_smul_quatDiv (q : Quaternion ℤ) (c : ℤ)
    (hre : c ∣ q.re) (hI : c ∣ q.imI) (hJ : c ∣ q.imJ) (hK : c ∣ q.imK) :
    c • r3legQuatDiv q c = q := by
  apply Quaternion.ext
  · change c * (q.re / c) = q.re
    exact Int.mul_ediv_cancel' hre
  · change c * (q.imI / c) = q.imI
    exact Int.mul_ediv_cancel' hI
  · change c * (q.imJ / c) = q.imJ
    exact Int.mul_ediv_cancel' hJ
  · change c * (q.imK / c) = q.imK
    exact Int.mul_ediv_cancel' hK

private lemma r3leg_descend_even {p m : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (q : Quaternion ℤ) (w : r3legModVec p)
    (hm : 0 < m) (hm2 : 2 ∣ m)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p)
    (halign : r3legAligned p q w) :
    ∃ q' : Quaternion ℤ,
      Quaternion.normSq q' = ((m / 2 : ℕ) : ℤ) * p ∧
      0 < m / 2 ∧ m / 2 < m ∧ r3legAligned p q' w := by
  have hnorm2 : (2 : ℤ) ∣ Quaternion.normSq q := by
    obtain ⟨k, hk⟩ := hm2
    refine ⟨(k : ℤ) * p, ?_⟩
    rw [hnorm, hk]
    push_cast
    ring
  obtain ⟨e, he, hre, hI, hJ, hK⟩ := r3leg_even_right_factor q hnorm2
  let q' := r3legQuatDiv (q * e) 2
  have hscale : (2 : ℤ) • q' = q * e := by
    exact r3leg_smul_quatDiv _ _ hre hI hJ hK
  have hnscale := congrArg Quaternion.normSq hscale
  rw [Quaternion.normSq_smul, map_mul, he, hnorm] at hnscale
  have hnorm' : Quaternion.normSq q' = ((m / 2 : ℕ) : ℤ) * p := by
    obtain ⟨k, hk⟩ := hm2
    subst m
    norm_num at hnscale ⊢
    nlinarith
  have hmdivpos : 0 < m / 2 := Nat.div_pos (by omega) (by decide)
  have hmdivlt : m / 2 < m := Nat.div_lt_self hm (by decide)
  have htwo : ((2 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have hnat : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hnat
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hd
    omega
  refine ⟨q', hnorm', hmdivpos, hmdivlt, ?_⟩
  exact r3leg_aligned_transfer htwo hscale halign

private lemma r3leg_bmod_sq_le (z : ℤ) (k : ℕ) :
    (z.bmod (2 * k + 1)) ^ 2 ≤ (k : ℤ) ^ 2 := by
  have hlo := Int.le_bmod (x := z) (m := 2 * k + 1) (by omega)
  have hhi := Int.bmod_lt (x := z) (m := 2 * k + 1) (by omega)
  norm_num [Nat.cast_add, Nat.cast_mul] at hlo hhi
  have hdivlo : (2 * (k : ℤ) + 1) / 2 = k := by omega
  have hdivhi : (2 * (k : ℤ) + 1 + 1) / 2 = k + 1 := by omega
  rw [hdivlo] at hlo
  rw [hdivhi] at hhi
  nlinarith

private def r3legQuatBmod (q : Quaternion ℤ) (m : ℕ) : Quaternion ℤ :=
  { re := q.re.bmod m, imI := q.imI.bmod m,
    imJ := q.imJ.bmod m, imK := q.imK.bmod m }

private lemma r3leg_bmod_cast (z : ℤ) (m : ℕ) :
    ((z.bmod m : ℤ) : ZMod m) = (z : ZMod m) := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mpr
  exact Int.bmod_emod

private lemma r3leg_norm_bmod_dvd (q : Quaternion ℤ) (m p : ℕ)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p) :
    (m : ℤ) ∣ Quaternion.normSq (r3legQuatBmod q m) := by
  have hz : ((Quaternion.normSq q : ℤ) : ZMod m) = 0 := by
    rw [hnorm]
    push_cast
    simp
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Quaternion.normSq_def']
  push_cast
  simp only [r3legQuatBmod, r3leg_bmod_cast]
  rw [Quaternion.normSq_def'] at hz
  push_cast at hz
  exact hz

private lemma r3leg_norm_bmod_ne_zero {p m : ℕ} [Fact (Nat.Prime p)]
    (q : Quaternion ℤ) (hm3 : 3 ≤ m) (hmp : m < p)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p) :
    Quaternion.normSq (r3legQuatBmod q m) ≠ 0 := by
  intro hz
  have hqzero : r3legQuatBmod q m = 0 := Quaternion.normSq_eq_zero.mp hz
  have hre0 : q.re.bmod m = 0 := congrArg (fun a : Quaternion ℤ => a.re) hqzero
  have hI0 : q.imI.bmod m = 0 := congrArg (fun a : Quaternion ℤ => a.imI) hqzero
  have hJ0 : q.imJ.bmod m = 0 := congrArg (fun a : Quaternion ℤ => a.imJ) hqzero
  have hK0 : q.imK.bmod m = 0 := congrArg (fun a : Quaternion ℤ => a.imK) hqzero
  have hre : (m : ℤ) ∣ q.re := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [← r3leg_bmod_cast q.re m, hre0]
    simp
  have hI : (m : ℤ) ∣ q.imI := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [← r3leg_bmod_cast q.imI m, hI0]
    simp
  have hJ : (m : ℤ) ∣ q.imJ := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [← r3leg_bmod_cast q.imJ m, hJ0]
    simp
  have hK : (m : ℤ) ∣ q.imK := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [← r3leg_bmod_cast q.imK m, hK0]
    simp
  obtain ⟨a, ha⟩ := hre
  obtain ⟨b, hb⟩ := hI
  obtain ⟨c, hc⟩ := hJ
  obtain ⟨d, hd⟩ := hK
  have hsq : (m : ℤ) ^ 2 ∣ Quaternion.normSq q := by
    refine ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, ?_⟩
    rw [Quaternion.normSq_def', ha, hb, hc, hd]
    ring
  rw [hnorm] at hsq
  have hmint : (m : ℤ) ∣ (p : ℤ) := by
    refine Int.dvd_of_mul_dvd_mul_left (a := (m : ℤ)) (m := (m : ℤ))
      (n := (p : ℤ)) ?_ ?_
    · exact_mod_cast (show m ≠ 0 by omega)
    · simpa [pow_two, mul_assoc] using hsq
  have hmnat : m ∣ p := by exact_mod_cast hmint
  rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hmnat with hm1 | hmp'
  · omega
  · omega

private lemma r3leg_mul_star_bmod_dvd (q : Quaternion ℤ) (m : ℕ)
    (hr : (m : ℤ) ∣ Quaternion.normSq (r3legQuatBmod q m)) :
    (m : ℤ) ∣ (q * star (r3legQuatBmod q m)).re ∧
      (m : ℤ) ∣ (q * star (r3legQuatBmod q m)).imI ∧
      (m : ℤ) ∣ (q * star (r3legQuatBmod q m)).imJ ∧
      (m : ℤ) ∣ (q * star (r3legQuatBmod q m)).imK := by
  let r := r3legQuatBmod q m
  have hre : (r.re : ZMod m) = q.re := r3leg_bmod_cast q.re m
  have hI : (r.imI : ZMod m) = q.imI := r3leg_bmod_cast q.imI m
  have hJ : (r.imJ : ZMod m) = q.imJ := r3leg_bmod_cast q.imJ m
  have hK : (r.imK : ZMod m) = q.imK := r3leg_bmod_cast q.imK m
  have hrzero : ((Quaternion.normSq r : ℤ) : ZMod m) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hr
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]
    push_cast
    rw [← hre, ← hI, ← hJ, ← hK]
    rw [Quaternion.normSq_def'] at hrzero
    push_cast at hrzero
    linear_combination hrzero
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Quaternion.imI_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]
    push_cast
    rw [← hre, ← hI, ← hJ, ← hK]
    ring
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Quaternion.imJ_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]
    push_cast
    rw [← hre, ← hI, ← hJ, ← hK]
    ring
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]
    push_cast
    rw [← hre, ← hI, ← hJ, ← hK]
    ring

private lemma r3leg_descend_odd {p m : ℕ} [Fact (Nat.Prime p)]
    (q : Quaternion ℤ) (w : r3legModVec p)
    (hm3 : 3 ≤ m) (hmp : m < p) (hodd : Odd m)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p)
    (halign : r3legAligned p q w) :
    ∃ m' : ℕ, ∃ q' : Quaternion ℤ,
      0 < m' ∧ m' < m ∧ Quaternion.normSq q' = (m' : ℤ) * p ∧
      r3legAligned p q' w := by
  let r := r3legQuatBmod q m
  have hrdiv : (m : ℤ) ∣ Quaternion.normSq r := by
    simpa [r] using r3leg_norm_bmod_dvd q m p hnorm
  have hrne : Quaternion.normSq r ≠ 0 := by
    simpa [r] using r3leg_norm_bmod_ne_zero q hm3 hmp hnorm
  have hrpos : 0 < Quaternion.normSq r := by
    have hrnonneg : 0 ≤ Quaternion.normSq r := Quaternion.normSq_nonneg
    omega
  obtain ⟨k, hk⟩ := hodd.exists_bit1
  have hrlt : Quaternion.normSq r < (m : ℤ) ^ 2 := by
    have h₀ := r3leg_bmod_sq_le q.re k
    have h₁ := r3leg_bmod_sq_le q.imI k
    have h₂ := r3leg_bmod_sq_le q.imJ k
    have h₃ := r3leg_bmod_sq_le q.imK k
    rw [Quaternion.normSq_def']
    dsimp [r, r3legQuatBmod]
    rw [hk]
    push_cast
    nlinarith
  have hcoords := r3leg_mul_star_bmod_dvd q m (by simpa [r] using hrdiv)
  obtain ⟨t, ht⟩ := hrdiv
  have htpos : 0 < t := by
    have hmpos : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
    nlinarith
  let m' := t.natAbs
  have htcast : (m' : ℤ) = t := by
    exact Int.natAbs_of_nonneg (le_of_lt htpos)
  have hm'pos : 0 < m' := Int.natAbs_pos.mpr (ne_of_gt htpos)
  have htlt : t < (m : ℤ) := by
    have hmpos : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
    nlinarith
  have hm'lt : m' < m := by
    have hm'lt' : (m' : ℤ) < (m : ℤ) := by rw [htcast]; exact htlt
    exact_mod_cast hm'lt'
  have hrnorm : Quaternion.normSq r = (m : ℤ) * m' := by
    rw [ht, htcast]
  obtain ⟨hre, hI, hJ, hK⟩ := hcoords
  let q' := r3legQuatDiv (q * star r) m
  have hscale : (m : ℤ) • q' = q * star r := by
    exact r3leg_smul_quatDiv _ _ hre hI hJ hK
  have hnscale := congrArg Quaternion.normSq hscale
  rw [Quaternion.normSq_smul, map_mul, Quaternion.normSq_star, hnorm, hrnorm] at hnscale
  have hnorm' : Quaternion.normSq q' = (m' : ℤ) * p := by
    have hmpos : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
    nlinarith
  have hmcast : ((m : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hnat : ((m : ℕ) : ZMod p) = 0 := by exact_mod_cast hz
    have hd : p ∣ m := (ZMod.natCast_eq_zero_iff m p).mp hnat
    have hple : p ≤ m := Nat.le_of_dvd (by omega) hd
    omega
  refine ⟨m', q', hm'pos, hm'lt, hnorm', ?_⟩
  exact r3leg_aligned_transfer hmcast hscale halign

private def r3legLift {p : ℕ} (w : r3legModVec p) : r3legIntVec :=
  ((w.1.1.valMinAbs, w.1.2.valMinAbs), w.2.valMinAbs)

private lemma r3leg_red_lift {p : ℕ} (w : r3legModVec p) :
    r3legRed p (r3legLift w) = w := by
  apply Prod.ext
  · apply Prod.ext <;> simp [r3legRed, r3legLift, ZMod.coe_valMinAbs]
  · simp [r3legRed, r3legLift, ZMod.coe_valMinAbs]

private lemma r3leg_pure_aligned {p : ℕ} (u : r3legIntVec)
    (hu : r3legQ (r3legRed p u) = 0) :
    r3legAligned p (r3legPure u) (r3legRed p u) := by
  intro x
  refine ⟨2 * r3legB (r3legRed p x) (r3legRed p u), ?_⟩
  apply Prod.ext
  · apply Prod.ext
    · change ((r3legPhi (r3legPure u) x).1.1 : ZMod p) =
        (2 * r3legB (r3legRed p x) (r3legRed p u)) * (u.1.1 : ZMod p)
      rw [r3leg_phi_fst_fst]
      simp only [r3legPure]
      push_cast
      dsimp [r3legB, r3legRed, r3legQ] at hu ⊢
      linear_combination -(x.1.1 : ZMod p) * hu
    · change ((r3legPhi (r3legPure u) x).1.2 : ZMod p) =
        (2 * r3legB (r3legRed p x) (r3legRed p u)) * (u.1.2 : ZMod p)
      rw [r3leg_phi_fst_snd]
      simp only [r3legPure]
      push_cast
      dsimp [r3legB, r3legRed, r3legQ] at hu ⊢
      linear_combination -(x.1.2 : ZMod p) * hu
  · change ((r3legPhi (r3legPure u) x).2 : ZMod p) =
      (2 * r3legB (r3legRed p x) (r3legRed p u)) * (u.2 : ZMod p)
    rw [r3leg_phi_snd]
    simp only [r3legPure]
    push_cast
    dsimp [r3legB, r3legRed, r3legQ] at hu ⊢
    linear_combination -(x.2 : ZMod p) * hu

private lemma r3leg_valMinAbs_sq_le {p : ℕ} [NeZero p] (a : ZMod p) :
    a.valMinAbs ^ 2 ≤ ((p / 2 : ℕ) : ℤ) ^ 2 := by
  have h := ZMod.natAbs_valMinAbs_le a
  have hsq := Nat.pow_le_pow_left h 2
  rw [← Int.natAbs_sq]
  exact_mod_cast hsq

private lemma r3leg_initial_aligned_factor {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legModVec p) (hwne : w ≠ 0) (hwq : r3legQ w = 0) :
    ∃ m : ℕ, ∃ q : Quaternion ℤ,
      0 < m ∧ m < p ∧ Quaternion.normSq q = (m : ℤ) * p ∧
      r3legAligned p q w := by
  let u := r3legLift w
  let q := r3legPure u
  have hred : r3legRed p u = w := r3leg_red_lift w
  have huq : r3legQ (r3legRed p u) = 0 := by rw [hred]; exact hwq
  have hune : u ≠ 0 := by
    intro hu
    apply hwne
    rw [← hred, hu]
    simp [r3legRed]
  have hqne : q ≠ 0 := by
    intro hq
    apply hune
    have hI := congrArg (fun a : Quaternion ℤ => a.imI) hq
    have hJ := congrArg (fun a : Quaternion ℤ => a.imJ) hq
    have hK := congrArg (fun a : Quaternion ℤ => a.imK) hq
    exact Prod.ext (Prod.ext (by simpa [q, r3legPure] using hI)
      (by simpa [q, r3legPure] using hJ)) (by simpa [q, r3legPure] using hK)
  have hnormpos : 0 < Quaternion.normSq q := by
    have hnonneg : 0 ≤ Quaternion.normSq q := Quaternion.normSq_nonneg
    have hne : Quaternion.normSq q ≠ 0 := mt Quaternion.normSq_eq_zero.mp hqne
    omega
  have hpdvd : (p : ℤ) ∣ Quaternion.normSq q := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [r3leg_normSq_pure]
    dsimp [r3legQ, r3legRed] at huq ⊢
    push_cast
    exact huq
  have hnormlt : Quaternion.normSq q < (p : ℤ) ^ 2 := by
    have h₁ := r3leg_valMinAbs_sq_le w.1.1
    have h₂ := r3leg_valMinAbs_sq_le w.1.2
    have h₃ := r3leg_valMinAbs_sq_le w.2
    have hhalf : 2 * (p / 2) ≤ p := Nat.mul_div_le p 2
    rw [r3leg_normSq_pure, r3legQ]
    dsimp [q, u, r3legLift]
    have hhalf' : (2 : ℤ) * (p / 2 : ℕ) ≤ p := by exact_mod_cast hhalf
    have hp' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    nlinarith
  obtain ⟨t, ht⟩ := hpdvd
  have htpos : 0 < t := by
    have hp : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
    nlinarith
  let m := t.natAbs
  have htcast : (m : ℤ) = t := Int.natAbs_of_nonneg (le_of_lt htpos)
  have hmpos : 0 < m := Int.natAbs_pos.mpr (ne_of_gt htpos)
  have htlt : t < (p : ℤ) := by
    have hp : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
    nlinarith
  have hmlt : m < p := by
    have : (m : ℤ) < (p : ℤ) := by rw [htcast]; exact htlt
    exact_mod_cast this
  refine ⟨m, q, hmpos, hmlt, ?_, ?_⟩
  · rw [ht, htcast]
    ring
  · rw [← hred]
    exact r3leg_pure_aligned u huq

private lemma r3leg_descend_to_one {p m : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legModVec p) (q : Quaternion ℤ)
    (hmpos : 0 < m) (hmp : m < p)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p)
    (halign : r3legAligned p q w) :
    ∃ π : Quaternion ℤ, Quaternion.normSq π = p ∧ r3legAligned p π w := by
  induction m using Nat.strong_induction_on generalizing q with
  | h m ih =>
      by_cases hm1 : m = 1
      · subst m
        refine ⟨q, ?_, halign⟩
        simpa using hnorm
      rcases Nat.even_or_odd m with heven | hodd
      · have hm2 : 2 ∣ m := heven.two_dvd
        obtain ⟨q', hnorm', hmpos', hmlt, halign'⟩ :=
          r3leg_descend_even hp3 q w hmpos hm2 hnorm halign
        exact ih (m / 2) hmlt q' hmpos' (lt_trans hmlt hmp) hnorm' halign'
      · have hm3 : 3 ≤ m := by
          obtain ⟨k, hk⟩ := hodd.exists_bit1
          omega
        obtain ⟨m', q', hmpos', hmlt, hnorm', halign'⟩ :=
          r3leg_descend_odd q w hm3 hmp hodd hnorm halign
        exact ih m' hmlt q' hmpos' (lt_trans hmlt hmp) hnorm' halign'

private lemma r3leg_aligned_norm_prime {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legModVec p) (hwne : w ≠ 0) (hwq : r3legQ w = 0) :
    ∃ π : Quaternion ℤ, Quaternion.normSq π = p ∧ r3legAligned p π w := by
  obtain ⟨m, q, hmpos, hmp, hnorm, halign⟩ :=
    r3leg_initial_aligned_factor hp3 w hwne hwq
  exact r3leg_descend_to_one hp3 w q hmpos hmp hnorm halign

private def r3legE₁ : r3legIntVec := ((1, 0), 0)

private def r3legE₂ : r3legIntVec := ((0, 1), 0)

private def r3legE₃ : r3legIntVec := ((0, 0), 1)

private lemma r3leg_two_ne_zero {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    ((2 : ℤ) : ZMod p) ≠ 0 := by
  intro h
  have hnat : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hnat
  have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hd
  omega

private lemma r3leg_nonzero_column {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (π : Quaternion ℤ) (hnorm : Quaternion.normSq π = p) :
    ∃ e : r3legIntVec,
      (e = r3legE₁ ∨ e = r3legE₂ ∨ e = r3legE₃) ∧
      r3legQ e = 1 ∧ r3legRed p (r3legPhi π e) ≠ 0 := by
  by_cases h₁ : r3legRed p (r3legPhi π r3legE₁) ≠ 0
  · exact ⟨r3legE₁, Or.inl rfl, by decide, h₁⟩
  by_cases h₂ : r3legRed p (r3legPhi π r3legE₂) ≠ 0
  · exact ⟨r3legE₂, Or.inr (Or.inl rfl), by decide, h₂⟩
  by_cases h₃ : r3legRed p (r3legPhi π r3legE₃) ≠ 0
  · exact ⟨r3legE₃, Or.inr (Or.inr rfl), by decide, h₃⟩
  have h₁' := not_ne_iff.mp h₁
  have h₂' := not_ne_iff.mp h₂
  have h₃' := not_ne_iff.mp h₃
  have hd₁ :
      ((π.re ^ 2 + π.imI ^ 2 - π.imJ ^ 2 - π.imK ^ 2 : ℤ) : ZMod p) = 0 := by
    have h := congrArg (fun v : r3legModVec p => v.1.1) h₁'
    change ((r3legPhi π r3legE₁).1.1 : ZMod p) = 0 at h
    rw [r3leg_phi_fst_fst] at h
    simpa [r3legE₁] using h
  have hd₂ :
      ((π.re ^ 2 - π.imI ^ 2 + π.imJ ^ 2 - π.imK ^ 2 : ℤ) : ZMod p) = 0 := by
    have h := congrArg (fun v : r3legModVec p => v.1.2) h₂'
    change ((r3legPhi π r3legE₂).1.2 : ZMod p) = 0 at h
    rw [r3leg_phi_fst_snd] at h
    simpa [r3legE₂] using h
  have hd₃ :
      ((π.re ^ 2 - π.imI ^ 2 - π.imJ ^ 2 + π.imK ^ 2 : ℤ) : ZMod p) = 0 := by
    have h := congrArg (fun v : r3legModVec p => v.2) h₃'
    change ((r3legPhi π r3legE₃).2 : ZMod p) = 0 at h
    rw [r3leg_phi_snd] at h
    simpa [r3legE₃] using h
  have hn :
      (π.re : ZMod p) ^ 2 + π.imI ^ 2 + π.imJ ^ 2 + π.imK ^ 2 = 0 := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) hnorm
    rw [Quaternion.normSq_def'] at h
    push_cast at h
    simpa using h
  push_cast at hd₁ hd₂ hd₃
  have htwo := r3leg_two_ne_zero hp3
  have hAB : (π.re : ZMod p) ^ 2 + π.imI ^ 2 = 0 := by
    have h : (2 : ZMod p) * ((π.re : ZMod p) ^ 2 + π.imI ^ 2) = 0 := by
      linear_combination hd₁ + hn
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast htwo)
  have hAC : (π.re : ZMod p) ^ 2 + π.imJ ^ 2 = 0 := by
    have h : (2 : ZMod p) * ((π.re : ZMod p) ^ 2 + π.imJ ^ 2) = 0 := by
      linear_combination hd₂ + hn
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast htwo)
  have hAD : (π.re : ZMod p) ^ 2 + π.imK ^ 2 = 0 := by
    have h : (2 : ZMod p) * ((π.re : ZMod p) ^ 2 + π.imK ^ 2) = 0 := by
      linear_combination hd₃ + hn
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast htwo)
  have hA : (π.re : ZMod p) ^ 2 = 0 := by
    have h : (2 : ZMod p) * (π.re : ZMod p) ^ 2 = 0 := by
      linear_combination hAB + hAC + hAD - hn
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast htwo)
  have hB : (π.imI : ZMod p) ^ 2 = 0 := by linear_combination hAB - hA
  have hC : (π.imJ : ZMod p) ^ 2 = 0 := by linear_combination hAC - hA
  have hD : (π.imK : ZMod p) ^ 2 = 0 := by linear_combination hAD - hA
  have ha0 : (π.re : ZMod p) = 0 := (sq_eq_zero_iff).mp hA
  have hb0 : (π.imI : ZMod p) = 0 := (sq_eq_zero_iff).mp hB
  have hc0 : (π.imJ : ZMod p) = 0 := (sq_eq_zero_iff).mp hC
  have hd0 : (π.imK : ZMod p) = 0 := (sq_eq_zero_iff).mp hD
  have ha : (p : ℤ) ∣ π.re := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha0
  have hb : (p : ℤ) ∣ π.imI := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb0
  have hc : (p : ℤ) ∣ π.imJ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc0
  have hd : (p : ℤ) ∣ π.imK := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd0
  obtain ⟨a, ha'⟩ := ha
  obtain ⟨b, hb'⟩ := hb
  obtain ⟨c, hc'⟩ := hc
  obtain ⟨d, hd'⟩ := hd
  have hsq : (p : ℤ) ^ 2 ∣ Quaternion.normSq π := by
    refine ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, ?_⟩
    rw [Quaternion.normSq_def', ha', hb', hc', hd']
    ring
  rw [hnorm] at hsq
  have hpdiv : (p : ℤ) ∣ (1 : ℤ) := by
    refine Int.dvd_of_mul_dvd_mul_left (a := (p : ℤ)) (m := (p : ℤ))
      (n := 1) ?_ ?_
    · exact_mod_cast (show p ≠ 0 by omega)
    · simpa [pow_two] using hsq
  have hpdiv' : p ∣ 1 := by exact_mod_cast hpdiv
  have : p ≤ 1 := Nat.le_of_dvd (by decide) hpdiv'
  omega

private lemma r3leg_phi_scale (q : Quaternion ℤ) (c : ℤ) (x : r3legIntVec) :
    r3legPhi q (r3legScale c x) = r3legScale c (r3legPhi q x) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [r3legScale]
      rw [r3leg_phi_fst_fst, r3leg_phi_fst_fst]
      ring
    · simp only [r3legScale]
      rw [r3leg_phi_fst_snd, r3leg_phi_fst_snd]
      ring
  · simp only [r3legScale]
    rw [r3leg_phi_snd, r3leg_phi_snd]
    ring

private lemma r3leg_phi_add (q : Quaternion ℤ) (x y : r3legIntVec) :
    r3legPhi q (r3legAdd x y) = r3legAdd (r3legPhi q x) (r3legPhi q y) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [r3legAdd]
      rw [r3leg_phi_fst_fst, r3leg_phi_fst_fst, r3leg_phi_fst_fst]
      ring
    · simp only [r3legAdd]
      rw [r3leg_phi_fst_snd, r3leg_phi_fst_snd, r3leg_phi_fst_snd]
      ring
  · simp only [r3legAdd]
    rw [r3leg_phi_snd, r3leg_phi_snd, r3leg_phi_snd]
    ring

private lemma r3leg_red_sub (p : ℕ) (x y : r3legIntVec) :
    r3legRed p (r3legSub x y) = r3legSub (r3legRed p x) (r3legRed p y) := by
  apply Prod.ext
  · apply Prod.ext <;> simp [r3legRed, r3legSub]
  · simp [r3legRed, r3legSub]

private lemma r3leg_q_add_scaled (c d : ℤ) (x y : r3legIntVec) :
    r3legQ (r3legAdd (r3legScale c x) (r3legScale d y)) =
      c ^ 2 * r3legQ x + 2 * c * d * r3legB x y + d ^ 2 * r3legQ y := by
  simp only [r3legQ, r3legB, r3legAdd, r3legScale]
  ring

private lemma r3leg_scale_left_cancel {c : ℤ} (hc : c ≠ 0) {x y : r3legIntVec}
    (h : r3legScale c x = r3legScale c y) : x = y := by
  have h₁ := congrArg (fun z : r3legIntVec => z.1.1) h
  have h₂ := congrArg (fun z : r3legIntVec => z.1.2) h
  have h₃ := congrArg (fun z : r3legIntVec => z.2) h
  simp only [r3legScale] at h₁ h₂ h₃
  exact Prod.ext (Prod.ext (mul_left_cancel₀ hc h₁) (mul_left_cancel₀ hc h₂))
    (mul_left_cancel₀ hc h₃)

private lemma r3leg_phi_injective (q : Quaternion ℤ)
    (hnorm : Quaternion.normSq q ≠ 0) : Function.Injective (r3legPhi q) := by
  intro x y h
  have h' := congrArg (r3legPhi (star q)) h
  rw [r3leg_phi_phi_star, r3leg_phi_phi_star] at h'
  exact r3leg_scale_left_cancel (pow_ne_zero 2 hnorm) h'

private def r3legVecDvd (c : ℤ) (x : r3legIntVec) : Prop :=
  c ∣ x.1.1 ∧ c ∣ x.1.2 ∧ c ∣ x.2

private def r3legVecDiv (x : r3legIntVec) (c : ℤ) : r3legIntVec :=
  ((x.1.1 / c, x.1.2 / c), x.2 / c)

private lemma r3leg_scale_vecDiv {c : ℤ} {x : r3legIntVec}
    (h : r3legVecDvd c x) : r3legScale c (r3legVecDiv x c) = x := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  apply Prod.ext
  · apply Prod.ext
    · exact Int.mul_ediv_cancel' h₁
    · exact Int.mul_ediv_cancel' h₂
  · exact Int.mul_ediv_cancel' h₃

private noncomputable def r3legImageRep (p n : ℕ) (π : Quaternion ℤ) :
    Finset r3legIntVec := by
  classical
  exact (r3legRep (p ^ 2 * n)).filter
    (fun y => r3legVecDvd ((p : ℤ) ^ 2) (r3legPhi (star π) y))

private lemma r3leg_mem_imageRep {p n : ℕ} {π : Quaternion ℤ} {y : r3legIntVec} :
    y ∈ r3legImageRep p n π ↔
      r3legQ y = (p ^ 2 * n : ℕ) ∧
      r3legVecDvd ((p : ℤ) ^ 2) (r3legPhi (star π) y) := by
  classical
  rw [r3legImageRep, Finset.mem_filter, r3leg_mem_rep]

private lemma r3leg_imageRep_card {p n : ℕ} [Fact (Nat.Prime p)]
    (π : Quaternion ℤ) (hnorm : Quaternion.normSq π = p) :
    (r3legImageRep p n π).card = Nat.threeSquareRepresentationCount n := by
  rw [← r3leg_rep_card]
  symm
  refine Finset.card_bij (fun x _ => r3legPhi π x) ?_ ?_ ?_
  · intro x hx
    rw [r3leg_mem_imageRep]
    have hxq := r3leg_mem_rep.mp hx
    constructor
    · rw [r3leg_q_phi, hnorm, hxq]
      push_cast
      ring
    · rw [r3leg_phi_phi_star, hnorm]
      simp [r3legVecDvd, r3legScale]
  · intro x₁ _ x₂ _ h
    apply r3leg_phi_injective π (by rw [hnorm]; exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    exact h
  · intro y hy
    rw [r3leg_mem_imageRep] at hy
    let x := r3legVecDiv (r3legPhi (star π) y) ((p : ℤ) ^ 2)
    have hscale : r3legScale ((p : ℤ) ^ 2) x = r3legPhi (star π) y := by
      exact r3leg_scale_vecDiv hy.2
    have happly := congrArg (r3legPhi π) hscale
    rw [r3leg_phi_scale, r3leg_phi_star_phi, hnorm] at happly
    have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    have hphi : r3legPhi π x = y := r3leg_scale_left_cancel hp2 happly
    have hxq : r3legQ x = (n : ℤ) := by
      have hq := r3leg_q_phi π x
      rw [hphi, hnorm, hy.1] at hq
      push_cast at hq
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
      nlinarith
    refine ⟨x, r3leg_mem_rep.mpr hxq, hphi⟩

private abbrev r3legIso (p : ℕ) :=
  {w : r3legModVec p // w ≠ 0 ∧ r3legQ w = 0}

private noncomputable def r3legPi {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) : Quaternion ℤ :=
  Classical.choose (r3leg_aligned_norm_prime hp3 w w.property.1 w.property.2)

private lemma r3legPi_norm {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) : Quaternion.normSq (r3legPi hp3 w) = p :=
  (Classical.choose_spec (r3leg_aligned_norm_prime hp3 w w.property.1 w.property.2)).1

private lemma r3legPi_aligned {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) : r3legAligned p (r3legPi hp3 w) w :=
  (Classical.choose_spec (r3leg_aligned_norm_prime hp3 w w.property.1 w.property.2)).2

private def r3legInc {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p)
    (w : r3legIso p) (y : r3legIntVec) : Prop :=
  r3legVecDvd ((p : ℤ) ^ 2) (r3legPhi (star (r3legPi hp3 w)) y)

private lemma r3leg_cast_b (p : ℕ) (x y : r3legIntVec) :
    ((r3legB x y : ℤ) : ZMod p) = r3legB (r3legRed p x) (r3legRed p y) := by
  simp [r3legB, r3legRed]

private lemma r3leg_psi_red_eq_zero_iff {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (x : r3legIntVec) :
    r3legRed p (r3legPhi (star (r3legPi hp3 w)) x) = 0 ↔
      r3legB (r3legRed p x) w = 0 := by
  let π := r3legPi hp3 w
  have hnorm : Quaternion.normSq π = p := r3legPi_norm hp3 w
  have halign : r3legAligned p π w := r3legPi_aligned hp3 w
  constructor
  · intro hpsi
    obtain ⟨e, _, _, he⟩ := r3leg_nonzero_column hp3 π hnorm
    obtain ⟨μ, hμ⟩ := halign e
    have hμne : μ ≠ 0 := by
      intro h
      apply he
      rw [hμ, h]
      simp
    have hzero : ((r3legB (r3legPhi (star π) x) e : ℤ) : ZMod p) = 0 := by
      rw [r3leg_cast_b, hpsi]
      simp [r3legB]
    rw [r3leg_phi_adjoint] at hzero
    rw [r3leg_cast_b, hμ] at hzero
    have hmul : μ * r3legB (r3legRed p x) w = 0 := by
      dsimp [r3legB] at hzero ⊢
      linear_combination hzero
    exact (mul_eq_zero.mp hmul).resolve_left hμne
  · intro hb
    apply Prod.ext
    · apply Prod.ext
      · obtain ⟨μ, hμ⟩ := halign r3legE₁
        change ((r3legPhi (star π) x).1.1 : ZMod p) = 0
        calc
          ((r3legPhi (star π) x).1.1 : ZMod p) =
              ((r3legB (r3legPhi (star π) x) r3legE₁ : ℤ) : ZMod p) := by
            simp [r3legB, r3legE₁]
          _ = ((r3legB x (r3legPhi π r3legE₁) : ℤ) : ZMod p) := by
            rw [r3leg_phi_adjoint]
          _ = r3legB (r3legRed p x) (r3legRed p (r3legPhi π r3legE₁)) :=
            r3leg_cast_b p _ _
          _ = 0 := by
            rw [hμ]
            dsimp [r3legB] at hb ⊢
            linear_combination μ * hb
      · obtain ⟨μ, hμ⟩ := halign r3legE₂
        change ((r3legPhi (star π) x).1.2 : ZMod p) = 0
        calc
          ((r3legPhi (star π) x).1.2 : ZMod p) =
              ((r3legB (r3legPhi (star π) x) r3legE₂ : ℤ) : ZMod p) := by
            simp [r3legB, r3legE₂]
          _ = ((r3legB x (r3legPhi π r3legE₂) : ℤ) : ZMod p) := by
            rw [r3leg_phi_adjoint]
          _ = r3legB (r3legRed p x) (r3legRed p (r3legPhi π r3legE₂)) :=
            r3leg_cast_b p _ _
          _ = 0 := by
            rw [hμ]
            dsimp [r3legB] at hb ⊢
            linear_combination μ * hb
    · obtain ⟨μ, hμ⟩ := halign r3legE₃
      change ((r3legPhi (star π) x).2 : ZMod p) = 0
      calc
        ((r3legPhi (star π) x).2 : ZMod p) =
            ((r3legB (r3legPhi (star π) x) r3legE₃ : ℤ) : ZMod p) := by
          simp [r3legB, r3legE₃]
        _ = ((r3legB x (r3legPhi π r3legE₃) : ℤ) : ZMod p) := by
          rw [r3leg_phi_adjoint]
        _ = r3legB (r3legRed p x) (r3legRed p (r3legPhi π r3legE₃)) :=
          r3leg_cast_b p _ _
        _ = 0 := by
          rw [hμ]
          dsimp [r3legB] at hb ⊢
          linear_combination μ * hb

private lemma r3leg_vecDvd_iff_red_eq_zero (p : ℕ) (x : r3legIntVec) :
    r3legVecDvd (p : ℤ) x ↔ r3legRed p x = 0 := by
  constructor
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := h
    apply Prod.ext
    · apply Prod.ext
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h₁
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h₂
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h₃
  · intro h
    have h₁ := congrArg (fun z : r3legModVec p => z.1.1) h
    have h₂ := congrArg (fun z : r3legModVec p => z.1.2) h
    have h₃ := congrArg (fun z : r3legModVec p => z.2) h
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h₁,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h₂,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h₃⟩

private lemma r3leg_sq_dvd_mul_iff {p : ℕ} (hp : 0 < p) (a : ℤ) :
    (p : ℤ) ^ 2 ∣ (p : ℤ) * a ↔ (p : ℤ) ∣ a := by
  constructor
  · intro h
    apply Int.dvd_of_mul_dvd_mul_left (a := (p : ℤ)) (m := (p : ℤ))
      (n := a) (by exact_mod_cast (show p ≠ 0 by omega))
    simpa [pow_two] using h
  · rintro ⟨k, rfl⟩
    refine ⟨k, by ring⟩

private lemma r3leg_inc_scale_iff {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (x : r3legIntVec) :
    r3legInc hp3 w (r3legScale p x) ↔ r3legB (r3legRed p x) w = 0 := by
  rw [r3legInc, r3leg_phi_scale]
  have hp : 0 < p := by omega
  have hdiv :
      r3legVecDvd ((p : ℤ) ^ 2)
          (r3legScale p (r3legPhi (star (r3legPi hp3 w)) x)) ↔
        r3legVecDvd (p : ℤ) (r3legPhi (star (r3legPi hp3 w)) x) := by
    simp only [r3legVecDvd, r3legScale]
    exact and_congr (r3leg_sq_dvd_mul_iff hp _)
      (and_congr (r3leg_sq_dvd_mul_iff hp _) (r3leg_sq_dvd_mul_iff hp _))
  rw [hdiv, r3leg_vecDvd_iff_red_eq_zero,
    r3leg_psi_red_eq_zero_iff hp3 w x]

private lemma r3leg_inc_primitive_forward {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (y : r3legIntVec)
    (hyne : r3legRed p y ≠ 0) (hinc : r3legInc hp3 w y) :
    ∃ κ : ZMod p, κ ≠ 0 ∧ r3legRed p y = κ • (w : r3legModVec p) := by
  let π := r3legPi hp3 w
  have hnorm : Quaternion.normSq π = p := r3legPi_norm hp3 w
  have halign : r3legAligned p π w := r3legPi_aligned hp3 w
  let x := r3legVecDiv (r3legPhi (star π) y) ((p : ℤ) ^ 2)
  have hscale : r3legScale ((p : ℤ) ^ 2) x = r3legPhi (star π) y := by
    exact r3leg_scale_vecDiv hinc
  have happly := congrArg (r3legPhi π) hscale
  rw [r3leg_phi_scale, r3leg_phi_star_phi, hnorm] at happly
  have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  have hphi : r3legPhi π x = y := r3leg_scale_left_cancel hp2 happly
  obtain ⟨κ, hκ⟩ := halign x
  refine ⟨κ, ?_, ?_⟩
  · intro hκ0
    apply hyne
    rw [← hphi, hκ, hκ0]
    simp
  · rw [← hphi]
    exact hκ

private lemma r3leg_vecDvd_add_scale_sq (p k : ℤ) (e v : r3legIntVec)
    (hv : r3legVecDvd p v) :
    r3legVecDvd (p ^ 2)
      (r3legAdd (r3legScale k (r3legScale (p ^ 2) e)) (r3legScale p v)) := by
  obtain ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩, v₃, hv₃⟩ := hv
  constructor
  · refine ⟨k * e.1.1 + v₁, ?_⟩
    simp only [r3legAdd, r3legScale]
    rw [hv₁]
    ring
  constructor
  · refine ⟨k * e.1.2 + v₂, ?_⟩
    simp only [r3legAdd, r3legScale]
    rw [hv₂]
    ring
  · refine ⟨k * e.2 + v₃, ?_⟩
    simp only [r3legAdd, r3legScale]
    rw [hv₃]
    ring

private lemma r3leg_inc_primitive_backward {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (y : r3legIntVec)
    (hyq : r3legQ y = (p ^ 2 * n : ℕ)) {κ : ZMod p} (hκne : κ ≠ 0)
    (hyred : r3legRed p y = κ • (w : r3legModVec p)) : r3legInc hp3 w y := by
  let π := r3legPi hp3 w
  have hnorm : Quaternion.normSq π = p := r3legPi_norm hp3 w
  have halign : r3legAligned p π w := r3legPi_aligned hp3 w
  obtain ⟨e, _, heq, hecol⟩ := r3leg_nonzero_column hp3 π hnorm
  let a := r3legPhi π e
  obtain ⟨μ, hμ⟩ := halign e
  have hμne : μ ≠ 0 := by
    intro h
    apply hecol
    rw [hμ, h]
    simp
  let k : ℤ := (κ * μ⁻¹).valMinAbs
  have hkcast : (k : ZMod p) = κ * μ⁻¹ := ZMod.coe_valMinAbs _
  let d := r3legSub y (r3legScale k a)
  have hdred : r3legRed p d = 0 := by
    dsimp [d]
    rw [r3leg_red_sub, r3leg_red_scale, hyred]
    change r3legSub (κ • (w : r3legModVec p))
      ((k : ZMod p) • r3legRed p a) = 0
    rw [show r3legRed p a = μ • (w : r3legModVec p) by exact hμ, hkcast]
    apply Prod.ext
    · apply Prod.ext <;> simp [r3legSub, smul_smul, hμne]
    · simp [r3legSub, smul_smul, hμne]
  have hddiv : r3legVecDvd (p : ℤ) d :=
    (r3leg_vecDvd_iff_red_eq_zero p d).mpr hdred
  let z := r3legVecDiv d p
  have hzscale : r3legScale p z = d := r3leg_scale_vecDiv hddiv
  have hydecomp : y = r3legAdd (r3legScale k a) (r3legScale p z) := by
    apply Prod.ext
    · apply Prod.ext
      · have h := congrArg (fun v : r3legIntVec => v.1.1) hzscale
        dsimp [d, r3legScale, r3legSub, r3legAdd] at h ⊢
        linear_combination -h
      · have h := congrArg (fun v : r3legIntVec => v.1.2) hzscale
        dsimp [d, r3legScale, r3legSub, r3legAdd] at h ⊢
        linear_combination -h
    · have h := congrArg (fun v : r3legIntVec => v.2) hzscale
      dsimp [d, r3legScale, r3legSub, r3legAdd] at h ⊢
      linear_combination -h
  have haq : r3legQ a = (p : ℤ) ^ 2 := by
    dsimp [a]
    rw [r3leg_q_phi, hnorm, heq]
    ring
  have hq := congrArg r3legQ hydecomp
  rw [r3leg_q_add_scaled, hyq, haq] at hq
  push_cast at hq
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hcancel :
      (p : ℤ) * (2 * k * r3legB a z) =
        (p : ℤ) * ((p : ℤ) * ((n : ℤ) - k ^ 2 - r3legQ z)) := by
    linear_combination -hq
  have hmiddle : 2 * k * r3legB a z =
      (p : ℤ) * ((n : ℤ) - k ^ 2 - r3legQ z) :=
    mul_left_cancel₀ hpne hcancel
  have hbdvd : (p : ℤ) ∣ 2 * k * r3legB a z :=
    ⟨(n : ℤ) - k ^ 2 - r3legQ z, hmiddle⟩
  have hprod : (((2 * k * r3legB a z : ℤ) : ZMod p)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hbdvd
  push_cast at hprod
  have hkne : (k : ZMod p) ≠ 0 := by
    rw [hkcast]
    exact mul_ne_zero hκne (inv_ne_zero hμne)
  have h2kne : (2 : ZMod p) * (k : ZMod p) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast r3leg_two_ne_zero hp3) hkne
  have hbcast : ((r3legB a z : ℤ) : ZMod p) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left h2kne
  rw [r3leg_cast_b, hμ] at hbcast
  have hmub : μ * r3legB (r3legRed p z) w = 0 := by
    dsimp [r3legB] at hbcast ⊢
    linear_combination hbcast
  have hbzw : r3legB (r3legRed p z) w = 0 :=
    (mul_eq_zero.mp hmub).resolve_left hμne
  have hpsiz : r3legVecDvd (p : ℤ) (r3legPhi (star π) z) :=
    (r3leg_vecDvd_iff_red_eq_zero p _).mpr
      ((r3leg_psi_red_eq_zero_iff hp3 w z).mpr hbzw)
  have hpsia : r3legPhi (star π) a = r3legScale ((p : ℤ) ^ 2) e := by
    dsimp [a]
    rw [r3leg_phi_phi_star, hnorm]
  have hpsiy := congrArg (r3legPhi (star π)) hydecomp
  rw [r3leg_phi_add, r3leg_phi_scale, r3leg_phi_scale, hpsia] at hpsiy
  change r3legVecDvd ((p : ℤ) ^ 2) (r3legPhi (star π) y)
  rw [hpsiy]
  exact r3leg_vecDvd_add_scale_sq p k e (r3legPhi (star π) z) hpsiz

private lemma r3leg_inc_primitive_iff {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (y : r3legIntVec)
    (hyq : r3legQ y = (p ^ 2 * n : ℕ)) (hyne : r3legRed p y ≠ 0) :
    r3legInc hp3 w y ↔
      ∃ κ : ZMod p, κ ≠ 0 ∧ r3legRed p y = κ • (w : r3legModVec p) := by
  constructor
  · exact r3leg_inc_primitive_forward hp3 w y hyne
  · rintro ⟨κ, hκ, hy⟩
    exact r3leg_inc_primitive_backward hp3 w y hyq hκ hy

private abbrev r3legSqrtPairs (p : ℕ) (Δ : ZMod p) :=
  {z : ZMod p × ZMod p // z.1 ^ 2 = Δ * z.2 ^ 2}

private abbrev r3legSqrts (p : ℕ) (Δ : ZMod p) :=
  {z : ZMod p // z ^ 2 = Δ}

private noncomputable def r3leg_sqrtPairEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (Δ : ZMod p) :
    r3legSqrtPairs p Δ ≃ Option ((ZMod p)ˣ × r3legSqrts p Δ) where
  toFun z := if ht : z.1.2 = 0 then none else
    some (Units.mk0 z.1.2 ht, ⟨z.1.1 / z.1.2, by
      field_simp [ht]
      simpa [mul_comm] using z.2⟩)
  invFun z := match z with
    | none => ⟨(0, 0), by simp⟩
    | some z => ⟨(z.2 * z.1, z.1), by
        rw [mul_pow, z.2.property]⟩
  left_inv z := by
    dsimp
    split_ifs with ht
    · apply Subtype.ext
      apply Prod.ext
      · have hz : z.1.1 = 0 := by
          apply sq_eq_zero_iff.mp
          simpa [ht] using z.2
        exact hz.symm
      · exact ht.symm
    · apply Subtype.ext
      apply Prod.ext
      · simp [ht]
      · rfl
  right_inv z := by
    cases z with
    | none => simp
    | some z =>
        have ht : (z.1 : ZMod p) ≠ 0 := Units.ne_zero z.1
        simp [ht]

private lemma r3leg_sqrtPairs_card {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (Δ : ZMod p) :
    (Fintype.card (r3legSqrtPairs p Δ) : ℤ) =
      1 + ((p : ℤ) - 1) * (1 + quadraticChar (ZMod p) Δ) := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hsqrt : (Fintype.card (r3legSqrts p Δ) : ℤ) =
      quadraticChar (ZMod p) Δ + 1 := by
    let s := {x : ZMod p | x ^ 2 = Δ}.toFinset
    let e : r3legSqrts p Δ ≃ ↥s := Equiv.subtypeEquiv (Equiv.refl _) (by
      intro x
      simp [s])
    have hc := Fintype.card_congr e
    rw [Fintype.card_coe] at hc
    rw [hc]
    simpa [s] using quadraticChar_card_sqrts hchar Δ
  have hu : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [Fintype.card_units, ZMod.card]
  have hcard := Fintype.card_congr (r3leg_sqrtPairEquiv Δ)
  rw [Fintype.card_option, Fintype.card_prod, hu] at hcard
  have hcard' : (Fintype.card (r3legSqrtPairs p Δ) : ℤ) =
      ((p - 1 : ℕ) : ℤ) * Fintype.card (r3legSqrts p Δ) + 1 := by
    exact_mod_cast hcard
  have hsub : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  rw [hsub, hsqrt] at hcard'
  linear_combination hcard'

private abbrev r3legBinaryZeros (p : ℕ) (a b d : ZMod p) :=
  {z : ZMod p × ZMod p // a * z.1 ^ 2 + 2 * b * z.1 * z.2 + d * z.2 ^ 2 = 0}

private noncomputable def r3leg_binaryLinearEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (a b : ZMod p) (ha : a ≠ 0) : ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun z := (a * z.1 + b * z.2, z.2)
  invFun z := ((z.1 - b * z.2) / a, z.2)
  left_inv z := by
    apply Prod.ext
    · dsimp
      field_simp [ha]
      ring
    · rfl
  right_inv z := by
    apply Prod.ext
    · dsimp
      field_simp [ha]
      ring
    · rfl

private noncomputable def r3leg_binarySqrtEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (a b d : ZMod p) (ha : a ≠ 0) :
    r3legBinaryZeros p a b d ≃ r3legSqrtPairs p (b ^ 2 - a * d) :=
  Equiv.subtypeEquiv (r3leg_binaryLinearEquiv a b ha) (fun z => by
    change a * z.1 ^ 2 + 2 * b * z.1 * z.2 + d * z.2 ^ 2 = 0 ↔
      (a * z.1 + b * z.2) ^ 2 = (b ^ 2 - a * d) * z.2 ^ 2
    constructor
    · intro h
      linear_combination a * h
    · intro h
      have h' : a * (a * z.1 ^ 2 + 2 * b * z.1 * z.2 + d * z.2 ^ 2) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp h').resolve_left ha)

private lemma r3leg_binary_card_of_left_ne_zero {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (a b d : ZMod p) (ha : a ≠ 0) :
    (Fintype.card (r3legBinaryZeros p a b d) : ℤ) =
      1 + ((p : ℤ) - 1) *
        (1 + quadraticChar (ZMod p) (b ^ 2 - a * d)) := by
  rw [Fintype.card_congr (r3leg_binarySqrtEquiv a b d ha)]
  exact r3leg_sqrtPairs_card hp3 _

private def r3leg_binarySwapEquiv {p : ℕ} (a b d : ZMod p) :
    r3legBinaryZeros p a b d ≃ r3legBinaryZeros p d b a :=
  Equiv.subtypeEquiv (Equiv.prodComm _ _) (fun z => by
    change a * z.1 ^ 2 + 2 * b * z.1 * z.2 + d * z.2 ^ 2 = 0 ↔
      d * z.2 ^ 2 + 2 * b * z.2 * z.1 + a * z.1 ^ 2 = 0
    constructor <;> intro h <;> linear_combination h)

private abbrev r3legZeroProd (p : ℕ) :=
  {z : ZMod p × ZMod p // z.1 * z.2 = 0}

private noncomputable def r3leg_zeroProdEquiv {p : ℕ} [Fact (Nat.Prime p)] :
    r3legZeroProd p ≃ (ZMod p ⊕ (ZMod p)ˣ) where
  toFun z := if ht : z.1.2 = 0 then Sum.inl z.1.1 else Sum.inr (Units.mk0 z.1.2 ht)
  invFun z := match z with
    | Sum.inl s => ⟨(s, 0), by simp⟩
    | Sum.inr t => ⟨(0, t), by simp⟩
  left_inv z := by
    dsimp
    split_ifs with ht
    · apply Subtype.ext
      exact Prod.ext rfl ht.symm
    · apply Subtype.ext
      apply Prod.ext
      · have hs : z.1.1 = 0 :=
          (mul_eq_zero.mp z.2).resolve_right ht
        exact hs.symm
      · rfl
  right_inv z := by
    cases z with
    | inl s => simp
    | inr t =>
        have ht : (t : ZMod p) ≠ 0 := Units.ne_zero t
        simp [ht]

private lemma r3leg_zeroProd_card {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Fintype.card (r3legZeroProd p) : ℤ) = 2 * (p : ℤ) - 1 := by
  have hcard := Fintype.card_congr (r3leg_zeroProdEquiv (p := p))
  rw [Fintype.card_sum, ZMod.card, Fintype.card_units, ZMod.card] at hcard
  have hcard' : (Fintype.card (r3legZeroProd p) : ℤ) =
      (p : ℤ) + ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hcard
  have hsub : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  rw [hsub] at hcard'
  linear_combination hcard'

private lemma r3leg_binary_card {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (a b d : ZMod p) (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0) :
    (Fintype.card (r3legBinaryZeros p a b d) : ℤ) =
      1 + ((p : ℤ) - 1) *
        (1 + quadraticChar (ZMod p) (b ^ 2 - a * d)) := by
  by_cases ha : a = 0
  · subst a
    by_cases hd : d = 0
    · subst d
      have hb : b ≠ 0 := by tauto
      have h2b : (2 : ZMod p) * b ≠ 0 :=
        mul_ne_zero (by exact_mod_cast r3leg_two_ne_zero hp3) hb
      let e : r3legBinaryZeros p 0 b 0 ≃ r3legZeroProd p :=
        Equiv.subtypeEquiv (Equiv.refl _) (fun z => by
          change 0 * z.1 ^ 2 + 2 * b * z.1 * z.2 + 0 * z.2 ^ 2 = 0 ↔
            z.1 * z.2 = 0
          constructor
          · intro h
            have h' : ((2 : ZMod p) * b) * (z.1 * z.2) = 0 := by
              linear_combination h
            exact (mul_eq_zero.mp h').resolve_left h2b
          · intro h
            linear_combination ((2 : ZMod p) * b) * h)
      rw [Fintype.card_congr e, r3leg_zeroProd_card hp3]
      simp only [zero_mul, sub_zero]
      rw [quadraticChar_sq_one' hb]
      ring
    · have hswap := r3leg_binary_card_of_left_ne_zero hp3 d b 0 hd
      rw [Fintype.card_congr (r3leg_binarySwapEquiv 0 b d)]
      simpa [mul_comm] using hswap
  · exact r3leg_binary_card_of_left_ne_zero hp3 a b d ha

private abbrev r3legPlane (p : ℕ) (x : r3legModVec p) :=
  {w : r3legModVec p // r3legB w x = 0}

private abbrev r3legOrthCone (p : ℕ) (x : r3legModVec p) :=
  {w : r3legModVec p // r3legQ w = 0 ∧ r3legB w x = 0}

private noncomputable def r3leg_planeEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (x : r3legModVec p) (hx : x.2 ≠ 0) :
    ZMod p × ZMod p ≃ r3legPlane p x where
  toFun z := ⟨((z.1, z.2), -(x.1.1 * z.1 + x.1.2 * z.2) / x.2), by
    dsimp [r3legB]
    field_simp [hx]
    ring⟩
  invFun w := (w.1.1.1, w.1.1.2)
  left_inv z := rfl
  right_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply (div_eq_iff hx).mpr
      have hw := w.2
      dsimp [r3legB] at hw
      linear_combination -hw

private def r3leg_planeOrthEquiv {p : ℕ} (x : r3legModVec p) :
    {w : r3legPlane p x // r3legQ (w : r3legModVec p) = 0} ≃
      r3legOrthCone p x where
  toFun w := ⟨w.1, w.2, w.1.2⟩
  invFun w := ⟨⟨w.1, w.2.2⟩, w.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def r3leg_binaryOrthEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (x : r3legModVec p) (hx : x.2 ≠ 0) :
    r3legBinaryZeros p (x.1.1 ^ 2 + x.2 ^ 2) (x.1.1 * x.1.2)
        (x.1.2 ^ 2 + x.2 ^ 2) ≃ r3legOrthCone p x := by
  let e : r3legBinaryZeros p (x.1.1 ^ 2 + x.2 ^ 2) (x.1.1 * x.1.2)
      (x.1.2 ^ 2 + x.2 ^ 2) ≃
      {w : r3legPlane p x // r3legQ (w : r3legModVec p) = 0} :=
    Equiv.subtypeEquiv (r3leg_planeEquiv x hx) (fun z => by
      let w : r3legModVec p :=
        ((z.1, z.2), -(x.1.1 * z.1 + x.1.2 * z.2) / x.2)
      have hid : x.2 ^ 2 * r3legQ w =
          (x.1.1 ^ 2 + x.2 ^ 2) * z.1 ^ 2 +
            2 * (x.1.1 * x.1.2) * z.1 * z.2 +
            (x.1.2 ^ 2 + x.2 ^ 2) * z.2 ^ 2 := by
        dsimp [w, r3legQ]
        field_simp [hx]
        ring
      change (x.1.1 ^ 2 + x.2 ^ 2) * z.1 ^ 2 +
          2 * (x.1.1 * x.1.2) * z.1 * z.2 +
          (x.1.2 ^ 2 + x.2 ^ 2) * z.2 ^ 2 = 0 ↔ r3legQ w = 0
      constructor
      · intro h
        have h' : x.2 ^ 2 * r3legQ w = 0 := by rw [hid, h]
        exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 2 hx)
      · intro h
        rw [← hid, h, mul_zero])
  exact e.trans (r3leg_planeOrthEquiv x)

private lemma r3leg_orthCone_card_of_third_ne_zero {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legModVec p) (hx : x.2 ≠ 0) :
    (Fintype.card (r3legOrthCone p x) : ℤ) =
      (p : ℤ) + ((p : ℤ) - 1) * quadraticChar (ZMod p) (-r3legQ x) := by
  let a := x.1.1 ^ 2 + x.2 ^ 2
  let b := x.1.1 * x.1.2
  let d := x.1.2 ^ 2 + x.2 ^ 2
  have hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0 := by
    by_cases h₁ : x.1.1 = 0
    · left
      simp [a, h₁, hx]
    · by_cases h₂ : x.1.2 = 0
      · right; right
        simp [d, h₂, hx]
      · right; left
        exact mul_ne_zero h₁ h₂
  have hcard := r3leg_binary_card hp3 a b d hcoeff
  rw [Fintype.card_congr (r3leg_binaryOrthEquiv x hx)] at hcard
  have hdisc : b ^ 2 - a * d = x.2 ^ 2 * (-r3legQ x) := by
    dsimp [a, b, d, r3legQ]
    ring
  have hchar : quadraticChar (ZMod p) (b ^ 2 - a * d) =
      quadraticChar (ZMod p) (-r3legQ x) := by
    rw [hdisc, map_mul, quadraticChar_sq_one' hx, one_mul]
  rw [hchar] at hcard
  linear_combination hcard

private def r3legRot {R : Type*} : ((R × R) × R) ≃ ((R × R) × R) where
  toFun x := ((x.1.2, x.2), x.1.1)
  invFun x := ((x.2, x.1.1), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private lemma r3leg_q_rot {R : Type*} [CommSemiring R] (x : (R × R) × R) :
    r3legQ (r3legRot x) = r3legQ x := by
  change x.1.2 ^ 2 + x.2 ^ 2 + x.1.1 ^ 2 =
    x.1.1 ^ 2 + x.1.2 ^ 2 + x.2 ^ 2
  ring

private lemma r3leg_b_rot {R : Type*} [CommSemiring R] (x y : (R × R) × R) :
    r3legB (r3legRot x) (r3legRot y) = r3legB x y := by
  change x.1.2 * y.1.2 + x.2 * y.2 + x.1.1 * y.1.1 =
    x.1.1 * y.1.1 + x.1.2 * y.1.2 + x.2 * y.2
  ring

private def r3leg_rotOrthEquiv {p : ℕ} (x : r3legModVec p) :
    r3legOrthCone p x ≃ r3legOrthCone p (r3legRot x) :=
  Equiv.subtypeEquiv r3legRot (fun w => by
    constructor
    · rintro ⟨hq, hb⟩
      exact ⟨by rw [r3leg_q_rot, hq], by rw [r3leg_b_rot, hb]⟩
    · rintro ⟨hq, hb⟩
      exact ⟨by rw [r3leg_q_rot] at hq; exact hq,
        by rw [r3leg_b_rot] at hb; exact hb⟩)

private lemma r3leg_orthCone_card {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legModVec p) (hx : x ≠ 0) :
    (Fintype.card (r3legOrthCone p x) : ℤ) =
      (p : ℤ) + ((p : ℤ) - 1) * quadraticChar (ZMod p) (-r3legQ x) := by
  by_cases h₃ : x.2 = 0
  · by_cases h₁ : x.1.1 = 0
    · have h₂ : x.1.2 ≠ 0 := by
        intro h₂
        apply hx
        apply Prod.ext
        · exact Prod.ext h₁ h₂
        · exact h₃
      let x' := r3legRot (r3legRot x)
      have hx' : x'.2 ≠ 0 := by simpa [x', r3legRot] using h₂
      have hcard := r3leg_orthCone_card_of_third_ne_zero hp3 x' hx'
      have hc₁ := Fintype.card_congr (r3leg_rotOrthEquiv x)
      have hc₂ := Fintype.card_congr (r3leg_rotOrthEquiv (r3legRot x))
      have hq : r3legQ x' = r3legQ x := by
        dsimp [x']
        rw [r3leg_q_rot, r3leg_q_rot]
      rw [hq] at hcard
      have hc : Fintype.card (r3legOrthCone p x) =
          Fintype.card (r3legOrthCone p x') := hc₁.trans hc₂
      have hc' : (Fintype.card (r3legOrthCone p x) : ℤ) =
          Fintype.card (r3legOrthCone p x') := by exact_mod_cast hc
      rw [hc']
      exact hcard
    · let x' := r3legRot x
      have hx' : x'.2 ≠ 0 := by simpa [x', r3legRot] using h₁
      have hcard := r3leg_orthCone_card_of_third_ne_zero hp3 x' hx'
      have hc := Fintype.card_congr (r3leg_rotOrthEquiv x)
      have hq : r3legQ x' = r3legQ x := by
        dsimp [x']
        rw [r3leg_q_rot]
      rw [hq] at hcard
      have hc' : (Fintype.card (r3legOrthCone p x) : ℤ) =
          Fintype.card (r3legOrthCone p x') := by exact_mod_cast hc
      rw [hc']
      exact hcard
  · exact r3leg_orthCone_card_of_third_ne_zero hp3 x h₃

private abbrev r3legTwoSq (p : ℕ) (c : ZMod p) :=
  {z : ZMod p × ZMod p // z.1 ^ 2 + z.2 ^ 2 = c}

private noncomputable def r3leg_twoSqLinearEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (α β c : ZMod p) (hc : c ≠ 0) (hab : α ^ 2 + β ^ 2 = c) :
    ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun z := (α * z.1 - β * z.2, β * z.1 + α * z.2)
  invFun z := ((α * z.1 + β * z.2) / c, (-β * z.1 + α * z.2) / c)
  left_inv z := by
    apply Prod.ext
    · dsimp
      field_simp [hc]
      linear_combination z.1 * hab
    · dsimp
      field_simp [hc]
      linear_combination z.2 * hab
  right_inv z := by
    apply Prod.ext
    · dsimp
      field_simp [hc]
      linear_combination z.1 * hab
    · dsimp
      field_simp [hc]
      linear_combination z.2 * hab

private noncomputable def r3leg_twoSqEquivOne {p : ℕ} [Fact (Nat.Prime p)]
    (c : ZMod p) (hc : c ≠ 0) : r3legTwoSq p 1 ≃ r3legTwoSq p c := by
  let h := ZMod.sq_add_sq p c
  let α := Classical.choose h
  let β := Classical.choose (Classical.choose_spec h)
  have hab : α ^ 2 + β ^ 2 = c := Classical.choose_spec (Classical.choose_spec h)
  exact Equiv.subtypeEquiv (r3leg_twoSqLinearEquiv α β c hc hab) (fun z => by
    change z.1 ^ 2 + z.2 ^ 2 = 1 ↔
      (α * z.1 - β * z.2) ^ 2 + (β * z.1 + α * z.2) ^ 2 = c
    constructor
    · intro hz
      calc
        (α * z.1 - β * z.2) ^ 2 + (β * z.1 + α * z.2) ^ 2 =
            (α ^ 2 + β ^ 2) * (z.1 ^ 2 + z.2 ^ 2) := by ring
        _ = c * (z.1 ^ 2 + z.2 ^ 2) := by rw [hab]
        _ = c := by rw [hz, mul_one]
    · intro hz
      have hmul : c * (z.1 ^ 2 + z.2 ^ 2) = c * 1 := by
        calc
          c * (z.1 ^ 2 + z.2 ^ 2) =
              (α * z.1 - β * z.2) ^ 2 + (β * z.1 + α * z.2) ^ 2 := by
            rw [← hab]
            ring
          _ = c := hz
          _ = c * 1 := by ring
      exact mul_left_cancel₀ hc hmul)

private lemma r3leg_twoSq_card_eq_one {p : ℕ} [Fact (Nat.Prime p)]
    (c : ZMod p) (hc : c ≠ 0) :
    Fintype.card (r3legTwoSq p c) = Fintype.card (r3legTwoSq p 1) := by
  symm
  exact Fintype.card_congr (r3leg_twoSqEquivOne c hc)

private noncomputable def r3leg_twoSqSigmaEquiv {p : ℕ} [Fact (Nat.Prime p)] :
    (Σ c : ZMod p, r3legTwoSq p c) ≃ ZMod p × ZMod p where
  toFun z := z.2
  invFun z := ⟨z.1 ^ 2 + z.2 ^ 2, ⟨z, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨c, ⟨z, hz⟩⟩
    subst c
    rfl
  right_inv _ := rfl

private abbrev r3legCone (p : ℕ) :=
  {w : r3legModVec p // r3legQ w = 0}

private noncomputable def r3leg_coneSigmaEquiv {p : ℕ} [Fact (Nat.Prime p)] :
    r3legCone p ≃ (Σ t : ZMod p, r3legTwoSq p (-t ^ 2)) where
  toFun w := ⟨w.1.2, ⟨w.1.1, by
    have hw := w.2
    dsimp [r3legQ] at hw
    linear_combination hw⟩⟩
  invFun z := ⟨(z.2.1, z.1), by
    dsimp [r3legQ]
    linear_combination z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma r3leg_sum_twoSq_comp {p : ℕ} [Fact (Nat.Prime p)]
    (g : ZMod p → ZMod p) (hg : ∀ t, g t = 0 ↔ t = 0) :
    (∑ t : ZMod p, Fintype.card (r3legTwoSq p (g t))) =
      Fintype.card (r3legTwoSq p 0) +
        (p - 1) * Fintype.card (r3legTwoSq p 1) := by
  classical
  let f := fun t : ZMod p => Fintype.card (r3legTwoSq p (g t))
  have hzero : g 0 = 0 := (hg 0).mpr rfl
  have herase :
      (∑ t ∈ (Finset.univ.erase (0 : ZMod p)), f t) =
        (p - 1) * Fintype.card (r3legTwoSq p 1) := by
    calc
      (∑ t ∈ (Finset.univ.erase (0 : ZMod p)), f t) =
          ∑ _t ∈ (Finset.univ.erase (0 : ZMod p)),
            Fintype.card (r3legTwoSq p 1) := by
        apply Finset.sum_congr rfl
        intro t ht
        apply r3leg_twoSq_card_eq_one
        intro hgt
        have ht0 := (hg t).mp hgt
        exact (Finset.mem_erase.mp ht).1 ht0
      _ = (Finset.univ.erase (0 : ZMod p)).card *
          Fintype.card (r3legTwoSq p 1) := by simp
      _ = (p - 1) * Fintype.card (r3legTwoSq p 1) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : ZMod p))
  rw [herase] at hsplit
  dsimp [f] at hsplit ⊢
  rw [hzero] at hsplit
  omega

private lemma r3leg_cone_card {p : ℕ} [Fact (Nat.Prime p)] :
    Fintype.card (r3legCone p) = p ^ 2 := by
  have hcone := Fintype.card_congr (r3leg_coneSigmaEquiv (p := p))
  rw [Fintype.card_sigma,
    r3leg_sum_twoSq_comp (fun t : ZMod p => -t ^ 2) (by
      intro t
      constructor
      · intro h
        have : t ^ 2 = 0 := by simpa using congrArg Neg.neg h
        exact sq_eq_zero_iff.mp this
      · rintro rfl
        simp)] at hcone
  have hpairs := Fintype.card_congr (r3leg_twoSqSigmaEquiv (p := p))
  rw [Fintype.card_sigma,
    r3leg_sum_twoSq_comp (fun t : ZMod p => t) (fun t => Iff.rfl),
    Fintype.card_prod, ZMod.card] at hpairs
  rw [pow_two]
  omega

private noncomputable def r3leg_isoConeEquiv {p : ℕ} [Fact (Nat.Prime p)] :
    r3legIso p ≃ {w : r3legCone p // (w.1 : r3legModVec p) ≠ 0} where
  toFun w := ⟨⟨w, w.2.2⟩, w.2.1⟩
  invFun w := ⟨w.1, w.2, w.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma r3leg_iso_card {p : ℕ} [Fact (Nat.Prime p)] :
    Fintype.card (r3legIso p) = p ^ 2 - 1 := by
  rw [Fintype.card_congr (r3leg_isoConeEquiv (p := p)),
    Fintype.card_subtype_compl, r3leg_cone_card]
  have hzero :
      Fintype.card {w : r3legCone p // (w.1 : r3legModVec p) = 0} = 1 := by
    let z : r3legCone p := ⟨(0 : r3legModVec p), by simp [r3legQ]⟩
    calc
      Fintype.card {w : r3legCone p // (w.1 : r3legModVec p) = 0} =
          Fintype.card {w : r3legCone p // w = z} :=
        Fintype.card_congr (Equiv.subtypeEquivRight fun w => by
          simp [z, Subtype.ext_iff])
      _ = 1 := Fintype.card_subtype_eq z
  rw [hzero]

private lemma r3leg_q_red (p : ℕ) (x : r3legIntVec) :
    r3legQ (r3legRed p x) = ((r3legQ x : ℤ) : ZMod p) := by
  simp [r3legQ, r3legRed]

private lemma r3leg_q_smul {R : Type*} [CommSemiring R] (c : R) (x : (R × R) × R) :
    r3legQ (c • x) = c ^ 2 * r3legQ x := by
  simp [r3legQ]
  ring

private lemma r3leg_smul_right_injective {p : ℕ} [Fact (Nat.Prime p)]
    (v : r3legModVec p) (hv : v ≠ 0) :
    Function.Injective (fun c : ZMod p => c • v) := by
  intro a b hab
  rcases v with ⟨⟨x, y⟩, z⟩
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · have hz : z ≠ 0 := by
        intro hz
        apply hv
        simp [hx, hy, hz]
      have h := congrArg (fun w : r3legModVec p => w.2) hab
      exact mul_right_cancel₀ hz (by simpa using h)
    · have h := congrArg (fun w : r3legModVec p => w.1.2) hab
      exact mul_right_cancel₀ hy (by simpa using h)
  · have h := congrArg (fun w : r3legModVec p => w.1.1) hab
    exact mul_right_cancel₀ hx (by simpa using h)

private def r3leg_primitiveUnitMap {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (y : r3legIntVec) (hyq : r3legQ y = (p ^ 2 * n : ℕ))
    (hyne : r3legRed p y ≠ 0) :
    (ZMod p)ˣ → {w : r3legIso p // r3legInc hp3 w y} := by
  let v := r3legRed p y
  have hvne : v ≠ 0 := hyne
  have hvq : r3legQ v = 0 := by
    dsimp [v]
    rw [r3leg_q_red, hyq]
    push_cast
    simp
  intro u
  let w : r3legIso p :=
    ⟨(u : ZMod p) • v, smul_ne_zero (Units.ne_zero u) hvne, by
      rw [r3leg_q_smul, hvq, mul_zero]⟩
  refine ⟨w, (r3leg_inc_primitive_iff hp3 w y hyq hyne).2 ?_⟩
  refine ⟨((u⁻¹ : (ZMod p)ˣ) : ZMod p), Units.ne_zero u⁻¹, ?_⟩
  change v = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) • ((u : ZMod p) • v)
  rw [smul_smul, Units.inv_mul, one_smul]

private noncomputable instance r3legIncDecidable {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (y : r3legIntVec) :
    DecidablePred (fun w : r3legIso p => r3legInc hp3 w y) :=
  Classical.decPred _

private lemma r3leg_primitiveUnitMap_injective {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (y : r3legIntVec) (hyq : r3legQ y = (p ^ 2 * n : ℕ))
    (hyne : r3legRed p y ≠ 0) :
    Function.Injective (r3leg_primitiveUnitMap hp3 y hyq hyne) := by
  intro u v huv
  apply Units.ext
  apply r3leg_smul_right_injective (r3legRed p y) hyne
  have h := congrArg
    (fun w : {w : r3legIso p // r3legInc hp3 w y} => (w.1.1 : r3legModVec p)) huv
  exact h

private lemma r3leg_primitiveUnitMap_surjective {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (y : r3legIntVec) (hyq : r3legQ y = (p ^ 2 * n : ℕ))
    (hyne : r3legRed p y ≠ 0) :
    Function.Surjective (r3leg_primitiveUnitMap hp3 y hyq hyne) := by
  intro w
  obtain ⟨κ, hκ, hyred⟩ := (r3leg_inc_primitive_iff hp3 w.1 y hyq hyne).mp w.2
  let u : (ZMod p)ˣ := Units.mk0 κ hκ
  refine ⟨u⁻¹, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ((u⁻¹ : (ZMod p)ˣ) : ZMod p) • r3legRed p y = (w.1.1 : r3legModVec p)
  change r3legRed p y = (u : ZMod p) • (w.1.1 : r3legModVec p) at hyred
  rw [hyred, smul_smul, Units.inv_mul, one_smul]

private lemma r3leg_primitive_inc_card {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (y : r3legIntVec) (hyq : r3legQ y = (p ^ 2 * n : ℕ))
    (hyne : r3legRed p y ≠ 0) :
    Fintype.card {w : r3legIso p // r3legInc hp3 w y} = p - 1 := by
  let e := Equiv.ofBijective (r3leg_primitiveUnitMap hp3 y hyq hyne)
    ⟨r3leg_primitiveUnitMap_injective hp3 y hyq hyne,
      r3leg_primitiveUnitMap_surjective hp3 y hyq hyne⟩
  calc
    Fintype.card {w : r3legIso p // r3legInc hp3 w y} =
        Fintype.card (ZMod p)ˣ := (Fintype.card_congr e).symm
    _ = p - 1 := by rw [Fintype.card_units, ZMod.card]

private lemma r3leg_b_comm {R : Type*} [CommSemiring R] (x y : (R × R) × R) :
    r3legB x y = r3legB y x := by
  simp [r3legB]
  ring

private def r3leg_scaledIncOrthEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legIntVec) :
    {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} ≃
      {w : r3legOrthCone p (r3legRed p x) // (w.1 : r3legModVec p) ≠ 0} where
  toFun w := ⟨⟨w.1.1, w.1.2.2, by
    rw [r3leg_b_comm]
    exact (r3leg_inc_scale_iff hp3 w.1 x).mp w.2⟩, w.1.2.1⟩
  invFun w := ⟨⟨w.1.1, w.2, w.1.2.1⟩, by
    apply (r3leg_inc_scale_iff hp3 _ x).mpr
    rw [r3leg_b_comm]
    exact w.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma r3leg_scaled_inc_card_of_ne {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legIntVec) (hx : r3legRed p x ≠ 0) :
    (Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} : ℤ) =
      ((p : ℤ) - 1) * (1 + quadraticChar (ZMod p) (-r3legQ (r3legRed p x))) := by
  let z : r3legOrthCone p (r3legRed p x) :=
    ⟨(0 : r3legModVec p), by simp [r3legQ, r3legB]⟩
  have hzero :
      Fintype.card
          {w : r3legOrthCone p (r3legRed p x) // (w.1 : r3legModVec p) = 0} = 1 := by
    calc
      Fintype.card
          {w : r3legOrthCone p (r3legRed p x) // (w.1 : r3legModVec p) = 0} =
          Fintype.card {w : r3legOrthCone p (r3legRed p x) // w = z} :=
        Fintype.card_congr (Equiv.subtypeEquivRight fun w => by
          simp [z, Subtype.ext_iff])
      _ = 1 := Fintype.card_subtype_eq z
  have hcard :
      Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} =
        Fintype.card (r3legOrthCone p (r3legRed p x)) - 1 := by
    rw [Fintype.card_congr (r3leg_scaledIncOrthEquiv hp3 x),
      Fintype.card_subtype_compl, hzero]
  have hpos : 0 < Fintype.card (r3legOrthCone p (r3legRed p x)) :=
    Fintype.card_pos_iff.mpr ⟨z⟩
  have hcard' :
      Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} + 1 =
        Fintype.card (r3legOrthCone p (r3legRed p x)) := by
    omega
  have hcardz :
      (Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} : ℤ) + 1 =
        Fintype.card (r3legOrthCone p (r3legRed p x)) := by
    exact_mod_cast hcard'
  have horth := r3leg_orthCone_card hp3 (r3legRed p x) hx
  calc
    (Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} : ℤ) =
        (Fintype.card (r3legOrthCone p (r3legRed p x)) : ℤ) - 1 := by
      omega
    _ = (p : ℤ) + ((p : ℤ) - 1) *
          quadraticChar (ZMod p) (-r3legQ (r3legRed p x)) - 1 := by rw [horth]
    _ = ((p : ℤ) - 1) *
          (1 + quadraticChar (ZMod p) (-r3legQ (r3legRed p x))) := by ring

private lemma r3leg_scaled_inc_card_of_eq {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legIntVec) (hx : r3legRed p x = 0) :
    Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} = p ^ 2 - 1 := by
  let e : {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} ≃ r3legIso p :=
    { toFun := fun w => w.1
      invFun := fun w => ⟨w, (r3leg_inc_scale_iff hp3 w x).mpr (by
        rw [hx]
        simp [r3legB])⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, r3leg_iso_card]

private abbrev r3legRepType (n : ℕ) :=
  {x : r3legIntVec // x ∈ r3legRep n}

private lemma r3leg_repType_card (n : ℕ) :
    Fintype.card (r3legRepType n) = Nat.threeSquareRepresentationCount n := by
  rw [Fintype.card_coe, r3leg_rep_card]

private lemma r3leg_q_scale (c : ℤ) (x : r3legIntVec) :
    r3legQ (r3legScale c x) = c ^ 2 * r3legQ x := by
  simp [r3legQ, r3legScale]
  ring

private noncomputable def r3leg_scaleRepEquiv {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) :
    r3legRepType n ≃
      {y : r3legRepType (p ^ 2 * n) // r3legRed p (y : r3legIntVec) = 0} where
  toFun x := ⟨⟨r3legScale p x, r3leg_mem_rep.mpr (by
    rw [r3leg_q_scale, r3leg_mem_rep.mp x.2]
    push_cast
    ring)⟩, by
      rw [r3leg_red_scale]
      change ((p : ℤ) : ZMod p) • r3legRed p x = 0
      simp⟩
  invFun y := ⟨r3legVecDiv y p, r3leg_mem_rep.mpr (by
    have hdiv : r3legVecDvd (p : ℤ) y :=
      (r3leg_vecDvd_iff_red_eq_zero p y).mpr y.2
    have hscale : r3legScale p (r3legVecDiv y p) = y := r3leg_scale_vecDiv hdiv
    have hq := congrArg r3legQ hscale
    rw [r3leg_q_scale, r3leg_mem_rep.mp y.1.2] at hq
    push_cast at hq
    have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
    nlinarith)⟩
  left_inv x := by
    apply Subtype.ext
    have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    apply r3leg_scale_left_cancel hpne
    exact r3leg_scale_vecDiv
      ⟨⟨(x : r3legIntVec).1.1, rfl⟩, ⟨(x : r3legIntVec).1.2, rfl⟩,
        (x : r3legIntVec).2, rfl⟩
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact r3leg_scale_vecDiv ((r3leg_vecDvd_iff_red_eq_zero p y).mpr y.2)

private lemma r3leg_sq_dvd_of_red_eq_zero {p n : ℕ} (x : r3legRepType n)
    (hx : r3legRed p (x : r3legIntVec) = 0) : p ^ 2 ∣ n := by
  have hdiv := (r3leg_vecDvd_iff_red_eq_zero p x).mpr hx
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, c, hc⟩ := hdiv
  apply Int.natCast_dvd_natCast.mp
  change (p : ℤ) ^ 2 ∣ (n : ℤ)
  rw [← r3leg_mem_rep.mp x.2]
  refine ⟨a ^ 2 + b ^ 2 + c ^ 2, ?_⟩
  simp only [r3legQ]
  rw [ha, hb, hc]
  ring

private lemma r3leg_zeroRed_rep_card_of_dvd {p n : ℕ} [Fact (Nat.Prime p)]
    (hdiv : p ^ 2 ∣ n) :
    Fintype.card {x : r3legRepType n // r3legRed p (x : r3legIntVec) = 0} =
      Nat.threeSquareRepresentationCount (n / p ^ 2) := by
  have hmul : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' hdiv
  have hcard := Fintype.card_congr (r3leg_scaleRepEquiv (p := p) (n / p ^ 2))
  rw [hmul, r3leg_repType_card] at hcard
  exact hcard.symm

private lemma r3leg_zeroRed_rep_card_of_not_dvd {p n : ℕ} [Fact (Nat.Prime p)]
    (hdiv : ¬p ^ 2 ∣ n) :
    Fintype.card {x : r3legRepType n // r3legRed p (x : r3legIntVec) = 0} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun x => hdiv (r3leg_sq_dvd_of_red_eq_zero x.1 x.2)⟩

private lemma r3leg_zeroRed_rep_card {p n : ℕ} [Fact (Nat.Prime p)] :
    Fintype.card {x : r3legRepType n // r3legRed p (x : r3legIntVec) = 0} =
      if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0 := by
  split_ifs with h
  · exact r3leg_zeroRed_rep_card_of_dvd h
  · exact r3leg_zeroRed_rep_card_of_not_dvd h

private noncomputable instance r3legIncRepDecidable {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) :
    DecidablePred (fun y : r3legRepType (p ^ 2 * n) => r3legInc hp3 w y) :=
  Classical.decPred _

private def r3leg_incRepImageEquiv {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) :
    {y : r3legRepType (p ^ 2 * n) // r3legInc hp3 w y} ≃
      (r3legImageRep p n (r3legPi hp3 w) : Type) where
  toFun y := ⟨y.1, r3leg_mem_imageRep.mpr
    ⟨r3leg_mem_rep.mp y.1.2, y.2⟩⟩
  invFun y := ⟨⟨y, r3leg_mem_rep.mpr (r3leg_mem_imageRep.mp y.2).1⟩,
    (r3leg_mem_imageRep.mp y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma r3leg_incRep_card {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) :
    Fintype.card {y : r3legRepType (p ^ 2 * n) // r3legInc hp3 w y} =
      Nat.threeSquareRepresentationCount n := by
  rw [Fintype.card_congr (r3leg_incRepImageEquiv hp3 w), Fintype.card_coe,
    r3leg_imageRep_card _ (r3legPi_norm hp3 w)]

private def r3leg_incidenceSwap {p n : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Σ w : r3legIso p,
      {y : r3legRepType (p ^ 2 * n) // r3legInc hp3 w y}) ≃
    (Σ y : r3legRepType (p ^ 2 * n),
      {w : r3legIso p // r3legInc hp3 w y}) where
  toFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma r3leg_incidence_sum {p n : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    ∑ y : r3legRepType (p ^ 2 * n),
        Fintype.card {w : r3legIso p // r3legInc hp3 w y} =
      (p ^ 2 - 1) * Nat.threeSquareRepresentationCount n := by
  have hswap := Fintype.card_congr (r3leg_incidenceSwap (n := n) hp3)
  rw [Fintype.card_sigma, Fintype.card_sigma] at hswap
  calc
    ∑ y : r3legRepType (p ^ 2 * n),
        Fintype.card {w : r3legIso p // r3legInc hp3 w y} =
        ∑ w : r3legIso p,
          Fintype.card {y : r3legRepType (p ^ 2 * n) // r3legInc hp3 w y} := hswap.symm
    _ = ∑ _w : r3legIso p, Nat.threeSquareRepresentationCount n := by
      apply Finset.sum_congr rfl
      intro w _
      exact r3leg_incRep_card hp3 w
    _ = Fintype.card (r3legIso p) * Nat.threeSquareRepresentationCount n := by simp
    _ = (p ^ 2 - 1) * Nat.threeSquareRepresentationCount n := by rw [r3leg_iso_card]

private lemma r3leg_quadraticChar_rep {p n : ℕ} [Fact (Nat.Prime p)]
    (x : r3legRepType n) :
    quadraticChar (ZMod p) (-r3legQ (r3legRed p x)) = legendreSym p (-(n : ℤ)) := by
  rw [r3leg_q_red, r3leg_mem_rep.mp x.2]
  simp [legendreSym]

private lemma r3leg_zeroRed_filter_card {p n : ℕ} [Fact (Nat.Prime p)] :
    (Finset.univ.filter
      (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) = 0)).card =
      if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0 := by
  rw [← Fintype.card_subtype]
  exact r3leg_zeroRed_rep_card

private lemma r3leg_nonzeroRed_filter_card_add {p n : ℕ} [Fact (Nat.Prime p)] :
    (Finset.univ.filter
        (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) ≠ 0)).card +
      (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) =
      Nat.threeSquareRepresentationCount n := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) = 0)
  rw [r3leg_zeroRed_filter_card, Finset.card_univ, r3leg_repType_card] at h
  simpa only [ne_eq, add_comm] using h

private lemma r3leg_zeroRed_scaled_filter_card {p n : ℕ} [Fact (Nat.Prime p)] :
    (Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
      r3legRed p (y : r3legIntVec) = 0)).card =
      Nat.threeSquareRepresentationCount n := by
  rw [← Fintype.card_subtype]
  calc
    Fintype.card
        {y : r3legRepType (p ^ 2 * n) // r3legRed p (y : r3legIntVec) = 0} =
        Fintype.card (r3legRepType n) :=
      (Fintype.card_congr (r3leg_scaleRepEquiv (p := p) n)).symm
    _ = Nat.threeSquareRepresentationCount n := r3leg_repType_card n

private lemma r3leg_nonzeroRed_scaled_filter_card_add {p n : ℕ}
    [Fact (Nat.Prime p)] :
    (Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
        r3legRed p (y : r3legIntVec) ≠ 0)).card +
      Nat.threeSquareRepresentationCount n =
      Nat.threeSquareRepresentationCount (p ^ 2 * n) := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun y : r3legRepType (p ^ 2 * n) => r3legRed p (y : r3legIntVec) = 0)
  rw [r3leg_zeroRed_scaled_filter_card, Finset.card_univ, r3leg_repType_card] at h
  simpa only [ne_eq, add_comm] using h

private lemma r3leg_primitive_inc_sum {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) :
    (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
        r3legRed p (y : r3legIntVec) ≠ 0),
      (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)) =
      ((Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
        Nat.threeSquareRepresentationCount n) * ((p : ℤ) - 1) := by
  let s := Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
    r3legRed p (y : r3legIntVec) ≠ 0)
  have hcount := r3leg_nonzeroRed_scaled_filter_card_add (p := p) (n := n)
  have hcountz : (s.card : ℤ) + Nat.threeSquareRepresentationCount n =
      Nat.threeSquareRepresentationCount (p ^ 2 * n) := by
    exact_mod_cast hcount
  have hp1 : 1 ≤ p := by omega
  calc
    (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
        r3legRed p (y : r3legIntVec) ≠ 0),
      (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)) =
        ∑ _y ∈ s, ((p - 1 : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyne : r3legRed p (y : r3legIntVec) ≠ 0 := (Finset.mem_filter.mp hy).2
      exact_mod_cast r3leg_primitive_inc_card hp3 y (r3leg_mem_rep.mp y.2) hyne
    _ = (s.card : ℤ) * ((p - 1 : ℕ) : ℤ) := by simp
    _ = (s.card : ℤ) * ((p : ℤ) - 1) := by rw [Nat.cast_sub hp1]; norm_num
    _ = ((Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
        Nat.threeSquareRepresentationCount n) * ((p : ℤ) - 1) := by
      rw [show (s.card : ℤ) =
          (Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
            Nat.threeSquareRepresentationCount n by omega]

private lemma r3leg_zeroRed_inc_sum {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) :
    (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
        r3legRed p (y : r3legIntVec) = 0),
      (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)) =
      ∑ x : r3legRepType n,
        (Fintype.card
          {w : r3legIso p // r3legInc hp3 w (r3legScale p (x : r3legIntVec))} : ℤ) := by
  let e := r3leg_scaleRepEquiv (p := p) n
  calc
    (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
        r3legRed p (y : r3legIntVec) = 0),
      (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)) =
        ∑ y : {y : r3legRepType (p ^ 2 * n) //
            r3legRed p (y : r3legIntVec) = 0},
          (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ) := by
      apply Finset.sum_subtype
      intro y
      simp
    _ = ∑ x : r3legRepType n,
        (Fintype.card
          {w : r3legIso p // r3legInc hp3 w (r3legScale p (x : r3legIntVec))} : ℤ) := by
      symm
      apply Fintype.sum_equiv e
      intro x
      rfl

private lemma r3leg_scaled_inc_sum {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) :
    (∑ x : r3legRepType n,
      (Fintype.card
        {w : r3legIso p // r3legInc hp3 w (r3legScale p (x : r3legIntVec))} : ℤ)) =
      ((Nat.threeSquareRepresentationCount n : ℤ) -
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) *
          ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) +
        (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) *
          ((p : ℤ) ^ 2 - 1) := by
  let f := fun x : r3legRepType n =>
    (Fintype.card
      {w : r3legIso p // r3legInc hp3 w (r3legScale p (x : r3legIntVec))} : ℤ)
  let r' := if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0
  let s₀ := Finset.univ.filter
    (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) = 0)
  let s₁ := Finset.univ.filter
    (fun x : r3legRepType n => r3legRed p (x : r3legIntVec) ≠ 0)
  have hzeroCard : s₀.card = r' := r3leg_zeroRed_filter_card
  have hnonzeroCard := r3leg_nonzeroRed_filter_card_add (p := p) (n := n)
  have hnonzeroCardz : (s₁.card : ℤ) + (r' : ℤ) =
      Nat.threeSquareRepresentationCount n := by
    exact_mod_cast hnonzeroCard
  have hp2 : 1 ≤ p ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero)
  have hzero : (∑ x ∈ s₀, f x) = (r' : ℤ) * ((p : ℤ) ^ 2 - 1) := by
    calc
      (∑ x ∈ s₀, f x) = ∑ _x ∈ s₀, ((p ^ 2 - 1 : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx0 : r3legRed p (x : r3legIntVec) = 0 := (Finset.mem_filter.mp hx).2
        dsimp [f]
        exact_mod_cast r3leg_scaled_inc_card_of_eq hp3 x hx0
      _ = (s₀.card : ℤ) * ((p ^ 2 - 1 : ℕ) : ℤ) := by simp
      _ = (r' : ℤ) * ((p ^ 2 - 1 : ℕ) : ℤ) := by rw [hzeroCard]
      _ = (r' : ℤ) * ((p : ℤ) ^ 2 - 1) := by
        rw [Nat.cast_sub hp2]
        push_cast
        rfl
  have hnonzero : (∑ x ∈ s₁, f x) =
      ((Nat.threeSquareRepresentationCount n : ℤ) - (r' : ℤ)) *
        ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) := by
    calc
      (∑ x ∈ s₁, f x) =
          ∑ _x ∈ s₁,
            (((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ)))) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxne : r3legRed p (x : r3legIntVec) ≠ 0 := (Finset.mem_filter.mp hx).2
        dsimp [f]
        rw [r3leg_scaled_inc_card_of_ne hp3 x hxne, r3leg_quadraticChar_rep]
      _ = (s₁.card : ℤ) *
          (((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ)))) := by simp
      _ = ((Nat.threeSquareRepresentationCount n : ℤ) - (r' : ℤ)) *
          ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) := by
        rw [show (s₁.card : ℤ) =
            (Nat.threeSquareRepresentationCount n : ℤ) - (r' : ℤ) by omega]
        ring
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun x : r3legRepType n => r3legRed p (x : r3legIntVec) = 0) f
  have hsplit' : (∑ x ∈ s₀, f x) + (∑ x ∈ s₁, f x) = ∑ x, f x := by
    simpa only [s₀, s₁, ne_eq] using hsplit
  change (∑ x, f x) = _
  rw [← hsplit', hzero, hnonzero]
  dsimp [r']
  ring

private lemma r3leg_double_count {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) :
    ((p : ℤ) ^ 2 - 1) * Nat.threeSquareRepresentationCount n =
      ((p : ℤ) - 1) *
          ((Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
            Nat.threeSquareRepresentationCount n) +
        ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) *
          ((Nat.threeSquareRepresentationCount n : ℤ) -
            (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) +
        ((p : ℤ) ^ 2 - 1) *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) := by
  let f := fun y : r3legRepType (p ^ 2 * n) =>
    (Fintype.card {w : r3legIso p // r3legInc hp3 w y} : ℤ)
  have hp2 : 1 ≤ p ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero)
  have htotalNat := r3leg_incidence_sum (n := n) hp3
  have htotalCast : (∑ y : r3legRepType (p ^ 2 * n), f y) =
      ((((p ^ 2 - 1) * Nat.threeSquareRepresentationCount n : ℕ) : ℤ)) := by
    dsimp [f]
    exact_mod_cast htotalNat
  have htotal : (∑ y : r3legRepType (p ^ 2 * n), f y) =
      ((p : ℤ) ^ 2 - 1) * Nat.threeSquareRepresentationCount n := by
    rw [htotalCast, Nat.cast_mul, Nat.cast_sub hp2]
    push_cast
    rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun y : r3legRepType (p ^ 2 * n) => r3legRed p (y : r3legIntVec) = 0) f
  have hsplit' :
      (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
          r3legRed p (y : r3legIntVec) = 0), f y) +
        (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
          r3legRed p (y : r3legIntVec) ≠ 0), f y) = ∑ y, f y := by
    simpa only [ne_eq] using hsplit
  calc
    ((p : ℤ) ^ 2 - 1) * Nat.threeSquareRepresentationCount n = ∑ y, f y :=
      htotal.symm
    _ =
        (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
          r3legRed p (y : r3legIntVec) = 0), f y) +
        (∑ y ∈ Finset.univ.filter (fun y : r3legRepType (p ^ 2 * n) =>
          r3legRed p (y : r3legIntVec) ≠ 0), f y) := hsplit'.symm
    _ =
        (((Nat.threeSquareRepresentationCount n : ℤ) -
            (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) *
            ((p : ℤ) - 1) * (1 + legendreSym p (-(n : ℤ))) +
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) *
            ((p : ℤ) ^ 2 - 1)) +
        (((Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) -
            Nat.threeSquareRepresentationCount n) * ((p : ℤ) - 1)) := by
      rw [r3leg_zeroRed_inc_sum hp3, r3leg_scaled_inc_sum hp3,
        r3leg_primitive_inc_sum hp3]
    _ = _ := by ring

private lemma r3leg_legendre_mul_correction_eq_zero {p n : ℕ}
    [Fact (Nat.Prime p)] :
    legendreSym p (-(n : ℤ)) *
      (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) = 0 := by
  split_ifs with hdiv
  · have hpdiv : p ∣ n := dvd_trans (⟨p, by simp [pow_two]⟩ : p ∣ p ^ 2) hdiv
    have hnzero : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpdiv
    have hleg : legendreSym p (-(n : ℤ)) = 0 := by
      apply (legendreSym.eq_zero_iff p (-(n : ℤ))).mpr
      push_cast
      rw [hnzero, neg_zero]
    rw [hleg, zero_mul]
  · simp

private lemma r3leg_alpha_one {p n : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Nat.threeSquareRepresentationCount (p ^ 2 * n) : ℤ) =
      ((p : ℤ) + 1 - legendreSym p (-(n : ℤ))) *
          Nat.threeSquareRepresentationCount n -
        (p : ℤ) *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) := by
  have hcount := r3leg_double_count (n := n) hp3
  have hleg := r3leg_legendre_mul_correction_eq_zero (p := p) (n := n)
  have hpne : (p : ℤ) - 1 ≠ 0 := by
    have : (1 : ℤ) < p := by exact_mod_cast (show 1 < p by omega)
    omega
  apply mul_left_cancel₀ hpne
  nlinarith

private def r3legG (p k : ℕ) : ℤ :=
  ((p : ℤ) ^ k - 1) / ((p : ℤ) - 1)

private lemma r3leg_g_eq_sum {p k : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    r3legG p k = ∑ i ∈ Finset.range k, (p : ℤ) ^ i := by
  apply Int.ediv_eq_of_eq_mul_left
  · have : (1 : ℤ) < p := by exact_mod_cast (show 1 < p by omega)
    omega
  · exact (geom_sum_mul (p : ℤ) k).symm

private lemma r3leg_g_zero {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    r3legG p 0 = 0 := by
  rw [r3leg_g_eq_sum hp3]
  simp

private lemma r3leg_g_one {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    r3legG p 1 = 1 := by
  rw [r3leg_g_eq_sum hp3]
  simp

private lemma r3leg_g_two {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    r3legG p 2 = (p : ℤ) + 1 := by
  rw [r3leg_g_eq_sum hp3]
  norm_num [Finset.sum_range_succ]
  ring

private lemma r3leg_g_succ {p k : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    r3legG p (k + 1) = r3legG p k + (p : ℤ) ^ k := by
  rw [r3leg_g_eq_sum hp3, r3leg_g_eq_sum hp3, Finset.sum_range_succ]

private lemma r3leg_g_rec {p k : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    r3legG p (k + 2) = ((p : ℤ) + 1) * r3legG p (k + 1) -
      (p : ℤ) * r3legG p k := by
  rw [show k + 2 = (k + 1) + 1 by omega, r3leg_g_succ hp3,
    r3leg_g_succ hp3, pow_succ]
  ring

private lemma r3leg_rep_rec {p n k : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Nat.threeSquareRepresentationCount (p ^ (2 * (k + 2)) * n) : ℤ) =
      ((p : ℤ) + 1) *
          Nat.threeSquareRepresentationCount (p ^ (2 * (k + 1)) * n) -
        (p : ℤ) * Nat.threeSquareRepresentationCount (p ^ (2 * k) * n) := by
  have hfactor : p ^ (2 * (k + 1)) * n = p ^ 2 * (p ^ (2 * k) * n) := by
    rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
    ring
  have hnext : p ^ 2 * (p ^ (2 * (k + 1)) * n) = p ^ (2 * (k + 2)) * n := by
    rw [show 2 * (k + 2) = 2 + 2 * (k + 1) by omega, pow_add]
    ring
  have hdiv : p ^ 2 ∣ p ^ (2 * (k + 1)) * n := ⟨p ^ (2 * k) * n, hfactor⟩
  have hp2pos : 0 < p ^ 2 := pow_pos (Fact.out : Nat.Prime p).pos 2
  have hquot : (p ^ (2 * (k + 1)) * n) / p ^ 2 = p ^ (2 * k) * n := by
    rw [hfactor, Nat.mul_div_cancel_left _ hp2pos]
  have hpdiv : p ∣ p ^ (2 * (k + 1)) * n :=
    dvd_trans (⟨p, by simp [pow_two]⟩ : p ∣ p ^ 2) hdiv
  have hmzero : ((p ^ (2 * (k + 1)) * n : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hpdiv
  have hleg : legendreSym p (-((p ^ (2 * (k + 1)) * n : ℕ) : ℤ)) = 0 := by
    apply (legendreSym.eq_zero_iff p _).mpr
    rw [Int.cast_neg, Int.cast_natCast, hmzero, neg_zero]
  have h := r3leg_alpha_one (n := p ^ (2 * (k + 1)) * n) hp3
  rw [hnext, hleg, ite_eq_left hdiv, hquot] at h
  simpa using h

private lemma r3leg_formula {p n α : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Nat.threeSquareRepresentationCount (p ^ (2 * α) * n) : ℤ) =
      (r3legG p (α + 1) - legendreSym p (-(n : ℤ)) * r3legG p α) *
          Nat.threeSquareRepresentationCount n -
        (p : ℤ) * r3legG p α *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0) := by
  let P : ℕ → Prop := fun a =>
    (Nat.threeSquareRepresentationCount (p ^ (2 * a) * n) : ℤ) =
      (r3legG p (a + 1) - legendreSym p (-(n : ℤ)) * r3legG p a) *
          Nat.threeSquareRepresentationCount n -
        (p : ℤ) * r3legG p a *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)
  change P α
  apply Nat.twoStepInduction (motive := P)
  · dsimp [P]
    rw [r3leg_g_zero hp3, r3leg_g_one hp3]
    simp
  · dsimp [P]
    rw [r3leg_g_one hp3, r3leg_g_two hp3]
    simpa using r3leg_alpha_one (n := n) hp3
  · intro k hk hk1
    dsimp [P] at hk hk1 ⊢
    rw [r3leg_rep_rec hp3, hk1, hk]
    have hg0 := r3leg_g_rec (p := p) (k := k) hp3
    have hg1 := r3leg_g_rec (p := p) (k := k + 1) hp3
    rw [hg1, hg0]
    ring

/--
**Legendre-symbol recursion for three-square counts.** For a natural number $m$, let $r_3(m)$
denote the number of ordered triples of integers $(x, y, z)$ with $x^2 + y^2 + z^2 = m$. Let
$p \ge 3$ be a prime and let $n \ge 1$ and $\alpha \ge 0$ be natural numbers. Then
$$
r_3(p^{2\alpha} n) = \left(\frac{p^{\alpha+1} - 1}{p - 1} - \left(\frac{-n}{p}\right)
\frac{p^{\alpha} - 1}{p - 1}\right) r_3(n) - p \, \frac{p^{\alpha} - 1}{p - 1} \, r_3(n/p^2),
$$
where $\left(\frac{-n}{p}\right)$ is the Legendre symbol, both quotients by $p - 1$ are exact
integer divisions, and the term $r_3(n/p^2)$ is read as $0$ when $p^2$ does not divide $n$.

Proof: The route is an elementary p-neighbour double count using quaternionic descent and
finite-field conic counts, followed by a two-step induction on the exponent.

Proves `Wanted` entry `r3_legendre_recursion`.

Source: Liuquan Wang, "Another Proof of a Conjecture by Hirschhorn and Sellers on Overpartitions", Journal of Integer Sequences 17 (2014), Article 14.9.8, Lemma `r3relation`, lines 228-232, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Wang2/wang15.tex>.
-/
public theorem r3_legendre_recursion
    {p n α : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) (hn : 1 ≤ n) :
    (Nat.threeSquareRepresentationCount (p ^ (2 * α) * n) : ℤ) =
      (((((p : ℤ) ^ (α + 1) - 1) / ((p : ℤ) - 1)) -
          legendreSym p (-(n : ℤ)) *
            (((p : ℤ) ^ α - 1) / ((p : ℤ) - 1))) *
          Nat.threeSquareRepresentationCount n -
        (p : ℤ) * (((p : ℤ) ^ α - 1) / ((p : ℤ) - 1)) *
          (if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0)) := by
  simpa [r3legG] using r3leg_formula (p := p) (n := n) (α := α) hp3

end MetaMathlibExt
