/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/GreensOpenProblems/25.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

import Mathlib
















import FormalConjecturesUtil













open Asymptotics Filter Finset

namespace Green25





def Property25 (k N : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ N ∧
  ∀ P : Finpartition (Icc 1 N), #P.parts = k →
  10 * #(P.parts.biUnion Finset.restrictedSumset) ≥ N


noncomputable def bestUpper (N : ℕ) : ℝ := (N : ℝ) / Real.log N


def candidate25 (N : ℕ) : ℕ :=
  max 1 (N / (Nat.log 2 N) ^ 2)


lemma candidate25_special (t : ℕ) (ht : 5 ≤ t) :
    candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) =
      2 ^ (4 * (2 ^ t) ^ 2 - (4 + 4 * t)) := by
  rw [candidate25, Nat.log_pow (by omega)]
  have he : (4 * (2 ^ t) ^ 2) ^ 2 = 2 ^ (4 + 4 * t) := by
    ring_nf
  rw [he]
  have hpow : ∀ a : ℕ, a ≤ 2 ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
        rw [pow_succ]
        have hp : 1 ≤ 2 ^ a := one_le_pow₀ (by omega)
        omega
  have hle : 4 + 4 * t ≤ 4 * (2 ^ t) ^ 2 := by
    have hp : 1 ≤ 2 ^ t := one_le_pow₀ (by omega)
    have := hpow t
    nlinarith
  rw [Nat.pow_div hle (by omega)]
  exact max_eq_right (one_le_pow₀ (by omega))


def complementKey (Q a : ℕ) : ℕ := min a (Q - 1 - a)



def digitKey (Q r : ℕ) (L : List ℕ) : List ℕ :=
  L.mapIdx fun i a => if i < r then complementKey Q a else a

private lemma complementKey_eq_iff (Q a b : ℕ) (ha : a < Q) (hb : b < Q)
    (heven : 2 ∣ Q) :
    complementKey Q a = complementKey Q b ↔ b = a ∨ b = Q - 1 - a := by
  obtain ⟨k, rfl⟩ := heven
  simp only [complementKey, min_def]
  split_ifs <;> omega

private lemma ne_complement (Q a : ℕ) (ha : a < Q) (heven : 2 ∣ Q) :
    a ≠ Q - 1 - a := by
  obtain ⟨k, rfl⟩ := heven
  omega

private def digitVector (Q m x : ℕ) [NeZero (Q ^ m)] : Fin m → Fin Q :=
  finFunctionFinEquiv.symm (Fin.ofNat (Q ^ m) (x - 1))

private def encodeVector {Q m : ℕ} (v : Fin m → Fin Q) : ℕ :=
  (finFunctionFinEquiv v : ℕ) + 1

private lemma encodeVector_injective (Q m : ℕ) :
    Function.Injective (@encodeVector Q m) := by
  intro v w h
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  simp only [encodeVector] at h
  omega

private lemma digitVector_encode (Q m : ℕ) [NeZero (Q ^ m)] (v : Fin m → Fin Q) :
    digitVector Q m (encodeVector v) = v := by
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  have h := (finFunctionFinEquiv v).isLt
  simp only [digitVector, encodeVector, Equiv.apply_symm_apply, Fin.ofNat,
    Nat.add_sub_cancel]
  exact Nat.mod_eq_of_lt h

private lemma encodeVector_mem (Q m : ℕ) (v : Fin m → Fin Q) :
    encodeVector v ∈ Icc 1 (Q ^ m) := by
  simp only [Finset.mem_Icc, encodeVector]
  constructor <;> omega

private lemma encode_digitVector (Q m x : ℕ) [NeZero (Q ^ m)]
    (hx : x ∈ Icc 1 (Q ^ m)) : encodeVector (digitVector Q m x) = x := by
  simp only [Finset.mem_Icc] at hx
  simp only [encodeVector, digitVector, Equiv.apply_symm_apply, Fin.ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private def vectorKey (Q m r : ℕ) [NeZero (Q ^ m)] (x : ℕ) : Fin m → ℕ := fun i =>
  if i.1 < r then complementKey Q (digitVector Q m x i) else digitVector Q m x i

private def flipVector (Q r : ℕ) {m : ℕ} (v : Fin m → Fin Q)
    (b : Fin r → Bool) : Fin m → Fin Q := fun i =>
  if h : i.1 < r then
    if b ⟨i, h⟩ then ⟨Q - 1 - v i, by have := (v i).isLt; omega⟩ else v i
  else v i







lemma complemented_digit_partition (Q m r : ℕ) (hQ : 2 ≤ Q) (heven : 2 ∣ Q)
    (hr : r ≤ m) :
    ∃ P : Finpartition (Icc 1 (Q ^ m)),
      #P.parts = Q ^ m / 2 ^ r ∧
      #(P.parts.biUnion Finset.restrictedSumset) ≤ r * (2 * Q) ^ (m - 1) := by
  letI : NeZero (Q ^ m) := ⟨pow_ne_zero _ (by omega)⟩
  let s : Setoid ℕ := Setoid.ker (vectorKey Q m r)
  letI : DecidableRel s.r := Classical.decRel _
  let P : Finpartition (Icc 1 (Q ^ m)) := Finpartition.ofSetSetoid s _
  have hcardpart : ∀ p ∈ P.parts, #p = 2 ^ r := by
    intro p hp
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hp
    have haI : a ∈ Icc 1 (Q ^ m) := P.subset hp ha
    rw [← P.part_eq_of_mem hp ha]
    let v := digitVector Q m a
    let f : (Fin r → Bool) → ℕ := fun b => encodeVector (flipVector Q r v b)
    have hfmem : ∀ b : Fin r → Bool, f b ∈ P.part a := by
      intro b
      rw [show P = Finpartition.ofSetSetoid s (Icc 1 (Q ^ m)) by rfl]
      rw [Finpartition.mem_part_ofSetSetoid_iff_rel]
      exact ⟨haI, encodeVector_mem Q m (flipVector Q r v b), by
        change (Setoid.ker (vectorKey Q m r)) a (f b)
        rw [Setoid.ker_def]
        funext i
        change (if i.1 < r then complementKey Q (digitVector Q m a i)
          else digitVector Q m a i) =
          (if i.1 < r then complementKey Q (digitVector Q m (encodeVector (flipVector Q r v b)) i)
          else digitVector Q m (encodeVector (flipVector Q r v b)) i)
        rw [digitVector_encode Q m]
        simp only [v]
        by_cases hi : i.1 < r
        · by_cases hb : b ⟨i, hi⟩ = true
          · have hc : complementKey Q (digitVector Q m a i) =
                complementKey Q (Q - 1 - digitVector Q m a i) :=
              (complementKey_eq_iff Q _ _ (by omega) (by omega) heven).2 (Or.inr rfl)
            simpa [flipVector, hi, hb] using hc
          · simp [flipVector, hi, hb]
        · simp [hi, flipVector]
        ⟩
    have hfinj : Function.Injective f := by
      intro b c hbc
      have hv : flipVector Q r v b = flipVector Q r v c := by
        apply finFunctionFinEquiv.injective
        apply Fin.ext
        simpa [f, encodeVector] using congrArg (fun n => n - 1) hbc
      funext j
      let i : Fin m := ⟨j, lt_of_lt_of_le j.isLt hr⟩
      have hij : i.1 < r := j.isLt
      have hh := congrFun hv i
      have hhval := congrArg Fin.val hh
      have hji : (⟨i, hij⟩ : Fin r) = j := Fin.ext rfl
      simp only [flipVector, dif_pos hij, hji] at hhval
      have hn := ne_complement Q (v i) (v i).isLt heven
      cases hb : b j <;> cases hc : c j
      · rfl
      · exfalso
        simp [hb, hc] at hhval
        apply hn
        omega
      · exfalso
        simp [hb, hc] at hhval
        apply hn
        omega
      · rfl
    have hc := Finset.card_bij (fun b (_ : b ∈ (Finset.univ : Finset (Fin r → Bool))) => f b)
      (fun b _ => hfmem b)
      (fun b _ c _ h => hfinj h)
      (fun x hx => by
        rw [show P = Finpartition.ofSetSetoid s (Icc 1 (Q ^ m)) by rfl] at hx
        rw [Finpartition.mem_part_ofSetSetoid_iff_rel] at hx
        let w := digitVector Q m x
        let b : Fin r → Bool := fun j => decide (w ⟨j, lt_of_lt_of_le j.isLt hr⟩ ≠
          v ⟨j, lt_of_lt_of_le j.isLt hr⟩)
        refine ⟨b, Finset.mem_univ _, ?_⟩
        change f b = x
        rw [← encode_digitVector Q m x hx.2.1]
        change encodeVector (flipVector Q r v b) = encodeVector (digitVector Q m x)
        apply congrArg encodeVector
        ext i
        by_cases hi : i.1 < r
        · have hkey := congrFun hx.2.2 i
          simp only [s, Setoid.ker_def, vectorKey, hi, ↓reduceIte] at hkey
          have hkey' : complementKey Q (v i) = complementKey Q (w i) := by
            simpa [v, w] using hkey
          have hor := (complementKey_eq_iff Q _ _ (v i).isLt (w i).isLt heven).1 hkey'
          change (flipVector Q r v b i).1 = (w i).1
          by_cases heq : w i = v i
          · simpa [flipVector, hi, b, heq]
          · rcases hor with hor | hor
            · exact (heq (Fin.ext hor)).elim
            · simpa [flipVector, hi, b, heq] using hor.symm
        · have hkey := congrFun hx.2.2 i
          simp only [s, Setoid.ker_def, vectorKey, hi, ↓reduceIte] at hkey
          change (flipVector Q r v b i).1 = (w i).1
          simpa [flipVector, hi, v, w] using hkey)
    simpa [Fintype.card_fun] using hc.symm
  refine ⟨P, ?_, ?_⟩
  · have hs := P.sum_card_parts
    have heq : #P.parts * 2 ^ r = Q ^ m := by
      calc
        #P.parts * 2 ^ r = ∑ p ∈ P.parts, 2 ^ r := by simp
        _ = ∑ p ∈ P.parts, #p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hcardpart p hp]
        _ = #(Icc 1 (Q ^ m)) := hs
        _ = Q ^ m := by simp [Nat.card_Icc]
    exact (Nat.div_eq_of_eq_mul_left (by positivity) heq.symm).symm
  · by_cases hr0 : r = 0
    · subst r
      simp only [zero_mul, Nat.le_zero]
      rw [Finset.card_eq_zero]
      ext z
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨p, hp, hz⟩
        rw [Finset.restrictedSumset] at hz
        obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_offDiag] at hxy
        have hc := hcardpart p hp
        rw [pow_zero] at hc
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        simp_all
      · simp
    · have hm0 : m ≠ 0 := by omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      let C := Fin r × (Fin n → Fin (2 * Q))
      let decode : C → ℕ := fun c =>
        let j : Fin (n + 1) := ⟨c.1.1, lt_of_lt_of_le c.1.2 hr⟩
        let d : Fin (n + 1) → Fin (2 * Q) :=
          Fin.insertNth j ⟨Q - 1, by omega⟩ c.2
        2 + ∑ i, (d i : ℕ) * Q ^ (i : ℕ)
      have hsubset : P.parts.biUnion Finset.restrictedSumset ⊆
          (Finset.univ : Finset C).image decode := by
        intro z hz
        rw [Finset.mem_biUnion] at hz
        obtain ⟨p, hp, hz⟩ := hz
        rw [Finset.restrictedSumset] at hz
        obtain ⟨xy, hxy, hsum⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_offDiag] at hxy
        let x := xy.1
        let y := xy.2
        have hx : x ∈ p := hxy.1
        have hy : y ∈ p := hxy.2.1
        have hne : x ≠ y := hxy.2.2
        have hxI : x ∈ Icc 1 (Q ^ (n + 1)) := P.subset hp hx
        have hyI : y ∈ Icc 1 (Q ^ (n + 1)) := P.subset hp hy
        have hyPart : y ∈ P.part x := by
          rw [P.part_eq_of_mem hp hx]
          exact hy
        have hrel : vectorKey Q (n + 1) r x = vectorKey Q (n + 1) r y := by
          rw [show P = Finpartition.ofSetSetoid s (Icc 1 (Q ^ (n + 1))) by rfl] at hyPart
          rw [Finpartition.mem_part_ofSetSetoid_iff_rel] at hyPart
          exact hyPart.2.2
        let vx := digitVector Q (n + 1) x
        let vy := digitVector Q (n + 1) y
        have hvne : vx ≠ vy := by
          intro hv
          apply hne
          rw [← encode_digitVector Q (n + 1) x hxI,
            ← encode_digitVector Q (n + 1) y hyI]
          change encodeVector vx = encodeVector vy
          rw [hv]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hvne
        have hir : i.1 < r := by
          by_contra hir
          have hk := congrFun hrel i
          simp only [vectorKey, hir, ↓reduceIte] at hk
          exact hi (Fin.ext hk)
        have hk := congrFun hrel i
        simp only [vectorKey, hir, ↓reduceIte] at hk
        have hk' : complementKey Q (vx i) = complementKey Q (vy i) := by
          simpa [vx, vy] using hk
        have hor := (complementKey_eq_iff Q _ _ (vx i).isLt (vy i).isLt heven).1 hk'
        have hcomp : (vy i : ℕ) = Q - 1 - (vx i : ℕ) := by
          rcases hor with hor | hor
          · exact (hi (Fin.ext hor.symm)).elim
          · exact hor
        let j : Fin r := ⟨i.1, hir⟩
        let jm : Fin (n + 1) := ⟨j.1, lt_of_lt_of_le j.2 hr⟩
        have hjm : jm = i := Fin.ext rfl
        let d : Fin (n + 1) → Fin (2 * Q) := fun k =>
          ⟨(vx k : ℕ) + (vy k : ℕ), by
            have hxlt := (vx k).isLt
            have hylt := (vy k).isLt
            omega⟩
        have hdjm : d jm = (⟨Q - 1, by omega⟩ : Fin (2 * Q)) := by
          apply Fin.ext
          simp only [d, hjm]
          omega
        let c : C := (j, Fin.removeNth jm d)
        refine Finset.mem_image.mpr ⟨c, Finset.mem_univ _, ?_⟩
        have hrecon : Fin.insertNth jm (⟨Q - 1, by omega⟩ : Fin (2 * Q))
            (Fin.removeNth jm d) = d := by
          rw [Fin.insertNth_removeNth]
          rw [show (⟨Q - 1, by omega⟩ : Fin (2 * Q)) = d jm from hdjm.symm]
          simp
        change 2 + ∑ k, ((Fin.insertNth jm (⟨Q - 1, by omega⟩ : Fin (2 * Q))
          (Fin.removeNth jm d)) k : ℕ) * Q ^ (k : ℕ) = z
        rw [hrecon]
        change x + y = z at hsum
        rw [← hsum]
        rw [← encode_digitVector Q (n + 1) x hxI,
          ← encode_digitVector Q (n + 1) y hyI]
        simp only [encodeVector, finFunctionFinEquiv_apply, d, vx, vy,
          Nat.add_mul, Finset.sum_add_distrib]
        omega
      calc
        #(P.parts.biUnion Finset.restrictedSumset) ≤
            #((Finset.univ : Finset C).image decode) := Finset.card_le_card hsubset
        _ ≤ #(Finset.univ : Finset C) := Finset.card_image_le
        _ = r * (2 * Q) ^ ((n + 1) - 1) := by
          simp [C, Fintype.card_fun]




lemma digit_partition (t : ℕ) (ht : 5 ≤ t) :
    ∃ P : Finpartition (Icc 1 (2 ^ (4 * (2 ^ t) ^ 2))),
      #P.parts = candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) ∧
      20 * #(P.parts.biUnion Finset.restrictedSumset) <
        2 ^ (4 * (2 ^ t) ^ 2) := by
  have hrall : ∀ u : ℕ, 5 ≤ u → 4 + 4 * u ≤ 2 ^ u := by
    intro u hu
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hu
    induction v with
    | zero => norm_num
    | succ v ih =>
      specialize ih (by omega)
      rw [show 5 + (v + 1) = (5 + v) + 1 by omega, pow_succ]
      have hp : 4 ≤ 2 ^ (5 + v) := by
        calc
          4 ≤ 2 ^ 5 := by norm_num
          _ ≤ 2 ^ (5 + v) := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
  have hr : 4 + 4 * t ≤ 2 ^ t := hrall t ht
  let m := 2 ^ t
  let Q := 2 ^ (4 * m)
  let r := 4 + 4 * t
  have hm : 0 < m := by simp [m]
  have hQ : 2 ≤ Q := by
    dsimp [Q]
    exact Nat.one_lt_two_pow (by positivity)
  have heven : 2 ∣ Q := by
    dsimp [Q]
    exact dvd_pow_self 2 (by positivity)
  have hN : Q ^ m = 2 ^ (4 * (2 ^ t) ^ 2) := by
    simp only [Q, m, ← pow_mul]
    congr 1
    ring
  have hpart := complemented_digit_partition Q m r hQ heven (by simpa [m, r])
  rw [hN] at hpart
  obtain ⟨P, hcard, hsum⟩ := hpart
  refine ⟨P, ?_, ?_⟩
  · rw [candidate25_special t ht, hcard]
    simp only [r]
    have hle : 4 + 4 * t ≤ 4 * (2 ^ t) ^ 2 := by
      apply hr.trans
      have hp : 1 ≤ 2 ^ t := one_le_pow₀ (by omega)
      nlinarith
    rw [Nat.pow_div hle (by omega)]
  · calc
      20 * #(P.parts.biUnion Finset.restrictedSumset) ≤
          20 * (r * (2 * Q) ^ (m - 1)) := Nat.mul_le_mul_left 20 hsum
      _ < Q ^ m := by
        have hm6 : 6 ≤ 2 ^ t := by
          calc
            6 ≤ 2 ^ 5 := by norm_num
            _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
        have hten : ∀ n : ℕ, 6 ≤ n → 10 * n < 2 ^ n := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => norm_num
          | succ n hn ih =>
            rw [pow_succ]
            have hp : 10 ≤ 2 ^ n := by
              calc
                10 ≤ 2 ^ 6 := by norm_num
                _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
            omega
        have hcoef : 20 * (4 + 4 * t) < 2 ^ (3 * 2 ^ t + 1) := by
          have hsmall := hten (2 ^ t) hm6
          have hrle : 4 + 4 * t ≤ 2 ^ t := hrall t ht
          have hfirst : 20 * (4 + 4 * t) < 2 ^ (2 ^ t + 1) := by
            rw [pow_succ]
            nlinarith
          exact hfirst.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
        have hmul := Nat.mul_lt_mul_of_pos_right hcoef
          (show 0 < 2 ^ ((4 * 2 ^ t + 1) * (2 ^ t - 1)) by positivity)
        have hmpos : 0 < 2 ^ t := by positivity
        have hexp : (3 * 2 ^ t + 1) + (4 * 2 ^ t + 1) * (2 ^ t - 1) =
            4 * (2 ^ t) ^ 2 := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
          rw [hk]
          simp
          ring
        have hbase : 2 * 2 ^ (4 * 2 ^ t) = 2 ^ (4 * 2 ^ t + 1) := by
          rw [pow_succ]
          omega
        simp only [r, Q, m]
        rw [hbase]
        rw [mul_assoc] at hmul
        rw [← pow_add, hexp] at hmul
        simpa [← pow_mul, pow_two, mul_assoc] using hmul
      _ = 2 ^ (4 * (2 ^ t) ^ 2) := hN




lemma digit_counterexample (t : ℕ) (ht : 5 ≤ t) :
    ¬ Property25 (candidate25 (2 ^ (4 * (2 ^ t) ^ 2)))
        (2 ^ (4 * (2 ^ t) ^ 2)) := by
  intro h
  obtain ⟨P, hcard, hsmall⟩ := digit_partition t ht
  have hsmall' : 10 * #(P.parts.biUnion Finset.restrictedSumset) <
      2 ^ (4 * (2 ^ t) ^ 2) := by omega
  exact (not_le_of_gt hsmall') (h.2.2 P hcard)

private def shift25 (a : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.image (a + ·)

private lemma shift25_injective (a : ℕ) : Function.Injective (shift25 a) := by
  intro s t h
  ext x
  have hmem := Finset.ext_iff.mp h (a + x)
  simpa [shift25] using hmem

private def shiftPartition25 {s : Finset ℕ} (a : ℕ) (P : Finpartition s) :
    Finpartition (shift25 a s) where
  parts := P.parts.image (shift25 a)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, Finset.mem_image]
    rintro A ⟨p, hp, rfl⟩ B ⟨q, hq, rfl⟩ hAB
    rw [Function.onFun, id_eq, Finset.disjoint_left]
    intro z hzp hzq
    change z ∈ shift25 a p at hzp
    change z ∈ shift25 a q at hzq
    rw [shift25, Finset.mem_image] at hzp hzq
    obtain ⟨x, hx, rfl⟩ := hzp
    obtain ⟨y, hy, hxy⟩ := hzq
    have hxy' : x = y := by omega
    subst y
    have hd := P.disjoint hp hq (fun h => hAB (congrArg (shift25 a) h))
    change Disjoint p q at hd
    rw [Finset.disjoint_left] at hd
    exact hd hx hy
  sup_parts := by
    ext x
    simp only [Finset.mem_sup, Finset.mem_image]
    constructor
    · rintro ⟨u, ⟨p, hp, hpu⟩, hu⟩
      subst u
      change x ∈ shift25 a p at hu
      rw [shift25, Finset.mem_image] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      rw [shift25, Finset.mem_image]
      refine ⟨y, ?_, rfl⟩
      rw [← P.sup_parts, Finset.mem_sup]
      exact ⟨p, hp, hy⟩
    · change x ∈ s.image (a + ·) → _
      rw [Finset.mem_image]
      rintro ⟨y, hy, rfl⟩
      rw [← P.sup_parts, Finset.mem_sup] at hy
      obtain ⟨p, hp, hyp⟩ := hy
      refine ⟨shift25 a p, ⟨p, hp, rfl⟩, ?_⟩
      change a + y ∈ shift25 a p
      exact Finset.mem_image.mpr ⟨y, hyp, rfl⟩
  bot_notMem := by
    rw [Finset.mem_image]
    rintro ⟨p, hp, hzero⟩
    have hpzero : p = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      have hm : a + x ∈ shift25 a p := by
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      rw [hzero] at hm
      exact (Finset.notMem_empty _ hm).elim
    subst p
    exact P.bot_notMem hp

private lemma shiftPartition25_card {s : Finset ℕ} (a : ℕ) (P : Finpartition s) :
    #(shiftPartition25 a P).parts = #P.parts := by
  exact Finset.card_image_iff.mpr fun _ _ _ _ h => shift25_injective a h

private def repeatPartition25 {B : ℕ} (q : ℕ) (hB : 0 < B)
    (P : Finpartition (Icc 1 B)) : Finpartition (Icc 1 (q * B)) := by
  let block : Fin q → Finset ℕ := fun i => shift25 (i.1 * B) (Icc 1 B)
  let part : (i : Fin q) → Finpartition (block i) := fun i => shiftPartition25 (i.1 * B) P
  have hind : (Finset.univ : Finset (Fin q)).SupIndep block := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, Finset.mem_univ,
      Function.onFun, id_eq, ne_eq, forall_const]
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [block, shift25, Finset.mem_image, Finset.mem_Icc] at hxi hxj
    obtain ⟨u, ⟨hu1, huB⟩, hux⟩ := hxi
    obtain ⟨v, ⟨hv1, hvB⟩, hvx⟩ := hxj
    have heq : i.1 = j.1 := by nlinarith
    exact hij (Fin.ext heq)
  have hsup : (Finset.univ : Finset (Fin q)).sup block = Icc 1 (q * B) := by
    ext x
    simp only [Finset.mem_sup, Finset.mem_univ, true_and, block, shift25,
      Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨i, y, ⟨hy1, hyB⟩, rfl⟩
      constructor
      · omega
      · have hi := i.isLt
        nlinarith
    · rintro ⟨hx1, hxq⟩
      let i : Fin q := ⟨(x - 1) / B, by
        apply (Nat.div_lt_iff_lt_mul hB).2
        omega⟩
      let y := (x - 1) % B + 1
      refine ⟨i, y, ?_, ?_⟩
      · constructor
        · omega
        · have hm := Nat.mod_lt (x - 1) hB
          omega
      · dsimp [i, y]
        calc
          (x - 1) / B * B + ((x - 1) % B + 1) =
              (x - 1) % B + B * ((x - 1) / B) + 1 := by ac_rfl
          _ = x := by
            calc
              (x - 1) % B + B * ((x - 1) / B) + 1 = (x - 1) + 1 :=
                congrArg (· + 1) (Nat.mod_add_div (x - 1) B)
              _ = x := Nat.sub_add_cancel hx1
  exact {
    parts := (Finset.univ : Finset (Fin q)).biUnion fun i => (part i).parts
    supIndep := Finset.SupIndep.biUnion (by
      change (Finset.univ : Finset (Fin q)).SupIndep
        (fun i => (part i).parts.sup id)
      have heq : (fun i => (part i).parts.sup id) = block := by
        funext i
        exact (part i).sup_parts
      rw [heq]
      exact hind)
      (fun i _ => (part i).supIndep)
    sup_parts := by
      rw [Finset.sup_biUnion]
      calc
        (Finset.univ : Finset (Fin q)).sup (fun i => (part i).parts.sup id) =
            (Finset.univ : Finset (Fin q)).sup block := by
              apply Finset.sup_congr rfl
              intro i _
              exact (part i).sup_parts
        _ = Icc 1 (q * B) := hsup
    bot_notMem := by
      rw [Finset.mem_biUnion]
      push_neg
      exact fun i _ => (part i).bot_notMem }

private lemma repeatPartition25_card_le {B : ℕ} (q : ℕ) (hB : 0 < B)
    (P : Finpartition (Icc 1 B)) :
    #(repeatPartition25 q hB P).parts ≤ q * #P.parts := by
  simp only [repeatPartition25]
  rw [show q * #P.parts = ∑ _i : Fin q, #P.parts by simp]
  calc
    _ ≤ ∑ i : Fin q, #(shiftPartition25 (i.1 * B) P).parts :=
      Finset.card_biUnion_le
    _ = _ := by simp [shiftPartition25_card]

private lemma restrictedSumset_shift25 (a : ℕ) (s : Finset ℕ) :
    (shift25 a s).restrictedSumset = shift25 (2 * a) s.restrictedSumset := by
  ext z
  simp only [Finset.restrictedSumset, Finset.mem_image, Finset.mem_offDiag, shift25,
    Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨⟨u, hu, hux⟩, ⟨v, hv, hvy⟩, hxy⟩, rfl⟩
    subst x
    subst y
    refine ⟨u + v, ⟨u, v, ⟨hu, hv, ?_⟩, rfl⟩, ?_⟩
    · intro huv
      apply hxy
      omega
    · omega
  · rintro ⟨w, ⟨u, v, ⟨hu, hv, huv⟩, rfl⟩, rfl⟩
    refine ⟨a + u, a + v, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact ⟨u, hu, rfl⟩
    · exact ⟨v, hv, rfl⟩
    · intro h
      apply huv
      omega
    · omega

private lemma repeatPartition25_sum_le {B : ℕ} (q : ℕ) (hB : 0 < B)
    (P : Finpartition (Icc 1 B)) :
    #((repeatPartition25 q hB P).parts.biUnion Finset.restrictedSumset) ≤
      q * #(P.parts.biUnion Finset.restrictedSumset) := by
  let U := (Finset.univ : Finset (Fin q)).biUnion fun i =>
    shift25 (2 * (i.1 * B)) (P.parts.biUnion Finset.restrictedSumset)
  have hsub : (repeatPartition25 q hB P).parts.biUnion Finset.restrictedSumset ⊆ U := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    simp only [repeatPartition25, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
    obtain ⟨i, hp⟩ := hp
    change p ∈ P.parts.image (shift25 (i.1 * B)) at hp
    rw [Finset.mem_image] at hp
    obtain ⟨p0, hp0, rfl⟩ := hp
    rw [restrictedSumset_shift25] at hzp
    dsimp [U]
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [shift25, Finset.mem_image] at hzp ⊢
    obtain ⟨w, hw, rfl⟩ := hzp
    refine ⟨w, ?_, rfl⟩
    rw [Finset.mem_biUnion]
    exact ⟨p0, hp0, hw⟩
  calc
    _ ≤ #U := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin q, #(shift25 (2 * (i.1 * B))
        (P.parts.biUnion Finset.restrictedSumset)) := Finset.card_biUnion_le
    _ = q * #(P.parts.biUnion Finset.restrictedSumset) := by
      have hc : ∀ i : Fin q, #(shift25 (2 * (i.1 * B))
          (P.parts.biUnion Finset.restrictedSumset)) =
          #(P.parts.biUnion Finset.restrictedSumset) := by
        intro i
        exact Finset.card_image_iff.mpr fun _ _ _ _ h => Nat.add_left_cancel h
      simp_rw [hc]
      simp


private lemma restrict_partition25 {s t : Finset ℕ} (P : Finpartition s) (ht : t ⊆ s) :
    ∃ Q : Finpartition t,
      #Q.parts ≤ #P.parts ∧
      Q.parts.biUnion Finset.restrictedSumset ⊆
        P.parts.biUnion Finset.restrictedSumset := by
  let raw := P.parts.image (fun p => p ∩ t)
  have hind : raw.SupIndep id := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, raw, Finset.mem_image]
    rintro A ⟨p, hp, rfl⟩ B ⟨q, hq, rfl⟩ hAB
    exact (P.disjoint hp hq (fun h => hAB (congrArg (fun u => u ∩ t) h))).mono
      (Finset.inter_subset_left) (Finset.inter_subset_left)
  have hsup : raw.sup id = t := by
    apply Finset.ext
    intro x
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨u, hu, hxu⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_inter.mp hxu).2
    · intro hxt
      obtain ⟨p, hp, hxp⟩ := P.exists_mem (ht hxt)
      refine ⟨p ∩ t, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
      exact Finset.mem_inter.mpr ⟨hxp, hxt⟩
  let Q : Finpartition t := Finpartition.ofErase raw hind hsup
  refine ⟨Q, ?_, ?_⟩
  · calc
      #Q.parts ≤ #raw := Finset.card_erase_le
      _ ≤ #P.parts := Finset.card_image_le
  · intro z hz
    rw [Finset.mem_biUnion] at hz ⊢
    obtain ⟨u, huQ, hzu⟩ := hz
    change u ∈ (P.parts.image (fun p => p ∩ t)).erase ∅ at huQ
    have huRaw : u ∈ P.parts.image (fun p => p ∩ t) := (Finset.mem_erase.mp huQ).2
    obtain ⟨p, hp, hup⟩ := Finset.mem_image.mp huRaw
    subst u
    refine ⟨p, hp, ?_⟩
    rw [Finset.restrictedSumset] at hzu ⊢
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hzu
    refine Finset.mem_image.mpr ⟨xy, ?_, rfl⟩
    rw [Finset.mem_offDiag] at hxy ⊢
    exact ⟨(Finset.mem_inter.mp hxy.1).1,
      (Finset.mem_inter.mp hxy.2.1).1, hxy.2.2⟩



lemma tiled_digit_partition (t N : ℕ) (ht : 5 ≤ t)
    (hN : 2 ^ (4 * (2 ^ t) ^ 2) ≤ N) :
    ∃ P : Finpartition (Icc 1 N),
      #P.parts ≤ (N / (2 ^ (4 * (2 ^ t) ^ 2)) + 1) *
        candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) ∧
      10 * #(P.parts.biUnion Finset.restrictedSumset) < N := by
  let B := 2 ^ (4 * (2 ^ t) ^ 2)
  let q := N / B + 1
  have hB : 0 < B := by positivity
  obtain ⟨P₀, hPcard, hPsum⟩ := digit_partition t ht
  have hNB : N ≤ q * B := by
    calc
      N = N % B + B * (N / B) := (Nat.mod_add_div N B).symm
      _ = N % B + (N / B) * B := by ac_rfl
      _ ≤ B + (N / B) * B :=
        Nat.add_le_add_right (Nat.le_of_lt (Nat.mod_lt N hB)) _
      _ = q * B := by simp [q]; ring
  have hsub : Icc 1 N ⊆ Icc 1 (q * B) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.trans hNB⟩
  let R := repeatPartition25 q hB P₀
  obtain ⟨P, hPparts, hPsubset⟩ := restrict_partition25 R hsub
  refine ⟨P, ?_, ?_⟩
  · calc
      #P.parts ≤ #R.parts := hPparts
      _ ≤ q * #P₀.parts := repeatPartition25_card_le q hB P₀
      _ = q * candidate25 B := by
        simpa [B] using congrArg (q * ·) hPcard
      _ = (N / (2 ^ (4 * (2 ^ t) ^ 2)) + 1) *
          candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) := by rfl
  · have hsum : #(P.parts.biUnion Finset.restrictedSumset) ≤
        q * #(P₀.parts.biUnion Finset.restrictedSumset) := by
      exact (Finset.card_le_card hPsubset).trans
        (repeatPartition25_sum_le q hB P₀)
    have hq : 0 < q := by simp [q]
    have hqsmall : q * (20 * #(P₀.parts.biUnion Finset.restrictedSumset)) < q * B := by
      apply Nat.mul_lt_mul_of_pos_left
      · simpa [B] using hPsum
      · exact hq
    have hqB : q * B ≤ N + B := by
      simp only [q, Nat.add_mul]
      simpa using Nat.add_le_add_right (Nat.div_mul_le_self N B) B
    calc
      10 * #(P.parts.biUnion Finset.restrictedSumset) ≤
          10 * (q * #(P₀.parts.biUnion Finset.restrictedSumset)) :=
        Nat.mul_le_mul_left 10 hsum
      _ < N := by
        have hBN : B ≤ N := by simpa [B] using hN
        nlinarith


private def scale25 (t : ℕ) : ℕ := 2 ^ (4 * (2 ^ t) ^ 2)



private def level25 (N : ℕ) : ℕ := Nat.log 4 (Nat.log 2 N) - 1

private lemma scale25_exponent (t : ℕ) :
    4 * (2 ^ t) ^ 2 = 4 ^ (t + 1) := by
  conv_lhs =>
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [← pow_mul]
    rw [← pow_add]
  conv_rhs =>
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [← pow_mul]
  congr 1
  omega

private lemma level25_good (N : ℕ) (hL : 4 ^ 6 ≤ Nat.log 2 N) :
    5 ≤ level25 N ∧ scale25 (level25 N) ≤ N := by
  let L := Nat.log 2 N
  let u := Nat.log 4 L
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hu : 6 ≤ u := Nat.le_log_of_pow_le (by omega) (by simpa [L] using hL)
  have ht : level25 N + 1 = u := by
    change u - 1 + 1 = u
    omega
  have hN0 : N ≠ 0 := by
    intro h
    subst N
    simp [L] at hLpos
  have hE : 4 ^ (level25 N + 1) ≤ L := by
    rw [ht]
    exact Nat.pow_log_le_self 4 hLpos.ne'
  constructor
  · change 5 ≤ u - 1
    omega
  · rw [scale25, scale25_exponent]
    exact (Nat.pow_le_pow_right (by omega) hE).trans
      (Nat.pow_log_le_self 2 hN0)

private noncomputable def fallbackPartition25 (N : ℕ) : Finpartition (Icc 1 N) := by
  let s : Setoid ℕ := ⊤
  letI : DecidableRel s.r := Classical.decRel _
  exact Finpartition.ofSetSetoid s _

private noncomputable def selectedPartition25 (N : ℕ) : Finpartition (Icc 1 N) :=
  if h : 5 ≤ level25 N ∧ scale25 (level25 N) ≤ N then
    Classical.choose (tiled_digit_partition (level25 N) N h.1 (by simpa [scale25] using h.2))
  else fallbackPartition25 N

private lemma selectedPartition25_spec (N : ℕ)
    (h : 5 ≤ level25 N ∧ scale25 (level25 N) ≤ N) :
    #(selectedPartition25 N).parts ≤
        (N / scale25 (level25 N) + 1) * candidate25 (scale25 (level25 N)) ∧
      10 * #((selectedPartition25 N).parts.biUnion Finset.restrictedSumset) < N := by
  rw [selectedPartition25, dif_pos h]
  simpa [scale25] using
    (Classical.choose_spec
      (tiled_digit_partition (level25 N) N h.1 (by simpa [scale25] using h.2)))

private lemma linear_le_pow25 (u : ℕ) (hu : 5 ≤ u) : 4 + 4 * u ≤ 2 ^ u := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hu
  induction v with
  | zero => norm_num
  | succ v ih =>
    specialize ih (by omega)
    rw [show 5 + (v + 1) = (5 + v) + 1 by omega, pow_succ]
    have hp : 4 ≤ 2 ^ (5 + v) := by
      calc
        4 ≤ 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (5 + v) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith

set_option maxHeartbeats 800000 in

@[category research open, AMS 5 11]
theorem green_25.upper :
    ∃ (candidateAnswer : ℕ → ℕ),
      let ans := (candidateAnswer : ℕ → ℕ)
    (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧
    (fun N => (ans N : ℝ)) =o[atTop] bestUpper ∧
    ∀ᶠ N in atTop, ¬ Property25 (ans N) N
:= by
  let ans : ℕ → ℕ := fun N => #(selectedPartition25 N).parts
  refine ⟨ans, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (2 ^ (4 ^ 6))] with N hN
    have hL : 4 ^ 6 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) hN
    have hg := level25_good N hL
    have hN1 : 1 ≤ N := by
      calc
        1 ≤ 2 ^ (4 ^ 6) := one_le_pow₀ (by omega)
        _ ≤ N := hN
    constructor
    · change 1 ≤ #(selectedPartition25 N).parts
      exact ((selectedPartition25 N).parts_nonempty (by
        simp [hN1])).card_pos
    · change #(selectedPartition25 N).parts ≤ N
      simpa [Nat.card_Icc] using (selectedPartition25 N).card_parts_le_card
  · rw [Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (64 / c)
    filter_upwards [eventually_ge_atTop (2 ^ (max (4 ^ 6) M))] with N hN
    let L := Nat.log 2 N
    let t := level25 N
    let B := scale25 t
    let D := 2 ^ (4 + 4 * t)
    have hLbig : max (4 ^ 6) M ≤ L := by
      exact Nat.le_log_of_pow_le (by omega) hN
    have hL : 4 ^ 6 ≤ L := (le_max_left _ _).trans hLbig
    have hLM : M ≤ L := (le_max_right _ _).trans hLbig
    have hg : 5 ≤ t ∧ B ≤ N := by
      simpa [L, t, B] using level25_good N (by simpa [L] using hL)
    have hspec := selectedPartition25_spec N (by simpa [t, B] using hg)
    have htpow : 4 + 4 * t ≤ 2 ^ t := linear_le_pow25 t hg.1
    have hd : 4 + 4 * t ≤ 4 * (2 ^ t) ^ 2 := by
      have hp : 1 ≤ 2 ^ t := one_le_pow₀ (by omega)
      nlinarith
    have hcandD : candidate25 B * D = B := by
      rw [show candidate25 B = 2 ^ (4 * (2 ^ t) ^ 2 - (4 + 4 * t)) by
        simpa [B, scale25, t] using candidate25_special t hg.1]
      simp only [D, ← pow_add, Nat.sub_add_cancel hd, B, scale25]
    have hqB : (N / B + 1) * B ≤ 2 * N := by
      calc
        (N / B + 1) * B ≤ N + B := by
          rw [Nat.add_mul]
          simpa using Nat.add_le_add_right (Nat.div_mul_le_self N B) B
        _ ≤ 2 * N := by omega
    have hansD : ans N * D ≤ 2 * N := by
      calc
        ans N * D ≤ ((N / B + 1) * candidate25 B) * D :=
          Nat.mul_le_mul_right D hspec.1
        _ = (N / B + 1) * B := by rw [mul_assoc, hcandD]
        _ ≤ 2 * N := hqB
    let u := Nat.log 4 L
    have hu : 6 ≤ u := Nat.le_log_of_pow_le (by omega) hL
    have htu : t + 1 = u := by
      change u - 1 + 1 = u
      omega
    have hLupper : L < 4 * 4 ^ (t + 1) := by
      have hh := Nat.lt_pow_succ_log_self (by omega : 1 < 4) L
      rw [show Nat.log 4 L = u by rfl, ← htu, pow_succ] at hh
      simpa [mul_comm] using hh
    have hDE : D = (4 ^ (t + 1)) ^ 2 := by
      simp only [D, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega
    have hansL : ans N * L ^ 2 ≤ 32 * N := by
      have hsq : L ^ 2 ≤ 16 * D := by
        rw [hDE]
        nlinarith
      nlinarith
    have hN1 : 1 < N := by
      have hbase : 2 ^ (4 ^ 6) ≤ N :=
        (Nat.pow_le_pow_right (by omega) (le_max_left _ _)).trans hN
      have hpowbig : 1 < 2 ^ (4 ^ 6) := Nat.one_lt_two_pow (by norm_num)
      omega
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
    have hlogle : Real.log (N : ℝ) ≤ 2 * (L : ℝ) := by
      have hpow := Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
      have hcast : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
        exact_mod_cast (Nat.le_of_lt (by simpa [L] using hpow))
      have hh := Real.strictMonoOn_log.monotoneOn
        (show (N : ℝ) ∈ Set.Ioi 0 by
          change (0 : ℝ) < N
          exact_mod_cast (Nat.zero_lt_of_lt hN1))
        (show (2 : ℝ) ^ (L + 1) ∈ Set.Ioi 0 by
          change (0 : ℝ) < (2 : ℝ) ^ (L + 1)
          positivity) hcast
      rw [Real.log_pow] at hh
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at this ⊢
        exact this
      have hLone : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
      calc
        Real.log (N : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * Real.log 2 := hh
        _ ≤ ((L + 1 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ ≤ 2 * (L : ℝ) := by push_cast; nlinarith
    have hcL : 64 < c * (L : ℝ) := by
      have hMc : 64 / c < (M : ℝ) := hM
      have hcpos : (0 : ℝ) < c := hc
      have hML : (M : ℝ) ≤ L := by exact_mod_cast hLM
      apply (div_lt_iff₀ hcpos).mp at hMc
      nlinarith
    have hansreal : (ans N : ℝ) * (L : ℝ) ^ 2 ≤ 32 * (N : ℝ) := by
      exact_mod_cast hansL
    have hmain : (ans N : ℝ) * Real.log (N : ℝ) ≤ c * (N : ℝ) := by
      have hansnonneg : (0 : ℝ) ≤ ans N := by positivity
      have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
      refine le_of_mul_le_mul_right ?_ hLpos
      calc
        ((ans N : ℝ) * Real.log (N : ℝ)) * (L : ℝ) ≤
            ((ans N : ℝ) * (2 * (L : ℝ))) * (L : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogle hansnonneg) hLpos.le
        _ = 2 * ((ans N : ℝ) * (L : ℝ) ^ 2) := by ring
        _ ≤ 64 * (N : ℝ) := by nlinarith
        _ ≤ (c * (N : ℝ)) * (L : ℝ) := by
          have hh := mul_le_mul_of_nonneg_right hcL.le (show (0 : ℝ) ≤ N by positivity)
          nlinarith
    rw [show bestUpper N = (N : ℝ) / Real.log (N : ℝ) by rfl]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_pos (div_pos (by positivity) hlogpos)]
    have hdiv : (ans N : ℝ) ≤ (c * (N : ℝ)) / Real.log (N : ℝ) :=
      (le_div_iff₀ hlogpos).2 hmain
    calc
      (ans N : ℝ) ≤ (c * (N : ℝ)) / Real.log (N : ℝ) := hdiv
      _ = c * ((N : ℝ) / Real.log (N : ℝ)) := by ring
  · filter_upwards [eventually_ge_atTop (2 ^ (4 ^ 6))] with N hN
    have hL : 4 ^ 6 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) hN
    have hg := level25_good N hL
    intro hprop
    have hsmall := (selectedPartition25_spec N hg).2
    exact (not_le_of_gt hsmall) (hprop.2.2 (selectedPartition25 N) rfl)
end Green25
