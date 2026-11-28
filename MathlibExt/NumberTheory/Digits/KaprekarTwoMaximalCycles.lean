/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.KaprekarMaximalPeriod
import Mathlib.Data.Fintype.Prod
import MathlibExt.NumberTheory.Digits.KaprekarStructuralClassification

/-!
# Two Kaprekar cycles of projective-order length

On the doubling orbit of the sign class of `1`, the unordered pairs at cyclic distances
`1` and `2` form two disjoint orbits of full length as soon as the orbit has length at least `5`.
The structural conjugacy carries these orbits to the four-digit Kaprekar map.

## References

* Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar Dynamics in
  Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, pp. 1–21. We use the
  conjugacy of Theorem 1 and the same-cycle part of the proof of Theorem 24 to prove
  Corollary 27(i) directly, without the full cycle-count formula.
-/

namespace MetaMathlibExt

open Function

namespace two_mul_projectiveOrderTwo_le_card_kaprekar_cycles

private def signClass {B : ℕ} (x : ZMod B) : Finset (ZMod B) := {x, -x}

private def doubleClass {B : ℕ} (C : Finset (ZMod B)) : Finset (ZMod B) := C.image (· * 2)

private def doublePair {B : ℕ} (S : Finset (Finset (ZMod B))) : Finset (Finset (ZMod B)) :=
  S.image doubleClass

private theorem doubleClass_signClass {B : ℕ} (x : ZMod B) :
    doubleClass (signClass x) = signClass (x * 2) := by
  simp [doubleClass, signClass, neg_mul]

private theorem signClass_eq_one_iff {B : ℕ} {x : ZMod B} :
    signClass x = signClass 1 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    have hx : x ∈ signClass 1 := h ▸ Finset.mem_insert_self _ _
    simpa [signClass] using hx
  · rintro (rfl | rfl)
    · rfl
    · simp [signClass, Finset.pair_comm]

private theorem iterate_signClass_one (B n : ℕ) :
    (doubleClass (B := B))^[n] (signClass 1) = signClass ((2 : ZMod B) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', ih, doubleClass_signClass, pow_succ]

private theorem projectiveOrderTwo_spec {B : ℕ} [NeZero B] (hB : Odd B) :
    0 < projectiveOrderTwo B ∧
      ((2 : ZMod B) ^ projectiveOrderTwo B = 1 ∨ (2 : ZMod B) ^ projectiveOrderTwo B = -1) := by
  change projectiveOrderTwo B ∈
    {n : ℕ | 0 < n ∧ ((2 : ZMod B) ^ n = 1 ∨ (2 : ZMod B) ^ n = -1)}
  apply Nat.sInf_mem
  let u := ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hB)
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_finite u).exists_pow_eq_one
  exact ⟨n, hn, Or.inl (by simpa [u, ZMod.coe_unitOfCoprime] using congrArg Units.val hpow)⟩

private theorem five_le_projectiveOrderTwo {B : ℕ} [NeZero B] (hB : Odd B) (hB17 : 17 < B) :
    5 ≤ projectiveOrderTwo B := by
  obtain ⟨hpos, hpow⟩ := projectiveOrderTwo_spec hB
  by_contra! hsmall
  let n := (2 : ℕ) ^ projectiveOrderTwo B
  have hn : 1 < n := by
    simpa [n] using (Nat.pow_lt_pow_right (by decide : 1 < 2) hpos)
  have hle : n ≤ 16 := Nat.pow_le_pow_right (by decide) (by omega : projectiveOrderTwo B ≤ 4)
  have hnB : n < B := by omega
  have hcast : (n : ZMod B) = (2 : ZMod B) ^ projectiveOrderTwo B := by simp [n]
  rw [← hcast] at hpow
  rcases hpow with h | h
  · have heq := (ZMod.natCast_eq_natCast_iff' n 1 B).mp (by simpa only [Nat.cast_one] using h)
    rw [Nat.mod_eq_of_lt hnB, Nat.mod_eq_of_lt (by omega : 1 < B)] at heq
    omega
  · have hz : ((n + 1 : ℕ) : ZMod B) = 0 := by simp [h]
    have := Nat.le_of_dvd (Nat.succ_pos n) ((ZMod.natCast_eq_zero_iff (n + 1) B).mp hz)
    omega

private theorem minimalPeriod_signClass_one {B : ℕ} [NeZero B] (hB : Odd B) :
    minimalPeriod (doubleClass (B := B)) (signClass 1) = projectiveOrderTwo B := by
  obtain ⟨hpos, hpow⟩ := projectiveOrderTwo_spec hB
  have hperiod : IsPeriodicPt (doubleClass (B := B)) (projectiveOrderTwo B) (signClass 1) := by
    change _ = _
    rw [iterate_signClass_one, signClass_eq_one_iff]
    exact hpow
  refine le_antisymm (hperiod.minimalPeriod_le hpos)
    (Nat.sInf_le ⟨hperiod.minimalPeriod_pos hpos, ?_⟩)
  have h := iterate_minimalPeriod (f := doubleClass (B := B)) (x := signClass 1)
  rwa [iterate_signClass_one, signClass_eq_one_iff] at h

private theorem signClass_pow_eq_iff {B i j : ℕ} [NeZero B] (hB : Odd B) :
    signClass ((2 : ZMod B) ^ i) = signClass (2 ^ j) ↔ i ≡ j [MOD projectiveOrderTwo B] := by
  let f := doubleClass (B := B)
  let x := signClass (1 : ZMod B)
  have hp : minimalPeriod f x = projectiveOrderTwo B := minimalPeriod_signClass_one hB
  have hpos : 0 < minimalPeriod f x := hp.symm ▸ (projectiveOrderTwo_spec hB).1
  change _ ↔ i % projectiveOrderTwo B = j % projectiveOrderTwo B
  rw [← hp, ← iterate_signClass_one, ← iterate_signClass_one,
    ← iterate_mod_minimalPeriod_eq (f := f) (x := x) (n := i),
    ← iterate_mod_minimalPeriod_eq (f := f) (x := x) (n := j)]
  exact iterate_eq_iterate_iff_of_lt_minimalPeriod (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)

private def orbitPair (B i d : ℕ) : Finset (Finset (ZMod B)) :=
  {signClass ((2 : ZMod B) ^ i), signClass (2 ^ (i + d))}

private theorem iterate_orbitPair (B i d n : ℕ) :
    (doublePair (B := B))^[n] (orbitPair B i d) = orbitPair B (i + n) d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    simp only [doublePair, orbitPair, Finset.image_insert, Finset.image_singleton,
      doubleClass_signClass, ← pow_succ, add_right_comm (i + n) d 1, ← Nat.add_assoc]

private theorem orbitPair_distinct {B i d : ℕ} [NeZero B] (hB : Odd B)
    (hd : 0 < d) (hdL : d < projectiveOrderTwo B) :
    signClass ((2 : ZMod B) ^ i) ≠ signClass (2 ^ (i + d)) := by
  intro heq
  have hdvd := Nat.left_modEq_add_iff.mp ((signClass_pow_eq_iff hB).mp heq)
  exact hdL.not_ge (Nat.le_of_dvd hd hdvd)

private theorem orbitPair_admissible {B i d : ℕ} [NeZero B] (hB : Odd B) (hB17 : 17 < B)
    (hd₁ : 0 < d) (hd₂ : d ≤ 2) :
    (orbitPair B i d).card = 2 ∧
      ∀ C ∈ orbitPair B i d, ∃ x : ZMod B, x ≠ 0 ∧ C = {x, -x} := by
  have : Fact (1 < B) := ⟨by omega⟩
  have htwo : IsUnit (2 : ZMod B) :=
    (ZMod.isUnit_iff_coprime 2 B).mpr (Nat.coprime_two_left.mpr hB)
  have hL := five_le_projectiveOrderTwo hB hB17
  have hne := orbitPair_distinct (i := i) hB hd₁ (by omega)
  refine ⟨by simp [orbitPair, hne], ?_⟩
  intro C hC
  simp only [orbitPair, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl
  · exact ⟨_, (htwo.pow i).ne_zero, rfl⟩
  · exact ⟨_, (htwo.pow (i + d)).ne_zero, rfl⟩

private theorem orbitPair_eq {B i j d e : ℕ} [NeZero B] (hB : Odd B)
    (hL : 5 ≤ projectiveOrderTwo B) (hd₁ : 0 < d) (hd₂ : d ≤ 2) (he₁ : 0 < e) (he₂ : e ≤ 2)
    (h : orbitPair B i d = orbitPair B j e) : i ≡ j [MOD projectiveOrderTwo B] ∧ d = e := by
  have hmem (k : ℕ) : signClass ((2 : ZMod B) ^ k) ∈ orbitPair B i d →
      k ≡ j [MOD projectiveOrderTwo B] ∨ k ≡ j + e [MOD projectiveOrderTwo B] := by
    rw [h]
    simp only [orbitPair, Finset.mem_insert, Finset.mem_singleton, signClass_pow_eq_iff hB,
      imp_self]
  have hi := hmem i (by simp [orbitPair])
  have hid := hmem (i + d) (by simp [orbitPair])
  have hne : ¬ i ≡ i + d [MOD projectiveOrderTwo B] := fun hc =>
    orbitPair_distinct hB hd₁ (by omega) ((signClass_pow_eq_iff hB).mpr hc)
  rcases hi with hij | hije
  · have hde := hij.add_left_cancel (hid.resolve_left (fun hc => hne (hij.trans hc.symm)))
    exact ⟨hij, (Nat.mod_eq_of_lt (by omega : d < projectiveOrderTwo B)).symm.trans
      (Nat.mod_eq_of_modEq hde (by omega))⟩
  · -- Exchanging the two endpoints would make the positive distance `e + d` a multiple of L.
    have hdj := hid.resolve_right (fun hc => hne (hije.trans hc.symm))
    have hswap := hdj.symm.trans (hije.add_right d)
    rw [add_assoc, Nat.left_modEq_add_iff] at hswap
    exact False.elim ((by omega : e + d < projectiveOrderTwo B).not_ge
      (Nat.le_of_dvd (by omega) hswap))

private theorem minimalPeriod_orbitPair {B i d : ℕ} [NeZero B] (hB : Odd B) (hB17 : 17 < B)
    (hd₁ : 0 < d) (hd₂ : d ≤ 2) :
    minimalPeriod (doublePair (B := B)) (orbitPair B i d) = projectiveOrderTwo B := by
  obtain ⟨hpos, hle⟩ := projective_doubling_minimalPeriod_le_projectiveOrderTwo B hB
    (by omega) _ (orbitPair_admissible hB hB17 hd₁ hd₂)
  have hfix := iterate_minimalPeriod (f := doublePair (B := B)) (x := orbitPair B i d)
  rw [iterate_orbitPair] at hfix
  have hmod := (orbitPair_eq hB (five_le_projectiveOrderTwo hB hB17) hd₁ hd₂ hd₁ hd₂ hfix).1
  exact le_antisymm hle (Nat.le_of_dvd hpos (Nat.add_modEq_left_iff.mp hmod))

end two_mul_projectiveOrderTwo_le_card_kaprekar_cycles

open two_mul_projectiveOrderTwo_le_card_kaprekar_cycles

/-- **At least two Kaprekar cycles whose length is the projective order of 2.** Let $\lambda(B)$
denote the projective order of $2$ modulo $B$. For every odd base $B > 17$, at least $2\lambda(B)$
points of the state space $X_B$ have minimal period exactly $\lambda(B)$ under the four-digit
Kaprekar map $K_B$.

Each terminal cycle of $K_B$ of length $\lambda(B)$ consists of $\lambda(B)$ such points, so this
says that $K_B$ has at least two terminal cycles of length $\lambda(B)$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 27 (i) (`jis-2026-26.4.7-cor-27`). -/
public theorem two_mul_projectiveOrderTwo_le_card_kaprekar_cycles (B : ℕ)
    (hB : Odd B) (hB3 : 17 < B) :
    2 * projectiveOrderTwo B ≤
      ((kaprekarFourDigitStates B).filter fun d =>
        Function.minimalPeriod (kaprekarFourDigitStep B) d = projectiveOrderTwo B).card := by
  classical
  have : NeZero B := ⟨by omega⟩
  let L := projectiveOrderTwo B
  have hL : 5 ≤ L := five_le_projectiveOrderTwo hB hB3
  obtain ⟨hstable, -, -, -, e, he, hconj⟩ :=
    four_digit_kaprekar_structural_classification B hB (by omega)
  have hmaps : Set.MapsTo (kaprekarFourDigitStep B) _ _ := hstable
  have heinj : Injective (fun x => (e x).val) := fun _ _ h => e.injective (Subtype.ext h)
  have hsem : Semiconj (fun x => (e x).val) (hmaps.restrict (kaprekarFourDigitStep B) _ _)
      (doublePair (B := B)) := fun x =>
    (hconj x).trans (congrArg (doublePair (B := B)) (he x).symm)
  have hperiod (x : _) : minimalPeriod (kaprekarFourDigitStep B) x.val =
      minimalPeriod (doublePair (B := B)) (e x).val := by
    apply minimalPeriod_eq_minimalPeriod_iff.mpr
    intro n
    change (kaprekarFourDigitStep B)^[n] x.val = x.val ↔
      (doublePair (B := B))^[n] (e x).val = (e x).val
    rw [← hsem.iterate_right n x, heinj.eq_iff, ← hmaps.coe_iterate_restrict x n]
    exact Subtype.ext_iff.symm
  let pull (p : Fin L × Fin 2) := e.symm
    ⟨orbitPair B p.1 (p.2.val + 1),
      orbitPair_admissible hB hB3 (by omega) (by have := p.2.isLt; omega)⟩
  have hpull (p : Fin L × Fin 2) : (e (pull p)).val = orbitPair B p.1 (p.2.val + 1) :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hinj : Injective (fun p => (pull p).val) := by
    intro p q h
    have heq := congrArg (fun x => (e x).val) (Subtype.ext h : pull p = pull q)
    rw [hpull p, hpull q] at heq
    have hp := p.2.isLt
    have hq := q.2.isLt
    obtain ⟨hmod, hoffset⟩ := orbitPair_eq hB hL (by omega) (by omega) (by omega) (by omega) heq
    refine Prod.ext (Fin.ext ?_) (Fin.ext (by omega))
    change p.1.val % L = q.1.val % L at hmod
    simpa only [Nat.mod_eq_of_lt p.1.isLt, Nat.mod_eq_of_lt q.1.isLt] using hmod
  let emb : Fin L × Fin 2 ↪ ℕ × ℕ := ⟨fun p => (pull p).val, hinj⟩
  calc
    2 * L = (Finset.univ.map emb).card := by simp [Fintype.card_prod, Nat.mul_comm]
    _ ≤ _ := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hx
      have hstate := (pull p).property.1
      change 1 ≤ (pull p).val.1 ∧ (pull p).val.1 < B ∧ (pull p).val.2 ≤ (pull p).val.1 at hstate
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simp only [emb, Function.Embedding.coeFn_mk, kaprekarFourDigitStates, Finset.mem_filter,
          Finset.mem_product, Finset.mem_range]
        omega
      · change minimalPeriod (kaprekarFourDigitStep B) (pull p).val = L
        rw [hperiod, hpull]
        exact minimalPeriod_orbitPair hB hB3 (by omega) (by have := p.2.isLt; omega)

end MetaMathlibExt
