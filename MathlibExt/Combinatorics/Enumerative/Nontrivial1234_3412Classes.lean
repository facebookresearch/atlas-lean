/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Relation
import all MathlibExt.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Nontrivial {1234, 3412}-equivalence classes

The number of nontrivial classes of `S_n` under the {1234, 3412}-replacement move is
`(n^3 + 6n^2 - 55n + 54)/6` for `n ≥ 7`. The definitions and the structural part of the proof
are in `MathlibExt.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Basic`, imported with
`import all` because they are private; this module adds the kernel-checked finite certificates
and the final count.
-/

namespace MetaMathlibExt

private def ntCode {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ :=
  List.ofFn fun i => (σ i).val

private lemma ntCode_getD {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) (hi : i < n) :
    (ntCode σ).getD i 0 = (σ ⟨i, hi⟩).val := by
  rw [List.getD_eq_getElem]
  · simp [ntCode]
  · simpa [ntCode] using hi

private lemma ntCode_injective {n : ℕ} :
    Function.Injective (ntCode : Equiv.Perm (Fin n) → List ℕ) := by
  intro σ τ h
  apply Equiv.Perm.ext
  intro i
  apply Fin.ext
  have hf : (fun i : Fin n => (σ i).val) = fun i : Fin n => (τ i).val :=
    List.ofFn_injective h
  exact congrFun hf i

private lemma ntCode_mem_permutations' {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ntCode σ ∈ List.permutations' (List.range n) := by
  rw [List.mem_permutations']
  have hnodup : (ntCode σ).Nodup := by
    unfold ntCode
    apply List.nodup_ofFn.mpr
    intro i j h
    exact σ.injective (Fin.ext h)
  apply (List.perm_ext_iff_of_nodup hnodup List.nodup_range).2
  intro a
  unfold ntCode
  rw [List.mem_ofFn']
  constructor
  · rintro ⟨i, rfl⟩
    exact List.mem_range.mpr (σ i).is_lt
  · intro ha
    have ha' := List.mem_range.mp ha
    obtain ⟨i, hi⟩ := σ.surjective ⟨a, ha'⟩
    exact ⟨i, congrArg Fin.val hi⟩

private lemma ntExists_perm_code {n : ℕ} {s : List ℕ}
    (hs : s ∈ List.permutations' (List.range n)) :
    ∃ σ : Equiv.Perm (Fin n), ntCode σ = s := by
  have hp : s.Perm (List.range n) := List.mem_permutations'.mp hs
  have hlen : s.length = n := by simpa using hp.length_eq
  have hnodup : s.Nodup := hp.nodup_iff.mpr List.nodup_range
  let idx : Fin n → Fin s.length := fun i => ⟨i.val, by rw [hlen]; exact i.is_lt⟩
  let f : Fin n → Fin n := fun i =>
    ⟨s.get (idx i), List.mem_range.mp (hp.mem_iff.mp (s.get_mem (idx i)))⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hget : s.get (idx i) = s.get (idx j) := congrArg Fin.val hij
    have hidx : idx i = idx j := hnodup.get_inj_iff.mp hget
    apply Fin.ext
    simpa only [idx] using congrArg Fin.val hidx
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_⟩
  apply List.ext_getElem
  · simpa [ntCode] using hlen.symm
  · intro i hiCode hiS
    have hi : i < n := by simpa [ntCode] using hiCode
    simp only [ntCode, List.getElem_ofFn]
    change (f ⟨i, hi⟩).val = s[i]
    rfl

private noncomputable def ntPermOfCode {n : ℕ} (s : List ℕ)
    (hs : s ∈ List.permutations' (List.range n)) : Equiv.Perm (Fin n) :=
  Classical.choose (ntExists_perm_code hs)

private lemma ntCode_permOfCode {n : ℕ} (s : List ℕ)
    (hs : s ∈ List.permutations' (List.range n)) :
    ntCode (ntPermOfCode s hs) = s :=
  Classical.choose_spec (ntExists_perm_code hs)

private def ntQuads (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    (List.range n).flatMap fun c => (List.range n).filterMap fun d =>
      if a < b ∧ b < c ∧ c < d then some (a, b, c, d) else none

private def ntHasPatB (q : List (ℕ × ℕ × ℕ × ℕ)) (s : List ℕ) : Bool :=
  q.any fun (a, b, c, d) =>
    let x := s.getD a 0
    let y := s.getD b 0
    let z := s.getD c 0
    let w := s.getD d 0
    (x < y && y < z && z < w) || (z < w && w < x && x < y)

private def ntSemiVal (n j i : ℕ) : ℕ :=
  (j + n - 1 - i) % n

private def ntInTB (n : ℕ) (s : List ℕ) : Bool :=
  (List.range n).any fun j => (List.range n).any fun p =>
    (List.range n).any fun q => p != q && (List.range n).all fun i =>
      s.getD i 0 == if i = p then ntSemiVal n j q
        else if i = q then ntSemiVal n j p else ntSemiVal n j i

private def ntIsGB (n : ℕ) (q : List (ℕ × ℕ × ℕ × ℕ)) (s : List ℕ) : Bool :=
  s.headD 0 != n - 1 && s.getLastD 0 != 0 && ntHasPatB q s && !ntInTB n s

private def ntNbrAt (s : List ℕ) (q : ℕ × ℕ × ℕ × ℕ) : Option (List ℕ) :=
  let (a, b, c, d) := q
  let x := s.getD a 0
  let y := s.getD b 0
  let z := s.getD c 0
  let w := s.getD d 0
  if (x < y && y < z && z < w) || (z < w && w < x && x < y) then
    some (((((s.set a z).set c x).set b w).set d y))
  else none

private def ntNbrs (q : List (ℕ × ℕ × ℕ × ℕ)) (s : List ℕ) : List (List ℕ) :=
  q.filterMap (ntNbrAt s)

private def ntFact : ℕ → ℕ
  | 0 => 1
  | k + 1 => (k + 1) * ntFact k

private def ntLehmer : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.countP (· < x)) * ntFact xs.length + ntLehmer xs

private lemma ntQuad_mem {n : ℕ} {a b c d : Fin n}
    (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val) :
    (a.val, b.val, c.val, d.val) ∈ ntQuads n := by
  simp [ntQuads, a.is_lt, b.is_lt, c.is_lt, d.is_lt, hab, hbc, hcd]

private lemma nt_mem_quads_iff {n a b c d : ℕ} :
    (a, b, c, d) ∈ ntQuads n ↔
      a < n ∧ b < n ∧ c < n ∧ d < n ∧ a < b ∧ b < c ∧ c < d := by
  simp [ntQuads]

private lemma ntHasPatB_of_pat {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : ntPat n σ) : ntHasPatB (ntQuads n) (ntCode σ) = true := by
  unfold ntHasPatB
  rw [List.any_eq_true]
  rcases hσ with ⟨a, b, c, d, hab, hbc, hcd, hvab, hvbc, hvcd⟩ |
    ⟨a, b, c, d, hab, hbc, hcd, hvcd, hvda, hvab⟩
  · refine ⟨(a.val, b.val, c.val, d.val), ntQuad_mem hab hbc hcd, ?_⟩
    dsimp only
    rw [ntCode_getD σ a.val a.is_lt, ntCode_getD σ b.val b.is_lt,
      ntCode_getD σ c.val c.is_lt, ntCode_getD σ d.val d.is_lt]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨⟨hvab, hvbc⟩, hvcd⟩
  · refine ⟨(a.val, b.val, c.val, d.val), ntQuad_mem hab hbc hcd, ?_⟩
    dsimp only
    rw [ntCode_getD σ a.val a.is_lt, ntCode_getD σ b.val b.is_lt,
      ntCode_getD σ c.val c.is_lt, ntCode_getD σ d.val d.is_lt]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨⟨hvcd, hvda⟩, hvab⟩

private lemma ntHasPatB_sound {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : ntHasPatB (ntQuads n) (ntCode σ) = true) : ntPat n σ := by
  unfold ntHasPatB at hσ
  rw [List.any_eq_true] at hσ
  obtain ⟨⟨a, b, c, d⟩, hquad, hpat⟩ := hσ
  obtain ⟨ha, hb, hc, hd, hab, hbc, hcd⟩ := nt_mem_quads_iff.mp hquad
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpat
  rw [ntCode_getD σ a ha, ntCode_getD σ b hb,
    ntCode_getD σ c hc, ntCode_getD σ d hd] at hpat
  rcases hpat with h1234 | h3412
  · exact Or.inl ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩,
      hab, hbc, hcd, h1234.1.1, h1234.1.2, h1234.2⟩
  · exact Or.inr ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩,
      hab, hbc, hcd, h3412.1.1, h3412.1.2, h3412.2⟩

private lemma ntSemiVal_eq_beta {n j i : ℕ} (hj : j + 1 ≤ n) (hi : i < n) :
    ntSemiVal n j i = ((ntBeta n j hj) ⟨i, hi⟩).val := by
  rw [ntBeta_val]
  unfold ntSemiVal
  by_cases hij : i < j
  · rw [ite_eq_left hij]
    have heq : j + n - 1 - i = n + (j - 1 - i) := by omega
    have ha : j - 1 - i < n := by omega
    rw [heq, Nat.add_mod]
    simp only [Nat.mod_self, zero_add, Nat.mod_eq_of_lt ha]
  · rw [ite_eq_right hij]
    have hlt : j + n - 1 - i < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    change j + n - 1 - i = n + j - 1 - i
    omega

private lemma ntInTB_sound {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ntInTB n (ntCode σ) = true) :
    ∃ j : ℕ, ∃ hj : j + 1 ≤ n, σ ∈ ntT n j hj := by
  unfold ntInTB at h
  rw [List.any_eq_true] at h
  obtain ⟨j, hjmem, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨p, hpmem, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨q, hqmem, h⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpq, hall⟩ := h
  have hjlt := List.mem_range.mp hjmem
  have hplt := List.mem_range.mp hpmem
  have hqlt := List.mem_range.mp hqmem
  have hjn : j + 1 ≤ n := by omega
  have hpq' : p ≠ q := by
    intro heq
    subst q
    simp at hpq
  let P : Fin n := ⟨p, hplt⟩
  let Q : Fin n := ⟨q, hqlt⟩
  have hPQ : P ≠ Q := by
    intro heq
    exact hpq' (congrArg Fin.val heq)
  refine ⟨j, hjn, P, Q, hPQ, ?_⟩
  apply Equiv.Perm.ext
  intro i
  apply Fin.ext
  rw [Equiv.Perm.mul_apply]
  by_cases hiP : i = P
  · subst i
    rw [Equiv.swap_apply_left]
    have heq := (List.all_eq_true.mp hall) p hpmem
    rw [beq_iff_eq] at heq
    rw [ntCode_getD σ p hplt, ite_eq_left rfl,
      ntSemiVal_eq_beta hjn hqlt] at heq
    exact heq
  · by_cases hiQ : i = Q
    · subst i
      rw [Equiv.swap_apply_right]
      have heq := (List.all_eq_true.mp hall) q hqmem
      rw [beq_iff_eq] at heq
      have hqp : q ≠ p := Ne.symm hpq'
      rw [ntCode_getD σ q hqlt, ite_eq_right hqp, ite_eq_left rfl,
        ntSemiVal_eq_beta hjn hplt] at heq
      exact heq
    · rw [Equiv.swap_apply_of_ne_of_ne hiP hiQ]
      have heq := (List.all_eq_true.mp hall) i.val
        (List.mem_range.mpr i.is_lt)
      rw [beq_iff_eq] at heq
      have hip : i.val ≠ p := fun heq' => hiP (Fin.ext heq')
      have hiq : i.val ≠ q := fun heq' => hiQ (Fin.ext heq')
      rw [ntCode_getD σ i.val i.is_lt, ite_eq_right hip, ite_eq_right hiq,
        ntSemiVal_eq_beta hjn i.is_lt] at heq
      exact heq

private lemma ntIsGB_of_memG7 {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ ntG 6) :
    ntIsGB 7 (ntQuads 7) (ntCode σ) = true := by
  simp only [ntIsGB, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, ntHasPatB_of_pat hσ.2.1⟩, ?_⟩
  · apply bne_iff_ne.mpr
    simp only [ntCode, List.ofFn_succ, List.headD_cons]
    intro heq
    apply hσ.1.1
    apply Fin.ext
    simpa using heq
  · apply bne_iff_ne.mpr
    simp only [ntCode]
    rw [show (List.ofFn fun i : Fin 7 => (σ i).val).getLastD 0 =
      (σ (Fin.last 6)).val by simp [List.ofFn_succ]]
    intro heq
    apply hσ.1.2
    apply Fin.ext
    exact heq
  · apply Bool.eq_false_iff.mpr
    intro hT
    obtain ⟨j, hj, hσT⟩ := ntInTB_sound hT
    exact hσ.2.2 j hj ⟨hσT, hσ.2.1⟩

private lemma ntIsGB_of_memG8 {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ ntG 7) :
    ntIsGB 8 (ntQuads 8) (ntCode σ) = true := by
  simp only [ntIsGB, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, ntHasPatB_of_pat hσ.2.1⟩, ?_⟩
  · apply bne_iff_ne.mpr
    simp only [ntCode, List.ofFn_succ, List.headD_cons]
    intro heq
    apply hσ.1.1
    apply Fin.ext
    simpa using heq
  · apply bne_iff_ne.mpr
    simp only [ntCode]
    rw [show (List.ofFn fun i : Fin 8 => (σ i).val).getLastD 0 =
      (σ (Fin.last 7)).val by simp [List.ofFn_succ]]
    intro heq
    apply hσ.1.2
    apply Fin.ext
    exact heq
  · apply Bool.eq_false_iff.mpr
    intro hT
    obtain ⟨j, hj, hσT⟩ := ntInTB_sound hT
    exact hσ.2.2 j hj ⟨hσT, hσ.2.1⟩

private lemma ntCode_double_swap {n : ℕ} (σ : Equiv.Perm (Fin n))
    {a b c d : Fin n} (hab : a.val < b.val) (hbc : b.val < c.val)
    (hcd : c.val < d.val) :
    ntCode (σ * Equiv.swap a c * Equiv.swap b d) =
      ((((ntCode σ).set a.val (σ c).val).set c.val (σ a).val).set b.val
        (σ d).val).set d.val (σ b).val := by
  apply List.ext_getElem
  · simp [ntCode]
  · intro i hi₁ hi₂
    have hi : i < n := by simpa [ntCode] using hi₁
    have hac : a ≠ c := by
      intro h
      subst c
      omega
    have had : a ≠ d := by
      intro h
      subst d
      omega
    have hbc' : b ≠ c := by
      intro h
      subst c
      omega
    have hbd : b ≠ d := by
      intro h
      subst d
      omega
    have hcd' : c ≠ d := by
      intro h
      subst d
      omega
    have hab' : a ≠ b := by
      intro h
      subst b
      omega
    simp only [List.getElem_set]
    simp only [ntCode, List.getElem_ofFn]
    simp only [Equiv.Perm.mul_apply]
    by_cases hia : i = a.val
    · have hiA : (⟨i, hi⟩ : Fin n) = a := Fin.ext hia
      subst hiA
      rw [Equiv.swap_apply_of_ne_of_ne hab' had, Equiv.swap_apply_left]
      split_ifs <;> try omega
    · by_cases hib : i = b.val
      · have hiB : (⟨i, hi⟩ : Fin n) = b := Fin.ext hib
        subst hiB
        rw [Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hcd')]
        split_ifs <;> try omega
      · by_cases hic : i = c.val
        · have hiC : (⟨i, hi⟩ : Fin n) = c := Fin.ext hic
          subst hiC
          rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hbc') hcd',
            Equiv.swap_apply_right]
          split_ifs <;> try omega
        · by_cases hid : i = d.val
          · have hiD : (⟨i, hi⟩ : Fin n) = d := Fin.ext hid
            subst hiD
            rw [Equiv.swap_apply_right,
              Equiv.swap_apply_of_ne_of_ne (Ne.symm hab') hbc']
            split_ifs <;> try omega
          · have hiA : (⟨i, hi⟩ : Fin n) ≠ a := fun h => hia (congrArg Fin.val h)
            have hiB : (⟨i, hi⟩ : Fin n) ≠ b := fun h => hib (congrArg Fin.val h)
            have hiC : (⟨i, hi⟩ : Fin n) ≠ c := fun h => hic (congrArg Fin.val h)
            have hiD : (⟨i, hi⟩ : Fin n) ≠ d := fun h => hid (congrArg Fin.val h)
            rw [Equiv.swap_apply_of_ne_of_ne hiB hiD,
              Equiv.swap_apply_of_ne_of_ne hiA hiC]
            simp only [ite_eq_right (Ne.symm hid), ite_eq_right (Ne.symm hib),
              ite_eq_right (Ne.symm hic), ite_eq_right (Ne.symm hia)]

private lemma ntNbrs_sound {n : ℕ} {σ : Equiv.Perm (Fin n)} {t : List ℕ}
    (ht : t ∈ ntNbrs (ntQuads n) (ntCode σ)) :
    ∃ τ : Equiv.Perm (Fin n), ntCode τ = t ∧
      (ntMove n σ τ ∨ ntMove n τ σ) := by
  unfold ntNbrs at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨⟨a, b, c, d⟩, hquad, hstep⟩ := ht
  unfold ntNbrAt at hstep
  obtain ⟨ha, hb, hc, hd, hab, hbc, hcd⟩ := nt_mem_quads_iff.mp hquad
  have hpat :
      (((ntCode σ).getD a 0 < (ntCode σ).getD b 0 &&
          (ntCode σ).getD b 0 < (ntCode σ).getD c 0 &&
          (ntCode σ).getD c 0 < (ntCode σ).getD d 0) ||
        ((ntCode σ).getD c 0 < (ntCode σ).getD d 0 &&
          (ntCode σ).getD d 0 < (ntCode σ).getD a 0 &&
          (ntCode σ).getD a 0 < (ntCode σ).getD b 0)) = true := by
    by_contra hfalse
    have heq :
        (((ntCode σ).getD a 0 < (ntCode σ).getD b 0 &&
            (ntCode σ).getD b 0 < (ntCode σ).getD c 0 &&
            (ntCode σ).getD c 0 < (ntCode σ).getD d 0) ||
          ((ntCode σ).getD c 0 < (ntCode σ).getD d 0 &&
            (ntCode σ).getD d 0 < (ntCode σ).getD a 0 &&
            (ntCode σ).getD a 0 < (ntCode σ).getD b 0)) = false :=
      Bool.eq_false_iff.mpr hfalse
    simp only [heq, Bool.false_eq_true, ↓reduceIte] at hstep
    contradiction
  have hresult : t =
      (((((ntCode σ).set a ((ntCode σ).getD c 0)).set c
        ((ntCode σ).getD a 0)).set b ((ntCode σ).getD d 0)).set d
          ((ntCode σ).getD b 0)) := by
    simpa only [hpat, ↓reduceIte, Option.some.injEq] using hstep.symm
  let A : Fin n := ⟨a, ha⟩
  let B : Fin n := ⟨b, hb⟩
  let C : Fin n := ⟨c, hc⟩
  let D : Fin n := ⟨d, hd⟩
  let τ := σ * Equiv.swap A C * Equiv.swap B D
  refine ⟨τ, ?_, ?_⟩
  · rw [hresult]
    change ntCode (σ * Equiv.swap A C * Equiv.swap B D) = _
    rw [ntCode_getD σ a ha, ntCode_getD σ b hb,
      ntCode_getD σ c hc, ntCode_getD σ d hd]
    exact ntCode_double_swap σ hab hbc hcd
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpat
    rw [ntCode_getD σ a ha, ntCode_getD σ b hb,
      ntCode_getD σ c hc, ntCode_getD σ d hd] at hpat
    rcases hpat with h1234 | h3412
    · exact Or.inl (ntMove_of_1234 hab hbc hcd h1234.1.1 h1234.1.2 h1234.2)
    · exact Or.inr (ntMove_of_3412 hab hbc hcd h3412.1.1 h3412.1.2 h3412.2)

private lemma ntMove_code_mem_nbrs {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : ntMove n σ τ) : ntCode τ ∈ ntNbrs (ntQuads n) (ntCode σ) := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hvab, hvbc, hvcd,
    ht1, ht2, ht3, ht4, hrest⟩ := h
  have hτ := ntMove_eq hab hbc hcd hvab hvbc hvcd ht1 ht2 ht3 ht4 hrest
  rw [hτ]
  unfold ntNbrs
  rw [List.mem_filterMap]
  refine ⟨(a.val, b.val, c.val, d.val), ntQuad_mem hab hbc hcd, ?_⟩
  unfold ntNbrAt
  have hcond :
      (((ntCode σ).getD a.val 0 < (ntCode σ).getD b.val 0 &&
          (ntCode σ).getD b.val 0 < (ntCode σ).getD c.val 0 &&
          (ntCode σ).getD c.val 0 < (ntCode σ).getD d.val 0) ||
        ((ntCode σ).getD c.val 0 < (ntCode σ).getD d.val 0 &&
          (ntCode σ).getD d.val 0 < (ntCode σ).getD a.val 0 &&
          (ntCode σ).getD a.val 0 < (ntCode σ).getD b.val 0)) = true := by
    rw [ntCode_getD σ a.val a.is_lt, ntCode_getD σ b.val b.is_lt,
      ntCode_getD σ c.val c.is_lt, ntCode_getD σ d.val d.is_lt]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨⟨hvab, hvbc⟩, hvcd⟩
  simp only [hcond, ↓reduceIte, Option.some.injEq]
  rw [ntCode_getD σ a.val a.is_lt, ntCode_getD σ b.val b.is_lt,
    ntCode_getD σ c.val c.is_lt, ntCode_getD σ d.val d.is_lt]
  exact (ntCode_double_swap σ hab hbc hcd).symm

private def ntRepCodes5 : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 1, 2, 4, 3], [0, 1, 3, 2, 4],
    [0, 1, 3, 4, 2], [0, 1, 4, 2, 3], [0, 2, 1, 3, 4],
    [1, 0, 2, 3, 4], [1, 2, 3, 4, 0], [4, 0, 1, 2, 3]]

private def ntRepCodes6 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 5, 4], [0, 1, 2, 4, 5, 3],
    [0, 1, 2, 5, 4, 3], [0, 1, 4, 3, 2, 5], [0, 1, 5, 3, 4, 2],
    [0, 2, 1, 3, 5, 4], [0, 3, 2, 1, 4, 5], [1, 0, 2, 4, 3, 5],
    [1, 2, 3, 4, 5, 0], [1, 2, 3, 5, 4, 0], [1, 2, 4, 3, 5, 0],
    [1, 2, 4, 5, 3, 0], [1, 2, 5, 3, 4, 0], [1, 3, 2, 4, 5, 0],
    [2, 1, 3, 4, 5, 0], [2, 3, 4, 5, 1, 0], [5, 0, 1, 2, 3, 4],
    [5, 0, 1, 2, 4, 3], [5, 0, 1, 3, 2, 4], [5, 0, 1, 3, 4, 2],
    [5, 0, 1, 4, 2, 3], [5, 0, 2, 1, 3, 4], [5, 1, 0, 2, 3, 4],
    [5, 1, 2, 3, 4, 0], [5, 4, 0, 1, 2, 3]]

private def ntJoin64 (chunks : List ℕ) : ℕ :=
  chunks.foldl (fun acc chunk => (acc <<< 64) + chunk) 0

private def ntL5 : ℕ :=
  ntJoin64 [
    0xfffffff8,
    0xfffffffffffffff8,
    0xf07523f5fffff0ff,
    0xfff6fff5f2ff01f4,
    0xff10fffffffffff4,
    0xfffffff6ffffff75,
    0xf3fffff6fffff2f0,
    0xfff4ff23f5f43210,
  ]

private def ntD5 : ℕ :=
  ntJoin64 [
    0xfffffff1,
    0xfffffffffffffff0,
    0xf11111f1fffff1ff,
    0xfff1fff2f1ff11f1,
    0xff11fffffffffff2,
    0xfffffff1ffffff02,
    0xf2fffff0fffff2f1,
    0xfff2ff22f0f00000,
  ]

private def ntL6 : ℕ :=
  ntJoin64 [
    0xffff,
    0xfffff9ffffffffff,
    0xfffffffff9fc7169,
    0xd3f6ffffffc7ffff,
    0xff7ffff6fcfff8cb,
    0xf5ffe51fffffffff,
    0xfffff5fffffffff7,
    0xffffffff16fd3fff,
    0xfff7ffffffcff1ff,
    0xff5ffe74fdbf5a4e,
    0x51f85221060071c2,
    0x2585821048210420,
    0xf89c708be7ffffff,
    0x8bfffffe1fffe7f8,
    0x522107e2ffc22f87,
    0xfffffe2fffe2f81e,
    0x108be1ffffff81c7,
    0xf8be3fffe1f84224,
    0x07e2fffe2f8422f9,
    0xfe210422f896120b,
    0xe1ffc01489410984,
    0x108841f85a2117e2,
    0xffc2050522304221,
    0x0422f8bff09be1ff,
    0xcc1fffffffffffff,
    0xe1f87ff007e2ffc2,
    0x0ffda2f97fffffe2,
    0xfa3ff08be1ffc41f,
    0xfc45f8be1288c1f9,
    0x3ff107e2ffc22fff,
    0xffffc2200462f89e,
    0x108be1ffc41f8bff,
    0xffc4308041f87ff1,
    0x060071c22ffd82f8,
    0x46210420ffffffff,
    0xe3fffffffde1f8bf,
    0xffffe3ffffff87e2,
    0xfffe0ffc22f87e01,
    0x0422ffffffffe1ff,
    0xfffffd61f8bfffff,
    0xe1f8522407e2ffff,
    0xff85a2f97e2fffe2,
    0xfa3ff0896160841f,
    0xfdc7f8bff083e1ff,
    0xda2f958258422505,
    0x22307e200422ffff,
    0xffa3e1fffe1ffd01,
    0xf8be10a041ffffff,
    0x93e2fffe2ffc82f8,
    0x7e211022f804108b,
    0xe1fffe1f8045f8be,
    0x128841f87ff00482,
    0x10420ffc22f9fe01,
    0x0422ffc45f884120,
    0x8010884108be1088,
    0xc1f84a2104201102,
    0x2104221046210420,
  ]

private def ntD6 : ℕ :=
  ntJoin64 [
    0xfffffff1ffffffff,
    0xfffffff0f11111f1,
    0xfffff1fffff1fff2,
    0xf1ff11f1ff11ffff,
    0xfffffff2fffffff1,
    0xffffff02f2fffff0,
    0xfffff2f1fff2ff22,
    0xf0f00000f8133611,
    0x1161161454152922,
    0xf41143f1fffff4ff,
    0xfff9fff2f61356f3,
    0xff86f8fffff5fff4,
    0xf11861f8fffff122,
    0xf4f3fff9f76517f6,
    0xfff4f754f2f44575,
    0xf41417f6ff111518,
    0x81348737f61641f4,
    0xff11161518955663,
    0xf6ff81f4ff18ffff,
    0xfffffff5f6ff11f4,
    0xff11ff27f2fffff5,
    0xf1ff77f8ff85ff52,
    0xf5f52527f1ff49f3,
    0xff86ffffff811114,
    0xf21943f9ff56f4ff,
    0xff611118f2ff4602,
    0x2272ff25f5161811,
    0xfffffff3ffffff09,
    0xf2fffff2fffff3f4,
    0xfff3ff54f8f34373,
    0xfffffff6ffffff25,
    0xf8fffff5f71518f7,
    0xfffff727f2f5fff6,
    0xf1ff78272565ff02,
    0xf2ff33f8ff07f205,
    0x0556070427f63374,
    0xfffff2f7fff8ff28,
    0xf6f88076fffff2f6,
    0xfff4ff28f5f48295,
    0xf15661f6fffaf152,
    0xf5f82345f6ff1124,
    0x3a11ff52f0f34373,
    0xff52f73826339645,
    0x72f55607f3034531,
    0x6083485267050700,
  ]

private def ntLabel5 (s : List ℕ) : ℕ := (ntL5 >>> (4 * ntLehmer s)) % 16
private def ntDistance5 (s : List ℕ) : ℕ := (ntD5 >>> (4 * ntLehmer s)) % 16
private def ntLabel6 (s : List ℕ) : ℕ := (ntL6 >>> (5 * ntLehmer s)) % 32
private def ntDistance6 (s : List ℕ) : ℕ := (ntD6 >>> (4 * ntLehmer s)) % 16

private def ntClassOk (n m : ℕ) (reps : List (List ℕ))
    (label distance : List ℕ → ℕ) (s : List ℕ) : Bool :=
  let l := label s
  let d := distance s
  (!ntHasPatB (ntQuads n) s || l < m) &&
    (ntNbrs (ntQuads n) s).all (fun t => label t == l) &&
    (l ≥ m || d < 15 && if d = 0 then s == reps.getD l []
      else (ntNbrs (ntQuads n) s).any fun t => distance t + 1 == d)

-- These finite certificates are evaluated by the kernel.
set_option maxRecDepth 100000 in
-- Kernel evaluation over the 120 codes of `S₅` needs extra recursion depth.
private theorem ntCertificate5 :
    (List.permutations' (List.range 5)).all
      (ntClassOk 5 9 ntRepCodes5 ntLabel5 ntDistance5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Kernel evaluation over the 720 codes of `S₆` needs extra recursion depth.
private theorem ntCertificate6 :
    (List.permutations' (List.range 6)).all
      (ntClassOk 6 26 ntRepCodes6 ntLabel6 ntDistance6) = true := by
  decide +kernel

private lemma ntRepCode5_mem (k : Fin 9) :
    ntRepCodes5.getD k.val [] ∈ List.permutations' (List.range 5) := by
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
-- Deciding membership among the 720 codes of `S₆` needs extra recursion depth.
private lemma ntRepCode6_mem (k : Fin 26) :
    ntRepCodes6.getD k.val [] ∈ List.permutations' (List.range 6) := by
  fin_cases k <;> decide

private noncomputable def ntRep5 (k : Fin 9) : Equiv.Perm (Fin 5) :=
  ntPermOfCode (ntRepCodes5.getD k.val []) (ntRepCode5_mem k)

private noncomputable def ntRep6 (k : Fin 26) : Equiv.Perm (Fin 6) :=
  ntPermOfCode (ntRepCodes6.getD k.val []) (ntRepCode6_mem k)

private lemma ntCode_rep5 (k : Fin 9) :
    ntCode (ntRep5 k) = ntRepCodes5.getD k.val [] :=
  ntCode_permOfCode _ _

private lemma ntCode_rep6 (k : Fin 26) :
    ntCode (ntRep6 k) = ntRepCodes6.getD k.val [] :=
  ntCode_permOfCode _ _

private lemma ntLabel_rep5 (k : Fin 9) :
    ntLabel5 (ntCode (ntRep5 k)) = k.val := by
  rw [ntCode_rep5]
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
-- Evaluating the `S₆` label table needs extra recursion depth.
private lemma ntLabel_rep6 (k : Fin 26) :
    ntLabel6 (ntCode (ntRep6 k)) = k.val := by
  rw [ntCode_rep6]
  fin_cases k <;> decide

private lemma ntRep5_pat (k : Fin 9) : ntPat 5 (ntRep5 k) := by
  apply ntHasPatB_sound
  rw [ntCode_rep5]
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
-- Evaluating the pattern test on the 26 `S₆` representatives needs extra recursion depth.
private lemma ntRep6_pat (k : Fin 26) : ntPat 6 (ntRep6 k) := by
  apply ntHasPatB_sound
  rw [ntCode_rep6]
  fin_cases k <;> decide

private lemma ntClassOk_parts (n m : ℕ) (reps : List (List ℕ))
    (label distance : List ℕ → ℕ) {s : List ℕ}
    (h : ntClassOk n m reps label distance s = true) :
    (!ntHasPatB (ntQuads n) s || label s < m) = true ∧
      (ntNbrs (ntQuads n) s).all (fun t => label t == label s) = true ∧
      (label s ≥ m || distance s < 15 &&
        if distance s = 0 then s == reps.getD (label s) []
        else (ntNbrs (ntQuads n) s).any fun t =>
          distance t + 1 == distance s) = true := by
  dsimp only [ntClassOk] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private lemma ntClassOk_code {n m : ℕ} {reps : List (List ℕ)}
    {label distance : List ℕ → ℕ}
    (hcert : (List.permutations' (List.range n)).all
      (ntClassOk n m reps label distance) = true)
    (σ : Equiv.Perm (Fin n)) :
    ntClassOk n m reps label distance (ntCode σ) = true :=
  (List.all_eq_true.mp hcert) _ (ntCode_mem_permutations' σ)

private lemma ntPat_label_lt {n m : ℕ} {reps : List (List ℕ)}
    {label distance : List ℕ → ℕ}
    (hcert : (List.permutations' (List.range n)).all
      (ntClassOk n m reps label distance) = true)
    {σ : Equiv.Perm (Fin n)} (hσ : ntPat n σ) : label (ntCode σ) < m := by
  have hparts := ntClassOk_parts n m reps label distance
    (ntClassOk_code hcert σ)
  have hpat := ntHasPatB_of_pat hσ
  rw [hpat] at hparts
  simpa only [Bool.not_true, Bool.false_or, decide_eq_true_eq] using hparts.1

private lemma ntMove_label_eq {n m : ℕ} {reps : List (List ℕ)}
    {label distance : List ℕ → ℕ}
    (hcert : (List.permutations' (List.range n)).all
      (ntClassOk n m reps label distance) = true)
    {σ τ : Equiv.Perm (Fin n)} (h : ntMove n σ τ) :
    label (ntCode σ) = label (ntCode τ) := by
  have hparts := ntClassOk_parts n m reps label distance
    (ntClassOk_code hcert σ)
  have hlabel := (List.all_eq_true.mp hparts.2.1) (ntCode τ)
    (ntMove_code_mem_nbrs h)
  exact (beq_iff_eq.mp hlabel).symm

private lemma ntEqvGen_label_eq {n m : ℕ} {reps : List (List ℕ)}
    {label distance : List ℕ → ℕ}
    (hcert : (List.permutations' (List.range n)).all
      (ntClassOk n m reps label distance) = true)
    {σ τ : Equiv.Perm (Fin n)} (h : Relation.EqvGen (ntMove n) σ τ) :
    label (ntCode σ) = label (ntCode τ) := by
  induction h with
  | rel a b hab => exact ntMove_label_eq hcert hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private lemma ntDistance_reaches_aux {n m : ℕ} {reps : List (List ℕ)}
    {label distance : List ℕ → ℕ} (rep : Fin m → Equiv.Perm (Fin n))
    (hcode : ∀ k, ntCode (rep k) = reps.getD k.val [])
    (hcert : (List.permutations' (List.range n)).all
      (ntClassOk n m reps label distance) = true) (d : ℕ) :
    ∀ (σ : Equiv.Perm (Fin n)) (k : Fin m),
      label (ntCode σ) = k.val → distance (ntCode σ) = d →
        Relation.EqvGen (ntMove n) σ (rep k) := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
      intro σ k hlabel hdist
      have hparts := ntClassOk_parts n m reps label distance
        (ntClassOk_code hcert σ)
      have hthird := hparts.2.2
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hthird
      rw [hlabel, hdist] at hthird
      obtain ⟨hdsmall, hbranch⟩ : d < 15 ∧
          (if d = 0 then ntCode σ == reps.getD k.val []
            else (ntNbrs (ntQuads n) (ntCode σ)).any fun t =>
              distance t + 1 == d) = true := by
        rcases hthird with hlarge | hsmall
        · omega
        · exact hsmall
      by_cases hd0 : d = 0
      · rw [ite_eq_left hd0] at hbranch
        have hroot : ntCode σ = reps.getD k.val [] := beq_iff_eq.mp hbranch
        have hσ : σ = rep k := ntCode_injective (hroot.trans (hcode k).symm)
        rw [hσ]
        exact Relation.EqvGen.refl _
      · rw [ite_eq_right hd0] at hbranch
        rw [List.any_eq_true] at hbranch
        obtain ⟨t, ht, htd⟩ := hbranch
        rw [beq_iff_eq] at htd
        obtain ⟨τ, hτcode, hmove⟩ := ntNbrs_sound ht
        have hτlabelRaw := (List.all_eq_true.mp hparts.2.1) t ht
        have hτlabel : label (ntCode τ) = k.val := by
          rw [hτcode]
          exact (beq_iff_eq.mp hτlabelRaw).trans hlabel
        have hτdist : distance (ntCode τ) < d := by
          rw [hτcode]
          omega
        have hτreach := ih (distance (ntCode τ)) hτdist τ k hτlabel rfl
        have hστ : Relation.EqvGen (ntMove n) σ τ := by
          rcases hmove with hmove | hmove
          · exact Relation.EqvGen.rel _ _ hmove
          · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hmove)
        exact Relation.EqvGen.trans _ _ _ hστ hτreach

private lemma ntDistance_reaches {n m : ℕ} {reps : List (List ℕ)}
    {label distance : List ℕ → ℕ} (rep : Fin m → Equiv.Perm (Fin n))
    (hcode : ∀ k, ntCode (rep k) = reps.getD k.val [])
    (hcert : (List.permutations' (List.range n)).all
      (ntClassOk n m reps label distance) = true)
    (σ : Equiv.Perm (Fin n)) (k : Fin m)
    (hlabel : label (ntCode σ) = k.val) :
    Relation.EqvGen (ntMove n) σ (rep k) :=
  ntDistance_reaches_aux rep hcode hcert (distance (ntCode σ)) σ k hlabel rfl

/-- A pattern occurrence yields a move out of or into the permutation. -/
private lemma ntPat_move {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : ntPat n σ) :
    ∃ y, ntMove n σ y ∨ ntMove n y σ := by
  rcases h with ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, s31, s42, s13⟩
  · exact ⟨_, Or.inl (ntMove_of_1234 h12 h23 h34 s12 s23 s34)⟩
  · exact ⟨_, Or.inr (ntMove_of_3412 h12 h23 h34 s31 s42 s13)⟩

private def ntCert7Block : ℕ → ℕ → Array ℕ
  | 0, 0 => #[
      0, 0, 6, 213, 245, 326, 85, 101, 21, 340, 356, 340, 37, 372,
      4, 4, 545, 67, 388, 372, 4, 4, 147, 15, 20, 212, 37, 213,
      293, 38, 6, 118, 4, 5, 4, 340, 195, 179, 20, 20, 69, 37,
      4, 117, 20, 117, 5, 5, 38, 38, 291, 100, 291, 37, 37, 37,
      101, 36, 70, 83, 481, 497, 6, 36
    ]
  | 0, 1 => #[
      5, 5, 481, 497, 149, 36, 5, 5, 68, 36, 52, 68, 21, 21,
      53, 38, 69, 69, 529, 19, 118, 37, 15, 117, 21, 21, 117, 5,
      5, 6, 513, 3, 69, 420, 68, 117, 69, 69, 132, 83, 69, 86,
      147, 69, 132, 116, 101, 85, 70, 71, 117, 133, 149, 119, 147, 15,
      70, 422, 68, 420, 452, 15, 469, 102
    ]
  | 0, 2 => #[
      436, 420, 69, 69, 468, 85, 101, 85, 69, 69, 532, 229, 133, 117,
      245, 15, 245, 38, 387, 371, 20, 54, 4, 340, 5, 261, 53, 341,
      36, 52, 21, 84, 21, 21, 36, 38, 133, 117, 53, 22, 548, 277,
      19, 19, 19, 19, 53, 54, 52, 21, 99, 21, 5, 37, 52, 6,
      19, 19, 5, 7, 52, 6, 19, 19
    ]
  | 0, 3 => #[
      468, 37, 51, 35, 149, 21, 51, 35, 277, 261, 101, 83, 53, 37,
      133, 15, 21, 23, 147, 5, 4, 117, 5, 4, 468, 261, 131, 115,
      149, 15, 85, 85, 277, 69, 67, 85, 150, 86, 101, 85, 549, 70,
      147, 15, 135, 119, 15, 15, 293, 118, 515, 164, 515, 166, 452, 85,
      500, 484, 245, 85, 211, 227, 227, 211
    ]
  | 0, 4 => #[
      69, 165, 211, 227, 227, 211, 245, 15, 214, 15, 133, 117, 293, 15,
      148, 86, 69, 69, 70, 86, 99, 83, 227, 211, 165, 165, 309, 15,
      227, 211, 15, 15, 321, 321, 53, 37, 53, 37, 37, 37, 132, 116,
      53, 37, 53, 37, 51, 35, 322, 165, 309, 5, 51, 35, 466, 7,
      53, 261, 337, 353, 21, 22, 53, 37
    ]
  | 0, 5 => #[
      275, 259, 20, 22, 53, 37, 53, 39, 405, 15, 3, 3, 517, 5,
      405, 7, 277, 261, 337, 353, 294, 359, 293, 15, 275, 259, 15, 15,
      102, 437, 102, 86, 69, 69, 307, 390, 15, 15, 405, 15, 164, 500,
      164, 164, 164, 166, 149, 182, 243, 165, 195, 181, 101, 85, 101, 86,
      163, 163, 229, 215, 229, 214, 245, 15
    ]
  | 0, 6 => #[
      148, 214, 291, 117, 291, 15, 181, 181, 197, 181, 197, 179, 417, 433,
      102, 86, 69, 69, 417, 433, 230, 213, 469, 15, 261, 277, 133, 117,
      293, 15, 15, 15, 134, 118, 15, 15, 195, 179, 101, 85, 468, 68,
      309, 437, 15, 15, 469, 15, 277, 37, 53, 38, 19, 19, 291, 37,
      52, 261, 21, 20, 369, 385, 54, 37
    ]
  | 0, 7 => #[
      22, 23, 452, 5, 5, 374, 405, 15, 277, 277, 293, 325, 291, 342,
      291, 357, 326, 326, 358, 342, 369, 385, 15, 15, 469, 15, 309, 373,
      404, 373, 406, 15, 165, 181, 165, 213, 165, 165, 228, 179, 277, 261,
      165, 179, 228, 212, 197, 181, 244, 167, 227, 211, 245, 421, 245, 15,
      229, 262, 227, 211, 245, 15, 197, 181
    ]
  | 1, 0 => #[
      276, 260, 465, 166, 246, 182, 197, 181, 166, 166, 309, 421, 230, 422,
      449, 15, 292, 261, 227, 211, 292, 15, 294, 15, 229, 213, 469, 15,
      308, 502, 198, 182, 165, 165, 309, 422, 438, 422, 532, 15, 275, 259,
      293, 262, 469, 15, 309, 15, 278, 263, 534, 15, 310, 15, 15, 15,
      548, 15, 309, 436, 437, 485, 518, 15
    ]
  | 1, 1 => #[
      322, 338, 341, 261, 341, 341, 388, 357, 277, 373, 324, 324, 310, 373,
      356, 340, 401, 326, 373, 374, 390, 374, 406, 15, 309, 485, 244, 213,
      197, 182, 181, 229, 277, 165, 163, 165, 214, 230, 15, 213, 165, 167,
      227, 211, 231, 214, 244, 15, 261, 230, 227, 211, 245, 15, 197, 179,
      276, 260, 198, 165, 246, 181, 229, 15
    ]
  | 1, 2 => #[
      550, 167, 309, 15, 230, 215, 15, 15, 292, 261, 227, 211, 294, 15,
      246, 15, 229, 213, 15, 15, 197, 502, 199, 183, 549, 15, 308, 502,
      15, 15, 532, 15, 275, 259, 279, 262, 293, 15, 309, 15, 278, 263,
      534, 15, 309, 15, 15, 15, 548, 15, 486, 501, 501, 485, 518, 15,
      309, 263, 15, 261, 295, 15, 308, 15
    ]
  | 1, 3 => #[
      277, 15, 15, 15, 311, 15, 15, 15, 550, 15, 15, 15, 15, 15,
      15, 15, 164, 166, 166, 198, 166, 166, 180, 180, 166, 166, 405, 166,
      214, 181, 15, 213, 165, 165, 214, 214, 389, 213, 405, 15, 293, 214,
      246, 214, 246, 15, 182, 182, 164, 164, 164, 164, 197, 181, 229, 15,
      165, 167, 246, 15, 229, 373, 15, 15
    ]
  | 1, 4 => #[
      262, 262, 453, 422, 293, 15, 245, 15, 438, 262, 15, 15, 197, 181,
      197, 183, 167, 15, 469, 501, 15, 15, 519, 15, 420, 436, 437, 261,
      453, 15, 294, 15, 277, 421, 533, 15, 469, 15, 15, 15, 533, 15,
      311, 487, 501, 485, 517, 15, 420, 436, 15, 261, 295, 15, 454, 15,
      277, 15, 15, 15, 311, 15, 15, 15
    ]
  | 1, 5 => #[
      549, 15, 15, 15, 15, 15, 15, 15, 133, 86, 131, 115, 68, 102,
      516, 86, 67, 67, 67, 67, 116, 132, 99, 83, 149, 69, 116, 118,
      150, 119, 149, 15, 245, 118, 20, 117, 22, 15, 149, 358, 4, 15,
      100, 15, 101, 85, 53, 15, 54, 15, 149, 54, 53, 15, 22, 15,
      148, 54, 21, 22, 147, 21, 293, 86
    ]
  | 1, 6 => #[
      21, 15, 101, 15, 53, 37, 54, 15, 67, 15, 53, 37, 54, 15,
      516, 15, 117, 115, 53, 37, 21, 21, 293, 37, 101, 15, 21, 15,
      99, 83, 54, 15, 533, 15, 484, 484, 131, 15, 6, 15, 117, 117,
      150, 118, 149, 15, 101, 102, 100, 15, 69, 15, 99, 83, 102, 15,
      70, 15, 151, 15, 131, 15, 15, 15
    ]
  | 1, 7 => #[
      117, 117, 133, 117, 149, 15, 83, 83, 101, 85, 101, 85, 147, 87,
      99, 83, 69, 70, 147, 15, 135, 119, 15, 15, 244, 118, 131, 115,
      150, 15, 150, 15, 132, 15, 103, 15, 243, 85, 133, 15, 163, 15,
      243, 15, 134, 15, 15, 15, 147, 37, 229, 213, 23, 37, 148, 38,
      53, 15, 53, 15, 53, 37, 99, 15
    ]
  | 2, 0 => #[
      532, 15, 53, 37, 53, 15, 532, 15, 53, 37, 53, 37, 21, 22,
      291, 38, 54, 15, 21, 15, 99, 83, 54, 15, 532, 15, 5, 437,
      516, 15, 6, 15, 309, 327, 134, 357, 343, 359, 291, 15, 277, 15,
      15, 15, 99, 83, 102, 15, 70, 15, 421, 437, 15, 15, 15, 15,
      148, 260, 133, 259, 293, 15, 150, 15
    ]
  | 2, 1 => #[
      131, 115, 15, 15, 309, 85, 101, 86, 67, 67, 309, 438, 15, 15,
      452, 15, 213, 213, 131, 115, 245, 15, 517, 182, 197, 15, 197, 15,
      101, 85, 227, 15, 550, 15, 246, 437, 227, 15, 455, 15, 149, 15,
      227, 211, 15, 15, 150, 15, 15, 15, 15, 15, 101, 85, 103, 15,
      165, 15, 485, 501, 15, 15, 518, 15
    ]
  | 2, 2 => #[
      53, 37, 53, 325, 21, 21, 54, 37, 275, 15, 357, 15, 53, 38,
      53, 15, 22, 15, 484, 484, 6, 15, 453, 15, 309, 390, 325, 325,
      357, 341, 295, 358, 275, 15, 357, 15, 375, 389, 15, 15, 550, 15,
      374, 15, 437, 15, 453, 15, 292, 500, 294, 486, 293, 15, 291, 15,
      502, 263, 470, 15, 309, 15, 15, 15
    ]
  | 2, 3 => #[
      469, 15, 420, 420, 453, 422, 454, 15, 229, 213, 246, 214, 243, 15,
      292, 183, 196, 15, 165, 15, 195, 179, 198, 15, 469, 15, 246, 423,
      437, 15, 453, 15, 246, 15, 230, 215, 470, 15, 245, 15, 278, 15,
      470, 15, 195, 179, 198, 15, 166, 15, 437, 421, 437, 15, 533, 15,
      307, 15, 15, 15, 469, 15, 294, 15
    ]
  | 2, 4 => #[
      279, 15, 533, 15, 15, 15, 15, 15, 532, 15, 517, 438, 516, 15,
      517, 15, 404, 389, 405, 374, 342, 15, 293, 342, 278, 15, 324, 15,
      358, 342, 356, 15, 325, 15, 389, 373, 389, 15, 405, 15, 292, 500,
      277, 261, 293, 15, 291, 15, 277, 261, 15, 15, 309, 15, 15, 15,
      549, 15, 309, 15, 15, 15, 15, 15
    ]
  | 2, 5 => #[
      229, 211, 246, 213, 246, 15, 292, 198, 197, 15, 197, 15, 195, 179,
      198, 15, 166, 15, 246, 15, 231, 15, 15, 15, 310, 15, 229, 215,
      15, 15, 245, 15, 230, 15, 15, 15, 195, 179, 198, 15, 166, 15,
      485, 501, 15, 15, 518, 15, 549, 15, 15, 15, 534, 15, 294, 15,
      279, 15, 533, 15, 15, 15, 15, 15
    ]
  | 2, 6 => #[
      532, 15, 517, 486, 516, 15, 517, 15, 310, 15, 15, 15, 15, 15,
      293, 15, 278, 15, 15, 15, 15, 15, 15, 15, 551, 15, 15, 15,
      15, 15, 15, 15, 389, 262, 403, 260, 403, 326, 308, 342, 276, 324,
      324, 326, 371, 387, 403, 342, 325, 325, 371, 387, 403, 375, 405, 15,
      421, 437, 229, 213, 453, 15, 340, 340
    ]
  | 2, 7 => #[
      164, 164, 164, 164, 245, 341, 198, 341, 325, 325, 403, 15, 230, 373,
      15, 15, 419, 419, 435, 419, 455, 15, 470, 15, 435, 419, 15, 15,
      357, 341, 357, 341, 516, 325, 469, 502, 15, 15, 516, 15, 437, 421,
      451, 423, 453, 15, 451, 15, 278, 421, 534, 15, 469, 15, 15, 15,
      533, 15, 467, 500, 501, 485, 518, 15
    ]
  | 3, 0 => #[
      437, 421, 451, 423, 454, 15, 467, 15, 279, 421, 15, 15, 470, 15,
      15, 15, 550, 15, 467, 15, 15, 15, 15, 15, 262, 262, 15, 421,
      453, 15, 454, 15, 437, 15, 15, 15, 469, 15, 15, 15, 551, 15,
      15, 15, 15, 15, 15, 15, 372, 372, 227, 211, 246, 15, 180, 180,
      325, 15, 166, 15, 357, 181, 229, 15
    ]
  | 3, 1 => #[
      325, 15, 246, 15, 387, 15, 15, 15, 405, 15, 227, 211, 15, 15,
      451, 15, 231, 15, 15, 15, 197, 341, 357, 15, 166, 15, 487, 503,
      15, 15, 15, 15, 310, 15, 15, 15, 533, 15, 294, 15, 435, 15,
      535, 15, 15, 15, 15, 15, 535, 15, 517, 15, 502, 15, 519, 15,
      309, 15, 15, 15, 15, 15, 294, 15
    ]
  | 3, 2 => #[
      277, 15, 15, 15, 15, 15, 15, 15, 550, 15, 15, 15, 15, 15,
      15, 15, 1, 1, 133, 485, 149, 7, 85, 85, 101, 53, 37, 53,
      101, 21, 131, 115, 34, 52, 21, 21, 131, 115, 36, 15, 117, 117,
      133, 117, 151, 15, 149, 86, 101, 15, 101, 15, 101, 86, 133, 15,
      69, 15, 149, 15, 133, 15, 15, 15
    ]
  | 3, 3 => #[
      245, 38, 131, 115, 84, 38, 149, 15, 131, 15, 55, 15, 2, 2,
      53, 15, 6, 15, 2, 2, 54, 15, 452, 15, 51, 35, 53, 37,
      22, 196, 147, 37, 134, 15, 530, 15, 101, 85, 52, 15, 548, 15,
      212, 228, 502, 15, 2, 15, 164, 69, 85, 102, 181, 196, 147, 15,
      134, 15, 15, 15, 101, 85, 103, 15
    ]
  | 3, 4 => #[
      69, 15, 212, 228, 15, 15, 290, 15, 149, 501, 501, 5, 5, 5,
      17, 17, 134, 117, 38, 55, 21, 21, 100, 53, 36, 50, 21, 21,
      37, 53, 15, 52, 149, 15, 133, 117, 15, 15, 149, 15, 499, 15,
      15, 15, 102, 85, 101, 15, 452, 15, 423, 438, 15, 15, 452, 15,
      243, 69, 133, 117, 181, 103, 149, 15
    ]
  | 3, 5 => #[
      135, 15, 15, 15, 116, 132, 15, 15, 164, 15, 117, 134, 15, 15,
      468, 15, 51, 35, 85, 101, 21, 21, 53, 37, 52, 15, 406, 15,
      54, 38, 55, 15, 18, 15, 6, 388, 514, 15, 404, 15, 547, 357,
      181, 101, 404, 197, 341, 357, 327, 15, 358, 15, 117, 132, 15, 15,
      306, 15, 118, 388, 452, 15, 404, 15
    ]
  | 3, 6 => #[
      309, 5, 499, 483, 2, 4, 534, 22, 33, 49, 39, 54, 532, 21,
      38, 54, 37, 53, 20, 15, 37, 53, 37, 53, 550, 15, 15, 15,
      470, 15, 515, 15, 277, 15, 470, 15, 15, 15, 15, 15, 469, 15,
      421, 436, 453, 15, 454, 15, 548, 70, 85, 101, 469, 102, 243, 15,
      230, 15, 470, 15, 197, 181, 199, 15
    ]
  | 3, 7 => #[
      515, 15, 212, 228, 453, 15, 292, 15, 68, 69, 182, 198, 86, 100,
      15, 15, 15, 15, 468, 15, 260, 228, 15, 15, 549, 15, 114, 130,
      502, 15, 452, 15, 372, 372, 340, 356, 325, 356, 388, 372, 388, 15,
      358, 15, 259, 275, 358, 15, 549, 15, 259, 275, 405, 15, 405, 15,
      5, 5, 499, 483, 4, 15, 293, 23
    ]
  | 4, 0 => #[
      33, 49, 38, 55, 21, 21, 38, 54, 37, 54, 18, 20, 37, 54,
      37, 53, 310, 15, 15, 15, 15, 15, 515, 15, 277, 15, 15, 15,
      15, 15, 15, 15, 551, 15, 15, 15, 15, 15, 15, 15, 245, 166,
      85, 101, 86, 102, 243, 15, 230, 15, 15, 15, 197, 181, 198, 15,
      149, 15, 116, 132, 15, 15, 531, 15
    ]
  | 4, 1 => #[
      68, 70, 182, 198, 85, 100, 15, 15, 15, 15, 534, 15, 260, 276,
      15, 15, 244, 15, 114, 130, 502, 15, 518, 15, 70, 70, 85, 101,
      85, 101, 15, 15, 15, 15, 15, 15, 214, 134, 15, 15, 150, 15,
      118, 278, 15, 15, 15, 15, 453, 374, 340, 326, 405, 15, 292, 342,
      325, 325, 355, 341, 373, 339, 405, 342
    ]
  | 4, 2 => #[
      325, 325, 374, 389, 389, 374, 405, 15, 308, 374, 451, 422, 451, 15,
      341, 341, 357, 341, 357, 339, 403, 341, 358, 342, 323, 326, 403, 15,
      390, 373, 15, 15, 451, 437, 229, 373, 453, 199, 469, 15, 390, 374,
      15, 15, 357, 341, 355, 181, 548, 326, 469, 502, 15, 15, 517, 15,
      469, 167, 181, 422, 453, 199, 451, 15
    ]
  | 4, 3 => #[
      438, 421, 534, 15, 213, 229, 15, 15, 533, 15, 261, 277, 517, 486,
      246, 15, 469, 421, 453, 197, 454, 199, 451, 15, 439, 423, 15, 15,
      213, 229, 15, 15, 550, 15, 261, 277, 15, 15, 15, 15, 420, 420,
      515, 422, 515, 15, 469, 15, 438, 421, 15, 15, 531, 15, 15, 15,
      549, 15, 531, 15, 15, 15, 15, 15
    ]
  | 4, 4 => #[
      373, 373, 389, 373, 405, 15, 405, 342, 357, 15, 357, 15, 357, 343,
      387, 15, 325, 15, 406, 15, 387, 15, 15, 15, 161, 161, 389, 373,
      182, 199, 245, 15, 230, 15, 15, 15, 197, 229, 357, 15, 162, 15,
      213, 229, 15, 15, 306, 15, 469, 166, 177, 193, 534, 198, 454, 15,
      435, 15, 533, 15, 261, 277, 15, 15
    ]
  | 4, 5 => #[
      245, 15, 213, 500, 502, 15, 245, 15, 469, 167, 177, 193, 182, 199,
      455, 15, 435, 15, 15, 15, 214, 277, 15, 15, 309, 15, 213, 230,
      15, 15, 245, 15, 485, 501, 517, 487, 517, 15, 293, 15, 278, 422,
      15, 15, 533, 15, 15, 15, 550, 15, 533, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 294, 15
    ]
  | 4, 6 => #[
      438, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 405, 167, 387, 197, 181, 15, 245, 15, 389, 15, 15, 15,
      420, 388, 199, 15, 292, 15, 213, 436, 15, 15, 292, 15, 165, 165,
      342, 199, 15, 197, 15, 15, 15, 15, 534, 15, 261, 278, 15, 15,
      404, 15, 214, 229, 518, 15, 292, 15
    ]
  | 4, 7 => #[
      165, 15, 183, 358, 181, 197, 15, 15, 15, 15, 15, 15, 261, 389,
      15, 15, 245, 15, 372, 229, 15, 15, 292, 15, 533, 486, 515, 52,
      515, 5, 515, 5, 132, 485, 6, 6, 99, 83, 36, 52, 452, 38,
      531, 277, 37, 22, 452, 54, 149, 23, 37, 101, 85, 15, 6, 7,
      499, 15, 5, 15, 101, 277, 101, 15
    ]
  | 5, 0 => #[
      293, 15, 117, 277, 22, 15, 293, 15, 65, 65, 134, 102, 86, 103,
      149, 15, 132, 15, 15, 15, 261, 133, 103, 15, 66, 15, 117, 133,
      15, 15, 306, 15, 84, 100, 53, 37, 84, 98, 53, 37, 70, 15,
      244, 15, 117, 133, 15, 15, 308, 15, 5, 500, 242, 15, 150, 15,
      164, 102, 85, 100, 100, 100, 117, 229
    ]
  | 5, 1 => #[
      69, 15, 244, 15, 213, 133, 15, 15, 308, 15, 246, 134, 242, 15,
      150, 15, 515, 4, 5, 5, 6, 53, 5, 5, 37, 5, 469, 6,
      21, 53, 22, 22, 148, 53, 261, 436, 22, 53, 309, 53, 531, 69,
      38, 55, 15, 101, 6, 6, 6, 15, 470, 15, 38, 278, 21, 15,
      548, 15, 118, 133, 453, 15, 308, 15
    ]
  | 5, 2 => #[
      550, 70, 81, 97, 470, 102, 15, 15, 15, 15, 469, 15, 484, 501,
      15, 15, 149, 15, 117, 436, 438, 15, 292, 15, 117, 69, 69, 196,
      194, 86, 117, 134, 165, 15, 148, 15, 214, 230, 15, 15, 148, 15,
      117, 134, 150, 15, 146, 15, 68, 164, 162, 101, 197, 181, 118, 388,
      404, 15, 307, 15, 117, 341, 406, 15
    ]
  | 5, 3 => #[
      149, 15, 148, 118, 293, 15, 291, 15, 515, 6, 5, 6, 36, 52,
      5, 7, 37, 53, 6, 54, 21, 21, 22, 22, 148, 53, 37, 53,
      36, 52, 148, 37, 69, 15, 39, 54, 85, 53, 6, 7, 6, 15,
      7, 15, 262, 54, 21, 15, 53, 15, 38, 133, 23, 15, 308, 15,
      70, 71, 81, 97, 86, 103, 15, 15
    ]
  | 5, 4 => #[
      15, 15, 15, 15, 484, 134, 15, 15, 517, 15, 117, 500, 15, 15,
      292, 15, 549, 68, 68, 165, 85, 196, 181, 133, 70, 15, 148, 15,
      214, 230, 15, 15, 148, 15, 117, 486, 150, 15, 146, 15, 66, 68,
      70, 68, 197, 181, 86, 133, 70, 15, 148, 15, 117, 133, 15, 15,
      547, 15, 148, 15, 293, 15, 294, 15
    ]
  | 5, 5 => #[
      405, 486, 389, 373, 405, 326, 453, 358, 437, 341, 405, 326, 389, 373,
      387, 371, 292, 327, 389, 373, 387, 371, 292, 15, 374, 15, 387, 371,
      453, 15, 517, 342, 436, 420, 327, 326, 261, 342, 387, 371, 326, 326,
      469, 277, 387, 371, 295, 15, 452, 438, 387, 371, 454, 15, 454, 15,
      389, 373, 15, 15, 262, 279, 358, 342
    ]
  | 5, 6 => #[
      325, 325, 469, 278, 15, 15, 518, 15, 437, 421, 435, 419, 197, 181,
      181, 197, 435, 419, 197, 181, 213, 231, 15, 15, 534, 15, 244, 214,
      501, 485, 293, 15, 437, 421, 435, 419, 197, 181, 181, 197, 435, 419,
      197, 181, 470, 229, 15, 15, 550, 15, 292, 15, 246, 214, 293, 15,
      452, 500, 453, 486, 453, 15, 451, 15
    ]
  | 5, 7 => #[
      502, 486, 15, 15, 469, 279, 15, 15, 549, 15, 469, 279, 15, 15,
      15, 15, 405, 374, 405, 374, 407, 15, 452, 15, 357, 15, 359, 15,
      257, 273, 389, 15, 294, 15, 257, 273, 391, 15, 309, 15, 549, 15,
      390, 375, 15, 15, 405, 15, 438, 15, 15, 15, 355, 339, 358, 15,
      308, 15, 261, 277, 15, 15, 309, 15
    ]
  | 6, 0 => #[
      213, 165, 165, 166, 181, 181, 451, 197, 166, 15, 309, 15, 209, 225,
      15, 15, 532, 15, 213, 229, 228, 15, 245, 15, 165, 165, 165, 165,
      244, 182, 451, 197, 437, 15, 198, 15, 209, 225, 15, 15, 309, 15,
      213, 213, 244, 15, 246, 15, 469, 502, 501, 485, 518, 15, 517, 15,
      435, 419, 15, 15, 262, 279, 15, 15
    ]
  | 6, 1 => #[
      293, 15, 533, 278, 15, 15, 292, 15, 550, 15, 15, 15, 15, 15,
      453, 15, 437, 15, 15, 15, 263, 279, 15, 15, 293, 15, 263, 279,
      15, 15, 293, 15, 326, 327, 342, 358, 342, 359, 403, 15, 390, 15,
      15, 15, 357, 341, 359, 15, 293, 15, 374, 437, 15, 15, 292, 15,
      165, 165, 166, 166, 182, 182, 182, 199
    ]
  | 6, 2 => #[
      165, 15, 197, 15, 374, 438, 15, 15, 308, 15, 260, 276, 292, 15,
      404, 15, 181, 197, 166, 166, 181, 197, 183, 198, 165, 15, 244, 15,
      422, 390, 15, 15, 245, 15, 260, 276, 245, 15, 404, 15, 517, 15,
      499, 483, 517, 15, 533, 15, 499, 483, 15, 15, 421, 437, 15, 15,
      308, 15, 421, 437, 15, 15, 308, 15
    ]
  | 6, 3 => #[
      549, 15, 15, 15, 15, 15, 515, 15, 503, 15, 15, 15, 262, 279,
      15, 15, 292, 15, 263, 278, 15, 15, 292, 15, 549, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 486, 15, 15, 15, 308, 15,
      15, 502, 15, 15, 452, 15, 165, 165, 181, 325, 182, 198, 341, 15,
      165, 15, 246, 15, 214, 231, 15, 15
    ]
  | 6, 4 => #[
      244, 15, 258, 274, 246, 15, 244, 15, 549, 197, 182, 197, 244, 197,
      15, 357, 168, 15, 404, 15, 215, 230, 15, 15, 244, 15, 258, 274,
      244, 15, 244, 15, 2, 2, 37, 5, 36, 52, 20, 21, 5, 21,
      4, 4, 6, 21, 4, 4, 3, 6, 22, 22, 34, 50, 19, 54,
      36, 69, 37, 69, 38, 52, 37, 6
    ]
  | 6, 5 => #[
      22, 15, 4, 15, 6, 6, 4, 15, 5, 15, 132, 116, 148, 15,
      21, 15, 85, 69, 20, 20, 53, 101, 38, 15, 20, 15, 150, 15,
      113, 129, 6, 15, 517, 15, 51, 35, 277, 15, 21, 15, 69, 101,
      70, 70, 85, 101, 86, 103, 69, 15, 531, 15, 117, 133, 15, 15,
      533, 15, 260, 276, 149, 15, 515, 15
    ]
  | 6, 6 => #[
      149, 86, 85, 101, 340, 340, 130, 114, 245, 15, 149, 15, 132, 116,
      134, 15, 164, 15, 229, 213, 133, 15, 149, 15, 2, 2, 501, 5,
      36, 52, 20, 22, 5, 485, 4, 4, 6, 20, 4, 4, 3, 38,
      116, 116, 34, 50, 19, 22, 20, 52, 70, 53, 85, 85, 517, 53,
      22, 15, 148, 15, 6, 6, 6, 15
    ]
  | 6, 7 => #[
      5, 15, 132, 116, 20, 15, 21, 15, 69, 69, 21, 102, 52, 36,
      15, 54, 24, 15, 52, 15, 113, 129, 7, 15, 5, 15, 51, 35,
      148, 15, 533, 15, 69, 69, 70, 70, 149, 101, 87, 102, 69, 15,
      531, 15, 117, 133, 15, 15, 533, 15, 260, 276, 149, 15, 515, 15,
      148, 70, 70, 118, 70, 15, 130, 114
    ]
  | 7, 0 => #[
      245, 15, 69, 15, 132, 116, 101, 15, 69, 15, 229, 213, 148, 15,
      150, 15, 324, 372, 357, 341, 310, 326, 357, 341, 357, 340, 325, 325,
      390, 374, 358, 342, 323, 323, 403, 276, 293, 262, 294, 15, 452, 375,
      389, 422, 403, 15, 357, 341, 356, 341, 309, 325, 355, 339, 358, 342,
      309, 327, 294, 263, 293, 262, 293, 15
    ]
  | 7, 1 => #[
      437, 421, 438, 373, 453, 15, 15, 15, 390, 374, 310, 15, 355, 339,
      359, 343, 326, 326, 277, 261, 277, 261, 532, 15, 451, 421, 438, 422,
      308, 15, 455, 15, 438, 422, 533, 15, 469, 15, 15, 15, 548, 15,
      470, 485, 276, 260, 517, 15, 228, 212, 244, 214, 182, 15, 453, 182,
      166, 166, 165, 166, 198, 182, 196, 212
    ]
  | 7, 2 => #[
      165, 167, 229, 213, 229, 213, 245, 15, 421, 486, 437, 419, 309, 15,
      455, 15, 435, 421, 311, 15, 469, 15, 15, 15, 550, 15, 262, 15,
      279, 262, 295, 15, 389, 373, 387, 371, 405, 15, 357, 343, 358, 15,
      305, 15, 357, 343, 357, 15, 310, 15, 262, 261, 278, 15, 289, 15,
      550, 15, 387, 371, 309, 15, 406, 15
    ]
  | 7, 3 => #[
      15, 15, 309, 15, 486, 341, 359, 15, 325, 15, 277, 262, 278, 15,
      293, 15, 469, 15, 15, 15, 310, 15, 454, 15, 439, 15, 534, 15,
      15, 15, 15, 15, 310, 15, 292, 276, 294, 15, 518, 15, 162, 178,
      181, 181, 181, 181, 228, 213, 437, 15, 245, 15, 244, 213, 198, 15,
      241, 15, 213, 214, 230, 15, 246, 15
    ]
  | 7, 4 => #[
      501, 485, 501, 485, 517, 15, 451, 15, 501, 485, 310, 15, 533, 15,
      15, 15, 309, 15, 260, 260, 293, 263, 294, 15, 534, 15, 15, 15,
      15, 15, 453, 15, 437, 15, 311, 15, 15, 15, 15, 15, 310, 15,
      261, 261, 294, 15, 295, 15, 403, 325, 342, 358, 310, 359, 407, 15,
      391, 15, 310, 15, 358, 342, 15, 15
    ]
  | 7, 5 => #[
      324, 15, 260, 276, 277, 15, 533, 15, 549, 326, 341, 357, 309, 359,
      15, 15, 15, 15, 309, 15, 420, 390, 15, 15, 532, 15, 260, 276,
      516, 15, 293, 15, 181, 197, 228, 197, 164, 164, 212, 212, 245, 15,
      164, 15, 197, 181, 230, 15, 165, 15, 213, 229, 229, 15, 453, 15,
      515, 487, 502, 486, 306, 15, 519, 15
    ]
  | 7, 6 => #[
      502, 486, 310, 15, 532, 439, 15, 15, 308, 15, 262, 262, 292, 262,
      294, 15, 533, 15, 15, 15, 310, 15, 518, 15, 503, 15, 310, 15,
      421, 437, 15, 15, 309, 15, 261, 276, 293, 15, 468, 15, 548, 15,
      15, 15, 309, 15, 15, 15, 15, 15, 311, 15, 484, 440, 15, 15,
      515, 15, 262, 500, 277, 15, 454, 15
    ]
  | 7, 7 => #[
      326, 325, 325, 326, 308, 342, 373, 360, 327, 15, 306, 15, 373, 389,
      15, 15, 310, 15, 277, 261, 278, 15, 290, 15, 180, 196, 180, 180,
      163, 180, 182, 196, 242, 15, 165, 15, 195, 179, 198, 15, 549, 15,
      213, 229, 404, 15, 245, 15, 501, 486, 516, 487, 310, 15, 15, 15,
      503, 486, 309, 15, 535, 15, 15, 15
    ]
  | 8, 0 => #[
      550, 15, 290, 260, 438, 262, 293, 15, 535, 15, 15, 15, 310, 15,
      519, 15, 15, 15, 309, 15, 15, 15, 15, 15, 310, 15, 276, 277,
      276, 15, 293, 15, 551, 15, 15, 15, 310, 15, 15, 15, 15, 15,
      309, 15, 486, 503, 15, 15, 310, 15, 437, 276, 278, 15, 531, 15,
      15, 15, 15, 15, 310, 15, 15, 15
    ]
  | 8, 1 => #[
      15, 15, 310, 15, 15, 15, 15, 15, 15, 15, 262, 501, 15, 15,
      294, 15, 178, 194, 166, 166, 165, 165, 182, 228, 246, 15, 196, 15,
      197, 181, 15, 15, 547, 15, 373, 228, 230, 15, 246, 15, 6, 100,
      132, 53, 2, 34, 4, 116, 67, 53, 52, 67, 18, 34, 101, 20,
      69, 38, 116, 132, 148, 118, 149, 15
    ]
  | 8, 2 => #[
      84, 100, 36, 101, 68, 68, 5, 52, 4, 15, 69, 15, 132, 133,
      132, 15, 549, 15, 36, 36, 149, 15, 21, 15, 66, 82, 85, 21,
      100, 84, 132, 52, 19, 15, 102, 15, 5, 5, 134, 15, 145, 15,
      117, 5, 3, 15, 5, 15, 100, 84, 84, 100, 21, 19, 116, 132,
      150, 15, 21, 15, 101, 85, 15, 15
    ]
  | 8, 3 => #[
      21, 15, 500, 5, 3, 15, 7, 15, 70, 70, 82, 98, 67, 70,
      116, 132, 146, 15, 69, 15, 99, 83, 102, 15, 71, 15, 117, 118,
      134, 15, 150, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 8, 4 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 8, 5 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 8, 6 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 8, 7 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 0 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 1 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 2 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 3 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 4 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 5 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 6 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15
    ]
  | _, _ => #[]

private def ntCert7Entry (s : List ℕ) : ℕ :=
  let rank := ntLehmer s
  (ntCert7Block (rank / 512) (rank / 64 % 8)).getD (rank % 64) 15

private def ntDist7 (s : List ℕ) : ℕ :=
  ntCert7Entry s % 16

private def ntDeleteCode (s : List ℕ) (y : ℕ) : List ℕ :=
  let v := s.getD y 0
  (s.eraseIdx y).map fun x => if v < x then x - 1 else x

private def ntInsertCodeZero (v : ℕ) (s : List ℕ) : List ℕ :=
  v :: s.map fun x => if x < v then x else x + 1

private lemma ntCode_ins_zero (v : Fin 8) (ρ : Equiv.Perm (Fin 7)) :
    ntCode (ntIns 0 v ρ) = ntInsertCodeZero v.val (ntCode ρ) := by
  unfold ntCode ntInsertCodeZero
  rw [List.ofFn_succ, ntIns_apply_same]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    have hi : i < 7 := by simpa using hi₂
    let I : Fin 7 := ⟨i, hi⟩
    simp only [List.getElem_map, List.getElem_ofFn]
    have hpos : (Fin.succ I : Fin 8) = (0 : Fin 8).succAbove I := by
      apply Fin.ext
      simp
    rw [hpos, ntIns_apply_succAbove, ntSuccAbove_val]

private lemma ntDeleteCode_ins (y v : Fin 8) (ρ : Equiv.Perm (Fin 7)) :
    ntDeleteCode (ntCode (ntIns y v ρ)) y.val = ntCode ρ := by
  have hyval : (ntCode (ntIns y v ρ)).getD y.val 0 = v.val := by
    rw [ntCode_getD (ntIns y v ρ) y.val y.is_lt]
    have hy : (⟨y.val, y.is_lt⟩ : Fin 8) = y := Fin.ext rfl
    rw [hy, ntIns_apply_same]
  unfold ntDeleteCode
  rw [hyval]
  apply List.ext_getElem
  · simp [ntCode, List.length_eraseIdx, y.is_lt]
  · intro i hi₁ hi₂
    have hi : i < 7 := by simpa [ntCode] using hi₂
    let I : Fin 7 := ⟨i, hi⟩
    simp only [List.getElem_map]
    have hiErase : i < ((ntCode (ntIns y v ρ)).eraseIdx y.val).length := by
      simpa using hi₁
    have herase :
        ((ntCode (ntIns y v ρ)).eraseIdx y.val)[i]'hiErase =
          (ntIns y v ρ (y.succAbove I)).val := by
      rw [List.getElem_eraseIdx]
      by_cases hiy : i < y.val
      · simp only [hiy, dite_true, ntCode, List.getElem_ofFn]
        apply congrArg Fin.val
        apply congrArg (ntIns y v ρ)
        apply Fin.ext
        rw [ntSuccAbove_val]
        simp [I, hiy]
      · simp only [hiy, dite_false, ntCode, List.getElem_ofFn]
        apply congrArg Fin.val
        apply congrArg (ntIns y v ρ)
        apply Fin.ext
        rw [ntSuccAbove_val]
        simp [I, hiy]
    rw [herase, ntIns_apply_succAbove, ntSuccAbove_val]
    simp only [ntCode, List.getElem_ofFn]
    change (if v.val < (if (ρ I).val < v.val then (ρ I).val else (ρ I).val + 1)
      then (if (ρ I).val < v.val then (ρ I).val else (ρ I).val + 1) - 1
      else if (ρ I).val < v.val then (ρ I).val else (ρ I).val + 1) = (ρ I).val
    split_ifs <;> omega

private def ntOk7 (s : List ℕ) : Bool :=
  let entry := ntCert7Entry s
  let d := entry % 16
  let q := ntQuads 7
  let i := entry / 16
  (d < 15 || !ntIsGB 7 q s) &&
    (d ≥ 15 || if d = 0 then
      (s == List.range 7 || s == (List.range 5 ++ [6, 5]))
    else i < q.length && match ntNbrAt s (q.getD i (0, 0, 0, 0)) with
      | some t => ntDist7 t + 1 == d
      | none => false)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Kernel reduction over all 5,040 codes needs extra depth and heartbeats.
private theorem ntCertificate7 :
    (List.permutations' (List.range 7)).all ntOk7 = true := by
  decide +kernel

private lemma ntCode_even7 : ntCode (ntEven 7) = List.range 7 := by
  decide

private lemma ntCode_odd5 : ntCode (ntOdd 5) = List.range 5 ++ [6, 5] := by
  decide

private lemma ntDist7_reaches_aux (d : ℕ) :
    ∀ σ : Equiv.Perm (Fin 7), ntDist7 (ntCode σ) = d → d < 15 →
      Relation.EqvGen (ntMove 7) σ (ntEven 7) ∨
        Relation.EqvGen (ntMove 7) σ (ntOdd 5) := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
      intro σ hdist hd
      have hok := (List.all_eq_true.mp ntCertificate7) (ntCode σ)
        (ntCode_mem_permutations' σ)
      dsimp only [ntOk7] at hok
      rw [Bool.and_eq_true] at hok
      have hbranch := hok.2
      change (ntDist7 (ntCode σ) ≥ 15 ||
        if ntDist7 (ntCode σ) = 0 then
          (ntCode σ == List.range 7 || ntCode σ == List.range 5 ++ [6, 5])
        else ntCert7Entry (ntCode σ) / 16 < (ntQuads 7).length &&
          match ntNbrAt (ntCode σ)
              ((ntQuads 7).getD (ntCert7Entry (ntCode σ) / 16) (0, 0, 0, 0)) with
          | some t => ntDist7 t + 1 == ntDist7 (ntCode σ)
          | none => false) = true at hbranch
      rw [Bool.or_eq_true] at hbranch
      have hnext :
          (if ntDist7 (ntCode σ) = 0 then
              (ntCode σ == List.range 7 || ntCode σ == List.range 5 ++ [6, 5])
            else ntCert7Entry (ntCode σ) / 16 < (ntQuads 7).length &&
              match ntNbrAt (ntCode σ)
                  ((ntQuads 7).getD (ntCert7Entry (ntCode σ) / 16)
                    (0, 0, 0, 0)) with
              | some t => ntDist7 t + 1 == ntDist7 (ntCode σ)
              | none => false) = true := by
        rcases hbranch with hlarge | hnext
        · have hlarge' : 15 ≤ ntDist7 (ntCode σ) := by
            simpa only [decide_eq_true_eq] using hlarge
          rw [hdist] at hlarge'
          omega
        · exact hnext
      by_cases hd0 : d = 0
      · rw [hdist, ite_eq_left hd0] at hnext
        simp only [Bool.or_eq_true, beq_iff_eq] at hnext
        rcases hnext with heven | hodd
        · have hσ : σ = ntEven 7 := ntCode_injective (heven.trans ntCode_even7.symm)
          rw [hσ]
          exact Or.inl (Relation.EqvGen.refl _)
        · have hσ : σ = ntOdd 5 := ntCode_injective (hodd.trans ntCode_odd5.symm)
          rw [hσ]
          exact Or.inr (Relation.EqvGen.refl _)
      · rw [hdist, ite_eq_right hd0] at hnext
        rw [Bool.and_eq_true] at hnext
        have hi : ntCert7Entry (ntCode σ) / 16 < (ntQuads 7).length := by
          simpa only [decide_eq_true_eq] using hnext.1
        have hstep :
            (match ntNbrAt (ntCode σ)
                ((ntQuads 7).getD (ntCert7Entry (ntCode σ) / 16) (0, 0, 0, 0)) with
              | some t => ntDist7 t + 1 == d
              | none => false) = true := hnext.2
        rw [List.getD_eq_getElem _ _ hi] at hstep
        cases hopt : ntNbrAt (ntCode σ)
            (ntQuads 7)[ntCert7Entry (ntCode σ) / 16] with
        | none => simp [hopt] at hstep
        | some t =>
          have htd : ntDist7 t + 1 = d := by
            simpa only [hopt, beq_iff_eq] using hstep
          have hquad :
              (ntQuads 7)[ntCert7Entry (ntCode σ) / 16] ∈ ntQuads 7 :=
            List.getElem_mem _
          have ht : t ∈ ntNbrs (ntQuads 7) (ntCode σ) := by
            unfold ntNbrs
            rw [List.mem_filterMap]
            exact ⟨_, hquad, hopt⟩
          obtain ⟨τ, hτcode, hmove⟩ := ntNbrs_sound ht
          have hτd : ntDist7 (ntCode τ) < d := by
            rw [hτcode]
            omega
          have hτsmall : ntDist7 (ntCode τ) < 15 := by omega
          have hτreach := ih (ntDist7 (ntCode τ)) hτd τ rfl hτsmall
          have hστ : Relation.EqvGen (ntMove 7) σ τ := by
            rcases hmove with hmove | hmove
            · exact Relation.EqvGen.rel _ _ hmove
            · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hmove)
          rcases hτreach with heven | hodd
          · exact Or.inl (Relation.EqvGen.trans _ _ _ hστ heven)
          · exact Or.inr (Relation.EqvGen.trans _ _ _ hστ hodd)

private lemma ntDist7_reaches (σ : Equiv.Perm (Fin 7))
    (hσ : ntDist7 (ntCode σ) < 15) :
    Relation.EqvGen (ntMove 7) σ (ntEven 7) ∨
      Relation.EqvGen (ntMove 7) σ (ntOdd 5) :=
  ntDist7_reaches_aux (ntDist7 (ntCode σ)) σ rfl hσ

private lemma ntG7_of_eqvGen {σ τ : Equiv.Perm (Fin 7)}
    (hτ : τ ∈ ntG 6) (hστ : Relation.EqvGen (ntMove 7) σ τ) : σ ∈ ntG 6 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (ntClosed_mem (ntE_closed (m := 5)) hστ).2 hτ.1
  · let P : Set (Equiv.Perm (Fin 7)) := {π | ntPat 7 π}
    have hP : ∀ x ∈ P, ∀ y, (ntMove 7 x y ∨ ntMove 7 y x) → y ∈ P := by
      intro x _ y hxy
      exact ntMove_pat (Or.symm hxy)
    exact (ntClosed_mem hP hστ).2 hτ.2.1
  · intro j hj hσK
    by_cases hj0 : j = 0
    · subst j
      rw [ntK_zero_empty hj] at hσK
      exact hσK
    · have hj1 : 1 ≤ j := by omega
      have hK : ∀ x ∈ ntK 7 j hj, ∀ y,
          (ntMove 7 x y ∨ ntMove 7 y x) → y ∈ ntK 7 j hj := by
        intro x hx y hxy
        exact ntK_closed (by omega) hj1 hj hx hxy
      have hτK : τ ∈ ntK 7 j hj :=
        (ntClosed_mem hK hστ).1 hσK
      exact hτ.2.2 j hj hτK

private lemma ntDist7_lt_memG (σ : Equiv.Perm (Fin 7))
    (hσ : ntDist7 (ntCode σ) < 15) : σ ∈ ntG 6 := by
  rcases ntDist7_reaches σ hσ with heven | hodd
  · exact ntG7_of_eqvGen (ntEven_memG (m := 5) (by omega)) heven
  · exact ntG7_of_eqvGen (ntOdd_memG (m := 5) (by omega)) hodd


/-- The `S_5` count. -/
private lemma ntSmall5 : ntncl (ntMove 5) Set.univ = 9 := by
  apply ntNcl_eq_of_reps (x := ntRep5)
  · intro k
    simp
  · intro k
    exact (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).2
      (ntPat_move (ntRep5_pat k))
  · intro k l hkl hrel
    have hlabel := ntEqvGen_label_eq ntCertificate5 hrel
    rw [ntLabel_rep5, ntLabel_rep5] at hlabel
    exact hkl (Fin.ext hlabel)
  · intro z _ hnontrivial
    obtain ⟨w, hstep⟩ :=
      (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).1 hnontrivial
    have hpat : ntPat 5 z := ntMove_pat hstep
    have hlt : ntLabel5 (ntCode z) < 9 := ntPat_label_lt ntCertificate5 hpat
    let k : Fin 9 := ⟨ntLabel5 (ntCode z), hlt⟩
    refine ⟨k, ntDistance_reaches ntRep5 ntCode_rep5 ntCertificate5 z k ?_⟩
    rfl

/-- The `S_6` count. -/
private lemma ntSmall6 : ntncl (ntMove 6) Set.univ = 26 := by
  apply ntNcl_eq_of_reps (x := ntRep6)
  · intro k
    simp
  · intro k
    exact (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).2
      (ntPat_move (ntRep6_pat k))
  · intro k l hkl hrel
    have hlabel := ntEqvGen_label_eq ntCertificate6 hrel
    rw [ntLabel_rep6, ntLabel_rep6] at hlabel
    exact hkl (Fin.ext hlabel)
  · intro z _ hnontrivial
    obtain ⟨w, hstep⟩ :=
      (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).1 hnontrivial
    have hpat : ntPat 6 z := ntMove_pat hstep
    have hlt : ntLabel6 (ntCode z) < 26 := ntPat_label_lt ntCertificate6 hpat
    let k : Fin 26 := ⟨ntLabel6 (ntCode z), hlt⟩
    refine ⟨k, ntDistance_reaches ntRep6 ntCode_rep6 ntCertificate6 z k ?_⟩
    rfl

/-- Every generic element of `S_7` reaches a reference permutation. -/
private lemma ntSmall7 {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ ntG 6) :
    Relation.EqvGen (ntMove 7) σ (ntEven 7) ∨
      Relation.EqvGen (ntMove 7) σ (ntOdd 5) := by
  have hok := (List.all_eq_true.mp ntCertificate7) (ntCode σ)
    (ntCode_mem_permutations' σ)
  have hG := ntIsGB_of_memG7 hσ
  dsimp only [ntOk7] at hok
  rw [Bool.and_eq_true] at hok
  have hlt : ntDist7 (ntCode σ) < 15 := by
    have hfirst := hok.1
    change (ntDist7 (ntCode σ) < 15 || !ntIsGB 7 (ntQuads 7) (ntCode σ)) =
      true at hfirst
    rw [hG] at hfirst
    simpa only [Bool.not_true, Bool.or_false, decide_eq_true_eq] using hfirst
  exact ntDist7_reaches σ hlt

private def ntDeletionChoiceBlock : ℕ → Array ℕ
  | 0 => #[
      0x400000000000000000000000,
      0x20000080000000000000000000000000000000030000000000000000000000,
      0x4000000000000000,
      0x320020000000000000200000000000002000000000000000,
      0x22002000000000000020002030000000,
      0x3000000000000000000000003022000000002200200000000000002000000000,
      0x202200000000220022200000200000000000000000200000,
      0x20000030000000000000000000000030000020220000000000000020000000,
      0x2000002028202000202000002000000000002000202000002000000000000000,
      0x2000000000200000400000000200000000000000400000000000000000000000,
      0x2020020020000020232020002020000020220020000022002020000022002000,
      0x1100100010000000001000008000000001000000000000008222222022202220,
      0x1110111010100100100000101310100010100000101100100000110010100000,
      0x10100010100010100010000040000000000000000000000081111110,
      0x3310301010001010003000001010001030001010000000001010001010001010,
      0x1000101000000000221020101000101010200000310010000000000000100000,
      0x1010000031220010100022102000000010100020100010100000000010100010,
      0x2022001010002211202100102010001010001010002000003011000000001100,
      0x1110100010100000301010202200101000000000201000101000101000000000,
      0x2020111020100010100020102020001020100010100010100020000030000010,
      0x8111101012101100101000004010001010001010001000002010002082212010,
      0x3221201020201110202200201000221020210010221020102000101000200000,
      0x10000040000000000000000000000088228220222122202081121020100020,
      0x1000001012101000101000001011000000001100101000001100100000000000,
      0x1000101000100000811111101110111010800100811110101110110010100000,
      0x1081111010101010311110101010111011110010100011101011001011101010,
      0x3310301010001010003000003000000000000000000000008811811011111110,
      0x1000331030000000101000301000101000000000101000101000101010000000,
      0x2000000030110010100011101031001001000000000000000000000030330010,
      0x3010002022001010000000002010001010001010000000002022001011002210,
      0x1000201020000000301000101111101010301110000010000000000000000000,
      0x10000040100010100010100000000020100080220020112100000020100010,
      0x2022002010002210200000008811811021111110108111100000000000000000,
      0x100000828800202200882181000000201000302200201121000000,
      0x1000000010110000000011001000000011001000000000000010000040000000,
      0x8111101011101100102000008111001011001100100000001000001012001000,
      0x2100101010000000101100101000111010000000111010101000101000100000,
      0x1081118181111010111011001010000080110010110011101000000010100010,
      0x1010003011001011110100001011001010001110101000008811811111111110,
      0x1000101000300000000000000000000000000000808800101100881181000010,
      0x50100010110010100000000030330010100033103000000030100010,
      0x3010001010001010000100000000000000000000000000005010003033001010,
      0x1000101000000000801000202200201000000000301000101100301131000000,
      0x8100000040100010200010100000001000000000000000000000000050100010,
      0x8020208088002020000000005010002022002010000000008088002011008811,
      0x110010100000100000000000000000100010400000000000000000000000,
      0x1020000080001010110000000000000010000010120000000000000010110000,
      0x1011001010001110101100101010001010001010101000008111001011001100,
      0x1100110010100000801000101100101000000000101000102100101000000000,
      0x10110010100011101000000080110010110011101081112080110010,
      0x8011001011001100101000108020001011002010000000001010002011001010,
      0x1100101010000000808801101110881188811110801100101100111010811110,
      0x80100080880010100100000050100010,
      0x5010003033003010000000004010001010003010300000004010001010001010,
      0x2000101000000000000000000000000000000000801000101000101000000000,
      0x20000080100080880030100000000040200020100030100100000040100010,
      0x1000000000000000001000004000000000000000000000008020002020002020,
      0x100000100000101310100010100000100000000000100011100000,
      0x1010001010100010100010100010000080001010111010001020000080000000,
      0x8010001010001010000000001010001031111010101011101010001010001011,
      0x1100101010000000801000101111101010811120800000101110100010100000,
      0x1010000080200010100020100000000010100030110010111100000010100010,
      0x8020001011008011828011108010001011001010108011108000001011001000,
      0x1110100011100000801000202000101000000000501000101100101000000000
    ]
  | 1 => #[
      0x8180111180100010110080118180111080100010111110111080111080000010,
      0x4000000000000000000000008010001011001010000000008011008188818011,
      0x3300301000000000403000301000301000000000401000103000101000000000,
      0x1111111141111111111111111111111180300030300030300000000050100030,
      0x1111111118111111111111111111111111111111111111111111111111111111,
      0x1111111111111111811111111111111111211111811111111111111111111111,
      0x1181111111111111811111111111111111111111111111111111111111111111,
      0x8811811111111111118111218111111111111111111111118811811111111111,
      0x1111881181111111111111811111111111111111111111111111111111111111,
      0x8281111181111111111111111181111181111111111111111111111181881111,
      0x8111118188111111111111118111111111111111111111118188111111118811,
      0x1111811181811111811111111111111111811111811111111111111111111111,
      0x1111111181111111111111111111111181111181888181118181111181111111,
      0x8188118111118811818111118811811181111111118111118111111118111111,
      0x888888818881888181811811811111818881811181811111,
      0x40000000,
      0x8000000000000000002000008000000000000000000000000000000008000000,
      0x8000000000000000000000000000000000000000000000000000000000000000,
      0x80002080000000000000000000000088008000000000000080000000000000,
      0x8000000000000000000000000000000000000000008800800000000000,
      0x800000800000000000000000000000808800000000880080000000,
      0x80000000000000000000000080880000000088008280000080000000,
      0x8000000000000000008000008000000000000000000000008000008088000000,
      0x800000808880800080800000800000000000800080800000,
      0x8080000088008000800000000080000080000000080000000000000080000000,
      0x8888888088808880808008008000008088808000808000008088008000008800,
      0x220020200000220020002000000000200000400000000200000000000000,
      0x82222220222022202020020020000020232020002020000020220020,
      0x7070007070007070000000007070007070007070004000008000000000000000,
      0x200000837030707000707000500000707000707000707000000000,
      0x70700070700070700000000072702070700070702040000032002000,
      0x3022000000002200202000007372007070007270200000007070007070007070,
      0x7000707000000000707200707000727220220020707000707000707000300000,
      0x30000030000020222020002020000070703070720070700000000070700070,
      0x7070007082227070202022207070007070007070202000207070007070007070,
      0x7000707000400000822220202220220020200000707000707000707000400000,
      0x2082222070700070722270702020222070720070700072702022002072702070,
      0x2200200000000000002000008000000000000000000000008872827072227270,
      0x2220220020800000200000203220200020200000202200000000220020200000,
      0x1011001081701070700070700080000081111110111011101010010088228020,
      0x8871817071117170108111107070107071117070101011107171007070007170,
      0x7000707010000000737030707000707000400000300000000000000000000000,
      0x70730070700073703000000070700070700070700000000070700070,
      0x7072007071007270200000007071007070007170103100100100000000000000,
      0x707000707200707000000000707000707000707000000000,
      0x2100000070700070700070702000000070700070711170701030111000001000,
      0x5000007070007070007070000000007070008072007071,
      0x7200707121000000707200707000727020000000887181707111717010811110,
      0x80000080000000000000000010000088880070720088718100000070700070,
      0x2000003022002000200000002022000000002200200000008800800000000000,
      0x7000707000400000811110101110110010100000828800202200880080000000,
      0x1000000070700070710070701000000070710070700071701000000071701070,
      0x8871817171118170808111118811801011101100108000008071007071007170,
      0x7100887181000010707000707100707111010000707100707000717010100000,
      0x3000000070700070700070700030000000000000000000000000000080880070,
      0x7070007073007070000000007070007071007070000000007073007070007370,
      0x7100707131000000707000707000707000010000000000000000000000000000,
      0x70700070700070700000000080700070720070700000000070700070,
      0x8088007071008871810000007070007070007070000000100000000000000000,
      0x807080808800707000000000707000707200707000000000,
      0x80880000000088008080000080000000000000000080001080000000,
      0x8111001011001100101000008000208088000000000000005000002022000000,
      0x7100707000000000707100707000717010110010707000707000707010400000,
      0x2081111080110010110011001080000080700070710070700000000070700070
    ]
  | 2 => #[
      0x7070007071007070000000007071007070007170100000008071007071007170,
      0x7100717010811110808800101100880080800010807000707100707000000000,
      0x100000070700070710070701000000080880170711088888188118080710070,
      0x7070007070007070000000000000000000000000000000008070008088007070,
      0x7000707000000000707000707300707000000000707000707000707030000000,
      0x100000070700070700070700000000000000000000000000000000080700070,
      0x8070007070007070008000008070008088007070000000007070007070007070,
      0x800081800000800000000000000000800000800000000000000000000000,
      0x1010000080000000000000000020000080000080888080008080000080000000,
      0x7070007070007071101000107070007070007070004000008000101011101000,
      0x1110100010800000807000707000707000000000707000707111707010101110,
      0x1100000070700070710070701000000080700070711170702081111080000010,
      0x8000001011008000808000008070007070007070000000007070007071007071,
      0x7100707000000000807000707100807281801180807000707100707010801110,
      0x1080111080000080888080008180000080700070700070700000000070700070,
      0x8071008188888071818088818070007071008071818011808070007071117071,
      0x7000707000000000800000000000000000000000807000707100707000000000,
      0x70700070730070700000000070700070700070700000000070700070,
      0x8811811141111111118111118111111114111111111111118070007070007070,
      0x8881883181811311811111818881811181811111818811611111881181811111,
      0x1111111171711171711171711141111181111111111111111111111188888381,
      0x8871817171117171118111117171117181117171111111117171117171117171,
      0x7111717111111111887181717111717121811111881181111111111111811111,
      0x8181111183881171711188718111111171711181711171711111111171711171,
      0x8188117171118872818811818171117171117171118111118188111111118811,
      0x8881811181811111817131818811717111111111817111717111717111111111,
      0x8181888181711171711181718181118181711171711171711181111181111181,
      0x8888818188818811818111118171117171117171115111118171118188888171,
      0x8888817181818881818811817111887181881181887181718111717111811111,
      0x40000000000000000000000088888881888888818188888181711181,
      0x3000000000000000000000000000000000000000000000000000000,
      0x800000000000000000100000800000000000000000000000,
      0x80000000000000300000000000000000000000000000000000000000000000,
      0x8800800000000000008000108000000000000000000000008800800000000000,
      0x880080000000000000300000000000000000000000000000000000000000,
      0x8180000080000000000000000080000080000000000000000000000080880000,
      0x8000008088000000000000005000000000000000000000008088000000008800,
      0x800080800000800000000000000000800000800000000000000000000000,
      0x80000000000000000000000080000080888080008080000080000000,
      0x8088002000008800808000008800800020000000008000008000000002000000,
      0x800000000000000888882808880882080800200800000808880800080800000,
      0x8080000080880080000088008080000088008000800000000080000080000000,
      0x8000000000000000000000008888888088808880808008008000008088808000,
      0x8000707000000000707000707000707000000000707000707000707000400000,
      0x2080000088008000000000000080000088708070700070700080000070700070,
      0x7070008070007070000000007070007070007070000000008870807070007070,
      0x7000707000800000808800000000880080800000888800707000887080000000,
      0x80700070700070700000000080880070700088728088008080700070,
      0x8070007070007070008000008000008088808000808000008070808088007070,
      0x7000707000800000807000808888807080808880807000707000807080800080,
      0x8088008088708070800070700080000088888080888088008080000080700070,
      0x8888888088888880808888808070008088888070808088808088008070008870,
      0x320020200000420020000000000000300000400000000000000000000000,
      0x2020020083323030322032002030000050000030322030002020000040320000,
      0x7272007070007270202200207270207070007070004000008222222022202220,
      0x887282707222727020822220707020707222707020202220,
      0x80700080700070704000000083703070700070700080000040000000,
      0x200000000000000000000008073008070007370400000008070008070007070,
      0x7000707000000000807200807200727040000000707200707000727020320020,
      0x2030222000002000000000000000000080700080720070700000000080700080,
      0x8070008072007072220000008070008070007070300000007070007072227070,
      0x7222727020822220000000000000000000200000807000807000707000000000,
      0x8200000080700080720070722200000080720080700072704000000088728270,
      0x4300300000000000003000004000000000000000001000008288008072008872
    ]
  | 3 => #[
      0x3200330030000000300000303200300020000000303200000000320020000000,
      0x2000000088708070700070700080000088228020222022002080000038330030,
      0x8088007072008870800000007070007072007070200000007072007070007270,
      0x7000817080100000887181717111717010811111411110101110110010100000,
      0x80880080710088718100001080700080710070711101000080710080,
      0x8073008070007370400000007070007070007070003000000000000000000000,
      0x807000807300707000000000807000807100707000000000,
      0x80700080710070713100000070700070700070700001000000000000,
      0x8070008070007070000000008070008072007070,
      0x7200707000000000808800807100887181000000707000707000707000000030,
      0x30001040000000000000000000000080801080880070700000000080700080,
      0x3000003032000000000000003033000000003300303000003000000000000000,
      0x7000707010800000828800202200880080800000300080303300000000000000,
      0x70700070720070700000000080880070700088708088008080700070,
      0x8071007071007170108111102011001011001100101000008070008088007070,
      0x7100707000000000807000807100707000000000807100807000717040000000,
      0x8111111080880070710088708088118010110010110011001010001080700080,
      0x8070008088007070010000008070008071007070100000008088018088108871,
      0x7000707030000000707000707000707000000000000000000000000000000000,
      0x80700080700070700000000080700080730070700000000080700080,
      0x8070008070007070010000007070007070007070000000000000000000000000,
      0x807000807000807000100000807000808800707000000000,
      0x3030000030000000000030003130000030000000000000000030000050000000,
      0x8000208088808000808000003000000000000000008000003000003033303000,
      0x8888807080808880807000707000807180800080807000707000707000800000,
      0x1081111020000010111010001010000080700070700070700000000080700080,
      0x8070008071007071110000008070008071007070400000008070007071117070,
      0x7100807080801180100000101100100010100000807000807000707000000000,
      0x80700080710070700000000080700080720080718110111080700070,
      0x8070008088888071808088801000001011101000111000008070008070007070,
      0x7100707000000000807100818811808888101111807000807100807181101110,
      0x80700070700070700000000010000000000000000000000080700080,
      0x8070008070007070000000008070008073007070000000008070008070007070,
      0x1111331131511111331131111111111111511111811111111111111111111111,
      0x8181121133333131333133113151111131111131333131113151111131331111,
      0x8288117171118871818811818871817171117171118111118888828188818821,
      0x1111111111111111888888818888887181888881817121818888817181818881,
      0x1111111181711181711171714111111188718171711171711181111121111111,
      0x1211111111111111111111118188118171118871811111118171118171117171,
      0x7111717111111111818811817211887181111111818811717111887181881181,
      0x8181888111112111111111111111111181711181881171711111111181711181,
      0x8171118188118188881111118171118171118171811111118171118188888171,
      0x8888887181888881111111111111111111511111817111817111717111111111,
      0x8811111181711181881181888811111181881181711188718111111188888881,
      0x8000000000000000000000008888118188118888,
      0x300000000000000000000000000000000000000,
      0x80000000000000000020000080000000,
      0x8800800000000000008000000000000030000000000000000000000000000000,
      0x880080000000000000800010400000000000000000000000,
      0x80880000000088008000000000000030000000000000000000000000,
      0x8088000000008800811000008000000000000000008000001000000000000000,
      0x800000808800000000000000500000000000000000000000,
      0x8010000080000000000080008010000080000000000000000080000010000000,
      0x1000000001000000000000008000000000000000000000008000008088108000,
      0x8810800080100000808800200000880080100000880080002000000000800000,
      0x80000080000000010000000000000088881180881088208010010080000080,
      0x8000008088808000808000008088001000008800808000008800800010000000,
      0x7000707000400000800000000000000000000000888881808880881080800100,
      0x80000070700070700070700000000070700070700070700000000070700070,
      0x8870807070007070108000004100100000000000001000008870807070007070,
      0x7000887080000000707000707000707000000000707000707000707000000000,
      0x8011001080700070700070700080000010110000000011001010000081880070,
      0x8070108088007070000000007070007070007070000000008088007070008871,
      0x7000807080100010807000707000707000800000100000101110100010100000
    ]
  | 4 => #[
      0x1050000080700070700070700010000080700080881180708010111080700070,
      0x8088007070008870801100108870807070007070008000001111101011101100,
      0x828811808811887080111110807000808811807080101110,
      0x8080000080880000000088008080000088008000000000000080000080000000,
      0x8888888088808880808008008888808088808800808000008000008088808000,
      0x8888807080808880888800807000887080880080887080708000707000800000,
      0x80000080000000000000000000000088888880888888808088888080708080,
      0x8070008070007070000000008070008070007070400000008870807070007070,
      0x7000887080880080080000000000000000000000808800807000887080000000,
      0x80700080700070700000000080880080720088708000000080880070,
      0x8070008088888070808088800000800000000000000000008080008088007070,
      0x7000807000000000807000808800808888000000807000807000807080000000,
      0x8000000088888880888888708088888000000000000000000080000080700080,
      0x8288008088008888880000008070008088008088880000008088008070008870,
      0x320030000000430030000000000000300000400000000000000000200000,
      0x2020000032330030320033003000000030000030320030002000000030320000,
      0x7072007070007270300000007470407070007070004000008222202022202200,
      0x2220220020200000807300707200737030000000707000707200707020000000,
      0x2202000080720080700072704020000088728272722272702082222242222020,
      0x8088008072008872820000208070008072007072,
      0x7400707000000000807300807000837080000000707000707000707000300000,
      0x2000000000000000000000000000080700080740070700000000080700080,
      0x8070008074007070000000008070008072007072320000007070007070007070,
      0x7000707000000020000000000000000000000000807000807000707000000000,
      0x80700080740070700000000080880080720088728200000070700070,
      0x3000000000000000003000102000000000000000000000008070208088007070,
      0x3300000000000000300000303200000000000000303300000000330030100000,
      0x3011001070700070700070701040000028220020220022002020000030001030,
      0x7080007073007070000000007070007072007070000000007073007070007370,
      0x7000887080000000808800707200887080882280202200202200220020200000,
      0x1010001080700080880070700000000080700080720070700000000080880080,
      0x8088018071108871811111107071007071007170103111101011001011001100,
      0x807000808800707001000000807000808800707010000000,
      0x80700080700070703000000070700070700070700000000000000000,
      0x8070008070007070000000008070008074007070,
      0x8800707000000000807000807000707003000000707000707000707000000000,
      0x30000020000000000000000000000080700080700070700010000080700080,
      0x3000003033103000301000003000000000003000311000003000000000000000,
      0x7000707000400000200080202220200020200000300000000000000000100000,
      0x70700070731170703010111070700070700070713010001070700070,
      0x8070008088888070808288802000002022202000202000007070007070008070,
      0x7000707000000000807000808800808888000000807000807100807080000000,
      0x8110111070700070710070701020111010000010110010001010000080700080,
      0x8070008070007070000000008070008074007070000000008070008071008071,
      0x8800808888101110707000707111707110101110100000101110100011100000,
      0x80700080710070700000000080710081881170711110111180700080,
      0x8070008070007070000000007070007070007070000000001000000000000000,
      0x1111111111511111807000807000707000000000807000807300707000000000,
      0x3111111131331111111133113111111133113111111111111151111121111111,
      0x2222212122212211218111113333113133113311311111113111113133113111,
      0x7311717131111111717311717111737131111111847141717111717111511111,
      0x8188888222222121222122112151111171731171731173713111111171711171,
      0x8171118188118188881211118188118171118871812111118888888288888871,
      0x7111717111211111111111111111111111111111818811818811888888111121,
      0x1111111181711181741171711111111181881181711188718111111171711171,
      0x7171117171117171111211111111111111111111111111118171118188117171,
      0x7111717111111111817111818811717111111111817111818811818888111111,
      0x8811111171711171711171711111113111111111111111111111111181711181,
      0x8181818188117171111111118171118188117171111111118188118188118888,
      0x400000000000000000000000,
      0x80000080000000000000000000000000000000030000000000000000000000,
      0x8000000000000000,
      0x810010000000000000100000000000003000000000000000,
      0x88008000000000000080002080000000
    ]
  | 5 => #[
      0x1000000000000000000000008088000000008800800000000000003000000000,
      0x808800000000880081100000400000000000000000300000,
      0x10000010000000000000000000000080000080880000000000000050000000,
      0x8000008088102000101000008000000000008000801000004000000000000000,
      0x2000000000100000100000000100000000000000800000000000000000000000,
      0x1010010080000080881020001010000080880020000088008010000041001000,
      0x8800800010000000008000008000000001000000000000008121818088102120,
      0x8810881080100100800000808810800080100000808800100000880080100000,
      0x80700070700070700080000080000000000000000000000088881180,
      0x8170107070007070001000007070007070007070000000007070007070007070,
      0x7000707000000000887080707000707020800000880080000000000000800000,
      0x1010000081880070700088708000000070700070700070700000000070700070,
      0x8088007070008871801100107070007070007070003000001011000000001100,
      0x1110100010100000807010808800707000000000707000707000707000000000,
      0x1010111080700070700080708010001070700070700070700010000010000010,
      0x1111101011101100101000008070007070007070001000008070008088117070,
      0x8811707010101110808800707000887080110010717010707000707000100000,
      0x80000080000000000000000000000081812180881171701011111080700080,
      0x8000008088108000801000008088000000008800801000008800800000000000,
      0x7000707000800000888881808880881080800100828810808810880080100000,
      0x8011111080701080881180708010111081880070700088708011001088708070,
      0x8870807070007070008000004000000000000000000000008188118088118870,
      0x7000887080000000807000807000707000000000807000807000707040000000,
      0x8000000070710070700071701031001001000000000000000000000080880080,
      0x8070008088007070000000008070008070007070000000008088008071008870,
      0x7000807080000000707000707111707010101110000010000000000000000000,
      0x10000080700080700070700000000080700080880070711100000080700080,
      0x8088008070008870800000007171117071117170101111300000000000000000,
      0x800000817100808800717111000000807000808800707111000000,
      0x8000000080880000000088008000000088008000000000000080000080000000,
      0x8888808088808800808000008288008088008800800000008000008088008000,
      0x8800807080000000808800707000887080000000887080707000707000800000,
      0x8088888888888080888088008080000080880080880088708000000080700080,
      0x8080008088008088880800008088008070008870808000008888888888888880,
      0x7000707000800000000000000000000000000000808800808800888888000080,
      0x80700080740070700000000080880080700088708000000080700070,
      0x7080007070007070000800000000000000000000000000008070008088007070,
      0x7000707000000000807000808800707000000000807000808800808888000000,
      0x8800000070700070700080700000008000000000000000000000000080700080,
      0x8070208088007070000000008070008088007070000000008088008088008888,
      0x330030200000300000000000000000300020200000000000000000000000,
      0x2020000030002030330000000000000030000030330000000000000030330000,
      0x7073007070007370302200207070007070007070204000002222002022002200,
      0x2200220020200000707000707300707000000000707000707300707000000000,
      0x80740080700074704000000080720070720072702082222020220020,
      0x2022002022002200202000208070008073007070000000008070008073007070,
      0x7400707020000000808802807220887282222220707200707200727020322220,
      0x80700080880070700200000080700080,
      0x8070008088007070000000008070008070007070300000007070007070007070,
      0x7000707000000000000000000000000000000000807000807000707000000000,
      0x20000080700080880070700000000080700080700070700200000070700070,
      0x3000000000000000002000002000000000000000000000008070008070007070,
      0x100000300000303310100010100000300000000000300031200000,
      0x3020002070700070700070700020000020001020221020002020000030000000,
      0x7070007070007070000000007070007073117070101011107070007070007071,
      0x7100707040000000708000707211707020282220200000202210200020200000,
      0x2020000080700080700070700000000080700080730070711100000080700080,
      0x8070008088008088882022207070007072007070202022202000002022002000,
      0x1110100011100000807000807000707000000000807000808800707000000000,
      0x1110111180700080710070713110111070700070711170711010111010000010,
      0x1000000000000000000000008070008071007070000000008071008188117071,
      0x7300707000000000807000807000707000000000707000707000707000000000,
      0x1121113121111111111111111111111180700080700070700000000080700080,
      0x3111113133111111111111113133111111113311312111113111111111111111
    ]
  | 6 => #[
      0x7111717121211111222211212211221121211111311131313311111111111111,
      0x1111111171711171731171711111111171731171711173713122112171711171,
      0x7172117172118271212222812122112122112211212111117171117173117171,
      0x7311717111111111817111817311717111111111817411817111747141111111,
      0x8822222171721171721172712122223121221121221122112121112181711181,
      0x8171118188117171121111118171118188117171211111118188128188218888,
      0x7111717121111111717111717111717111111111111111111111111111111111,
      0x1111111181711181711171711111111181711181881171711111111181711181,
      0x8171118171117171131111117171117171117171111111111111111111111111,
      0x817111817111817111811111817111818811717111111111,
      0x40000000,
      0x8000000000000000002000008000000000000000000000000000000003000000,
      0x3000000000000000000000000000000000000000000000000000000000000000,
      0x80008080000000000000000000000081001000000000000010000000000000,
      0x3000000000000000000000000000000000000000008100100000000000,
      0x800000800000000000000000000000802100000000210010000000,
      0x50000000000000000000000080880000000088008280000080000000,
      0x4000000000000000001000001000000000000000000000008000008088000000,
      0x800000808810300010100000400000000000300030100000,
      0x1010000041001000200000000010000010000000010000000000000080000000,
      0x8121112021102120108001008000008088103000101000004021002000003100,
      0x880080800000810010001000000000800000800000000100000000000000,
      0x81118180881011101010010080000080881010001010000080880010,
      0x7070007070007070000000007070007070007070004000008000000000000000,
      0x800000817010707000707000100000707000707000707000000000,
      0x70700070700070700000000081701070700080708080000081001000,
      0x8088000000008800808000008171007070007170100000007070007070007070,
      0x7000707000000000808800707000887280880080807000707000707000800000,
      0x10000010000010111010001010000080701080880070700000000070700070,
      0x8070008088117070101011107070007070007070301000107070007070007070,
      0x7000707000100000111110101110110010100000807000707000707000100000,
      0x1021111080700080881170701010111070710070700071701011001071701070,
      0x8100100000000000008000008000000000000000000000008171117071118170,
      0x8810110010100000800000808810100010100000808800000000880080800000,
      0x8088008081701070700070700080000088881180881088108080010081112080,
      0x8181118088117170101111108070108088117070101011108188007070008870,
      0x7000807080000000817010707000707000800000400000000000000000000000,
      0x80710080700071701000000080700080700070700000000080700080,
      0x8088008072008870800000008088007070008870808800800100000000000000,
      0x807000808800707000000000807000807000707000000000,
      0x1100000080700080700070703000000070700070711170701010111000001000,
      0x1000008070008070007070000000008070008088007071,
      0x8800707111000000807100807000717010000000717111707111717010111110,
      0x80000080000000000000000010000081710080710071711100000080700080,
      0x8000008088001000100000008088000000008800800000008100100000000000,
      0x7000707000800000828810808810880080800000811100808800110010000000,
      0x1000000080700080880070701000000080880070700088708000000081701070,
      0x8188118188118870808888818188108088108800808000008071008088007170,
      0x8800717111000010807000808800707111010000808800807000887080100000,
      0x8000000070700070700070700030000000000000000000000000000080710080,
      0x8070008088007070000000008070008074007070000000008088008070008870,
      0x7100707131000000707000707000707000010000000000000000000000000000,
      0x80700080700070700000000080700080880070700000000080700080,
      0x8071008071007171130000007070007070007070000000100000000000000000,
      0x807010807100707000000000807000808800707000000000,
      0x80880000000088008080000080000000000000000080008080000000,
      0x8288008088008800808000008000208088000000000000008000008088000000,
      0x8800707000000000808800707000887080880080807000707000807080800000,
      0x8088888080880080880088008080000080700080880070700000000080700080,
      0x8070008088007070000000008088008070008870800000008088008088008870,
      0x8800887080888880808800808800880080800080807000808800707000000000,
      0x800000080700080880080708000000080880880888088888888888080880080,
      0x7070007070007070000000000000000000000000000000008070008088007080,
      0x7000707000000000807000808800707000000000807000807000807080000000
    ]
  | 7 => #[
      0x800000070700070700070700000000000000000000000000000000080700080,
      0x8070008070007070002000008070008088007070000000008070008070007080,
      0x300032200000300000000000000000200000200000000000000000000000,
      0x2020000040000000000000000020000030000030332030002020000030000000,
      0x7070007070007072302000207070007070007070002000002000202022202000,
      0x2220200020200000707000707000707000000000707000707322707020202220,
      0x2200000080700080720070704000000070700070722270702022222020000020,
      0x2000002022002000202000008070008070007070000000008070008073007072,
      0x7400707000000000807000807200807282202220707000707200707020202220,
      0x2020222020000020222020002220000080700080700070700000000080700080,
      0x8072008288227072222022228070008072007072322022207070007072227072,
      0x7000707000000000400000000000000000000000807000807200707000000000,
      0x80700080730070700000000080700080700070700000000070700070,
      0x3111111111111111112111112111111111111111111111118070008070007070,
      0x1111111111311111311111313321311121211111311111111111311123211111,
      0x2121112171711171711171711121111121112121222121112121111141111111,
      0x7171117171117171111111117171117173227171212122217171117171117172,
      0x7211717121111111717111717222717121222221211111212221211121211111,
      0x2121111181711181711171711111111181711181731171722211111181711181,
      0x8171118172117182282122217171117172117171212122212111112122112111,
      0x2221211122211111817111817111717111111111817111817411717111111111,
      0x2221222281711181721171722321222171711171722271722121222121111121,
      0x8111111111111111111111118171118172117171111111118172118288227172,
      0x7311717111111111817111817111717111111111817111717111717111111111,
      0x50000000000000000000000081711181711171711111111181711181,
      0x3000000000000000000000000000000000000000000000000000000,
      0x800000000000000000200000800000000000000000000000,
      0x10000000000000300000000000000000000000000000000000000000000000,
      0x8100100000000000008000208000000000000000000000008100100000000000,
      0x210010000000000000300000000000000000000000000000000000000000,
      0x8880000080000000000000000080000080000000000000000000000080210000,
      0x8000002021000000000000005000000000000000000000008021000000008100,
      0x800080800000800000000000000000800000800000000000000000000000,
      0x80000000000000000000000080000080888080008080000080000000,
      0x4031003000003100101000004100100030000000001000008000000001000000,
      0x100000000000000813111303110313010100100500000303310300010100000,
      0x8080000080110010000081008080000081001000100000000080000080000000,
      0x8000000000000000000000008111111011101110108001008000008088808000,
      0x7000707000000000707000707000707000000000707000707000707000400000,
      0x2080000081001000000000000080000081701070700070700010000070700070,
      0x7070007070007070000000007070007070007070000000008170107070007070,
      0x7000707000800000801100000000810080800000817100707000717010000000,
      0x70700070700070700000000080710070700081888081008080700070,
      0x8070007070007070008000008000008088808000808000008070107071007070,
      0x7000707000100000807000808888807080808880807000707000807080800080,
      0x1011001081701070700070700010000041111010111011001010000080700070,
      0x8171117071117170101111107070007073117070101011107071007070007170,
      0x810080800000810010000000000000800000800000000000000000000000,
      0x8080010081111010111011001020000080000080888080008080000080110000,
      0x8171007070008170808100808170107070007070008000008111818088808110,
      0x817111707111817010111110807010808888807080808880,
      0x80700080700070704000000081701070700070700080000050000000,
      0x100000000000000000000008071008070007170100000008070008070007070,
      0x7000707000000000807100808800817080000000807100707000817080810080,
      0x8080888000001000000000000000000080700080710070700000000080700080,
      0x8070008088008088880000008070008070008070800000008070008088888070,
      0x7111717010111110000000000000000000100000807000807000707000000000,
      0x1100000080700080730070711100000080710080700071701000000071711170,
      0x8100100000000000008000008000000000000000001000008171008071007171,
      0x1100110010000000800000808800800080000000801100000000810080000000,
      0x8000000081701070700070700080000081112080888081008080000081110010,
      0x8071007071007170100000008070008088008070800000008071007070008170,
      0x7000817080100000818111818888817080888881811110808880810080800000,
      0x80710080710071711100001080700080880080888801000080710080
    ]
  | 8 => #[
      0x8071008070008170800000007070007070007070003000000000000000000000,
      0x807000807100707000000000807000808800707000000000,
      0x80700080880080888800000070700070700070700001000000000000,
      0x8070008070007070000000008070008088007070,
      0x7300707000000000807100807100717111000000707000707000707000000010,
      0x80001080000000000000000000000080701080710070700000000080700080,
      0x8000008088000000000000008011000000008100808000008000000000000000,
      0x7000707010800000811100808800810080800000800010101100000000000000,
      0x80700080880070700000000080710070700081708081008080700070,
      0x8071008088008170808288808011008088008100808000008070007071007070,
      0x7100707000000000807000808800707000000000807100807000817080000000,
      0x8881888080710080880081708081888080110080880081008080001080700080,
      0x8070008071007070010000008070008088007070100000008071018088108188,
      0x7000707030000000707000707000707000000000000000000000000000000000,
      0x80700080700070700000000080700080880070700000000080700080,
      0x8070008070007070010000007070007070007070000000000000000000000000,
      0x807000807000707000100000807000807300707000000000,
      0x8080000080000000000080008880000080000000000000000080000080000000,
      0x8000208088808000808000008000000000000000002000008000008088808000,
      0x8888807080808880807000707000808880800080807000707000707000800000,
      0x8082888080000080888080008080000080700070700070700000000080700080,
      0x8070008088008088880000008070008088008070800000008070008088888070,
      0x8800807080808880800000808800800080800000807000807000707000000000,
      0x80700080880070700000000080700080880080888880888080700080,
      0x8070008088888088808088808000008088808000888000008070008070007070,
      0x8800707000000000808800888888808888808888807000808800808888808880,
      0x70700070700070700000000040000000000000000000000080700080,
      0x8070008070007070000000008070008088007070000000008070008070007070,
      0x3222323222222222423222323222323222222222422222222222222222222222,
      0x2222222282322232322232322222222252322232332232322222222242322232,
      0x7272227272227272222222227272227272227272222222224222222222222222,
      0x2222222222222222827222727222727222222222727222727322727222222222,
      0x2222222282722282722272722222222272722272722272722222222242222222,
      0x4222222222222222222222228272228272227272222222228272228273227272,
      0x7422727222222222827222827222727222222222727222727222727222222222,
      0x2222222242222222222222222222222282722282722272722222222282722282,
      0x8272228288227272222222228272228272227272222222227272227272227272,
      0x7222727222222222422222222222222222222222827222827222727222222222,
      0x2222222282722282732272722222222282722282722272722222222272722272,
      0x8000000000000000000000008272228272227272,
      0x800000000000000000000000000000000000000,
      0x80000000000000000080000080000000,
      0x8800800000000000008000000000000080000000000000000000000000000000,
      0x880080000000000000800080800000000000000000000000,
      0x80880000000088008000000000000080000000000000000000000000,
      0x8088000000008800888000008000000000000000008000008000000000000000,
      0x800000808800000000000000800000000000000000000000,
      0x8080000080000000000080008080000080000000000000000080000080000000,
      0x8000000008000000000000008000000000000000000000008000008088808000,
      0x8880800080800000808800800000880080800000880080008000000000800000,
      0x80000080000000080000000000000088888880888088808080080080000080,
      0x8000008088808000808000008088008000008800808000008800800080000000,
      0x8000808000800000800000000000000000000000888888808880888080800800,
      0x80000080800080800080800000000080800080800080800000000080800080,
      0x8880808080008080808000008800800000000000008000008880808080008080,
      0x8000888080000000808000808000808000000000808000808000808000000000,
      0x8088008080800080800080800080000080880000000088008080000088880080,
      0x8080808088008080000000008080008080008080000000008088008080008888,
      0x8000808080800080808000808000808000800000800000808880800080800000,
      0x8080000080800080800080800080000080800080888880808080888080800080,
      0x8088008080008880808800808880808080008080008000008888808088808800,
      0x888888808888888080888880808000808888808080808880,
      0x8080000080880000000088008080000088008000000000000080000080000000,
      0x8888888088808880808008008888808088808800808000008000008088808000
    ]
  | 9 => #[
      0x8888808080808880888800808000888080880080888080808000808000800000,
      0x80000080000000000000000000000088888880888888808088888080808080,
      0x8080008080008080000000008080008080008080800000008880808080008080,
      0x8000888080880080080000000000000000000000808800808000888080000000,
      0x80800080800080800000000080880080880088808000000080880080,
      0x8080008088888080808088800000800000000000000000008080008088008080,
      0x8000808000000000808000808800808888000000808000808000808080000000,
      0x8000000088888880888888808088888000000000000000000080000080800080,
      0x8888008088008888880000008080008088008088880000008088008080008880,
      0x880080000000880080000000000000800000800000000000000000800000,
      0x8080000088880080880088008000000080000080880080008000000080880000,
      0x8088008080008880800000008880808080008080008000008888808088808800,
      0x8880880080800000808800808800888080000000808000808800808080000000,
      0x8808000080880080800088808080000088888888888888808088888888888080,
      0x8088008088008888880000808080008088008088,
      0x8800808000000000808800808000888080000000808000808000808000800000,
      0x8000000000000000000000000000080800080880080800000000080800080,
      0x8080008088008080000000008080008088008088880000008080008080008080,
      0x8000808000000080000000000000000000000000808000808000808000000000,
      0x80800080880080800000000080880080880088888800000080800080,
      0x8000000000000000008000808000000000000000000000008080808088008080,
      0x8800000000000000800000808800000000000000808800000000880080800000,
      0x8088008080800080800080808080000088880080880088008080000080008080,
      0x8080008088008080000000008080008088008080000000008088008080008880,
      0x8000888080000000808800808800888080888880808800808800880080800000,
      0x8080008080800080880080800000000080800080880080800000000080880080,
      0x8088088088808888888888808088008088008880808888808088008088008800,
      0x808000808800808008000000808000808800808080000000,
      0x80800080800080808000000080800080800080800000000000000000,
      0x8080008080008080000000008080008088008080,
      0x8800808000000000808000808000808008000000808000808000808000000000,
      0x80000080000000000000000000000080800080800080800080000080800080,
      0x8000008088808000808000008000000000008000888000008000000000000000,
      0x8000808000800000800080808880800080800000800000000000000000800000,
      0x80800080888880808080888080800080800080888080008080800080,
      0x8080008088888080808888808000008088808000808000008080008080008080,
      0x8000808000000000808000808800808888000000808000808800808080000000,
      0x8880888080800080880080808080888080000080880080008080000080800080,
      0x8080008080008080000000008080008088008080000000008080008088008088,
      0x8800808888808880808000808888808880808880800000808880800088800000,
      0x80800080880080800000000080880088888880888880888880800080,
      0x8080008080008080000000008080008080008080000000008000000000000000,
      0x8888888888888888808000808000808000000000808000808800808000000000,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888
    ]
  | _ => #[]


private def ntDeletionChoice (s : List ℕ) : ℕ :=
  let rank := ntLehmer s
  let word := (ntDeletionChoiceBlock (rank / 4096)).getD (rank / 64 % 64) 0
  (word >>> (4 * (rank % 64))) % 16

private def ntDeletionSliceOk (v : ℕ) (s : List ℕ) : Bool :=
  let full := ntInsertCodeZero v s
  let y := ntDeletionChoice full
  if y < 8 then ntDist7 (ntDeleteCode full y) < 15
  else !ntIsGB 8 (ntQuads 8) full

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- Each slice kernel-checks 5,040 deletion witnesses and needs extra reduction fuel.
private theorem ntDeletionCertificate0 :
    (List.permutations' (List.range 7)).all (ntDeletionSliceOk 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- Each slice kernel-checks 5,040 deletion witnesses and needs extra reduction fuel.
private theorem ntDeletionCertificate1 :
    (List.permutations' (List.range 7)).all (ntDeletionSliceOk 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- Each slice kernel-checks 5,040 deletion witnesses and needs extra reduction fuel.
private theorem ntDeletionCertificate2 :
    (List.permutations' (List.range 7)).all (ntDeletionSliceOk 2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- Each slice kernel-checks 5,040 deletion witnesses and needs extra reduction fuel.
private theorem ntDeletionCertificate3 :
    (List.permutations' (List.range 7)).all (ntDeletionSliceOk 3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- Each slice kernel-checks 5,040 deletion witnesses and needs extra reduction fuel.
private theorem ntDeletionCertificate4 :
    (List.permutations' (List.range 7)).all (ntDeletionSliceOk 4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- Each slice kernel-checks 5,040 deletion witnesses and needs extra reduction fuel.
private theorem ntDeletionCertificate5 :
    (List.permutations' (List.range 7)).all (ntDeletionSliceOk 5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- Each slice kernel-checks 5,040 deletion witnesses and needs extra reduction fuel.
private theorem ntDeletionCertificate6 :
    (List.permutations' (List.range 7)).all (ntDeletionSliceOk 6) = true := by
  decide +kernel

private lemma ntDeletionCertificate (v : Fin 7) :
    (List.permutations' (List.range 7)).all (ntDeletionSliceOk v.val) = true := by
  fin_cases v <;>
    first
    | simpa using ntDeletionCertificate0
    | simpa using ntDeletionCertificate1
    | simpa using ntDeletionCertificate2
    | simpa using ntDeletionCertificate3
    | simpa using ntDeletionCertificate4
    | simpa using ntDeletionCertificate5
    | simpa using ntDeletionCertificate6

/-- Deletion: every generic element is an insertion of a smaller generic one. -/
private lemma ntDeletion {k : ℕ} (hk : 6 ≤ k) {σ : Equiv.Perm (Fin (k + 2))}
    (hσ : σ ∈ ntG (k + 1)) :
    ∃ y : Fin (k + 2), ∃ ρ ∈ ntG k, σ = ntIns y (σ y) ρ := by
  by_cases h : k = 6
  · subst k
    have hvne : (σ 0).val ≠ 7 := by
      intro hv
      apply hσ.1.1
      apply Fin.ext
      simpa using hv
    have hvlt : (σ 0).val < 7 := by
      have := (σ 0).is_lt
      omega
    let v : Fin 7 := ⟨(σ 0).val, hvlt⟩
    obtain ⟨ρ, hσρ⟩ := ntIns_exists 0 (σ 0) σ rfl
    have hok := (List.all_eq_true.mp (ntDeletionCertificate v)) (ntCode ρ)
      (ntCode_mem_permutations' ρ)
    dsimp only [ntDeletionSliceOk] at hok
    have hfull : ntInsertCodeZero v.val (ntCode ρ) = ntCode σ := by
      rw [hσρ, ntCode_ins_zero]
    rw [hfull] at hok
    generalize hyval : ntDeletionChoice (ntCode σ) = y at hok
    by_cases hy : y < 8
    · rw [ite_eq_left hy] at hok
      have hdist : ntDist7 (ntDeleteCode (ntCode σ) y) < 15 := by
        simpa only [decide_eq_true_eq] using hok
      let Y : Fin 8 := ⟨y, hy⟩
      obtain ⟨τ, hστ⟩ := ntIns_exists Y (σ Y) σ rfl
      have hdelete : ntDeleteCode (ntCode σ) y = ntCode τ := by
        rw [hστ]
        exact ntDeleteCode_ins Y (σ Y) τ
      have hτdist : ntDist7 (ntCode τ) < 15 := by
        rwa [hdelete] at hdist
      exact ⟨Y, τ, ntDist7_lt_memG τ hτdist, hστ⟩
    · rw [ite_eq_right hy, ntIsGB_of_memG8 hσ] at hok
      simp at hok
  · exact ntDeletion_large (by omega) hσ

/-- Every generic element reaches a reference permutation. -/
private lemma ntG_two (m : ℕ) {σ : Equiv.Perm (Fin (m + 7))}
    (hσ : σ ∈ ntG (m + 6)) :
    Relation.EqvGen (ntMove (m + 7)) σ (ntEven (m + 7)) ∨
      Relation.EqvGen (ntMove (m + 7)) σ (ntOdd (m + 5)) := by
  induction m with
  | zero => exact ntSmall7 hσ
  | succ m IH =>
    have hE := hσ.1
    obtain ⟨y, ρ, hρ, heq⟩ := ntDeletion (k := m + 6) (by omega) hσ
    have hyv : (y ≠ 0 ∨ σ y ≠ Fin.last (m + 5 + 2)) ∧
        (y ≠ Fin.last (m + 5 + 2) ∨ σ y ≠ 0) := by
      constructor
      · by_cases hy : y = 0
        · refine Or.inr ?_
          intro hcon
          rw [hy] at hcon
          exact hE.1 hcon
        · exact Or.inl hy
      · by_cases hy : y = Fin.last (m + 5 + 2)
        · refine Or.inr ?_
          intro hcon
          rw [hy] at hcon
          exact hE.2 hcon
        · exact Or.inl hy
    have hIH : ∀ ρ ∈ ntG (m + 5 + 1),
        Relation.EqvGen (ntMove (m + 5 + 2)) ρ (ntEven (m + 5 + 2)) ∨
          Relation.EqvGen (ntMove (m + 5 + 2)) ρ (ntOdd (m + 5)) :=
      fun ρ hρ => IH hρ
    have hm55 : 5 ≤ m + 5 := by omega
    rw [heq]
    exact ntInsertion (m := m + 5) hm55 hIH hρ hyv

/-- The extreme-avoiding count is `n + 1`. -/
private lemma ntE_formula (m : ℕ) :
    ntncl (ntMove (m + 7)) (ntE (m + 6)) = m + 8 := by
  have hjpf : ∀ t : Fin (m + 6), t.val + 1 + 1 ≤ m + 7 := by
    intro t
    have ht := t.is_lt
    omega
  have hex : ∀ t : Fin (m + 6), ∃ hub ∈ ntK (m + 7) (t.val + 1) (hjpf t),
      ∀ κ ∈ ntK (m + 7) (t.val + 1) (hjpf t),
        Relation.EqvGen (ntMove (m + 7)) κ hub := by
    intro t
    have ht := t.is_lt
    exact ntK_hub (by omega) (by omega) (hjpf t)
  choose hub hhubmem hhubreach using hex
  have hsub : ∀ t : Fin (m + 6),
      ntK (m + 7) (t.val + 1) (hjpf t) ⊆ ntE (m + 6) := by
    intro t
    have ht := t.is_lt
    exact ntK_sub_E (by omega) (hjpf t)
  have hirr : ∀ a b : Equiv.Perm (Fin (m + 7)),
      ntMove (m + 7) a b → a ≠ b :=
    fun a b h => ntMove_ne h
  have hevenK : ∀ t : Fin (m + 6),
      ntEven (m + 7) ∉ ntK (m + 7) (t.val + 1) (hjpf t) := by
    intro t
    exact ntInc5_notK (k := m + 5) (by omega)
      (by have ht := t.is_lt; omega) (hjpf t) (ntEven_mem m).2.2
  have hoddK : ∀ t : Fin (m + 6),
      ntOdd (m + 5) ∉ ntK (m + 7) (t.val + 1) (hjpf t) := by
    intro t
    exact ntInc5_notK (k := m + 5) (by omega)
      (by have ht := t.is_lt; omega) (hjpf t) (ntOdd_mem m).2.2
  have hclosed : ∀ t : Fin (m + 6),
      ∀ x ∈ ntK (m + 7) (t.val + 1) (hjpf t), ∀ y : Equiv.Perm (Fin (m + 7)),
        (ntMove (m + 7) x y ∨ ntMove (m + 7) y x) →
          y ∈ ntK (m + 7) (t.val + 1) (hjpf t) := by
    intro t x hx y h
    have ht := t.is_lt
    exact ntK_closed (by omega) (by omega) (hjpf t) hx h
  refine ntNcl_eq_of_reps (x := fun k : Fin (m + 8) =>
    if h : k.val < m + 6 then hub ⟨k.val, h⟩
    else if _ : k.val = m + 6 then ntEven (m + 7) else ntOdd (m + 5)) ?_ ?_ ?_ ?_
  · intro k
    by_cases hk : k.val < m + 6
    · simp only [dite_eq_left hk]
      exact hsub ⟨k.val, hk⟩ (hhubmem _)
    · by_cases hk6 : k.val = m + 6
      · simp only [dite_eq_right hk, dite_eq_left hk6]
        exact (ntEven_mem m).1
      · simp only [dite_eq_right hk, dite_eq_right hk6]
        exact (ntOdd_mem m).1
  · intro k
    by_cases hk : k.val < m + 6
    · simp only [dite_eq_left hk]
      exact (ntNcl_nontrivial_iff hirr).mpr (ntPat_move (hhubmem _).2)
    · by_cases hk6 : k.val = m + 6
      · simp only [dite_eq_right hk, dite_eq_left hk6]
        exact (ntNcl_nontrivial_iff hirr).mpr (ntPat_move (ntEven_mem m).2.1)
      · simp only [dite_eq_right hk, dite_eq_right hk6]
        exact (ntNcl_nontrivial_iff hirr).mpr (ntPat_move (ntOdd_mem m).2.1)
  · intro k l hkl h
    have hsign_even : Equiv.Perm.sign (ntEven (m + 7)) = 1 := by
      unfold ntEven
      exact Equiv.Perm.sign_one
    have hsign_odd : Equiv.Perm.sign (ntOdd (m + 5)) = -1 := by
      unfold ntOdd
      apply Equiv.Perm.sign_swap
      intro hcon
      have e2 : m + 5 = m + 5 + 1 := congrArg Fin.val hcon
      omega
    by_cases hk : k.val < m + 6 <;> by_cases hl : l.val < m + 6
    · simp only [dite_eq_left hk, dite_eq_left hl] at h
      set t1 : Fin (m + 6) := ⟨k.val, hk⟩
      set t2 : Fin (m + 6) := ⟨l.val, hl⟩
      have hv1 : t1.val = k.val := rfl
      have hv2 : t2.val = l.val := rfl
      have ht12 : t1 ≠ t2 := by
        intro e
        apply hkl
        have e3 := congrArg Fin.val e
        exact Fin.ext (hv1.symm.trans (e3.trans hv2))
      have hj12 : t1.val + 1 ≠ t2.val + 1 := by
        intro e
        apply ht12
        apply Fin.ext
        omega
      have hdisj := ntK_disjoint (n := m + 7) (j := t1.val + 1) (k := t2.val + 1)
        (by omega) (by have h1 := t1.is_lt; omega) (hjpf t1)
        (by have h2 := t2.is_lt; omega) (hjpf t2) hj12
      have hmem1 : hub t2 ∈ ntK (m + 7) (t1.val + 1) (hjpf t1) :=
        (ntClosed_mem (hclosed t1) h).mp (hhubmem t1)
      exact Set.disjoint_left.mp hdisj hmem1 (hhubmem t2)
    · by_cases hl6 : l.val = m + 6
      · simp only [dite_eq_left hk, dite_eq_right hl, dite_eq_left hl6] at h
        set t1 : Fin (m + 6) := ⟨k.val, hk⟩
        have hmemE : ntEven (m + 7) ∈ ntK (m + 7) (t1.val + 1) (hjpf t1) :=
          (ntClosed_mem (hclosed t1) h).mp (hhubmem t1)
        exact hevenK t1 hmemE
      · simp only [dite_eq_left hk, dite_eq_right hl, dite_eq_right hl6] at h
        set t1 : Fin (m + 6) := ⟨k.val, hk⟩
        have hmemO : ntOdd (m + 5) ∈ ntK (m + 7) (t1.val + 1) (hjpf t1) :=
          (ntClosed_mem (hclosed t1) h).mp (hhubmem t1)
        exact hoddK t1 hmemO
    · by_cases hk6 : k.val = m + 6
      · simp only [dite_eq_right hk, dite_eq_left hk6, dite_eq_left hl] at h
        set t2 : Fin (m + 6) := ⟨l.val, hl⟩
        have h' : Relation.EqvGen (ntMove (m + 7)) (hub t2) (ntEven (m + 7)) :=
          Relation.EqvGen.symm _ _ h
        have hmemE : ntEven (m + 7) ∈ ntK (m + 7) (t2.val + 1) (hjpf t2) :=
          (ntClosed_mem (hclosed t2) h').mp (hhubmem t2)
        exact hevenK t2 hmemE
      · simp only [dite_eq_right hk, dite_eq_right hk6, dite_eq_left hl] at h
        set t2 : Fin (m + 6) := ⟨l.val, hl⟩
        have h' : Relation.EqvGen (ntMove (m + 7)) (hub t2) (ntOdd (m + 5)) :=
          Relation.EqvGen.symm _ _ h
        have hmemO : ntOdd (m + 5) ∈ ntK (m + 7) (t2.val + 1) (hjpf t2) :=
          (ntClosed_mem (hclosed t2) h').mp (hhubmem t2)
        exact hoddK t2 hmemO
    · by_cases hk6 : k.val = m + 6 <;> by_cases hl6 : l.val = m + 6
      · apply hkl
        apply Fin.ext
        omega
      · simp only [dite_eq_right hk, dite_eq_left hk6, dite_eq_right hl,
          dite_eq_right hl6] at h
        have hs := ntEqvGen_sign h
        rw [hsign_even, hsign_odd] at hs
        exact absurd hs (by decide)
      · simp only [dite_eq_right hk, dite_eq_right hk6, dite_eq_right hl,
          dite_eq_left hl6] at h
        have hs := ntEqvGen_sign h
        rw [hsign_odd, hsign_even] at hs
        exact absurd hs (by decide)
      · apply hkl
        apply Fin.ext
        have hkk := k.is_lt
        have hll := l.is_lt
        omega
  · intro z hzE hcardz
    obtain ⟨y, hy⟩ := (ntNcl_nontrivial_iff hirr).mp hcardz
    have hpat : ntPat (m + 7) z := ntMove_pat hy
    by_cases hex : ∃ t : Fin (m + 6), z ∈ ntK (m + 7) (t.val + 1) (hjpf t)
    · obtain ⟨t, hmem⟩ := hex
      have htk : t.val < m + 8 := by
        have ht := t.is_lt
        omega
      refine ⟨⟨t.val, htk⟩, ?_⟩
      have hlt : (⟨t.val, htk⟩ : Fin (m + 8)).val < m + 6 := t.is_lt
      simp only [dite_eq_left hlt]
      have hteq : (⟨(⟨t.val, htk⟩ : Fin (m + 8)).val, hlt⟩ : Fin (m + 6)) = t :=
        Fin.ext rfl
      rw [hteq]
      exact hhubreach t z hmem
    · have hzG : z ∈ ntG (m + 6) := by
        refine ⟨hzE, hpat, ?_⟩
        intro j hj hmem
        by_cases hj0 : j = 0
        · subst hj0
          rw [ntK_zero_empty hj] at hmem
          exact absurd hmem (Set.notMem_empty z)
        · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          have hjm : j' < m + 6 := by omega
          refine hex ⟨⟨j', hjm⟩, ?_⟩
          exact hmem
      rcases ntG_two m hzG with h | h
      · have htk : m + 6 < m + 8 := by omega
        refine ⟨⟨m + 6, htk⟩, ?_⟩
        have hval : ((⟨m + 6, htk⟩ : Fin (m + 8)).val) = m + 6 := rfl
        have hnlt : ¬ ((⟨m + 6, htk⟩ : Fin (m + 8)).val < m + 6) := by omega
        simp only [dite_eq_right hnlt]
        exact h
      · have htk : m + 7 < m + 8 := by omega
        refine ⟨⟨m + 7, htk⟩, ?_⟩
        have hval : ((⟨m + 7, htk⟩ : Fin (m + 8)).val) = m + 7 := rfl
        have hnlt : ¬ ((⟨m + 7, htk⟩ : Fin (m + 8)).val < m + 6) := by omega
        have hne6 : ¬ ((⟨m + 7, htk⟩ : Fin (m + 8)).val = m + 6) := by omega
        simp only [dite_eq_right hnlt, dite_eq_right hne6]
        exact h

/-- The truncated subtraction in the formula never truncates for `n ≥ 5`. -/
private lemma ntNoTrunc (n : ℕ) (hn : 5 ≤ n) : 55 * n ≤ n ^ 3 + 6 * n ^ 2 := by
  have h2 : 25 ≤ n ^ 2 := by
    have h := Nat.mul_le_mul hn hn
    simpa [pow_two] using h
  have h6 : 30 ≤ 6 * n := by omega
  have h55 : 55 ≤ n ^ 2 + 6 * n := by omega
  have hmul := Nat.mul_le_mul (le_refl n) h55
  rw [mul_comm 55 n, show n ^ 3 + 6 * n ^ 2 = n * (n ^ 2 + 6 * n) from by ring]
  exact hmul

/-- The formula numerator casts to integers without truncation issues. -/
private lemma ntNum_cast (k : ℕ) (hk : 5 ≤ k) :
    (((k ^ 3 + 6 * k ^ 2 - 55 * k + 54 : ℕ)) : ℤ) =
      (k : ℤ) ^ 3 + 6 * (k : ℤ) ^ 2 - 55 * (k : ℤ) + 54 := by
  have hle := ntNoTrunc k hk
  rw [Nat.cast_add, Nat.cast_sub hle]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- The multiplied-out step identity for the formula numerator, over `ℤ`. -/
private lemma ntPoly_step (n : ℕ) :
    2 * ((((n + 6 : ℕ)) : ℤ) ^ 3 + 6 * (((n + 6 : ℕ)) : ℤ) ^ 2 -
        55 * (((n + 6 : ℕ)) : ℤ) + 54) -
      ((((n + 5 : ℕ)) : ℤ) ^ 3 + 6 * (((n + 5 : ℕ)) : ℤ) ^ 2 -
        55 * (((n + 5 : ℕ)) : ℤ) + 54) +
      6 * ((((n : ℕ)) : ℤ) + 8) =
      ((((n + 7 : ℕ)) : ℤ) ^ 3 + 6 * (((n + 7 : ℕ)) : ℤ) ^ 2 -
        55 * (((n + 7 : ℕ)) : ℤ) + 54) := by
  push_cast
  ring

/-- The class count equals the formula for all `n ≥ 5`. -/
private lemma ntCount_eq (k : ℕ) (hk : 5 ≤ k) :
    ntncl (ntMove k) Set.univ = (k ^ 3 + 6 * k ^ 2 - 55 * k + 54) / 6 := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 5 := ⟨k - 5, by omega⟩
  have htwo : ∀ t, 6 * ntncl (ntMove (t + 5)) Set.univ =
      (t + 5) ^ 3 + 6 * (t + 5) ^ 2 - 55 * (t + 5) + 54 := by
    intro t
    induction t using Nat.twoStepInduction with
    | zero =>
      have h : 6 * ntncl (ntMove 5) Set.univ =
          5 ^ 3 + 6 * 5 ^ 2 - 55 * 5 + 54 := by
        norm_num [ntSmall5]
      exact h
    | one =>
      have h : 6 * ntncl (ntMove 6) Set.univ =
          6 ^ 3 + 6 * 6 ^ 2 - 55 * 6 + 54 := by
        norm_num [ntSmall6]
      exact h
    | more n ih1 ih2 =>
      have hrec := ntCount_recursion (n + 5)
      have he' : ntncl (ntMove (n + 5 + 2)) (ntE (n + 5 + 1)) = n + 8 :=
        ntE_formula n
      rw [he'] at hrec
      have hrec' : ntncl (ntMove (n + 7)) Set.univ +
          ntncl (ntMove (n + 5)) Set.univ =
          2 * ntncl (ntMove (n + 6)) Set.univ + (n + 8) := hrec
      have hgoal : 6 * ntncl (ntMove (n + 7)) Set.univ =
          (n + 7) ^ 3 + 6 * (n + 7) ^ 2 - 55 * (n + 7) + 54 := by
        have ih1Z : (6 : ℤ) * ((ntncl (ntMove (n + 5)) Set.univ : ℕ) : ℤ) =
            ((((n + 5) ^ 3 + 6 * (n + 5) ^ 2 - 55 * (n + 5) + 54 : ℕ)) : ℤ) := by
          exact_mod_cast ih1
        have ih2Z : (6 : ℤ) * ((ntncl (ntMove (n + 6)) Set.univ : ℕ) : ℤ) =
            ((((n + 6) ^ 3 + 6 * (n + 6) ^ 2 - 55 * (n + 6) + 54 : ℕ)) : ℤ) := by
          exact_mod_cast ih2
        have hrecZ : (6 : ℤ) * ((ntncl (ntMove (n + 7)) Set.univ : ℕ) : ℤ) =
            2 * (6 * ((ntncl (ntMove (n + 6)) Set.univ : ℕ) : ℤ)) -
              6 * ((ntncl (ntMove (n + 5)) Set.univ : ℕ) : ℤ) +
              6 * ((((n : ℕ) + 8 : ℕ)) : ℤ) := by
          have hZ : ((ntncl (ntMove (n + 7)) Set.univ : ℕ) : ℤ) +
              ((ntncl (ntMove (n + 5)) Set.univ : ℕ) : ℤ) =
              2 * ((ntncl (ntMove (n + 6)) Set.univ : ℕ) : ℤ) +
              ((((n : ℕ) + 8 : ℕ)) : ℤ) := by
            exact_mod_cast hrec'
          linarith
        rw [ih1Z, ih2Z] at hrecZ
        have hcast8 : ((((n : ℕ) + 8 : ℕ)) : ℤ) = ((n : ℕ) : ℤ) + 8 := by
          push_cast
          ring
        rw [hcast8] at hrecZ
        have h5 := ntNum_cast (n + 5) (by omega)
        have h6 := ntNum_cast (n + 6) (by omega)
        have h7 := ntNum_cast (n + 7) (by omega)
        rw [h5, h6] at hrecZ
        have hfin : (6 : ℤ) * ((ntncl (ntMove (n + 7)) Set.univ : ℕ) : ℤ) =
            ((((n + 7) ^ 3 + 6 * (n + 7) ^ 2 - 55 * (n + 7) + 54 : ℕ)) : ℤ) := by
          rw [hrecZ, h7]
          exact ntPoly_step n
        exact_mod_cast hfin
      exact hgoal
  have hP := htwo t
  omega

end MetaMathlibExt

@[expose] public section

namespace MetaMathlibExt

/-- **Nontrivial classes under {1234, 3412}-pattern replacement.** Let $n \ge 7$ and let $S_n$ be
the group of permutations of $\{0, 1, \dots, n - 1\}$. A move takes $\sigma \in S_n$ with positions
$i_1 < i_2 < i_3 < i_4$ such that $\sigma(i_1) < \sigma(i_2) < \sigma(i_3) < \sigma(i_4)$ to the
permutation $\tau$ with $\tau(i_1) = \sigma(i_3)$, $\tau(i_2) = \sigma(i_4)$,
$\tau(i_3) = \sigma(i_1)$, $\tau(i_4) = \sigma(i_2)$ and $\tau(j) = \sigma(j)$ for every other
position $j$; that is, it replaces an occurrence of the pattern $1234$ by one of $3412$. Call two
permutations equivalent when one is reached from the other by a finite sequence of moves and
reverse moves. Then the number of equivalence classes with more than one element is
$(n^3 + 6n^2 - 55n + 54)/6$.

This formula was conjectured by Ma; its values form sequence A330395 in the OEIS. The proof
decomposes the exceptional set into swap classes and a generic part. Kernel-checked finite
certificates handle the $S_5$ and $S_6$ classes, reachability in $S_7$ and the deletion boundary
in $S_8$. Point insertion then gives a recurrence, whose solution is the displayed polynomial.

Proves `Wanted` entry `card_nontrivial_1234_3412_classes`.

Source: Quinn Perian, Bella Xu, and Alexander Lu Zhang, "Counting the Nontrivial Equivalence Classes
of Sn Under {1234,3412}-Pattern-Replacement", Journal of Integer Sequences 23 (2020), Article
20.10.2, Theorem `thm:nontrivial`, lines 172-175,
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Zhang/zhang6.tex>.
-/
public theorem card_nontrivial_1234_3412_classes :
    ∀ (n : ℕ), 7 ≤ n →
      let OneMove : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop :=
        fun σ τ => ∃ i1 i2 i3 i4 : Fin n,
          i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
            σ i1 < σ i2 ∧ σ i2 < σ i3 ∧ σ i3 < σ i4 ∧
            τ i1 = σ i3 ∧ τ i2 = σ i4 ∧ τ i3 = σ i1 ∧ τ i4 = σ i2 ∧
            ∀ j : Fin n, j ≠ i1 → j ≠ i2 → j ≠ i3 → j ≠ i4 → τ j = σ j;
      Nat.card { C : Set (Equiv.Perm (Fin n)) //
          ∃ σ, C = { τ | Relation.EqvGen OneMove σ τ } ∧ 1 < Nat.card ↥C } =
        (n ^ 3 + 6 * n ^ 2 - 55 * n + 54) / 6 := by
  intro n hn
  have hequiv : Nat.card { C : Set (Equiv.Perm (Fin n)) //
        ∃ σ, C = { τ | Relation.EqvGen (ntMove n) σ τ } ∧ 1 < Nat.card ↥C } =
      ntncl (ntMove n) Set.univ :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun C => by
      constructor
      · rintro ⟨σ, hC, hcard⟩
        exact ⟨σ, Set.mem_univ σ, hC, hcard⟩
      · rintro ⟨σ, -, hC, hcard⟩
        exact ⟨σ, hC, hcard⟩))
  have hfin : ntncl (ntMove n) Set.univ =
      (n ^ 3 + 6 * n ^ 2 - 55 * n + 54) / 6 :=
    ntCount_eq n (by omega)
  exact hequiv.trans hfin

end MetaMathlibExt
