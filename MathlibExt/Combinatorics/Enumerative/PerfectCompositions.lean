/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

@[expose] public section

section

namespace MetaMathlibExt

/-- Fold-right sum equals `List.sum`. -/
private lemma foldr_add_eq_sum (l : List ℕ) : l.foldr (· + ·) 0 = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.sum_cons, ih]

/-- Expansion of symbolic runs into plain parts. -/
private def expandSym (S : List (ℕ × ℕ)) : List ℕ :=
  S.flatMap fun p => List.replicate p.2 p.1

/-- Canonical realization of a count function: take `c p.1` copies from each run. -/
private def canonSym (S : List (ℕ × ℕ)) (c : ℕ → ℕ) : List ℕ :=
  S.flatMap fun p => List.replicate (c p.1) p.1

/-- Count of a value in a run-expansion, as a sum over matching runs. -/
private lemma count_flatMap_replicate (S : List (ℕ × ℕ)) (g : (ℕ × ℕ) → ℕ) (a : ℕ) :
    (S.flatMap fun p => List.replicate (g p) p.1).count a =
      ((S.filter fun p => p.1 == a).map g).sum := by
  induction S with
  | nil => simp
  | cons q S' ih =>
    simp only [List.flatMap_cons, List.count_append, List.filter_cons]
    rw [List.count_replicate, ih]
    by_cases h : (q.1 == a) = true <;> simp [h]

/-- With distinct first components, filtering runs by value `p.1` gives `[p]`. -/
private lemma filter_fst_eq (S : List (ℕ × ℕ)) (hN : (S.map Prod.fst).Nodup) (p : ℕ × ℕ)
    (hp : p ∈ S) :
    S.filter (fun q => q.1 == p.1) = [p] := by
  set F := S.filter (fun q => q.1 == p.1) with hF
  have hFNodup : F.Nodup :=
    List.Sublist.nodup List.filter_sublist (List.Nodup.of_map _ hN)
  have hmem : ∀ q ∈ F, q.1 = p.1 := by
    intro q hq
    have hq2 := (List.mem_filter.mp hq).2
    exact beq_iff_eq.mp hq2
  have hmapNodup : (F.map Prod.fst).Nodup :=
    List.Sublist.nodup (List.Sublist.map _ List.filter_sublist) hN
  have hmap : F.map Prod.fst = List.replicate F.length p.1 := by
    have hL : (F.map Prod.fst).length = F.length := List.length_map _
    rw [← hL]
    apply List.eq_replicate_of_mem
    intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact hmem q hq
  have hlen : F.length ≤ 1 := by
    rw [hmap] at hmapNodup
    exact (List.nodup_replicate).mp hmapNodup
  have hpF : p ∈ F := List.mem_filter.mpr ⟨hp, by simp⟩
  have hlen1 : F.length = 1 := by
    have hpos : 0 < F.length := List.length_pos_of_mem hpF
    omega
  obtain ⟨p', hp'⟩ := (List.length_eq_one_iff).mp hlen1
  have hpp' : p = p' := by
    have h1 : p ∈ [p'] := hp' ▸ hpF
    exact List.mem_singleton.mp h1
  subst hpp'
  exact hp'

/-- Exact multiplicity of a run value in the expansion (distinct first components). -/
private lemma count_expand_eq (S : List (ℕ × ℕ)) (hN : (S.map Prod.fst).Nodup) (p : ℕ × ℕ)
    (hp : p ∈ S) :
    (expandSym S).count p.1 = p.2 := by
  change (S.flatMap fun q => List.replicate q.2 q.1).count p.1 = p.2
  rw [count_flatMap_replicate _ Prod.snd, filter_fst_eq S hN p hp]
  simp

/-- Exact multiplicity of a value in the canonical realization. -/
private lemma count_canon_eq (S : List (ℕ × ℕ)) (hN : (S.map Prod.fst).Nodup) (c : ℕ → ℕ)
    (a : ℕ) (ha : a ∈ S.map Prod.fst) :
    (canonSym S c).count a = c a := by
  change (S.flatMap fun p => List.replicate (c p.1) p.1).count a = c a
  rw [count_flatMap_replicate]
  obtain ⟨p, hpS, hpa⟩ := List.mem_map.mp ha
  have hfil : (S.filter fun q => q.1 == a) = [p] := by
    have h2 : (S.filter fun q => q.1 == p.1) = [p] := filter_fst_eq S hN p hpS
    simp only [hpa] at h2
    exact h2
  rw [hfil]
  simp [hpa]

/-- The canonical realization is a sublist of the expansion. -/
private lemma canon_sublist (S : List (ℕ × ℕ)) (c : ℕ → ℕ) (h : ∀ p ∈ S, c p.1 ≤ p.2) :
    (canonSym S c).Sublist (expandSym S) := by
  change (S.flatMap fun p => List.replicate (c p.1) p.1).Sublist
    (S.flatMap fun p => List.replicate p.2 p.1)
  induction S with
  | nil => simp
  | cons q S' ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append
      ((List.replicate_sublist_replicate _).mpr (h q (by simp)))
      (ih (fun p hp => h p (by simp [hp])))

/-- Every sublist of an expansion is the canonical realization of its counts. -/
private lemma canon_count_inverse (S : List (ℕ × ℕ)) (hN : (S.map Prod.fst).Nodup)
    (D : List ℕ) (hD : D.Sublist (expandSym S)) :
    canonSym S D.count = D := by
  induction S generalizing D with
  | nil =>
    have hDnil : D = [] := List.sublist_nil.mp (by simpa [expandSym] using hD)
    simp [canonSym, hDnil]
  | cons q S' ih =>
    have hN' : (S'.map Prod.fst).Nodup := (List.nodup_cons.mp hN).2
    have hqnotin : q.1 ∉ S'.map Prod.fst := (List.nodup_cons.mp hN).1
    have hflat : expandSym (q :: S') =
        List.replicate q.2 q.1 ++ expandSym S' := by
      simp [expandSym]
    rw [hflat] at hD
    obtain ⟨D₁, D₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hD
    have hD₁ : D₁ = List.replicate D₁.length q.1 := by
      apply List.eq_replicate_of_mem
      intro b hb
      exact (List.mem_replicate.mp (h₁.subset hb)).2
    have hD₂ : canonSym S' D₂.count = D₂ := ih hN' _ h₂
    have hE'no : q.1 ∉ expandSym S' := by
      intro hmem
      rw [expandSym, List.mem_flatMap] at hmem
      obtain ⟨p, hpS', hpmem⟩ := hmem
      have h2 : p.1 ∈ S'.map Prod.fst := List.mem_map.mpr ⟨p, hpS', rfl⟩
      have h4 : q.1 = p.1 := (List.mem_replicate.mp hpmem).2
      rw [← h4] at h2
      exact hqnotin h2
    have hD₂count0 : D₂.count q.1 = 0 :=
      List.count_eq_zero_of_not_mem (fun hmem => hE'no (h₂.subset hmem))
    have hcount1 : (D₁ ++ D₂).count q.1 = D₁.length := by
      have e : D₁.count q.1 = D₁.length := by
        conv_lhs => rw [hD₁]
        rw [List.count_replicate_self]
      rw [List.count_append, hD₂count0, add_zero, e]
    have hRep : List.replicate ((D₁ ++ D₂).count q.1) q.1 = D₁ := by
      rw [hcount1]; exact hD₁.symm
    have hR' : canonSym S' (D₁ ++ D₂).count = canonSym S' D₂.count := by
      change (S'.flatMap fun p => List.replicate ((D₁ ++ D₂).count p.1) p.1) =
        (S'.flatMap fun p => List.replicate (D₂.count p.1) p.1)
      apply List.flatMap_congr
      intro p hpS'
      have hne : p.1 ≠ q.1 := by
        intro heq
        have h2 : p.1 ∈ S'.map Prod.fst := List.mem_map.mpr ⟨p, hpS', rfl⟩
        rw [heq] at h2
        exact hqnotin h2
      have h0 : D₁.count p.1 = 0 := by
        have hneg : ¬((q.1 == p.1) = true) :=
          fun hc => hne (beq_iff_eq.mp hc).symm
        rw [hD₁, List.count_replicate]
        simp [hneg]
      have hcc : (D₁ ++ D₂).count p.1 = D₂.count p.1 := by
        rw [List.count_append, h0, zero_add]
      rw [hcc]
    change canonSym (q :: S') (D₁ ++ D₂).count = D₁ ++ D₂
    have e1 : canonSym (q :: S') (D₁ ++ D₂).count =
        List.replicate ((D₁ ++ D₂).count q.1) q.1 ++ canonSym S' (D₁ ++ D₂).count := rfl
    rw [e1, hRep, hR', hD₂]

/-- Counts of the canonical realization vanish off the support. -/
private lemma count_canon_support (S : List (ℕ × ℕ)) (c : ℕ → ℕ) (a : ℕ)
    (ha : a ∉ S.map Prod.fst) :
    (canonSym S c).count a = 0 := by
  apply List.count_eq_zero_of_not_mem
  change _ ∉ S.flatMap _
  rw [List.mem_flatMap]
  rintro ⟨p, hpS, hmem⟩
  exact ha (List.mem_map.mpr ⟨p, hpS, (List.mem_replicate.mp hmem).2.symm⟩)

/-- Right inverse: counts of the canonical realization recover `c`. -/
private lemma canon_count_eq_fun (S : List (ℕ × ℕ)) (hN : (S.map Prod.fst).Nodup)
    (c : ℕ → ℕ) (_hc : ∀ a, c a ≤ (expandSym S).count a)
    (hsup : ∀ a, a ∉ S.map Prod.fst → c a = 0) :
    (fun a => (canonSym S c).count a) = c := by
  funext a
  by_cases ha : a ∈ S.map Prod.fst
  · exact count_canon_eq S hN c a ha
  · rw [count_canon_support S c a ha, hsup a ha]

/-- Congruence for unique existence. -/
private lemma existsUnique_congr' {α : Sort*} {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    (∃! x, p x) ↔ (∃! x, q x) := by
  constructor
  · rintro ⟨x, hpx, huniq⟩
    exact ⟨x, (h x).mp hpx, fun y hy => huniq y ((h y).mpr hy)⟩
  · rintro ⟨x, hqx, huniq⟩
    exact ⟨x, (h x).mpr hqx, fun y hy => huniq y ((h y).mp hy)⟩

/-- Elements of the expansion are run values. -/
private lemma mem_expand_map (S : List (ℕ × ℕ)) (a : ℕ) (h : a ∈ expandSym S) :
    a ∈ S.map Prod.fst := by
  have h' : a ∈ S.flatMap (fun p => List.replicate p.2 p.1) := h
  rw [List.mem_flatMap] at h'
  obtain ⟨p, hpS, hpmem⟩ := h'
  exact List.mem_map.mpr ⟨p, hpS, (List.mem_replicate.mp hpmem).2.symm⟩

/-- Per-side correspondence: unique sublist witnesses match unique count vectors. -/
private lemma existsUnique_sublist_iff_canon (S : List (ℕ × ℕ)) (hN : (S.map Prod.fst).Nodup)
    (m : ℕ) :
    (∃! D : List ℕ, D.Sublist (expandSym S) ∧ D.sum = m) ↔
    (∃! c : ℕ → ℕ, (∀ a, c a ≤ (expandSym S).count a) ∧
      (∀ a, a ∉ S.map Prod.fst → c a = 0) ∧ (canonSym S c).sum = m) := by
  constructor
  · rintro ⟨Dstar, ⟨hsub, hsum⟩, huniq⟩
    refine ⟨Dstar.count, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro a
      exact List.Sublist.count_le _ hsub
    · intro a ha
      exact List.count_eq_zero_of_not_mem
        (fun hmem => ha (mem_expand_map S a (hsub.subset hmem)))
    · rw [canon_count_inverse S hN Dstar hsub]
      exact hsum
    · intro c ⟨hc, hsup, hcsum⟩
      -- c = Dstar.count
      have hRcsub : (canonSym S c).Sublist (expandSym S) := by
        apply canon_sublist
        intro p hpS
        calc c p.1 ≤ (expandSym S).count p.1 := hc p.1
          _ = p.2 := count_expand_eq S hN p hpS
      have hRc : canonSym S c = Dstar := huniq _ ⟨hRcsub, hcsum⟩
      have hcc : ∀ a, (canonSym S c).count a = Dstar.count a :=
        fun a => congrArg (List.count a) hRc
      have hfun := canon_count_eq_fun S hN c hc hsup
      have hfin : (fun a => Dstar.count a) = c := by
        funext a
        show Dstar.count a = c a
        rw [← hcc a]
        exact congrFun hfun a
      exact hfin.symm
  · rintro ⟨cstar, ⟨hc, hsup, hcsum⟩, huniq⟩
    refine ⟨canonSym S cstar, ⟨?_, hcsum⟩, ?_⟩
    · apply canon_sublist
      intro p hpS
      calc cstar p.1 ≤ (expandSym S).count p.1 := hc p.1
        _ = p.2 := count_expand_eq S hN p hpS
    · intro D ⟨hDsub, hDsum⟩
      -- D = canonSym S cstar
      have hcD : ∀ a, D.count a ≤ (expandSym S).count a :=
        fun a => List.Sublist.count_le _ hDsub
      have hsupD : ∀ a, a ∉ S.map Prod.fst → D.count a = 0 :=
        fun a ha => List.count_eq_zero_of_not_mem
          (fun hmem => ha (mem_expand_map S a (hDsub.subset hmem)))
      have hsumD : (canonSym S D.count).sum = m := by
        rw [canon_count_inverse S hN D hDsub]
        exact hDsum
      have heq : D.count = cstar := huniq _ ⟨hcD, hsupD, hsumD⟩
      calc D = canonSym S D.count := (canon_count_inverse S hN D hDsub).symm
        _ = canonSym S cstar := by rw [heq]

/-- Transfer of unique-sublist-sum statements along symbolic permutations. -/
private lemma transfer_perfect (S T : List (ℕ × ℕ)) (hNS : (S.map Prod.fst).Nodup)
    (hNT : (T.map Prod.fst).Nodup) (hperm : S.Perm T) (m : ℕ) :
    (∃! D : List ℕ, D.Sublist (expandSym S) ∧ D.sum = m) ↔
    (∃! D : List ℕ, D.Sublist (expandSym T) ∧ D.sum = m) := by
  rw [existsUnique_sublist_iff_canon S hNS m,
    existsUnique_sublist_iff_canon T hNT m]
  have hEperm : (expandSym S).Perm (expandSym T) := by
    change (S.flatMap fun p => List.replicate p.2 p.1).Perm
      (T.flatMap fun p => List.replicate p.2 p.1)
    exact hperm.flatMap (fun a _ => List.Perm.refl _)
  have hcount : ∀ a, (expandSym S).count a = (expandSym T).count a :=
    fun a => List.Perm.count_eq hEperm a
  have hmem : ∀ a, (a ∈ S.map Prod.fst) ↔ (a ∈ T.map Prod.fst) :=
    fun a => List.Perm.mem_iff (hperm.map Prod.fst)
  have hRsum : ∀ c : ℕ → ℕ, (canonSym S c).sum = (canonSym T c).sum := by
    intro c
    apply List.Perm.sum_eq
    change (S.flatMap fun p => List.replicate (c p.1) p.1).Perm
      (T.flatMap fun p => List.replicate (c p.1) p.1)
    exact hperm.flatMap (fun a _ => List.Perm.refl _)
  apply existsUnique_congr'
  intro c
  constructor
  · rintro ⟨hc, hsup, hsum⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rw [← hcount a]
      exact hc a
    · intro a ha
      exact hsup a (fun h => ha ((hmem a).mp h))
    · rw [← hRsum c]
      exact hsum
  · rintro ⟨hc, hsup, hsum⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rw [hcount a]
      exact hc a
    · intro a ha
      exact hsup a (fun h => ha ((hmem a).mpr h))
    · rw [hRsum c]
      exact hsum

/-- A list is a sublist of itself appended with anything on the right. -/
private lemma sublist_append_left' {α : Type*} (M R : List α) : M.Sublist (M ++ R) := by
  rw [List.sublist_append_iff]
  exact ⟨M, [], by simp, List.Sublist.refl _, by simp⟩

/-- A list is a sublist of anything appended on its left. -/
private lemma sublist_append_right' {α : Type*} (L M : List α) : M.Sublist (L ++ M) := by
  rw [List.sublist_append_iff]
  exact ⟨[], M, by simp, by simp, List.Sublist.refl _⟩

/-- A repeated part size with a nonempty middle yields two distinct sublist witnesses. -/
private lemma dup_runs_witnesses (L₁ : List (ℕ × ℕ)) (x z : ℕ × ℕ) (L' : List (ℕ × ℕ))
    (y : ℕ × ℕ) (R : List (ℕ × ℕ))
    (hpos : ∀ p ∈ ([x] ++ z :: L' ++ [y]), 0 < p.1 ∧ 0 < p.2)
    (hxy : x.1 = y.1) (hxz : x.1 ≠ z.1) :
    ∃ (m : ℕ) (D₁ D₂ : List ℕ), 0 < m ∧
      m < (expandSym (L₁ ++ [x] ++ z :: L' ++ [y] ++ R)).sum ∧ D₁ ≠ D₂ ∧
      D₁.Sublist (expandSym (L₁ ++ [x] ++ z :: L' ++ [y] ++ R)) ∧
      D₂.Sublist (expandSym (L₁ ++ [x] ++ z :: L' ++ [y] ++ R)) ∧
      D₁.sum = m ∧ D₂.sum = m := by
  have hBx1 : 0 < x.1 := (hpos x (by simp)).1
  have hBz2 : 0 < z.2 := (hpos z (by simp)).2
  have hBx2 : 0 < x.2 := (hpos x (by simp)).2
  have hBy1 : 0 < y.1 := (hpos y (by simp)).1
  have hBy2 : 0 < y.2 := (hpos y (by simp)).2
  have hBcons : expandSym (z :: L') =
      z.1 :: (List.replicate (z.2 - 1) z.1 ++ expandSym L') := by
    have hz2 : z.2 = (z.2 - 1) + 1 := by omega
    have e2 : (List.replicate z.2 z.1 ++ expandSym L') =
        z.1 :: (List.replicate (z.2 - 1) z.1 ++ expandSym L') := by
      nth_rewrite 1 [hz2]
      rw [List.replicate_succ, List.cons_append]
    exact e2
  refine ⟨x.1 + (expandSym (z :: L')).sum, [x.1] ++ expandSym (z :: L'),
    expandSym (z :: L') ++ [x.1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · -- m < total sum
    have hE : expandSym (L₁ ++ [x] ++ z :: L' ++ [y] ++ R) =
        expandSym L₁ ++
          ((List.replicate x.2 x.1 ++ expandSym (z :: L')) ++
            (List.replicate y.2 y.1 ++ expandSym R)) := by
      simp [expandSym, List.flatMap_append, List.append_assoc]
    have hEsum : (expandSym (L₁ ++ [x] ++ z :: L' ++ [y] ++ R)).sum =
        (expandSym L₁).sum +
          ((x.2 * x.1 + (expandSym (z :: L')).sum) +
            (y.2 * y.1 + (expandSym R).sum)) := by
      rw [hE]
      simp only [List.sum_append, List.sum_replicate, Nat.nsmul_eq_mul,
        List.append_assoc, add_assoc]
    rw [hEsum]
    obtain ⟨u, hu⟩ : ∃ u, x.2 = u + 1 := ⟨x.2 - 1, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, y.2 = v + 1 := ⟨y.2 - 1, by omega⟩
    have hX : x.1 ≤ x.2 * x.1 := by
      rw [hu, add_mul, one_mul]
      omega
    have hY : 1 ≤ y.2 * y.1 := by
      rw [hv, add_mul, one_mul]
      have h1 : 0 ≤ v * y.1 := Nat.zero_le _
      omega
    omega
  · -- D₁ ≠ D₂
    intro hcon
    rw [hBcons] at hcon
    simp only [List.cons_append] at hcon
    exact hxz (List.cons_eq_cons.mp hcon).1
  · -- D₁ sublist
    have hE : expandSym (L₁ ++ [x] ++ z :: L' ++ [y] ++ R) =
        (expandSym L₁ ++ List.replicate x.2 x.1) ++
          (expandSym (z :: L') ++
            (List.replicate y.2 y.1 ++ expandSym R)) := by
      simp [expandSym, List.flatMap_append, List.append_assoc]
    have h1 : [x.1].Sublist (List.replicate x.2 x.1) := by
      change (List.replicate 1 x.1).Sublist _
      exact (List.replicate_sublist_replicate _).mpr hBx2
    rw [hE]
    exact List.Sublist.append
      (h1.trans (sublist_append_right' _ _))
      (sublist_append_left' _ _)
  · -- D₂ sublist
    have hE : expandSym (L₁ ++ [x] ++ z :: L' ++ [y] ++ R) =
        (expandSym L₁ ++ (List.replicate x.2 x.1 ++ expandSym (z :: L'))) ++
          (List.replicate y.2 y.1 ++ expandSym R) := by
      simp [expandSym, List.flatMap_append, List.append_assoc]
    have h1y : [y.1].Sublist (List.replicate y.2 y.1) := by
      change (List.replicate 1 y.1).Sublist _
      exact (List.replicate_sublist_replicate _).mpr hBy2
    rw [hE]
    refine List.Sublist.append ?_ ?_
    · exact (sublist_append_right' _ _).trans (sublist_append_right' _ _)
    · have e : [x.1] = [y.1] := by rw [hxy]
      rw [e]
      exact h1y.trans (sublist_append_left' _ _)
  · -- sums
    simp
  · simp [add_comm]

/-- Either first components are distinct, or a repeated value with middle occurs. -/
private lemma nodup_or_dup_pattern (C : List (ℕ × ℕ))
    (hCadj : (C.map Prod.fst).IsChain (· ≠ ·)) :
    (C.map Prod.fst).Nodup ∨
    ∃ L₁ x z L' y R, C = L₁ ++ [x] ++ z :: L' ++ [y] ++ R ∧
      x.1 = y.1 ∧ x.1 ≠ z.1 := by
  induction C with
  | nil => exact Or.inl List.nodup_nil
  | cons x C' ih =>
    by_cases hxmem : x.1 ∈ C'.map Prod.fst
    · obtain ⟨y, hyC', hyx⟩ := List.mem_map.mp hxmem
      obtain ⟨L, R, hLR⟩ := List.append_of_mem hyC'
      cases L with
      | nil =>
        exfalso
        have hmap : (x :: C').map Prod.fst = x.1 :: y.1 :: (R.map Prod.fst) := by
          rw [hLR]; simp
        rw [hmap] at hCadj
        have h2 := (List.isChain_cons_cons.mp hCadj).1
        rw [hyx] at h2
        exact h2 rfl
      | cons z L' =>
        refine Or.inr ⟨[], x, z, L', y, R, ?_, ?_, ?_⟩
        · simp [hLR]
        · exact hyx.symm
        · have hmap : (x :: C').map Prod.fst =
              x.1 :: z.1 :: ((L'.map Prod.fst) ++ y.1 :: R.map Prod.fst) := by
            rw [hLR]; simp [List.map_append]
          rw [hmap] at hCadj
          exact (List.isChain_cons_cons.mp hCadj).1
    · have hCadj' : (C'.map Prod.fst).IsChain (· ≠ ·) := by
        have ht := hCadj.tail
        simpa using ht
      cases ih hCadj' with
      | inl hN => exact Or.inl (List.nodup_cons.mpr ⟨hxmem, hN⟩)
      | inr h =>
        obtain ⟨L₁, xx, z, L', y, R, hC, hxy, hxz⟩ := h
        refine Or.inr ⟨x :: L₁, xx, z, L', y, R, ?_, hxy, hxz⟩
        simp [hC]

/-- A perfect expansion has globally distinct first components. -/
private lemma perfect_imp_nodup (C : List (ℕ × ℕ))
    (hCpos : ∀ p ∈ C, 0 < p.1 ∧ 0 < p.2)
    (hCadj : (C.map Prod.fst).IsChain (· ≠ ·))
    (hperf : ∀ m : ℕ, 0 < m → m < (expandSym C).sum →
      ∃! D : List ℕ, D.Sublist (expandSym C) ∧ D.sum = m) :
    (C.map Prod.fst).Nodup := by
  by_contra hN
  obtain ⟨L₁, x, z, L', y, R, hC, hxy, hxz⟩ :=
    (nodup_or_dup_pattern C hCadj).resolve_left hN
  have hpos : ∀ p ∈ ([x] ++ z :: L' ++ [y]), 0 < p.1 ∧ 0 < p.2 := by
    intro p hp
    apply hCpos
    rw [hC]
    simp only [List.mem_append, List.mem_cons] at hp ⊢
    tauto
  obtain ⟨m, D₁, D₂, hm0, hmn, hne, hs1, hs2, he1, he2⟩ :=
    dup_runs_witnesses L₁ x z L' y R hpos hxy hxz
  rw [← hC] at hmn hs1 hs2
  exact hne (ExistsUnique.unique (hperf m hm0 hmn) ⟨hs1, he1⟩ ⟨hs2, he2⟩)

/-- Insert a run into a fst-sorted list. -/
private def insByFst (p : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [p]
  | q :: S => if p.1 ≤ q.1 then p :: q :: S else q :: insByFst p S

/-- Insertion sort by first component. -/
private def isortByFst : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | q :: S => insByFst q (isortByFst S)

private lemma mem_insByFst (p a : ℕ × ℕ) (S : List (ℕ × ℕ)) :
    a ∈ insByFst p S ↔ a = p ∨ a ∈ S := by
  induction S with
  | nil => simp [insByFst]
  | cons q S' ih =>
    by_cases h : p.1 ≤ q.1
    · simp only [insByFst, h, ite_true, List.mem_cons]
    · simp only [insByFst, h, ite_false, List.mem_cons, ih]
      tauto

private lemma perm_insByFst (p : ℕ × ℕ) (S : List (ℕ × ℕ)) :
    (insByFst p S).Perm (p :: S) := by
  induction S with
  | nil => exact List.Perm.refl _
  | cons q S' ih =>
    by_cases h : p.1 ≤ q.1
    · simp only [insByFst, h, ite_true]
      exact List.Perm.refl _
    · simp only [insByFst, h, ite_false]
      exact (ih.cons q).trans (List.Perm.swap p q S')

private lemma perm_isortByFst (S : List (ℕ × ℕ)) : (isortByFst S).Perm S := by
  induction S with
  | nil => exact List.Perm.refl _
  | cons q S' ih =>
    have e : isortByFst (q :: S') = insByFst q (isortByFst S') := rfl
    rw [e]
    exact (perm_insByFst q _).trans (ih.cons q)

private lemma pairwise_le_insByFst (p : ℕ × ℕ) (T : List (ℕ × ℕ))
    (hT : T.Pairwise (fun a b => a.1 ≤ b.1)) :
    (insByFst p T).Pairwise (fun a b => a.1 ≤ b.1) := by
  induction T with
  | nil => simp [insByFst]
  | cons r T' ih =>
    by_cases h : p.1 ≤ r.1
    · simp only [insByFst, h, ite_true]
      rw [List.pairwise_cons]
      refine ⟨?_, hT⟩
      intro x hx
      simp only [List.mem_cons] at hx
      cases hx with
      | inl heq => rw [heq]; exact h
      | inr hmem =>
        have hrx : r.1 ≤ x.1 := (List.pairwise_cons.mp hT).1 x hmem
        exact le_trans h hrx
    · simp only [insByFst, h, ite_false]
      rw [List.pairwise_cons]
      refine ⟨?_, ih (List.pairwise_cons.mp hT).2⟩
      intro x hx
      have hx' : x = p ∨ x ∈ T' := (mem_insByFst p x T').mp hx
      cases hx' with
      | inl heq => rw [heq]; exact le_of_not_ge h
      | inr hmem => exact (List.pairwise_cons.mp hT).1 x hmem

private lemma pairwise_le_isortByFst (S : List (ℕ × ℕ)) :
    (isortByFst S).Pairwise (fun a b => a.1 ≤ b.1) := by
  induction S with
  | nil => simp [isortByFst]
  | cons q S' ih =>
    have e : isortByFst (q :: S') = insByFst q (isortByFst S') := rfl
    rw [e]
    exact pairwise_le_insByFst q _ ih

/-- Pairwise `≤` on pairs gives pairwise `≤` on first components. -/
private lemma pairwise_map_fst_le (P : List (ℕ × ℕ))
    (h : P.Pairwise (fun a b => a.1 ≤ b.1)) :
    (P.map Prod.fst).Pairwise (· ≤ ·) := by
  induction P with
  | nil => simp
  | cons q P' ih =>
    simp only [List.map_cons] at h ⊢
    rw [List.pairwise_cons] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ih h2⟩
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact h1 r hr

/-- Pairwise `≤` plus distinctness gives pairwise `<`. -/
private lemma pairwise_lt_of_pairwise_le_nodup (L : List ℕ) (hle : L.Pairwise (· ≤ ·))
    (hn : L.Nodup) : L.Pairwise (· < ·) := by
  induction L with
  | nil => simp
  | cons a L' ih =>
    rw [List.pairwise_cons] at hle ⊢
    obtain ⟨hle1, hle2⟩ := hle
    have hn' : L'.Nodup := (List.nodup_cons.mp hn).2
    refine ⟨?_, ih hle2 hn'⟩
    intro x hx
    have hne : a ≠ x := by
      intro heq
      have hmem : a ∈ L' := heq ▸ hx
      exact (List.nodup_cons.mp hn).1 hmem
    exact lt_of_le_of_ne (hle1 x hx) hne

/-- Pairwise `<` gives distinctness. -/
private lemma pairwise_lt_nodup (L : List ℕ) (h : L.Pairwise (· < ·)) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a L' ih =>
    rw [List.pairwise_cons] at h
    refine List.nodup_cons.mpr ⟨?_, ih h.2⟩
    intro hmem
    exact absurd (h.1 _ hmem) (lt_irrefl _)

/--
**Perfect compositions are permuted perfect partitions.** Call a list $L$ of positive integers
perfect for $n$ if for every integer $m$ with $0 < m < n$ there is exactly one list of integers
that is a sublist of $L$ (its entries taken in order, not necessarily contiguous) and has sum
$m$. A symbolic part $(a, u)$ with $a, u > 0$ stands for a run of $u$ copies of $a$, and the
expansion of a list of symbolic parts is the concatenation of their runs. Let $n$ be a natural
number and let $C$ be a list of symbolic parts, any two adjacent ones having different values
$a$, whose expansion has sum $n$. Then the expansion of $C$ is perfect for $n$ if and only if
$C$ is a permutation of a list $P$ of symbolic parts $(a, u)$ with $a, u > 0$ and strictly
increasing values $a$ whose expansion has sum $n$ and is perfect for $n$.
-/
theorem perfect_composition_iff_symbolic_parts_perm_perfect_partition_general
    (n : ℕ)
    (C : List (ℕ × ℕ))
    (hCpos : ∀ p ∈ C, 0 < p.1 ∧ 0 < p.2)
    (hCadj : (C.map Prod.fst).IsChain (· ≠ ·))
    (hCsum : (C.flatMap fun p => List.replicate p.2 p.1).foldr (· + ·) 0 = n) :
    let expand : List (ℕ × ℕ) → List ℕ :=
      fun S => S.flatMap fun p => List.replicate p.2 p.1
    let IsPerfect : List (ℕ × ℕ) → ℕ → Prop :=
      fun S k =>
        ∀ m : ℕ, 0 < m → m < k →
          ∃! D : List ℕ, D.Sublist (expand S) ∧ D.foldr (· + ·) 0 = m
    IsPerfect C n ↔
      ∃ P : List (ℕ × ℕ),
        (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2) ∧
        (P.map Prod.fst).Pairwise (· < ·) ∧
        (expand P).foldr (· + ·) 0 = n ∧
        IsPerfect P n ∧ C.Perm P := by
  change ((∀ m : ℕ, 0 < m → m < n →
      ∃! D : List ℕ, D.Sublist (expandSym C) ∧ D.foldr (· + ·) 0 = m) ↔
    ∃ P : List (ℕ × ℕ),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2) ∧
      (P.map Prod.fst).Pairwise (· < ·) ∧
      (expandSym P).foldr (· + ·) 0 = n ∧
      (∀ m : ℕ, 0 < m → m < n →
        ∃! D : List ℕ, D.Sublist (expandSym P) ∧ D.foldr (· + ·) 0 = m) ∧
      C.Perm P)
  refine Iff.intro ?_ ?_
  · -- Forward: sort the runs.
    intro hPerf
    have hPerfS : ∀ m : ℕ, 0 < m → m < n →
        ∃! D : List ℕ, D.Sublist (expandSym C) ∧ D.sum = m := by
      intro m hm0 hmn
      obtain ⟨D, ⟨hDsub, hDsum⟩, huniq⟩ := hPerf m hm0 hmn
      refine ⟨D, ⟨hDsub, by rw [← foldr_add_eq_sum]; exact hDsum⟩, ?_⟩
      intro D' hD'
      obtain ⟨h1, h2⟩ := hD'
      exact huniq D' ⟨h1, by rw [foldr_add_eq_sum]; exact h2⟩
    have hnsum : (expandSym C).sum = n := by
      rw [← foldr_add_eq_sum]; exact hCsum
    have hNodupC : (C.map Prod.fst).Nodup := by
      apply perfect_imp_nodup C hCpos hCadj
      intro m hm0 hmn
      rw [hnsum] at hmn
      exact hPerfS m hm0 hmn
    have hpermC : (isortByFst C).Perm C := perm_isortByFst C
    have hNodupP : ((isortByFst C).map Prod.fst).Nodup :=
      (List.Perm.nodup_iff ((perm_isortByFst C).map Prod.fst)).mpr hNodupC
    refine ⟨isortByFst C, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      exact hCpos p ((List.Perm.mem_iff hpermC).mp hp)
    · exact pairwise_lt_of_pairwise_le_nodup _
        (pairwise_map_fst_le _ (pairwise_le_isortByFst C)) hNodupP
    · have hEperm : (expandSym (isortByFst C)).Perm (expandSym C) := by
        change ((isortByFst C).flatMap fun p => List.replicate p.2 p.1).Perm
          (C.flatMap fun p => List.replicate p.2 p.1)
        exact hpermC.flatMap (fun a _ => List.Perm.refl _)
      have hsum : (expandSym (isortByFst C)).sum = (expandSym C).sum :=
        hEperm.sum_eq
      rw [foldr_add_eq_sum, hsum, ← foldr_add_eq_sum]
      exact hCsum
    · intro m hm0 hmn
      obtain ⟨D, ⟨hDsub, hDsum⟩, huniq⟩ :=
        (transfer_perfect C (isortByFst C) hNodupC hNodupP hpermC.symm m).mp
          (hPerfS m hm0 hmn)
      refine ⟨D, ⟨hDsub, by rw [foldr_add_eq_sum]; exact hDsum⟩, ?_⟩
      intro D' hD'
      obtain ⟨h1, h2⟩ := hD'
      exact huniq D' ⟨h1, by rw [← foldr_add_eq_sum]; exact h2⟩
    · exact hpermC.symm
  · -- Reverse: transfer perfectness back along the permutation.
    intro hP
    obtain ⟨P, hPpos, hPpair, hPsum, hPperf, hPperm⟩ := hP
    have hNodupP : (P.map Prod.fst).Nodup := pairwise_lt_nodup _ hPpair
    have hNodupC : (C.map Prod.fst).Nodup :=
      (List.Perm.nodup_iff (hPperm.map Prod.fst)).mpr hNodupP
    intro m hm0 hmn
    obtain ⟨D, ⟨hDsub, hDsum⟩, huniq⟩ := hPperf m hm0 hmn
    have hPmS : ∃! D : List ℕ, D.Sublist (expandSym P) ∧ D.sum = m := by
      refine ⟨D, ⟨hDsub, by rw [← foldr_add_eq_sum]; exact hDsum⟩, ?_⟩
      intro D' hD'
      obtain ⟨h1, h2⟩ := hD'
      exact huniq D' ⟨h1, by rw [foldr_add_eq_sum]; exact h2⟩
    obtain ⟨D', ⟨hD'sub, hD'sum⟩, huniq'⟩ :=
      (transfer_perfect P C hNodupP hNodupC hPperm.symm m).mp hPmS
    refine ⟨D', ⟨hD'sub, by rw [foldr_add_eq_sum]; exact hD'sum⟩, ?_⟩
    intro D'' hD''
    obtain ⟨h1, h2⟩ := hD''
    exact huniq' D'' ⟨h1, by rw [← foldr_add_eq_sum]; exact h2⟩

set_option linter.unusedVariables false in
/--
**Munagi's theorem on perfect compositions.** Call a list $L$ of positive integers perfect for
$n$ if for every integer $m$ with $0 < m < n$ there is exactly one list of integers that is a
sublist of $L$ (its entries taken in order, not necessarily contiguous) and has sum $m$. A
symbolic part $(a, u)$ with $a, u > 0$ stands for a run of $u$ copies of $a$, and the expansion
of a list of symbolic parts is the concatenation of their runs. Let $n > 0$ and let $C$ be a list
of symbolic parts, any two adjacent ones having different values $a$, whose expansion has sum
$n$. Then the expansion of $C$ is perfect for $n$ if and only if $C$ is a permutation of a list
$P$ of symbolic parts $(a, u)$ with $a, u > 0$ and strictly increasing values $a$ whose
expansion has sum $n$ and is perfect for $n$.

Proves `Wanted` entry `perfect_composition_iff_symbolic_parts_perm_perfect_partition`.

Source: Augustine O. Munagi, "Perfect Compositions of Numbers," Journal of Integer
Sequences 23 (2020), Article 20.5.1, Theorem 1 (label `thm1`), lines 138–140,
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Munagi/munagi13.tex>.
-/
@[nolint unusedArguments]
theorem perfect_composition_iff_symbolic_parts_perm_perfect_partition
    (n : ℕ)
    (hn : 0 < n)
    (C : List (ℕ × ℕ))
    (hCpos : ∀ p ∈ C, 0 < p.1 ∧ 0 < p.2)
    (hCadj : (C.map Prod.fst).IsChain (· ≠ ·))
    (hCsum : (C.flatMap fun p => List.replicate p.2 p.1).foldr (· + ·) 0 = n) :
    let expand : List (ℕ × ℕ) → List ℕ :=
      fun S => S.flatMap fun p => List.replicate p.2 p.1
    let IsPerfect : List (ℕ × ℕ) → ℕ → Prop :=
      fun S k =>
        ∀ m : ℕ, 0 < m → m < k →
          ∃! D : List ℕ, D.Sublist (expand S) ∧ D.foldr (· + ·) 0 = m
    IsPerfect C n ↔
      ∃ P : List (ℕ × ℕ),
        (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2) ∧
        (P.map Prod.fst).Pairwise (· < ·) ∧
        (expand P).foldr (· + ·) 0 = n ∧
        IsPerfect P n ∧ C.Perm P := by
  exact perfect_composition_iff_symbolic_parts_perm_perfect_partition_general n C hCpos hCadj hCsum


end MetaMathlibExt
