/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- Fold a composition `a :: h'` of `k+1` into a palindrome of `2k`: the tail `h'`
becomes the outer half and `a` determines the (possibly empty) even middle part. -/
private def psi : List ℕ → List ℕ
  | [] => []
  | [a] => if a = 1 then [] else [2 * (a - 1)]
  | a :: x :: rest => x :: psi (a :: rest) ++ [x]
termination_by l => l.length

/-- Inverse of `psi`: unfold a palindrome into a composition. -/
private def phi (c : List ℕ) : List ℕ :=
  c.bidirectionalRecOn [1] (fun m => [m / 2 + 1]) (fun a _l _b ih => ih.headI :: a :: ih.tail)

@[simp] private theorem phi_nil : phi [] = [1] := by simp [phi]
@[simp] private theorem phi_singleton (m : ℕ) : phi [m] = [m / 2 + 1] := by simp [phi]
@[simp] private theorem phi_cons_append (a b : ℕ) (l : List ℕ) :
    phi (a :: (l ++ [b])) = (phi l).headI :: a :: (phi l).tail := by
  simp only [phi, List.bidirectionalRecOn]; rw [List.bidirectionalRec_cons_append]

private theorem phi_ne_nil (c : List ℕ) : phi c ≠ [] := by
  induction c using List.bidirectionalRecOn with
  | H0 => simp | H1 a => simp | Hn a l b _ => simp

private theorem psi_reverse : ∀ d : List ℕ, (psi d).reverse = psi d := by
  intro d
  induction d using psi.induct with
  | case1 => simp [psi]
  | case2 => simp [psi]
  | case3 a h => simp [psi, h]
  | case4 a x rest ih =>
    rw [psi]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [ih]

private theorem psi_sum : ∀ d : List ℕ, (∀ a ∈ d, 1 ≤ a) → d ≠ [] → (psi d).sum = 2 * d.sum -
    2 := by
  intro d
  induction d using psi.induct with
  | case1 => simp
  | case2 => simp [psi]
  | case3 a h =>
    intro hpos _
    have : 1 ≤ a := hpos a (by simp)
    simp only [psi, h, ite_false, List.sum_cons, List.sum_nil]
    omega
  | case4 a x rest ih =>
    intro hpos _
    have hposrest : ∀ b ∈ (a :: rest), 1 ≤ b := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hpos b (by simp)
      · exact hpos b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb))
    have IH := ih hposrest (by simp)
    have hx : 1 ≤ x := hpos x (by simp)
    have ha : 1 ≤ a := hpos a (by simp)
    have e1 : (psi (a :: x :: rest)).sum = 2 * x + (psi (a :: rest)).sum := by
      rw [psi]; simp [List.sum_append]; ring
    rw [e1, IH]
    simp only [List.sum_cons]
    omega

private theorem psi_valid : ∀ d : List ℕ, (∀ a ∈ d, 0 < a ∧ a ≠ 2) → d ≠ [] →
    ∀ b ∈ psi d, 0 < b ∧ b ≠ 2 := by
  intro d
  induction d using psi.induct with
  | case1 => simp
  | case2 => simp [psi]
  | case3 a h =>
    intro hval _
    have := hval a (by simp)
    simp only [psi, h, ite_false, List.mem_singleton]
    rintro b rfl
    omega
  | case4 a x rest ih =>
    intro hval _
    have hval' : ∀ c ∈ (a :: rest), 0 < c ∧ c ≠ 2 := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hval c (by simp)
      · exact hval c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
    have IH := ih hval' (by simp)
    have hx := hval x (by simp)
    rw [psi]
    intro b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with (rfl | hb) | rfl
    · exact hx
    · exact IH b hb
    · exact hx

private theorem phi_psi : ∀ d : List ℕ, (∀ a ∈ d, 0 < a ∧ a ≠ 2) → d ≠ [] → phi (psi d) = d := by
  intro d
  induction d using psi.induct with
  | case1 => intro _ hne; exact absurd rfl hne
  | case2 => intro _ _; simp [psi]
  | case3 a h =>
    intro hval _
    have ha := (hval a (by simp)).1
    simp only [psi, h, ite_false, phi_singleton]
    congr 1
    omega
  | case4 a x rest ih =>
    intro hval _
    have hval' : ∀ c ∈ (a :: rest), 0 < c ∧ c ≠ 2 := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hval c (by simp)
      · exact hval c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
    have IH := ih hval' (by simp)
    have hpsi : psi (a :: x :: rest) = x :: (psi (a :: rest) ++ [x]) := by
      rw [psi, List.cons_append]
    rw [hpsi, phi_cons_append, IH]
    simp

private theorem psi_phi : ∀ c : List ℕ, c.reverse = c → (∀ a ∈ c, 0 < a ∧ a ≠ 2) → Even c.sum →
    psi (phi c) = c := by
  intro c
  induction c using List.bidirectionalRecOn with
  | H0 => intro _ _ _; simp [psi]
  | H1 m =>
    intro _ hval heven
    have hme : Even m := by simpa using heven
    have hm0 : 0 < m := (hval m (by simp)).1
    simp only [phi_singleton]
    have h1 : m / 2 + 1 ≠ 1 := by obtain ⟨t, ht⟩ := hme; omega
    have h3 : 2 * (m / 2 + 1 - 1) = m := by obtain ⟨t, ht⟩ := hme; omega
    rw [psi]; simp only [h1, ite_false]; rw [h3]
  | Hn a l b ih =>
    intro hpal hval heven
    have key : b :: (l.reverse ++ [a]) = a :: (l ++ [b]) := by
      conv_rhs => rw [← hpal]
      simp
    rw [List.cons.injEq] at key
    obtain ⟨hba, hll⟩ := key
    subst hba
    have hlrev : l.reverse = l := by simpa using hll
    have hval_l : ∀ x ∈ l, 0 < x ∧ x ≠ 2 := fun x hx => hval x (by simp [hx])
    have heven_l : Even l.sum := by
      have hsum_c : (b :: (l ++ [b])).sum = l.sum + 2 * b := by
        simp only [List.sum_cons, List.sum_append, List.sum_nil]; omega
      rw [Nat.even_iff] at heven ⊢
      rw [hsum_c] at heven; omega
    have IHl := ih hlrev hval_l heven_l
    obtain ⟨h, t, hpl⟩ : ∃ h t, phi l = h :: t := by
      cases hpe : phi l with
      | nil => exact absurd hpe (phi_ne_nil l)
      | cons h t => exact ⟨h, t, rfl⟩
    rw [phi_cons_append, hpl]
    simp only [List.headI_cons, List.tail_cons]
    rw [psi, ← hpl, IHl]
    simp

private theorem phi_valid : ∀ c : List ℕ, c.reverse = c → (∀ a ∈ c, 0 < a ∧ a ≠ 2) → Even c.sum →
    ∀ x ∈ phi c, 0 < x ∧ x ≠ 2 := by
  intro c
  induction c using List.bidirectionalRecOn with
  | H0 => intro _ _ _; simp
  | H1 m =>
    intro _ hval heven
    have hme : Even m := by simpa using heven
    have hm := hval m (by simp)
    simp only [phi_singleton, List.mem_singleton]
    rintro x rfl
    obtain ⟨t, ht⟩ := hme
    omega
  | Hn a l b ih =>
    intro hpal hval heven
    have key : b :: (l.reverse ++ [a]) = a :: (l ++ [b]) := by
      conv_rhs => rw [← hpal]
      simp
    rw [List.cons.injEq] at key
    obtain ⟨hba, hll⟩ := key
    subst hba
    have hlrev : l.reverse = l := by simpa using hll
    have hval_l : ∀ x ∈ l, 0 < x ∧ x ≠ 2 := fun x hx => hval x (by simp [hx])
    have heven_l : Even l.sum := by
      have hsum_c : (b :: (l ++ [b])).sum = l.sum + 2 * b := by
        simp only [List.sum_cons, List.sum_append, List.sum_nil]; omega
      rw [Nat.even_iff] at heven ⊢
      rw [hsum_c] at heven; omega
    have IHl := ih hlrev hval_l heven_l
    obtain ⟨h, t, hpl⟩ : ∃ h t, phi l = h :: t := by
      cases hpe : phi l with
      | nil => exact absurd hpe (phi_ne_nil l)
      | cons h t => exact ⟨h, t, rfl⟩
    rw [phi_cons_append, hpl]
    simp only [List.headI_cons, List.tail_cons, List.mem_cons]
    rintro x (rfl | rfl | hx)
    · exact IHl x (by rw [hpl]; simp)
    · exact hval x (by simp)
    · exact IHl x (by rw [hpl]; simp [hx])

private def compSet (m : ℕ) : Set (List ℕ) := {c | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = m}
private def palSet (n : ℕ) : Set (List ℕ) :=
    {c | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = n ∧ c.reverse = c}

private theorem phi_sum {c : List ℕ} {k : ℕ} (hc : c ∈ palSet (2 * k)) : (phi c).sum = k + 1 := by
  simp only [palSet, Set.mem_ofPred_eq] at hc
  obtain ⟨hval, hsum, hrev⟩ := hc
  have heven : Even c.sum := ⟨k, by rw [hsum]; exact two_mul k⟩
  have hpv := phi_valid c hrev hval heven
  have h1 := psi_sum (phi c) (fun a ha => (hpv a ha).1) (phi_ne_nil c)
  rw [psi_phi c hrev hval heven] at h1
  obtain ⟨h, t, he⟩ : ∃ h t, phi c = h :: t := by
    cases hpe : phi c with
    | nil => exact absurd hpe (phi_ne_nil c)
    | cons h t => exact ⟨h, t, rfl⟩
  have hpos : 1 ≤ (phi c).sum := by
    rw [he, List.sum_cons]
    have := (hpv h (by rw [he]; simp)).1
    omega
  omega

private theorem conj1 (k : ℕ) : (palSet (2 * k)).ncard = (compSet (k + 1)).ncard := by
  have hli : Set.LeftInvOn phi psi (compSet (k + 1)) := by
    intro d hd
    simp only [compSet, Set.mem_ofPred_eq] at hd
    have hne : d ≠ [] := by rintro rfl; simp at hd
    exact phi_psi d hd.1 hne
  rw [← Set.InjOn.ncard_image hli.injOn]
  congr 1
  ext c
  simp only [Set.mem_image, compSet, palSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hval, hsum, hrev⟩
    have heven : Even c.sum := ⟨k, by rw [hsum]; exact two_mul k⟩
    refine ⟨phi c, ⟨phi_valid c hrev hval heven, ?_⟩, psi_phi c hrev hval heven⟩
    exact phi_sum (by simp only [palSet, Set.mem_ofPred_eq]; exact ⟨hval, hsum, hrev⟩)
  · rintro ⟨d, ⟨hval, hsum⟩, rfl⟩
    have hne : d ≠ [] := by rintro rfl; simp at hsum
    refine ⟨psi_valid d hval hne, ?_, psi_reverse d⟩
    rw [psi_sum d (fun a ha => (hval a ha).1) hne, hsum]; omega


/-- Odd-parity analogue of `psi`: the head `a` becomes the odd middle `2a-1`. -/
private def psiO : List ℕ → List ℕ
  | [] => []
  | [a] => [2 * a - 1]
  | a :: x :: rest => x :: psiO (a :: rest) ++ [x]
termination_by l => l.length

private def phiO (c : List ℕ) : List ℕ :=
  c.bidirectionalRecOn [] (fun m => [(m + 1) / 2]) (fun a _l _b ih => ih.headI :: a :: ih.tail)

@[simp] private theorem phiO_singleton (m : ℕ) : phiO [m] = [(m + 1) / 2] := by simp [phiO]
@[simp] private theorem phiO_cons_append (a b : ℕ) (l : List ℕ) :
    phiO (a :: (l ++ [b])) = (phiO l).headI :: a :: (phiO l).tail := by
  simp only [phiO, List.bidirectionalRecOn]; rw [List.bidirectionalRec_cons_append]

private theorem phiO_ne_nil : ∀ c : List ℕ, c ≠ [] → phiO c ≠ [] := by
  intro c
  induction c using List.bidirectionalRecOn with
  | H0 => intro h; exact absurd rfl h
  | H1 a => intro _; simp
  | Hn a l b _ => intro _; simp

private theorem psiO_reverse : ∀ d : List ℕ, (psiO d).reverse = psiO d := by
  intro d
  induction d using psiO.induct with
  | case1 => simp [psiO]
  | case2 a => simp [psiO]
  | case3 a x rest ih =>
    rw [psiO]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [ih]

private theorem psiO_sum : ∀ d : List ℕ, (∀ p ∈ d, 0 < p) → d ≠ [] → (psiO d).sum = 2 * d.sum -
    1 := by
  intro d
  induction d using psiO.induct with
  | case1 => simp
  | case2 a =>
    intro hpos _
    have : 1 ≤ a := hpos a (by simp)
    simp only [psiO, List.sum_cons, List.sum_nil]
    omega
  | case3 a x rest ih =>
    intro hpos _
    have hpos' : ∀ p ∈ (a :: rest), 0 < p := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hpos p (by simp)
      · exact hpos p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
    have IH := ih hpos' (by simp)
    have hx : 0 < x := hpos x (by simp)
    have ha : 0 < a := hpos a (by simp)
    have e1 : (psiO (a :: x :: rest)).sum = 2 * x + (psiO (a :: rest)).sum := by
      rw [psiO]; simp [List.sum_append]; ring
    rw [e1, IH]; simp only [List.sum_cons]; omega

private theorem psiO_valid : ∀ d : List ℕ, (∀ p ∈ d, 0 < p) → (∀ p ∈ d.tail, p ≠ 2) → d ≠ [] →
    ∀ b ∈ psiO d, 0 < b ∧ b ≠ 2 := by
  intro d
  induction d using psiO.induct with
  | case1 => simp
  | case2 a =>
    intro hpos _ _
    have : 0 < a := hpos a (by simp)
    simp only [psiO, List.mem_singleton]
    rintro b rfl
    omega
  | case3 a x rest ih =>
    intro hpos htail _
    have hpos' : ∀ p ∈ (a :: rest), 0 < p := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hpos p (by simp)
      · exact hpos p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
    have htail' : ∀ p ∈ (a :: rest).tail, p ≠ 2 := by
      intro p hp
      simp only [List.tail_cons] at hp
      exact htail p (by simp only [List.tail_cons]; exact List.mem_cons_of_mem _ hp)
    have IH := ih hpos' htail' (by simp)
    have hx0 : 0 < x := hpos x (by simp)
    have hx2 : x ≠ 2 := htail x (by simp only [List.tail_cons]; simp)
    rw [psiO]
    intro b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with (rfl | hb) | rfl
    · exact ⟨hx0, hx2⟩
    · exact IH b hb
    · exact ⟨hx0, hx2⟩

private theorem phiO_psiO : ∀ d : List ℕ, (∀ p ∈ d, 0 < p) → d ≠ [] → phiO (psiO d) = d := by
  intro d
  induction d using psiO.induct with
  | case1 => intro _ hne; exact absurd rfl hne
  | case2 a =>
    intro hpos _
    have ha := hpos a (by simp)
    simp only [psiO, phiO_singleton]
    congr 1; omega
  | case3 a x rest ih =>
    intro hpos _
    have hpos' : ∀ p ∈ (a :: rest), 0 < p := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hpos p (by simp)
      · exact hpos p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
    have IH := ih hpos' (by simp)
    have hpsi : psiO (a :: x :: rest) = x :: (psiO (a :: rest) ++ [x]) := by
      rw [psiO, List.cons_append]
    rw [hpsi, phiO_cons_append, IH]; simp

private theorem psiO_phiO : ∀ c : List ℕ, c.reverse = c → (∀ a ∈ c, 0 < a ∧ a ≠ 2) → Odd c.sum →
    psiO (phiO c) = c := by
  intro c
  induction c using List.bidirectionalRecOn with
  | H0 => intro _ _ hodd; simp at hodd
  | H1 m =>
    intro _ _ hodd
    have hmo : Odd m := by simpa using hodd
    simp only [phiO_singleton]
    obtain ⟨s, hs⟩ := hmo
    rw [psiO]; congr 1; omega
  | Hn a l b ih =>
    intro hpal hval hodd
    have key : b :: (l.reverse ++ [a]) = a :: (l ++ [b]) := by
      conv_rhs => rw [← hpal]; simp
    rw [List.cons.injEq] at key
    obtain ⟨hba, hll⟩ := key
    subst hba
    have hlrev : l.reverse = l := by simpa using hll
    have hval_l : ∀ x ∈ l, 0 < x ∧ x ≠ 2 := fun x hx => hval x (by simp [hx])
    have hodd_l : Odd l.sum := by
      have hsum_c : (b :: (l ++ [b])).sum = l.sum + 2 * b := by
        simp only [List.sum_cons, List.sum_append, List.sum_nil]; omega
      rw [Nat.odd_iff] at hodd ⊢
      rw [hsum_c] at hodd; omega
    have hlne : l ≠ [] := by rintro rfl; simp at hodd_l
    have IHl := ih hlrev hval_l hodd_l
    obtain ⟨h, t, hpl⟩ : ∃ h t, phiO l = h :: t := by
      cases hpe : phiO l with
      | nil => exact absurd hpe (phiO_ne_nil l hlne)
      | cons h t => exact ⟨h, t, rfl⟩
    rw [phiO_cons_append, hpl]
    simp only [List.headI_cons, List.tail_cons]
    rw [psiO, ← hpl, IHl]; simp

private theorem phiO_valid : ∀ c : List ℕ, c.reverse = c → (∀ a ∈ c, 0 < a ∧ a ≠ 2) → Odd c.sum →
    (∀ p ∈ phiO c, 0 < p) ∧ (∀ p ∈ (phiO c).tail, p ≠ 2) := by
  intro c
  induction c using List.bidirectionalRecOn with
  | H0 => intro _ _ hodd; simp at hodd
  | H1 m =>
    intro _ _ hodd
    have hmo : Odd m := by simpa using hodd
    obtain ⟨s, hs⟩ := hmo
    simp only [phiO_singleton, List.mem_singleton, List.tail_cons, List.not_mem_nil]
    refine ⟨?_, ?_⟩
    · rintro p rfl; omega
    · simp
  | Hn a l b ih =>
    intro hpal hval hodd
    have key : b :: (l.reverse ++ [a]) = a :: (l ++ [b]) := by
      conv_rhs => rw [← hpal]; simp
    rw [List.cons.injEq] at key
    obtain ⟨hba, hll⟩ := key
    subst hba
    have hlrev : l.reverse = l := by simpa using hll
    have hval_l : ∀ x ∈ l, 0 < x ∧ x ≠ 2 := fun x hx => hval x (by simp [hx])
    have hodd_l : Odd l.sum := by
      have hsum_c : (b :: (l ++ [b])).sum = l.sum + 2 * b := by
        simp only [List.sum_cons, List.sum_append, List.sum_nil]; omega
      rw [Nat.odd_iff] at hodd ⊢
      rw [hsum_c] at hodd; omega
    have hlne : l ≠ [] := by rintro rfl; simp at hodd_l
    obtain ⟨IHpos, IHtail⟩ := ih hlrev hval_l hodd_l
    obtain ⟨h, t, hpl⟩ : ∃ h t, phiO l = h :: t := by
      cases hpe : phiO l with
      | nil => exact absurd hpe (phiO_ne_nil l hlne)
      | cons h t => exact ⟨h, t, rfl⟩
    have hb2 := hval b (by simp)
    rw [phiO_cons_append, hpl]
    simp only [List.headI_cons, List.tail_cons, List.mem_cons]
    refine ⟨?_, ?_⟩
    · rintro p (rfl | rfl | hp)
      · exact IHpos p (by rw [hpl]; simp)
      · exact hb2.1
      · exact IHpos p (by rw [hpl]; simp [hp])
    · rintro p (rfl | hp)
      · exact hb2.2
      · exact IHtail p (by rw [hpl]; simpa using hp)

private def compSet' (m : ℕ) : Set (List ℕ) :=
    {d | (∀ p ∈ d, 0 < p) ∧ (∀ p ∈ d.tail, p ≠ 2) ∧ d.sum = m}

private theorem finite_S (m : ℕ) : {d : List ℕ | (∀ p ∈ d, 0 < p) ∧ d.sum = m}.Finite := by
  apply Set.Finite.subset (Set.finite_range (fun c : Composition m => c.blocks))
  intro d hd
  obtain ⟨hpos, hsum⟩ := hd
  exact ⟨⟨d, fun {i} hi => hpos i hi, hsum⟩, rfl⟩

private theorem compSet'_sub_S (m : ℕ) : compSet' m ⊆ {d : List ℕ | (∀ p ∈ d, 0 < p) ∧ d.sum = m} :=
  fun _d hd => ⟨hd.1, hd.2.2⟩
private theorem compSet_sub_S (m : ℕ) : compSet m ⊆ {d : List ℕ | (∀ p ∈ d, 0 < p) ∧ d.sum = m} :=
  fun _d hd => ⟨fun p hp => (hd.1 p hp).1, hd.2⟩

private theorem phiO_sum {c : List ℕ} {k : ℕ} (hc : c ∈ palSet (2 * k + 1)) : (phiO c).sum = k +
    1 := by
  simp only [palSet, Set.mem_ofPred_eq] at hc
  obtain ⟨hval, hsum, hrev⟩ := hc
  have hne : c ≠ [] := by rintro rfl; simp at hsum
  have hodd : Odd c.sum := ⟨k, by rw [hsum]⟩
  have hpv := (phiO_valid c hrev hval hodd).1
  have h1 := psiO_sum (phiO c) hpv (phiO_ne_nil c hne)
  rw [psiO_phiO c hrev hval hodd] at h1
  obtain ⟨h, t, he⟩ : ∃ h t, phiO c = h :: t := by
    cases hpe : phiO c with
    | nil => exact absurd hpe (phiO_ne_nil c hne)
    | cons h t => exact ⟨h, t, rfl⟩
  have hpos : 1 ≤ (phiO c).sum := by
    rw [he, List.sum_cons]; have := hpv h (by rw [he]; simp); omega
  omega

private theorem conj2a (k : ℕ) : (palSet (2 * k + 1)).ncard = (compSet' (k + 1)).ncard := by
  have hli : Set.LeftInvOn phiO psiO (compSet' (k + 1)) := by
    intro d hd
    simp only [compSet', Set.mem_ofPred_eq] at hd
    exact phiO_psiO d hd.1 (by rintro rfl; simp at hd)
  rw [← Set.InjOn.ncard_image hli.injOn]
  congr 1
  ext c
  simp only [Set.mem_image, compSet', palSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hval, hsum, hrev⟩
    have hodd : Odd c.sum := ⟨k, by rw [hsum]⟩
    have hpv := phiO_valid c hrev hval hodd
    refine ⟨phiO c, ⟨hpv.1, hpv.2, ?_⟩, psiO_phiO c hrev hval hodd⟩
    exact phiO_sum (by simp only [palSet, Set.mem_ofPred_eq]; exact ⟨hval, hsum, hrev⟩)
  · rintro ⟨d, ⟨hpos, htail, hsum⟩, rfl⟩
    have hne : d ≠ [] := by rintro rfl; simp at hsum
    refine ⟨psiO_valid d hpos htail hne, ?_, psiO_reverse d⟩
    rw [psiO_sum d hpos hne, hsum]; omega

private def head2Set (k : ℕ) : Set (List ℕ) := {d | d ∈ compSet' (k + 1) ∧ d.headI = 2}

private theorem conj2b (k : ℕ) :
    (compSet' (k + 1)).ncard = (compSet (k + 1)).ncard + (head2Set k).ncard := by
  have hsplit : compSet' (k + 1) = compSet (k + 1) ∪ head2Set k := by
    ext d
    simp only [compSet, compSet', head2Set, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hpos, htail, hsum⟩
      by_cases h2 : d.headI = 2
      · right; exact ⟨⟨hpos, htail, hsum⟩, h2⟩
      · left
        refine ⟨fun p hp => ⟨hpos p hp, ?_⟩, hsum⟩
        cases d with
        | nil => simp at hp
        | cons a t =>
          rcases List.mem_cons.mp hp with rfl | hp
          · simpa using h2
          · exact htail p (by simpa using hp)
    · rintro (⟨hval, hsum⟩ | ⟨hmem, _⟩)
      · exact ⟨fun p hp => (hval p hp).1, fun p hp => (hval p (List.tail_subset d hp)).2, hsum⟩
      · exact hmem
  have hdisj : Disjoint (compSet (k + 1)) (head2Set k) := by
    rw [Set.disjoint_left]
    rintro d hd hd2
    simp only [compSet, Set.mem_ofPred_eq] at hd
    simp only [head2Set, Set.mem_ofPred_eq] at hd2
    cases d with
    | nil => obtain ⟨_, hs⟩ := hd; simp at hs
    | cons a t =>
      have hne2 := (hd.1 a (by simp)).2
      simp only [List.headI_cons] at hd2
      exact hne2 hd2.2
  have hfin1 : (compSet (k + 1)).Finite := (finite_S (k + 1)).subset (compSet_sub_S (k + 1))
  have hfin2 : (head2Set k).Finite :=
    (finite_S (k + 1)).subset (fun d hd => compSet'_sub_S (k + 1) hd.1)
  rw [hsplit, Set.ncard_union_eq hdisj hfin1 hfin2]

private theorem head2_empty : head2Set 0 = ∅ := by
  ext d
  simp only [head2Set, compSet', Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hpos, _, hsum⟩, hhead⟩
  cases d with
  | nil => simp at hhead
  | cons a t =>
    simp only [List.headI_cons] at hhead
    subst hhead
    simp only [List.sum_cons] at hsum
    omega

private theorem head2_bij (k : ℕ) (hk : 1 ≤ k) : (head2Set k).ncard = (compSet (k - 1)).ncard := by
  have hinj : Set.InjOn List.tail (head2Set k) := by
    intro d1 hd1 d2 hd2 heq
    simp only [head2Set, Set.mem_ofPred_eq] at hd1 hd2
    have e1 : d1 = 2 :: d1.tail := by
      cases d1 with
      | nil => simp at hd1
      | cons a t => simp only [List.headI_cons] at hd1; simp [hd1.2]
    have e2 : d2 = 2 :: d2.tail := by
      cases d2 with
      | nil => simp at hd2
      | cons a t => simp only [List.headI_cons] at hd2; simp [hd2.2]
    rw [e1, e2, heq]
  rw [← Set.InjOn.ncard_image hinj]
  congr 1
  ext t
  simp only [Set.mem_image, head2Set, compSet, compSet', Set.mem_ofPred_eq]
  constructor
  · rintro ⟨d, ⟨⟨hpos, htail, hsum⟩, hhead⟩, rfl⟩
    cases d with
    | nil => simp at hhead
    | cons a s =>
      simp only [List.headI_cons] at hhead; subst hhead
      simp only [List.tail_cons, List.sum_cons] at *
      refine ⟨fun p hp => ⟨hpos p (by simp [hp]), htail p hp⟩, by omega⟩
  · rintro ⟨hval, hsum⟩
    refine ⟨2 :: t, ⟨⟨?_, ?_, ?_⟩, rfl⟩, rfl⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · exact (hval p hp).1
    · intro p hp; simp only [List.tail_cons] at hp; exact (hval p hp).2
    · simp only [List.sum_cons]; omega


private theorem fin_compSet' (m : ℕ) : (compSet' m).Finite :=
  (finite_S m).subset (fun _d hd => ⟨hd.1, hd.2.2⟩)
private theorem fin_compSet (m : ℕ) : (compSet m).Finite :=
  (finite_S m).subset (fun _d hd => ⟨fun p hp => (hd.1 p hp).1, hd.2⟩)

private theorem R1 (m : ℕ) :
    (compSet' (m+2)).ncard = (compSet (m+1)).ncard + (compSet' (m+1)).ncard := by
  set A := {d ∈ compSet' (m+2) | d.headI = 1} with hA
  set B := {d ∈ compSet' (m+2) | 2 ≤ d.headI} with hB
  have hsplit : compSet' (m+2) = A ∪ B := by
    ext d
    simp only [hA, hB, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hd
      obtain ⟨a, t, rfl⟩ : ∃ a t, d = a :: t := by
        cases d with
        | nil => obtain ⟨-, -, hs⟩ := hd; simp only [List.sum_nil] at hs; omega
        | cons a t => exact ⟨a, t, rfl⟩
      have ha : 0 < a := hd.1 a (by simp)
      simp only [List.headI_cons]
      rcases Nat.lt_or_ge a 2 with h | h
      · left; exact ⟨hd, by omega⟩
      · right; exact ⟨hd, h⟩
    · rintro (⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]; rintro d ⟨_, h1⟩ ⟨_, h2⟩; omega
  have hfinA : A.Finite := (fin_compSet' (m+2)).subset (fun d hd => hd.1)
  have hfinB : B.Finite := (fin_compSet' (m+2)).subset (fun d hd => hd.1)
  rw [hsplit, Set.ncard_union_eq hdisj hfinA hfinB]
  congr 1
  · rw [← Set.InjOn.ncard_image (f := List.tail) ?_]
    · congr 1; ext t
      simp only [hA, Set.mem_image, Set.mem_ofPred_eq, compSet, compSet']
      constructor
      · rintro ⟨d, ⟨⟨hpos, htail, hsum⟩, hhead⟩, rfl⟩
        obtain ⟨a, s, rfl⟩ : ∃ a s, d = a :: s := by
          cases d with | nil => simp at hhead | cons a s => exact ⟨a, s, rfl⟩
        simp only [List.headI_cons] at hhead; subst hhead
        simp only [List.tail_cons, List.sum_cons] at *
        exact ⟨fun p hp => ⟨hpos p (List.mem_cons_of_mem _ hp), htail p hp⟩, by omega⟩
      · rintro ⟨hval, hsum⟩
        refine ⟨1 :: t, ⟨⟨?_, ?_, ?_⟩, rfl⟩, rfl⟩
        · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
          · omega
          · exact (hval p hp).1
        · intro p hp; simp only [List.tail_cons] at hp; exact (hval p hp).2
        · simp only [List.sum_cons]; omega
    · rintro d1 ⟨hd1, h1⟩ d2 ⟨hd2, h2⟩ heq
      obtain ⟨a1, s1, rfl⟩ : ∃ a s, d1 = a :: s := by
        cases d1 with | nil => simp at h1 | cons a s => exact ⟨a, s, rfl⟩
      obtain ⟨a2, s2, rfl⟩ : ∃ a s, d2 = a :: s := by
        cases d2 with | nil => simp at h2 | cons a s => exact ⟨a, s, rfl⟩
      simp only [List.headI_cons] at h1 h2; subst h1; subst h2
      simp only [List.tail_cons] at heq; rw [heq]
  · rw [← Set.InjOn.ncard_image (f := fun d => (d.headI - 1) :: d.tail) ?_]
    · congr 1; ext s
      simp only [hB, Set.mem_image, Set.mem_ofPred_eq, compSet']
      constructor
      · rintro ⟨d, ⟨⟨hpos, htail, hsum⟩, hh⟩, rfl⟩
        obtain ⟨a, u, rfl⟩ : ∃ a u, d = a :: u := by
          cases d with | nil => simp at hh | cons a u => exact ⟨a, u, rfl⟩
        simp only [List.headI_cons, List.tail_cons] at *
        refine ⟨fun p hp => ?_, fun p hp => ?_, ?_⟩
        · rcases List.mem_cons.mp hp with rfl | hp
          · omega
          · exact hpos p (List.mem_cons_of_mem _ hp)
        · exact htail p hp
        · simp only [List.sum_cons] at hsum ⊢; omega
      · rintro ⟨hpos, htail, hsum⟩
        obtain ⟨b, u, rfl⟩ : ∃ b u, s = b :: u := by
          cases s with | nil => simp only [List.sum_nil] at hsum; omega | cons b u => exact
              ⟨b, u, rfl⟩
        simp only [List.sum_cons] at hsum
        have hb : 0 < b := hpos b (by simp)
        refine ⟨(b + 1) :: u, ⟨⟨fun p hp => ?_, fun p hp => ?_, ?_⟩, ?_⟩, ?_⟩
        · rcases List.mem_cons.mp hp with rfl | hp
          · omega
          · exact hpos p (List.mem_cons_of_mem _ hp)
        · simp only [List.tail_cons] at hp ⊢; exact htail p hp
        · rw [List.sum_cons]; omega
        · rw [List.headI_cons]; omega
        · rw [List.headI_cons, List.tail_cons]; simp
    · rintro d1 ⟨hd1, h1⟩ d2 ⟨hd2, h2⟩ heq
      obtain ⟨a1, u1, rfl⟩ : ∃ a u, d1 = a :: u := by
        cases d1 with | nil => simp at h1 | cons a u => exact ⟨a, u, rfl⟩
      obtain ⟨a2, u2, rfl⟩ : ∃ a u, d2 = a :: u := by
        cases d2 with | nil => simp at h2 | cons a u => exact ⟨a, u, rfl⟩
      simp only [List.headI_cons, List.tail_cons, List.cons.injEq] at heq h1 h2
      obtain ⟨hh, ht⟩ := heq
      rw [ht]; congr 1; omega

private theorem R3 (m : ℕ) :
    (compSet (m+3)).ncard = (compSet (m+2)).ncard + (compSet' (m+1)).ncard := by
  set A := {d ∈ compSet (m+3) | d.headI = 1} with hA
  set B := {d ∈ compSet (m+3) | 3 ≤ d.headI} with hB
  have hsplit : compSet (m+3) = A ∪ B := by
    ext d
    simp only [hA, hB, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hd
      obtain ⟨a, t, rfl⟩ : ∃ a t, d = a :: t := by
        cases d with
        | nil => obtain ⟨-, hs⟩ := hd; simp only [List.sum_nil] at hs; omega
        | cons a t => exact ⟨a, t, rfl⟩
      have ha := hd.1 a (by simp)
      simp only [List.headI_cons]
      rcases Nat.lt_or_ge a 3 with h | h
      · left; refine ⟨hd, by omega⟩
      · right; exact ⟨hd, h⟩
    · rintro (⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]; rintro d ⟨_, h1⟩ ⟨_, h2⟩; omega
  have hfinA : A.Finite := (fin_compSet (m+3)).subset (fun d hd => hd.1)
  have hfinB : B.Finite := (fin_compSet (m+3)).subset (fun d hd => hd.1)
  rw [hsplit, Set.ncard_union_eq hdisj hfinA hfinB]
  congr 1
  · rw [← Set.InjOn.ncard_image (f := List.tail) ?_]
    · congr 1; ext t
      simp only [hA, Set.mem_image, Set.mem_ofPred_eq, compSet]
      constructor
      · rintro ⟨d, ⟨⟨hval, hsum⟩, hhead⟩, rfl⟩
        obtain ⟨a, s, rfl⟩ : ∃ a s, d = a :: s := by
          cases d with | nil => simp at hhead | cons a s => exact ⟨a, s, rfl⟩
        simp only [List.headI_cons] at hhead; subst hhead
        simp only [List.tail_cons, List.sum_cons] at *
        exact ⟨fun p hp => hval p (List.mem_cons_of_mem _ hp), by omega⟩
      · rintro ⟨hval, hsum⟩
        refine ⟨1 :: t, ⟨⟨?_, ?_⟩, rfl⟩, rfl⟩
        · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨one_pos, by omega⟩
          · exact hval p hp
        · simp only [List.sum_cons]; omega
    · rintro d1 ⟨hd1, h1⟩ d2 ⟨hd2, h2⟩ heq
      obtain ⟨a1, s1, rfl⟩ : ∃ a s, d1 = a :: s := by
        cases d1 with | nil => simp at h1 | cons a s => exact ⟨a, s, rfl⟩
      obtain ⟨a2, s2, rfl⟩ : ∃ a s, d2 = a :: s := by
        cases d2 with | nil => simp at h2 | cons a s => exact ⟨a, s, rfl⟩
      simp only [List.headI_cons] at h1 h2; subst h1; subst h2
      simp only [List.tail_cons] at heq; rw [heq]
  · rw [← Set.InjOn.ncard_image (f := fun d => (d.headI - 2) :: d.tail) ?_]
    · congr 1; ext s
      simp only [hB, Set.mem_image, Set.mem_ofPred_eq, compSet, compSet']
      constructor
      · rintro ⟨d, ⟨⟨hval, hsum⟩, hh⟩, rfl⟩
        obtain ⟨a, u, rfl⟩ : ∃ a u, d = a :: u := by
          cases d with | nil => simp at hh | cons a u => exact ⟨a, u, rfl⟩
        simp only [List.headI_cons, List.tail_cons] at *
        refine ⟨fun p hp => ?_, fun p hp => ?_, ?_⟩
        · rcases List.mem_cons.mp hp with rfl | hp
          · omega
          · exact (hval p (List.mem_cons_of_mem _ hp)).1
        · exact (hval p (List.mem_cons_of_mem _ hp)).2
        · simp only [List.sum_cons] at hsum ⊢; omega
      · rintro ⟨hpos, htail, hsum⟩
        obtain ⟨b, u, rfl⟩ : ∃ b u, s = b :: u := by
          cases s with | nil => simp only [List.sum_nil] at hsum; omega | cons b u => exact
              ⟨b, u, rfl⟩
        simp only [List.sum_cons] at hsum
        have hb : 0 < b := hpos b (by simp)
        refine ⟨(b + 2) :: u, ⟨⟨fun p hp => ?_, ?_⟩, ?_⟩, ?_⟩
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨by omega, by omega⟩
          · refine ⟨hpos p (List.mem_cons_of_mem _ hp), ?_⟩
            exact htail p (by simpa using hp)
        · simp only [List.sum_cons]; omega
        · simp only [List.headI_cons]; omega
        · simp only [List.headI_cons, List.tail_cons, Nat.add_sub_cancel]
    · rintro d1 ⟨hd1, h1⟩ d2 ⟨hd2, h2⟩ heq
      obtain ⟨a1, u1, rfl⟩ : ∃ a u, d1 = a :: u := by
        cases d1 with | nil => simp at h1 | cons a u => exact ⟨a, u, rfl⟩
      obtain ⟨a2, u2, rfl⟩ : ∃ a u, d2 = a :: u := by
        cases d2 with | nil => simp at h2 | cons a u => exact ⟨a, u, rfl⟩
      simp only [List.headI_cons, List.tail_cons, List.cons.injEq] at heq h1 h2
      obtain ⟨hh, ht⟩ := heq
      rw [ht]; congr 1; omega

private theorem compSet_one : (compSet 1).ncard = 1 := by
  convert Set.ncard_singleton ([1] : List ℕ)
  ext c
  simp only [compSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hval, hsum⟩
    rcases c with _ | ⟨a, t⟩
    · simp at hsum
    · have ha := (hval a (by simp)).1
      rcases t with _ | ⟨b, s⟩
      · simp only [List.sum_cons, List.sum_nil] at hsum
        have : a = 1 := by omega
        subst this; rfl
      · exfalso; have hb := (hval b (by simp)).1
        simp only [List.sum_cons] at hsum; omega
  · rintro rfl; refine ⟨fun a ha => ?_, by simp⟩
    simp only [List.mem_singleton] at ha; omega

private theorem compSet'_one : (compSet' 1).ncard = 1 := by
  convert Set.ncard_singleton ([1] : List ℕ)
  ext c
  simp only [compSet', Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hpos, _, hsum⟩
    rcases c with _ | ⟨a, t⟩
    · simp at hsum
    · have ha := hpos a (by simp)
      rcases t with _ | ⟨b, s⟩
      · simp only [List.sum_cons, List.sum_nil] at hsum
        have : a = 1 := by omega
        subst this; rfl
      · exfalso; have hb := hpos b (by simp)
        simp only [List.sum_cons] at hsum; omega
  · rintro rfl
    refine ⟨fun a ha => ?_, by simp, by simp⟩
    simp only [List.mem_singleton] at ha; omega

private theorem compSet_two : (compSet 2).ncard = 1 := by
  convert Set.ncard_singleton ([1, 1] : List ℕ)
  ext c
  simp only [compSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hval, hsum⟩
    rcases c with _ | ⟨a, t⟩
    · simp at hsum
    · have ha := hval a (by simp)
      rcases t with _ | ⟨b, s⟩
      · exfalso; simp only [List.sum_cons, List.sum_nil] at hsum; omega
      · have hb := hval b (by simp)
        rcases s with _ | ⟨e, r⟩
        · simp only [List.sum_cons, List.sum_nil] at hsum
          have hA : a = 1 := by omega
          have hB : b = 1 := by omega
          subst hA; subst hB; rfl
        · exfalso; have he := hval e (by simp)
          simp only [List.sum_cons] at hsum; omega
  · rintro rfl
    refine ⟨fun a ha => ?_, by simp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega

/--
**Palindromic compositions without 2's.** For an integer $m \ge 0$, let $C(m)$ be the number of
compositions of $m$ (finite sequences of positive integers with sum $m$) with no part equal to
$2$, so that $C(0) = 1$ counts the empty composition, and set $C(m) = 0$ for $m < 0$. For a
natural number $n$, let $P(n)$ be the number of such compositions of $n$ that are palindromes.
Then for every natural number $k$, $P(2k) = C(k+1)$ and $P(2k+1) = C(k+1) + C(k-1)$, and the
generating function $G_P(x) = \sum_{n \ge 0} P(n)\, x^n$ satisfies
$(1 - x^2 - x^3)\, G_P(x) = 1 + x$ as formal power series with integer coefficients.

The generating-function identity is the source's $G_P(z) = (1 + z)/(1 - z^2 - z^3)$ cleared of
denominators.

Proves `Wanted` entry `palindromic_compositions_without_two`.

Source: Phyllis Chinn and Silvia Heubach, "Integer Sequences Related to Compositions
without 2's," Journal of Integer Sequences 6 (2003), Article 03.2.3, Theorem 10
(label `palnums`), lines 462–471,
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Heubach/heubach5.tex>.
-/
theorem palindromic_compositions_without_two :
    let C : ℤ → ℕ := fun m => if 0 ≤ m then
      Set.ncard {c : List ℕ | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = m.toNat} else 0
    let P : ℕ → ℕ := fun n => Set.ncard {c : List ℕ |
      (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = n ∧ c.reverse = c}
    (∀ k : ℕ, P (2 * k) = C ((k : ℤ) + 1)) ∧
      (∀ k : ℕ, P (2 * k + 1) = C ((k : ℤ) + 1) + C ((k : ℤ) - 1)) ∧
      (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3) *
          PowerSeries.mk (fun n : ℕ => (P n : ℤ)) = 1 + PowerSeries.X := by
  intro C P
  refine ⟨fun k => ?_, ?_, ?_⟩
  · -- conjunct 1
    have hC : C ((k : ℤ) + 1) = (compSet (k + 1)).ncard := by
      change (if (0:ℤ) ≤ (k : ℤ) + 1 then
        Set.ncard {c : List ℕ | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = ((k : ℤ) + 1).toNat}
        else 0) = _
      rw [ite_eq_left (by positivity)]
      rfl
    change (palSet (2 * k)).ncard = C ((k : ℤ) + 1)
    rw [hC]
    exact conj1 k
  · -- conjunct 2
    intro k
    have hC1 : C ((k : ℤ) + 1) = (compSet (k + 1)).ncard := by
      change (if (0:ℤ) ≤ (k : ℤ) + 1 then
        Set.ncard {c : List ℕ | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = ((k : ℤ) + 1).toNat}
        else 0) = _
      rw [ite_eq_left (by positivity)]; rfl
    have hCm1 : C ((k : ℤ) - 1) = (head2Set k).ncard := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · change (if (0:ℤ) ≤ (0 : ℤ) - 1 then _ else 0) = _
        rw [ite_eq_right (by norm_num), head2_empty, Set.ncard_empty]
      · change (if (0:ℤ) ≤ (k : ℤ) - 1 then
          Set.ncard {c : List ℕ | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = ((k : ℤ) - 1).toNat}
          else 0) = _
        rw [ite_eq_left (by omega)]
        have htn : ((k : ℤ) - 1).toNat = k - 1 := by omega
        rw [htn, head2_bij k hk]
        rfl
    change (palSet (2 * k + 1)).ncard = C ((k : ℤ) + 1) + C ((k : ℤ) - 1)
    rw [hC1, hCm1, conj2a k, conj2b k]
  · -- conjunct 3
    have hPe : ∀ k, P (2 * k) = (compSet (k + 1)).ncard := fun k => conj1 k
    have hPo : ∀ k, P (2 * k + 1) = (compSet' (k + 1)).ncard := fun k => conj2a k
    have hrec : ∀ n, P (n + 3) = P (n + 1) + P n := by
      intro n
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · subst hk
        have e3 : k + k + 3 = 2 * (k + 1) + 1 := by ring
        have e1 : k + k + 1 = 2 * k + 1 := by ring
        have e0 : k + k = 2 * k := by ring
        rw [e3, e1, e0, hPo (k + 1), hPo k, hPe k, R1 k]; ring
      · subst hk
        have e3 : 2 * k + 1 + 3 = 2 * (k + 2) := by ring
        have e1 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
        rw [e3, e1, hPe (k + 2), hPe (k + 1), hPo k, R3 k]
    have hf0 : P 0 = 1 := by have := hPe 0; simpa [compSet_one] using this
    have hf1 : P 1 = 1 := by have := hPo 0; simpa [compSet'_one] using this
    have hf2 : P 2 = P 0 := by
      rw [show (2 : ℕ) = 2 * 1 by ring, hPe 1, compSet_two, hf0]
    set f : ℕ → ℤ := fun n => (P n : ℤ) with hf
    have g0 : f 0 = 1 := by simp [hf, hf0]
    have g1 : f 1 = 1 := by simp [hf, hf1]
    have g2 : f 2 = f 0 := by simp [hf, hf2]
    have grec : ∀ n, f (n + 3) = f (n + 1) + f n := by
      intro n; simp only [hf]; rw [hrec n]; push_cast; ring
    change (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3) * PowerSeries.mk f = 1 + PowerSeries.X
    ext n
    rw [sub_mul, sub_mul, one_mul]
    simp only [map_sub, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
      PowerSeries.coeff_one, PowerSeries.coeff_X]
    match n with
    | 0 => simp [g0]
    | 1 => simp [g1]
    | 2 => simp; omega
    | (j + 3) =>
      simp only [Nat.add_sub_cancel]
      have := grec j
      norm_num
      omega

end MetaMathlibExt
