/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.Combinatorics.Enumerative.LuckyCars
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.OfFn
import Mathlib.Order.Fin.Basic
import all MathlibExt.Combinatorics.Enumerative.DescendingNaplesDyckPath
import all MathlibExt.Combinatorics.Enumerative.DescendingNaplesPaddedDyckWord
import all MathlibExt.Combinatorics.Enumerative.LuckyCarFactorialMoments
import all MathlibExt.Combinatorics.Enumerative.LuckyCarsIncreasing
import all MathlibExt.Combinatorics.Enumerative.PollakPartialParkingFunctions

/-!
# Lucky spots in weakly decreasing parking functions

For a weakly decreasing parking function of length `n`, a spot `j : Fin n` is lucky exactly
when it occurs among the preferences. In the corresponding Dyck word, such a column begins with
an Up step. Removing that step, its matching Down step, and the Dyck word between them gives
an ordered pair of Dyck words; the column determines where to insert the removed segment back.

## References

* Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats,
  *Lucky Cars and Lucky Spots in Parking Functions*, Journal of Integer Sequences 29 (2026),
  Article 26.1.1, pp. 1–18, Theorem 24 and the parking-function correspondence in Section 4.
* Richard P. Stanley, *Catalan Numbers*, Cambridge University Press (2015), and Catherine H. Yan,
  *Parking functions*, in *Handbook of Enumerative Combinatorics*, CRC Press (2015), pp. 835–893,
  cited in Section 4 for the Catalan enumeration.
* ATLAS modules `DescendingNaplesDyckPath` (`encode`, `decode`, `word_iff`, `exists_word`)
  and `DescendingNaplesPaddedDyckWord` (`toPaddedWord`, `exists_walk`, `stepHeight_steps`):
  the positional encoding and its conversion to Dyck words, used here with bound zero.
* ATLAS modules `LuckyCarsIncreasing` (`isParkingFunction_iff_le_id_of_monotone`),
  `LuckyCarFactorialMoments` (`parkSpotsFrom_eq_parkAssign`), and
  `PollakPartialParkingFunctions` (`parkAssign_inj`): the parking criterion and greedy assignments.
-/

set_option autoImplicit false

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt MetaMathlibExt.PollakPartialParking DyckStep
open MetaMathlibExt.descendingNaplesCount_eq_card_kDyckPath

private lemma nextFreeSpot_spec {n : ℕ} (occ : Finset (Fin n)) (a : Fin n) :
    a ≤ nextFreeSpot occ a ∧ (a ∉ occ → nextFreeSpot occ a = a) := by
  unfold nextFreeSpot
  split_ifs with h
  · exact ⟨(Finset.mem_filter.mp (Finset.min'_mem _ h)).2.1, fun ha =>
      le_antisymm (Finset.min'_le _ _ (by simp [ha]))
        (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.1⟩
  · exact ⟨le_rfl, fun _ => rfl⟩

private lemma getD_parkSpotsFrom_of_lt_before {n : ℕ} (l : List (Fin n)) (i : ℕ)
    (hi : i < l.length) (occ : Finset (Fin n)) (d : Fin n) (hfree : l[i] ∉ occ)
    (hprev : ∀ k, (hk : k < i) → l[i] < l[k]) :
    (parkSpotsFrom l occ).getD i d = l[i] := by
  induction l generalizing i occ with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => exact (nextFreeSpot_spec occ a).2 hfree
    | succ i =>
      have hit : i < l.length := by simpa using hi
      have ha : l[i] < a := hprev 0 (Nat.zero_lt_succ i)
      rw [parkSpotsFrom, List.getD_cons_succ]
      exact ih i hit _ (by
        rw [Finset.mem_insert, not_or]
        exact ⟨(ha.trans_le (nextFreeSpot_spec occ a).1).ne, hfree⟩)
        (fun k hk => hprev (k + 1) (Nat.succ_lt_succ hk))

private lemma parkSpots_injective {n : ℕ} {f : Fin n → Fin n}
    (hf : IsParkingFunction n f) : Function.Injective (parkSpots f) := by
  have hf' : LinSuccess n n f := (linSuccess_iff_isPartialParkingFunction n n f le_rfl).mpr hf
  have hassign (i : Fin n) : emb n (parkSpots f i) =
      parkAssign n n (lift n n f) le_rfl i.val i.isLt := by
    simpa [parkSpots] using parkSpotsFrom_eq_parkAssign f hf' i 0 (Nat.zero_le _) ⟨∅, by simp⟩
      (linOccAux_zero n n f) (by simp [parkOcc, parkOccAux])
  intro i k h
  apply Fin.ext
  by_contra hne
  exact parkAssign_inj n n (lift n n f) le_rfl i.val k.val i.isLt k.isLt hne
    ((hassign i).symm.trans ((congrArg (emb n) h).trans (hassign k)))

private lemma exists_lucky_of_preferred {n : ℕ} {f : Fin n → Fin n} (hf : Antitone f)
    {j : Fin n} (hj : ∃ i, f i = j) : ∃ i, f i = j ∧ IsLuckyCar f i := by
  classical
  let s := Finset.univ.filter fun i => f i = j
  have hs : s.Nonempty := by simpa [s, Finset.Nonempty] using hj
  let i := s.min' hs
  have hi : f i = j := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  refine ⟨i, hi, ?_⟩
  unfold IsLuckyCar parkSpots
  convert getD_parkSpotsFrom_of_lt_before (List.ofFn f) i.val (by simp) ∅ i (by simp) ?_ using 1
  · simp
  · intro k hk
    let k' : Fin n := ⟨k, hk.trans i.isLt⟩
    have hki : k' < i := hk
    have hne : f i ≠ f k' := by
      intro he
      have hm : k' ∈ s := by simp [s, ← he, hi]
      exact (not_le_of_gt hki) (Finset.min'_le s _ hm)
    simpa only [List.getElem_ofFn] using lt_of_le_of_ne (hf hki.le) hne

private abbrev Decreasing (n : ℕ) :=
  {f : Fin n → Fin n // IsParkingFunction n f ∧ Antitone f}

private abbrev Prefers {n : ℕ} (f : Decreasing n) (j : Fin n) : Prop := ∃ i, f.1 i = j

private noncomputable def luckySpotEquiv {n : ℕ} (j : Fin n) :
    (Σ i : Fin n, { f : Fin n → Fin n //
      IsParkingFunction n f ∧ Antitone f ∧ f i = j ∧ IsLuckyCar f i }) ≃
      {f : Decreasing n // Prefers f j} :=
  Equiv.ofBijective (fun x => ⟨⟨x.2.1, x.2.2.1, x.2.2.2.1⟩, x.1, x.2.2.2.2.1⟩) (by
    constructor
    · rintro ⟨i, f, hp, ha, hj, hl⟩ ⟨k, g, _, _, hgj, hgl⟩ h
      have he : f = g := congrArg (fun x : {f : Decreasing n // Prefers f j} => x.1.1) h
      subst g
      have hik : i = k := parkSpots_injective hp ((hl.trans hj).trans (hgl.trans hgj).symm)
      subst k
      rfl
    · rintro ⟨⟨f, hp, ha⟩, h⟩
      obtain ⟨i, hj, hl⟩ := exists_lucky_of_preferred ha h
      exact ⟨⟨i, f, hp, ha, hj, hl⟩, rfl⟩)

private abbrev SizedDyck (n : ℕ) := {p : DyckWord // p.semilength = n}

private lemma good_iff_parking {n : ℕ} (f : Fin n → Fin n) (hf : Antitone f) :
    Good 0 (fun i => (f i).val + 1) ↔ IsParkingFunction n f := by
  have hmono : Monotone (fun i : Fin n => f i.rev) :=
    fun _ _ h => hf (Fin.rev_le_rev.mpr h)
  have hcard (j : Fin n) :
      (Finset.univ.filter (fun i : Fin n => f i.rev ≤ j)).card =
        (Finset.univ.filter (fun i : Fin n => f i ≤ j)).card := by
    refine Finset.card_bij' (fun i _ => i.rev) (fun i _ => i.rev) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
  have hrev : IsParkingFunction n (fun i : Fin n => f i.rev) ↔ IsParkingFunction n f := by
    simp only [isParkingFunction_iff_card_filter_le, hcard]
  rw [← hrev, isParkingFunction_iff_le_id_of_monotone hmono]
  constructor
  · intro h i
    have hb := h.bound i.rev
    simp only [Fin.val_rev, Nat.add_zero] at hb
    exact Fin.le_def.mpr (by omega)
  · intro h
    refine ⟨fun i => ⟨by omega, by have := (f i).isLt; omega⟩,
      fun i k hik => Nat.succ_le_succ (Fin.le_def.mp (hf hik)), ?_⟩
    intro i
    have hb := Fin.le_def.mp (h i.rev)
    simp only [Fin.rev_rev, Fin.val_rev] at hb
    omega

private def parkingToPath {n : ℕ} (f : Decreasing n) : SizedDyck n := by
  have hg := (good_iff_parking f.1 f.2.2).mpr f.2.1
  exact toPaddedWord (word_encode hg)

private lemma parkingToPath_list {n : ℕ} (f : Decreasing n) :
    (parkingToPath f).1.toList =
      steps (word (encode ((good_iff_parking f.1 f.2.2).mpr f.2.1))) := by
  simp [parkingToPath, toPaddedWord, pad]

private noncomputable def parkingPathEquiv {n : ℕ} (hn : 1 ≤ n) : Decreasing n ≃ SizedDyck n := by
  refine Equiv.ofBijective parkingToPath ⟨?_, ?_⟩
  · intro f g h
    have hl := congrArg (fun p : SizedDyck n => p.1.toList) h
    rw [parkingToPath_list, parkingToPath_list] at hl
    have hw := List.ofFn_injective hl
    have he := word_injective (funext fun i => stepEquiv.injective (congrFun hw i))
    have hd := congrArg decode he
    rw [decode_encode, decode_encode] at hd
    exact Subtype.ext (funext fun i => Fin.ext (by have := congrFun hd i; omega))
  · rintro ⟨p, hp⟩
    have hlen := p.two_mul_semilength_eq_length
    rw [hp] at hlen
    have hne : p.toList ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    have hlast : p.toList.getLast? = some D := by
      rw [List.getLast?_eq_some_getLast hne, p.getLast_eq_D]
    obtain ⟨w, hw, hsteps⟩ := exists_walk (k := 0) p (by simp [pad]) hlen.symm hlast
    obtain ⟨e, rfl⟩ := exists_word hw
    have hg := good_decode hn e hw
    let f (i : Fin n) : Fin n := ⟨downs e i.rev, by
      have := (hg.valid i).2
      simpa [decode] using this⟩
    have hdec : (fun i => (f i).val + 1) = decode e := rfl
    have hgood : Good 0 (fun i => (f i).val + 1) := hdec ▸ hg
    have ha : Antitone f := fun i k h => by
      have hh := hgood.anti h
      change (f k).val + 1 ≤ (f i).val + 1 at hh
      exact Fin.le_def.mpr (by omega)
    refine ⟨⟨f, (good_iff_parking f ha).mp hgood, ha⟩, Subtype.ext (DyckWord.ext ?_)⟩
    rw [parkingToPath_list]
    have he : encode hgood = e := encode_decode e hg
    exact (congrArg (steps ∘ word) he).trans hsteps

/-- Column `j` contains an Up step, i.e. one preceded by exactly `j` Down steps. -/
private def HasColumn (j : ℕ) (p : List DyckStep) : Prop :=
  ∃ a t, p = a ++ U :: t ∧ a.count D = j

private lemma downs_before_up {n : ℕ} (e : Fin n ↪o Fin (2 * n)) (i : Fin n) :
    ((steps (word e)).take (e i).val).count D = downs e i := by
  have h := height_word e (e i).isLt.le
  rw [before_up, Fin.card_Iio, ← stepHeight_steps] at h
  let l := (steps (word e)).take (e i).val
  have hlen : l.length = (e i).val := by simp [l]
  have hc : l.length = l.count D + l.count U := by
    have hcompl : (fun s : DyckStep => decide ((s == D) ≠ true)) = (· == U) := by
      funext s
      cases s <;> rfl
    simpa only [List.count, hcompl] using l.length_eq_countP_add_countP (· == D)
  change stepHeight l = _ at h
  unfold stepHeight at h
  have := index_le e i
  change l.count D = (e i).val - i.val
  omega

private lemma column_steps_iff {n : ℕ} (e : Fin n ↪o Fin (2 * n)) (j : ℕ) :
    HasColumn j (steps (word e)) ↔ ∃ i, downs e i = j := by
  constructor
  · rintro ⟨a, t, he, hj⟩
    have hlen : a.length < 2 * n := by
      have := congrArg List.length he
      simp only [length_steps, List.length_append, List.length_cons] at this
      omega
    let k : Fin (2 * n) := ⟨a.length, hlen⟩
    have hget : (steps (word e))[a.length]'(by simpa using hlen) = U := by
      simp [he, List.getElem_append_right]
    have hk : word e k = true := by
      simpa [steps, stepEquiv, k, apply_dite, apply_ite] using hget
    obtain ⟨i, hi⟩ := of_decide_eq_true hk
    refine ⟨i, ?_⟩
    rw [← downs_before_up e i, hi, he]
    simpa [k] using hj
  · rintro ⟨i, hi⟩
    let l := steps (word e)
    have hlt : (e i).val < l.length := by simp [l]
    have hu : l[(e i).val] = U := by simp [l, steps, stepEquiv, word]
    refine ⟨l.take (e i).val, l.drop ((e i).val + 1), ?_, (downs_before_up e i).trans hi⟩
    calc
      l = l.take (e i).val ++ l.drop (e i).val := (List.take_append_drop ..).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hlt, hu]

private lemma column_parking_iff {n : ℕ} (f : Decreasing n) (j : Fin n) :
    HasColumn j.val (parkingToPath f).1.toList ↔ Prefers f j := by
  rw [parkingToPath_list, column_steps_iff]
  let hg := (good_iff_parking f.1 f.2.2).mpr f.2.1
  change (∃ i, downs (encode hg) i = j.val) ↔ ∃ i, f.1 i = j
  have hd (i : Fin n) : downs (encode hg) i = (f.1 i.rev).val := by
    change i.val + ((f.1 i.rev).val + 1 - 1) - i.val = (f.1 i.rev).val
    omega
  simp only [hd]
  exact ⟨fun ⟨i, hi⟩ => ⟨i.rev, Fin.ext hi⟩,
    fun ⟨i, hi⟩ => ⟨i.rev, by simp [hi]⟩⟩

private lemma dyck_height (p : DyckWord) : stepHeight p.toList = 0 := by
  simp [stepHeight, p.count_U_eq_count_D]

private lemma dyck_prefix_height (p : DyckWord) (i : ℕ) : 0 ≤ stepHeight (p.toList.take i) := by
  have := p.count_D_le_count_U i
  unfold stepHeight
  omega

-- A walk with negative final height crosses down from its starting height. Everything before
-- that first crossing is a Dyck word. An initial Up step is paired before continuing the search.
private lemma split_negative (t : List DyckStep) (h : stepHeight t < 0) :
    ∃ (b : DyckWord) (c : List DyckStep), t = b.toList ++ D :: c := by
  match t with
  | [] => simp [stepHeight] at h
  | D :: t => exact ⟨0, t, rfl⟩
  | U :: t =>
    have ht : stepHeight t < 0 := by
      unfold stepHeight at h ⊢
      simp at h
      omega
    obtain ⟨b, c, hb⟩ := split_negative t ht
    have hnest : U :: t = b.nest.toList ++ c := by
      rw [hb]
      simp [DyckWord.nest, List.append_assoc]
    rw [hnest, stepHeight_append, dyck_height, zero_add] at h
    have hlen : c.length < (U :: t).length := by rw [hnest]; simp [DyckWord.nest]; omega
    obtain ⟨b', c', hc⟩ := split_negative c h
    exact ⟨b.nest + b', c', by rw [hnest, hc]; exact (List.append_assoc ..).symm⟩
termination_by t.length

private def AtColumn (a : List DyckStep) : Prop := a = [] ∨ a.getLast? = some D

private lemma column_cut (w : List DyckStep) (j : ℕ) (hj : j ≤ w.count D) :
    ∃ a c, w = a ++ c ∧ a.count D = j ∧ AtColumn a := by
  induction w generalizing j with
  | nil =>
    have : j = 0 := by simpa using hj
    subst j
    exact ⟨[], [], rfl, rfl, Or.inl rfl⟩
  | cons s w ih =>
    cases j with
    | zero => exact ⟨[], s :: w, rfl, rfl, Or.inl rfl⟩
    | succ j =>
      cases s with
      | U =>
        obtain ⟨a, c, rfl, hcount, ha⟩ := ih (j + 1) (by simpa using hj)
        refine ⟨U :: a, c, rfl, by simpa using hcount, Or.inr ?_⟩
        cases a with
        | nil => simp at hcount
        | cons t a => simpa using ha.resolve_left (by simp)
      | D =>
        obtain ⟨a, c, rfl, hcount, ha⟩ := ih j (by simpa using hj)
        refine ⟨D :: a, c, rfl, by simpa using hcount, Or.inr ?_⟩
        cases a with
        | nil => rfl
        | cons t a => simpa using ha.resolve_left (by simp)

private lemma column_cut_with_up {j : ℕ} {w : List DyckStep} (h : HasColumn j w) :
    ∃ a c, w = a ++ U :: c ∧ a.count D = j ∧ AtColumn a := by
  obtain ⟨a', t, rfl, hj⟩ := h
  obtain ⟨a, e, rfl, ha, hb⟩ := column_cut a' j hj.ge
  have he : e.count D = 0 := by
    rw [List.count_append, ha] at hj
    omega
  rw [List.append_assoc]
  cases e with
  | nil => exact ⟨a, t, rfl, ha, hb⟩
  | cons s e =>
    cases s with
    | D => simp at he
    | U => exact ⟨a, e ++ U :: t, rfl, ha, hb⟩

private lemma column_cut_unique {a b c d : List DyckStep} (h : a ++ c = b ++ d)
    (hc : a.count D = b.count D) (ha : AtColumn a) (hb : AtColumn b) : a = b := by
  have noShort {a b c d : List DyckStep} (h : a ++ c = b ++ d)
      (hc : a.count D = b.count D) (hb : AtColumn b) : ¬ a.length < b.length := by
    intro hlt
    have he := congrArg (List.take a.length) h
    rw [List.take_left, List.take_append_of_le_length hlt.le] at he
    let e := b.drop a.length
    have hbe : a ++ e = b := by rw [he]; exact List.take_append_drop ..
    have he' : e ≠ [] := by simp [e, Nat.not_le.mpr hlt]
    have hzero : e.count D = 0 := by
      rw [← hbe, List.count_append] at hc
      omega
    have hlast := hb.resolve_left (by intro heq; simp [heq] at hlt)
    rw [← hbe, List.getLast?_append_of_ne_nil _ he'] at hlast
    obtain ⟨r, hr⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [hr] at hzero
    simp at hzero
  have hl := not_lt.mp (noShort h hc hb)
  have hr := not_lt.mp (noShort h.symm hc.symm ha)
  have he := congrArg (List.take a.length) h
  rw [List.take_left, hr.antisymm hl, List.take_left] at he
  exact he

-- Prefixes of the spliced list are prefixes of the outer list with a (possibly empty)
-- prefix of the inserted word added. The displayed index skips the inserted steps.
private lemma stepHeight_take_splice (a b c : List DyckStep) (i : ℕ) :
    stepHeight ((a ++ b ++ c).take i) =
      stepHeight ((a ++ c).take (i - min (i - a.length) b.length)) +
        stepHeight (b.take (i - a.length)) := by
  by_cases hi : i ≤ a.length
  · rw [List.append_assoc, List.take_append_of_le_length hi, Nat.sub_eq_zero_of_le hi]
    simp [List.take_append_of_le_length hi, stepHeight]
  · have h₁ : a.length ≤ i - min (i - a.length) b.length := by omega
    have h₂ : i - min (i - a.length) b.length - a.length = i - a.length - b.length := by omega
    simp only [List.append_assoc, List.take_append, stepHeight_append,
      List.take_of_length_le (show a.length ≤ i by omega), List.take_of_length_le h₁, h₂]
    omega

private lemma dyck_of_height (w : List DyckStep) (h : stepHeight w = 0)
    (hp : ∀ i, 0 ≤ stepHeight (w.take i)) : ∃ p : DyckWord, p.toList = w := by
  exact ⟨⟨w, by unfold stepHeight at h; omega, fun i => by
    have := hp i
    unfold stepHeight at this
    omega⟩, rfl⟩

private lemma splice_dyck (p b : DyckWord) {a c : List DyckStep} (h : p.toList = a ++ c) :
    ∃ w : DyckWord, w.toList = a ++ b.toList ++ c := by
  apply dyck_of_height
  · simpa [stepHeight_append, dyck_height b, h] using dyck_height p
  · intro i
    rw [stepHeight_take_splice, ← h]
    exact add_nonneg (dyck_prefix_height p _) (dyck_prefix_height b _)

private lemma erase_dyck (p b : DyckWord) {a c : List DyckStep}
    (h : p.toList = a ++ b.toList ++ c) : ∃ w : DyckWord, w.toList = a ++ c := by
  apply dyck_of_height
  · simpa [stepHeight_append, h, dyck_height b] using dyck_height p
  · intro i
    by_cases hi : i ≤ a.length
    · have hp := dyck_prefix_height p i
      rw [h, List.append_assoc, List.take_append_of_le_length hi] at hp
      rwa [List.take_append_of_le_length hi]
    · have hp := dyck_prefix_height p (i + b.toList.length)
      have hb : b.toList.length ≤ i + b.toList.length - a.length := by omega
      rw [h, stepHeight_take_splice, min_eq_right hb, Nat.add_sub_cancel,
        List.take_of_length_le hb, dyck_height, add_zero] at hp
      exact hp

private lemma nested_cut_unique {b b' : DyckWord} {c c' : List DyckStep}
    (h : b.nest.toList ++ c = b'.nest.toList ++ c') : b = b' ∧ c = c' := by
  have noShort {u v : DyckWord} {s t : List DyckStep}
      (h : u.nest.toList ++ s = v.nest.toList ++ t) :
      ¬ u.nest.toList.length < v.nest.toList.length := by
    intro hlt
    have hp := DyckWord.IsNested.nest (p := v)
    have hs : 0 < u.nest.toList.length := by simp [DyckWord.nest]
    have hn := hp.2 hs hlt
    have ht := congrArg (List.take u.nest.toList.length) h
    rw [List.take_left, List.take_append_of_le_length hlt.le] at ht
    rw [← ht, u.nest.count_U_eq_count_D] at hn
    exact (lt_irrefl _) hn
  have hl := (not_lt.mp (noShort h.symm)).antisymm (not_lt.mp (noShort h))
  have he := congrArg (List.take b.nest.toList.length) h
  rw [List.take_left, hl, List.take_left] at he
  have hb : b.nest = b'.nest := DyckWord.ext he
  refine ⟨?_, List.append_cancel_left (he ▸ h)⟩
  simpa using congrArg DyckWord.insidePart hb

private abbrev ColumnDyck (n j : ℕ) :=
  {p : SizedDyck n // HasColumn j p.1.toList}

private abbrev CatalanPairs (n j : ℕ) :=
  Σ k : Fin (n - j), SizedDyck (n - 1 - k.val) × SizedDyck k.val

private lemma splice_column_exists {n j : ℕ} (x : CatalanPairs n j) :
    ∃ (p : ColumnDyck n j) (a c : List DyckStep),
      a.count D = j ∧ AtColumn a ∧ x.2.1.1.toList = a ++ c ∧
        p.1.1.toList = a ++ x.2.2.1.nest.toList ++ c := by
  obtain ⟨k, ⟨q, hq⟩, ⟨b, hb⟩⟩ := x
  have hcol : j ≤ q.toList.count D := by
    rw [← q.semilength_eq_count_D, hq]
    have := k.isLt
    omega
  obtain ⟨a, c, hcut, ha, hbound⟩ := column_cut q.toList j hcol
  obtain ⟨p, hp⟩ := splice_dyck q b.nest hcut
  have hp' : p.semilength = n := by
    have hq' : q.semilength = a.count U + c.count U := by
      simp [DyckWord.semilength, hcut]
    have := k.isLt
    simp only [DyckWord.semilength, hp, List.count_append] at ⊢
    rw [show b.nest.toList.count U = k.val + 1 by
      change b.nest.semilength = _
      simp [hb]]
    omega
  refine ⟨⟨⟨p, hp'⟩, ⟨a, b.toList ++ D :: c, ?_, ha⟩⟩, a, c, ha, hbound, hcut, hp⟩
  simpa [DyckWord.nest, List.append_assoc] using hp

private noncomputable def spliceColumnEquiv (n j : ℕ) : CatalanPairs n j ≃ ColumnDyck n j := by
  classical
  let paste (x : CatalanPairs n j) := (splice_column_exists x).choose
  have spec (x : CatalanPairs n j) := (splice_column_exists x).choose_spec
  refine Equiv.ofBijective paste ⟨?_, ?_⟩
  · intro x y h
    obtain ⟨a, c, ha, hcol, hx, hp⟩ := spec x
    obtain ⟨a', c', ha', hcol', hy, hp'⟩ := spec y
    have he := hp.symm.trans ((congrArg (fun p : ColumnDyck n j => p.1.1.toList) h).trans hp')
    simp only [List.append_assoc] at he
    have hae := column_cut_unique he (ha.trans ha'.symm) hcol hcol'
    subst a'
    obtain ⟨hb, hc⟩ := nested_cut_unique (List.append_cancel_left he)
    subst c'
    have hk : x.1 = y.1 := Fin.ext <|
      x.2.2.2.symm.trans ((congrArg DyckWord.semilength hb).trans y.2.2.2)
    obtain ⟨k, q, b⟩ := x
    obtain ⟨k', q', b'⟩ := y
    change k = k' at hk
    subst k'
    have hh : (q, b) = (q', b') :=
      Prod.ext (Subtype.ext (DyckWord.ext (hx.trans hy.symm))) (Subtype.ext hb)
    exact congrArg (Sigma.mk k) hh
  · rintro ⟨⟨p, hp⟩, hm⟩
    obtain ⟨a, t, hcut, ha, hbound⟩ := column_cut_with_up hm
    have ht : stepHeight t < 0 := by
      have hbal := dyck_height p
      have hpre := dyck_prefix_height p a.length
      rw [hcut, List.take_left] at hpre
      rw [hcut, stepHeight_append] at hbal
      have hhead : stepHeight (U :: t) = stepHeight t + 1 := by simp [stepHeight]; omega
      omega
    obtain ⟨b, c, hbc⟩ := split_negative t ht
    have hs : p.toList = a ++ b.nest.toList ++ c := by
      rw [hcut, hbc]
      simp [DyckWord.nest, List.append_assoc]
    obtain ⟨q, hq⟩ := erase_dyck p b.nest hs
    have hsum : p.semilength = q.semilength + (b.semilength + 1) := by
      simp only [DyckWord.semilength, hs, hq, List.count_append]
      rw [show b.nest.toList.count U = b.toList.count U + 1 by exact b.semilength_nest]
      omega
    have hj : j ≤ q.semilength := by rw [q.semilength_eq_count_D, hq, List.count_append, ha]; omega
    let k : Fin (n - j) := ⟨b.semilength, by omega⟩
    have hqsize : q.semilength = n - 1 - k.val := by dsimp [k]; omega
    let x : CatalanPairs n j := ⟨k, ⟨q, hqsize⟩, ⟨b, rfl⟩⟩
    obtain ⟨a', c', ha', ha'bound, houter, hinner⟩ := spec x
    have hout : a ++ c = a' ++ c' := hq.symm.trans houter
    have he := column_cut_unique hout (ha.trans ha'.symm) hbound ha'bound
    subst a'
    have hc := List.append_cancel_left hout
    subst c'
    exact ⟨x, Subtype.ext (Subtype.ext (DyckWord.ext (hinner.trans hs.symm)))⟩

/-- **Lucky spots of weakly decreasing parking functions as a Catalan convolution.** Number the
cars and spots $0, \dots, n-1$. For cars $i$ and spots $j$, let $q^d_n(i, j)$ be the number of
weakly decreasing parking functions $f$ of length $n$ (that is, $f(0) \ge f(1) \ge \dots \ge
f(n-1)$) with $f(i) = j$ in which car $i$ is lucky. Then for every spot $j$,
$$\sum_{i=0}^{n-1} q^d_n(i, j) = \sum_{k=0}^{n-j-1} C_{n-1-k} \, C_k,$$
where $C_m$ is the $m$-th Catalan number.

The left side counts the weakly decreasing parking functions in which spot $j$ is lucky, that
is, taken by a car that prefers it.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 24. -/
public theorem card_dec_lucky_spot_eq_sum_catalan (n : ℕ)
    (j : Fin n) :
    (∑ i : Fin n, (qDec n i j : ℚ)) =
      ∑ k ∈ Finset.range (n - j.val),
        ((catalan (n - 1 - k) * catalan k : ℕ) : ℚ) := by
  have h : {f : Decreasing n // Prefers f j} ≃ ColumnDyck n j.val :=
    (parkingPathEquiv (Nat.one_le_of_lt j.isLt)).subtypeEquiv fun f =>
      (column_parking_iff f j).symm
  have hcard : Nat.card {f : Decreasing n // Prefers f j} = Nat.card (CatalanPairs n j.val) :=
    Nat.card_congr (h.trans (spliceColumnEquiv n j.val).symm)
  have hdyck (m : ℕ) : Nat.card (SizedDyck m) = catalan m := by
    rw [Nat.card_eq_fintype_card, DyckWord.card_dyckWord_semilength_eq_catalan]
  calc
    _ = (Nat.card (Σ i : Fin n, { f : Fin n → Fin n //
          IsParkingFunction n f ∧ Antitone f ∧ f i = j ∧ IsLuckyCar f i }) : ℚ) := by
      rw [Nat.card_sigma, Nat.cast_sum]
      rfl
    _ = (Nat.card (CatalanPairs n j.val) : ℚ) := by
      rw [Nat.card_congr (luckySpotEquiv j), hcard]
    _ = _ := by
      rw [Nat.card_sigma, Nat.cast_sum]
      simp only [Nat.card_prod, hdyck]
      exact Fin.sum_univ_eq_sum_range (fun k => ((catalan (n - 1 - k) * catalan k : ℕ) : ℚ)) _

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
