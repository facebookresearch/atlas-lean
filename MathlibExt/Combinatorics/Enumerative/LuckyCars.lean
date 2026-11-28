/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import MathlibExt.Probability.BertrandBallot

/-!
# Lucky cars in parking functions

The greedy parking rule assigns spots in arrival order. It determines which cars are lucky
and the counts of parking functions with a prescribed lucky car and spot.

## References

* Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats,
  *Lucky Cars and Lucky Spots in Parking Functions*, Journal of Integer Sequences 29 (2026),
  Article 26.1.1, pp. 1–18, Section 4.2 and Lemma 21.
* The proof of `nextFreeSpot_of_notMem` was moved from the ATLAS module `StirlingLuckyDisplacement`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt Polynomial

/-- **Next free spot.** Number the $n$ spots $0, \dots, n-1$. Given a set $S$ of occupied
spots and a spot $a$, the next free spot is the least spot $s \ge a$ with $s \notin S$; when
every spot $s \ge a$ is occupied, it is $a$ itself. -/
def nextFreeSpot {n : ℕ} (occ : Finset (Fin n)) (a : Fin n) : Fin n :=
  if h : (Finset.univ.filter (fun s : Fin n => a ≤ s ∧ s ∉ occ)).Nonempty then
    (Finset.univ.filter (fun s : Fin n => a ≤ s ∧ s ∉ occ)).min' h
  else a

/-- **Lower bound on the next free spot.** If a car prefers spot $a$, the greedy rule assigns it
a spot at or after $a$. This includes the fallback to $a$ when every eligible spot is occupied. -/
theorem le_nextFreeSpot {n : ℕ} (occ : Finset (Fin n)) (a : Fin n) :
    a ≤ nextFreeSpot occ a := by
  unfold nextFreeSpot
  split_ifs with h
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.1
  · exact le_rfl

/-- **Unoccupied preferred spot.** If the preferred spot $a$ is not occupied, then $a$ is the
next free spot. -/
theorem nextFreeSpot_of_notMem {m : ℕ} {occ : Finset (Fin m)} {a : Fin m}
    (ha : a ∉ occ) : nextFreeSpot occ a = a := by
  have hmem : a ∈ Finset.univ.filter (fun q : Fin m => a ≤ q ∧ q ∉ occ) := by simp [ha]
  have h := Finset.min'_mem _ ⟨a, hmem⟩
  rw [nextFreeSpot, dite_eq_left ⟨a, hmem⟩]
  exact le_antisymm (Finset.min'_le _ _ hmem) (Finset.mem_filter.mp h).2.1

/-- **Greedy parking from an occupied set.** Number the $n$ spots $0, \dots, n-1$. Given a list
$a_1, \dots, a_m$ of preferred spots and a set $S$ of occupied spots, cars $1, \dots, m$ arrive in
order and car $k$ takes the least spot at or after $a_k$ that is neither in $S$ nor taken by cars
$1, \dots, k-1$ (or $a_k$ itself if there is none). The result is the list of spots taken, in
arrival order. -/
def parkSpotsFrom {n : ℕ} : List (Fin n) → Finset (Fin n) → List (Fin n)
  | [], _ => []
  | a :: rest, occ =>
      nextFreeSpot occ a ::
        parkSpotsFrom rest (insert (nextFreeSpot occ a) occ)

/-- **Greedy parking outcome.** Let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the
preferred spot of each of $n$ cars. Starting from an empty lot with spots $0, \dots, n-1$, cars
$0, 1, \dots, n-1$ arrive in order, and each takes the least free spot at or after its preference
(or its preference itself if there is none). The outcome sends each car $i$ to the spot it takes. -/
def parkSpots {n : ℕ} (f : Fin n → Fin n) : Fin n → Fin n :=
  fun i => (parkSpotsFrom (List.ofFn f) ∅).getD i.val i

-- If the occupied set is small enough at each arrival, every next spot is fresh.
private lemma parkSpotsFrom_spec_of_room {n : ℕ} (l : List (Fin n)) (occ : Finset (Fin n))
    (hroom : ∀ (i : ℕ) (hi : i < l.length), occ.card + i < n - l[i].val) :
    (parkSpotsFrom l occ).length = l.length ∧ (parkSpotsFrom l occ).Nodup ∧
      ∀ s ∈ parkSpotsFrom l occ, s ∉ occ := by
  induction l generalizing occ with
  | nil => simp [parkSpotsFrom]
  | cons a l ih =>
    let free := Finset.univ.filter fun s : Fin n => a ≤ s ∧ s ∉ occ
    have hfree : free.Nonempty := by
      by_contra h
      have hsub : Finset.Ici a ⊆ occ := by
        intro b hb
        by_contra hbo
        exact h ⟨b, by simp [free, Finset.mem_Ici.mp hb, hbo]⟩
      have hc := Finset.card_le_card hsub
      rw [Fin.card_Ici] at hc
      have h0 := hroom 0 (by simp)
      exact (not_le_of_gt (by simpa using h0 : occ.card < n - a.val)) hc
    have ha : nextFreeSpot occ a ∉ occ := by
      rw [nextFreeSpot, dite_eq_left hfree]
      exact (Finset.mem_filter.mp (Finset.min'_mem free hfree)).2.2
    have hrest (i : ℕ) (hi : i < l.length) :
        (insert (nextFreeSpot occ a) occ).card + i < n - l[i].val := by
      have hc := Finset.card_insert_le (nextFreeSpot occ a) occ
      have h := hroom (i + 1) (by simpa using hi)
      change occ.card + (i + 1) < n - l[i].val at h
      omega
    obtain ⟨hlen, hnd, hdisj⟩ := ih _ hrest
    rw [parkSpotsFrom]
    refine ⟨by simp [hlen], hnd.cons (fun hs => hdisj _ hs (Finset.mem_insert_self ..)), ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ha
    · exact fun hocc => hdisj _ hs (Finset.mem_insert_of_mem hocc)

-- Cars preferring a strictly smaller spot than car `i` all arrive after it.
private lemma car_index_lt_room_of_antitone {n : ℕ} {f : Fin n → Fin n}
    (hf : IsParkingFunction n f) (hdec : Antitone f) (i : Fin n) :
    i.val < n - (f i).val := by
  by_cases h0 : (f i).val = 0
  · simp [h0]
  let j : Fin n := ⟨(f i).val - 1, (Nat.sub_le ..).trans_lt (f i).isLt⟩
  have hsub : Finset.univ.filter (fun k => f k ≤ j) ⊆ Finset.Ioi i := by
    intro k hk
    refine Finset.mem_Ioi.mpr (lt_of_not_ge fun hki => ?_)
    have h := Fin.le_def.mp ((hdec hki).trans (Finset.mem_filter.mp hk).2)
    change (f i).val ≤ (f i).val - 1 at h
    omega
  have h := ((isParkingFunction_iff_card_filter_le n f).mp hf j).trans
    (Finset.card_le_card hsub)
  rw [Fin.card_Ioi] at h
  change (f i).val - 1 + 1 ≤ n - 1 - i.val at h
  omega

/-- **Distinct greedy spots for decreasing preferences.** For a weakly decreasing parking
function, the greedy rule assigns distinct spots to distinct cars: each car has more eligible
spots than there are preceding cars. -/
theorem parkSpots_injective_of_antitone {n : ℕ} {f : Fin n → Fin n}
    (hf : IsParkingFunction n f) (hdec : Antitone f) : Function.Injective (parkSpots f) := by
  have hroom (i : ℕ) (hi : i < (List.ofFn f).length) :
      (∅ : Finset (Fin n)).card + i < n - (List.ofFn f)[i].val := by
    rw [Finset.card_empty, Nat.zero_add, List.getElem_ofFn]
    exact car_index_lt_room_of_antitone hf hdec ⟨i, by simpa using hi⟩
  obtain ⟨hlen, hnd, _⟩ := parkSpotsFrom_spec_of_room (List.ofFn f) ∅ hroom
  intro i j h
  have hi : i.val < (parkSpotsFrom (List.ofFn f) ∅).length := by simp [hlen]
  have hj : j.val < (parkSpotsFrom (List.ofFn f) ∅).length := by simp [hlen]
  unfold parkSpots at h
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact Fin.ext (hnd.getElem_inj_iff.mp h)

/-- **Lucky car under greedy parking.** Let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the
preferred spot of each of $n$ cars. Cars $0, 1, \dots, n-1$ arrive in order, and each takes the
least spot at or after its preference not taken by an earlier car, or its preferred spot itself
when there is no such spot. Car $i$ is lucky if the spot it takes is its preferred spot $f(i)$.

For a parking function a free spot always exists. -/
def IsLuckyCar {n : ℕ} (f : Fin n → Fin n) (i : Fin n) : Prop :=
  parkSpots f i = f i

/-- **Criterion for a lucky car.** For a preference map $f$, car $i$ is lucky exactly when
its assigned spot is $f(i)$. -/
theorem isLuckyCar_iff_parkSpots_eq {n : ℕ} (f : Fin n → Fin n) (i : Fin n) :
    IsLuckyCar f i ↔ parkSpots f i = f i := Iff.rfl

private lemma getD_parkSpotsFrom_of_lt_before {n : ℕ} (l : List (Fin n)) (i : ℕ)
    (hi : i < l.length) (occ : Finset (Fin n)) (d : Fin n) (hfree : l[i] ∉ occ)
    (hprev : ∀ k, (hk : k < i) → l[i] < l[k]) :
    (parkSpotsFrom l occ).getD i d = l[i] := by
  induction l generalizing i occ with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => exact nextFreeSpot_of_notMem hfree
    | succ i =>
      have hit : i < l.length := by simpa using hi
      have ha : l[i] < a := hprev 0 (Nat.zero_lt_succ i)
      rw [parkSpotsFrom, List.getD_cons_succ]
      exact ih i hit _ (by
        rw [Finset.mem_insert, not_or]
        exact ⟨(ha.trans_le (le_nextFreeSpot occ a)).ne, hfree⟩)
        (fun k hk => hprev (k + 1) (Nat.succ_lt_succ hk))

/-- **A preferred spot is lucky in decreasing order.** If the preferences are weakly decreasing
and some car prefers spot $j$, a car preferring $j$ is lucky. The first such car finds $j$ free
because all earlier preferences are larger.

Source: Steve Butler et al., *Lucky Cars and Lucky Spots in Parking Functions*,
Journal of Integer Sequences 29 (2026), Article 26.1.1, Section 4.2. -/
theorem exists_lucky_of_preferred {n : ℕ} {f : Fin n → Fin n} (hf : Antitone f)
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

/-- **Number of lucky cars.** Let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the preferred
spot of each of $n$ cars, and let cars $0, 1, \dots, n-1$ arrive in order, each taking the least
spot at or after its preference not taken by an earlier car, or its preferred spot itself when
there is no such spot. The number of lucky cars of $f$ is the number of cars $i$ whose spot is
$f(i)$. -/
def luckyCount {n : ℕ} (f : Fin n → Fin n) : ℕ :=
  (Finset.univ.filter (fun i => decide (parkSpots f i = f i))).card

/-- **Lucky-car counts.** Number the cars and spots $0, \dots, n-1$. For
$i, j \in \{0, \dots, n-1\}$, $q_n(i, j)$ is the number of parking functions
$f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $f(i) = j$ in which car $i$ is lucky, that is,
parks in spot $f(i)$.

In the one-based indexing of Butler et al. this is $q_n(i+1, j+1)$. -/
noncomputable def q (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ f i = j ∧ IsLuckyCar f i }

/-- **Increasing lucky-car counts.** Number the cars and spots $0, \dots, n-1$. For
$i, j \in \{0, \dots, n-1\}$, $q^{\mathrm{inc}}_n(i, j)$ is the number of weakly increasing parking
functions $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $f(i) = j$ in which car $i$ is lucky,
that is, parks in spot $f(i)$.

In the one-based indexing of Butler et al. this is $q^i_n(i+1, j+1)$. -/
noncomputable def qInc (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ Monotone f ∧ f i = j ∧
      IsLuckyCar f i }

/-- **Decreasing lucky-car counts.** Number the cars and spots $0, \dots, n-1$. For
$i, j \in \{0, \dots, n-1\}$, $q^{\mathrm{dec}}_n(i, j)$ is the number of weakly decreasing parking
functions $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $f(i) = j$ in which car $i$ is lucky,
that is, parks in spot $f(i)$.

In the one-based indexing of Butler et al. this is $q^d_n(i+1, j+1)$. -/
noncomputable def qDec (n : ℕ) (i j : Fin n) : ℕ :=
  Nat.card { f : Fin n → Fin n //
    IsParkingFunction n f ∧ Antitone f ∧ f i = j ∧
      IsLuckyCar f i }

/-- **Cardinality of decreasing lucky-car counts.** The number $q^{\mathrm{dec}}_n(i,j)$ is the
cardinality of the set of weakly decreasing parking functions of length $n$ in which car $i$
prefers spot $j$ and is lucky. -/
theorem qDec_eq_card (n : ℕ) (i j : Fin n) :
    qDec n i j = Nat.card {f : Fin n → Fin n //
      IsParkingFunction n f ∧ Antitone f ∧ f i = j ∧ IsLuckyCar f i} := rfl

/-- **Lucky-car polynomial.** For $n \in \mathbb{N}$, $f_n \in \mathbb{Q}[x]$ is the polynomial
$$f_n(x) = \frac{1}{n+1} \prod_{i=0}^{n-1} \bigl((n+1-i)\,x + i\bigr).$$

Equivalently, $f_n(x) = \frac{1}{n+1} \prod_{i=1}^{n} \bigl((n+2-i)\,x + (i-1)\bigr)$. -/
noncomputable def luckyGenPoly (n : ℕ) : Polynomial ℚ :=
  C (1 / (n + 1 : ℚ)) *
    ∏ i : Fin n, (C ((n + 1 - i.val : ℕ) : ℚ) * X + C (i.val : ℚ))

/-- **Ballot paths.** For $k, \ell \in \mathbb{N}$, a ballot path to $(k, \ell)$ is a word of length
$k + \ell$ in up steps and right steps with exactly $\ell$ up steps such that every prefix has at
least as many up steps as right steps; equivalently, a lattice path from $(0,0)$ to $(k, \ell)$
with unit up and right steps that stays on or above the line $y = x$. -/
def BallotPath (k ℓ : ℕ) : Type :=
  { w : List Bool // w.length = k + ℓ ∧ w.count true = ℓ ∧
    ∀ m : ℕ, m ≤ w.length →
      (w.take m).count false ≤ (w.take m).count true }

private theorem count_take_ofFn {n : ℕ} (f : Fin n → Bool) (m : ℕ) (b : Bool) :
    ((List.ofFn f).take m).count b =
      (Finset.univ.filter fun i => i.val < m ∧ f i = b).card := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [List.ofFn_succ, List.take_succ_cons, List.count_cons, ih]
      simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
        Nat.zero_lt_succ, true_and, Nat.succ_lt_succ_iff, beq_iff_eq]
      exact Nat.add_comm _ _

private def StrictBallotWord (n p : ℕ) : Type :=
  { f : Fin n → Bool //
    (Finset.univ.filter fun i => f i = true).card = p ∧
    ∀ j : Fin n, (Finset.univ.filter fun i => i ≤ j ∧ f i = false).card <
      (Finset.univ.filter fun i => i ≤ j ∧ f i = true).card }

private theorem strictBallotWord_iff {n p : ℕ} (f : Fin n → Bool) :
    ((Finset.univ.filter fun i => f i = true).card = p ∧
      ∀ j : Fin n, (Finset.univ.filter fun i => i ≤ j ∧ f i = false).card <
        (Finset.univ.filter fun i => i ≤ j ∧ f i = true).card) ↔
    (List.ofFn f).count true = p ∧
      ∀ m : ℕ, 0 < m → m ≤ n →
        ((List.ofFn f).take m).count false < ((List.ofFn f).take m).count true := by
  have htotal := count_take_ofFn f n true
  rw [List.take_of_length_le (by simp)] at htotal
  simp only [Fin.is_lt, true_and] at htotal
  rw [htotal]
  refine and_congr_right fun _ => ?_
  have hprefix (j : Fin n) (b : Bool) :
      ((List.ofFn f).take (j.val + 1)).count b =
        (Finset.univ.filter fun i => i ≤ j ∧ f i = b).card := by
    simpa only [Nat.lt_succ_iff, Fin.le_iff_val_le_val] using
      count_take_ofFn f (j.val + 1) b
  constructor
  · intro hf m hm hmn
    let j : Fin n := ⟨m - 1, by omega⟩
    have hj : j.val + 1 = m := by dsimp [j]; omega
    rw [← hj, hprefix, hprefix]
    exact hf j
  · intro hf j
    rw [← hprefix, ← hprefix]
    exact hf (j.val + 1) (by omega) (by omega)

private theorem ofFn_get_cast {w : List Bool} {n : ℕ} (hw : w.length = n) :
    List.ofFn (fun i : Fin n => w.get (Fin.cast hw.symm i)) = w := by
  subst n
  exact List.ofFn_get w

-- Prepending an up step makes all nonempty prefixes strictly positive.
private noncomputable def ballotPathEquiv (k ℓ : ℕ) :
    BallotPath k ℓ ≃ StrictBallotWord (k + ℓ + 1) (ℓ + 1) := by
  let prepend (w : BallotPath k ℓ) : Fin (k + ℓ + 1) → Bool :=
    Fin.cons true (fun i => w.val.get (Fin.cast w.property.1.symm i))
  have hprepend (w : BallotPath k ℓ) : List.ofFn (prepend w) = true :: w.val := by
    change List.ofFn (Fin.cons true fun i => w.val.get (Fin.cast w.property.1.symm i)) = _
    rw [List.ofFn_cons, ofFn_get_cast w.property.1]
  let toStrict (w : BallotPath k ℓ) : StrictBallotWord (k + ℓ + 1) (ℓ + 1) := by
    refine ⟨prepend w, (strictBallotWord_iff _).2 ?_⟩
    obtain ⟨hw, hc, hp⟩ := w.property
    rw [hprepend]
    refine ⟨by simp [hc], ?_⟩
    intro m hm hlen
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    simpa [List.take_succ_cons, Nat.lt_succ_iff] using hp m (by omega)
  refine Equiv.ofBijective toStrict ⟨?_, ?_⟩
  · intro a b hab
    have he := congrArg (fun w : StrictBallotWord (k + ℓ + 1) (ℓ + 1) =>
      List.ofFn w.val) hab
    change List.ofFn (prepend a) = List.ofFn (prepend b) at he
    rw [hprepend, hprepend] at he
    exact Subtype.ext (List.cons.inj he).2
  · rintro ⟨f, hf⟩
    obtain ⟨hc, hp⟩ := (strictBallotWord_iff f).1 hf
    have hhead : f 0 = true := by
      have hfirst := hp 1 (by omega) (by omega)
      rw [List.ofFn_succ, List.take_succ_cons] at hfirst
      cases h : f 0 <;> simp_all
    have hcons : List.ofFn f = true :: List.ofFn (Fin.tail f) := by
      rw [List.ofFn_succ, hhead]
      rfl
    rw [hcons] at hc hp
    let w : BallotPath k ℓ := ⟨List.ofFn (Fin.tail f), List.length_ofFn, by simpa using hc, by
      intro m hm
      simpa [List.take_succ_cons, Nat.lt_succ_iff] using
        hp (m + 1) (by omega) (by simpa using hm)⟩
    refine ⟨w, Subtype.ext (List.ofFn_injective ?_)⟩
    change List.ofFn (prepend w) = List.ofFn f
    rw [hprepend, hcons]

private theorem card_ballotPath_zero (ℓ : ℕ) : Nat.card (BallotPath 0 ℓ) = 1 := by
  have hrep (w : BallotPath 0 ℓ) : w.val = List.replicate ℓ true := by
    obtain ⟨hw, hc, _⟩ := w.property
    have hw' : w.val.length = ℓ := by simpa using hw
    exact List.eq_replicate_iff.mpr ⟨hw', fun b hb =>
      (List.count_eq_length.mp (hc.trans hw'.symm) b hb).symm⟩
  let _ : Subsingleton (BallotPath 0 ℓ) :=
    ⟨fun a b => Subtype.ext ((hrep a).trans (hrep b).symm)⟩
  let _ : Nonempty (BallotPath 0 ℓ) :=
    ⟨⟨List.replicate ℓ true, by simp [List.count_replicate]⟩⟩
  exact Nat.card_unique

/-- **Number of ballot paths.** For natural numbers $k \le \ell$, the number of lattice paths
from $(0,0)$ to $(k, \ell)$ with unit up and right steps that stay on or above the line $y = x$
is $\frac{\ell - k + 1}{\ell + 1} \binom{k + \ell}{k}$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 21. -/
theorem card_ballotPath (k ℓ : ℕ) (h : k ≤ ℓ) :
    (Nat.card (BallotPath k ℓ) : ℚ) =
      ((ℓ - k + 1 : ℚ) / (ℓ + 1)) * Nat.choose (k + ℓ) k := by
  by_cases hk : k = 0
  · subst k
    rw [card_ballotPath_zero]
    simp [div_self (show (ℓ : ℚ) + 1 ≠ 0 by positivity)]
  have hs : Nat.card (StrictBallotWord ((ℓ + 1) + k) (ℓ + 1)) * ((ℓ + 1) + k) =
      (ℓ + 1 - k) * Nat.choose ((ℓ + 1) + k) k := by
    unfold StrictBallotWord
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact MetaMathlibExt.bertrand_ballot (ℓ + 1) k (by omega) (by omega)
  have hn : (ℓ + 1) + k = k + ℓ + 1 := by omega
  rw [hn, ← Nat.card_congr (ballotPathEquiv k ℓ)] at hs
  -- Removing the extra step changes the binomial factor and its denominator.
  have hc := Nat.choose_mul_succ_eq (k + ℓ) k
  rw [show k + ℓ + 1 - k = ℓ + 1 by omega] at hc
  have he : Nat.card (BallotPath k ℓ) * (ℓ + 1) =
      (ℓ + 1 - k) * Nat.choose (k + ℓ) k := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < k + ℓ + 1 by omega)
    calc
      _ = (Nat.card (BallotPath k ℓ) * (k + ℓ + 1)) * (ℓ + 1) := by ac_rfl
      _ = (ℓ + 1 - k) * (Nat.choose (k + ℓ + 1) k * (ℓ + 1)) := by rw [hs, mul_assoc]
      _ = _ := by rw [← hc, mul_assoc]
  have heq : (Nat.card (BallotPath k ℓ) : ℚ) * ((ℓ : ℚ) + 1) =
      (↑(ℓ + 1 - k) : ℚ) * (Nat.choose (k + ℓ) k : ℚ) := by exact_mod_cast he
  rw [div_mul_eq_mul_div, eq_div_iff (show (ℓ : ℚ) + 1 ≠ 0 by positivity)]
  simpa [Nat.cast_sub (show k ≤ ℓ + 1 by omega), sub_add_eq_add_sub] using heq

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
