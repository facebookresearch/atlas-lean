/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Combinatorics.Enumerative.KNaplesParking
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.LinearCombination

/-!
# Descending Naples parking functions and bounded Dyck paths

Descending parking preferences are encoded by the positions of the Up steps. This gives
`descendingNaplesCount_eq_card_kDyckPath`, equating the two counts.
Counting the bounded paths gives the binomial formulas in `descendingNaplesCount_eq_choose`.
For `j : Fin n`, ordinary weakly decreasing parking functions with a car preferring `j`
correspond to paths having an Up step preceded by exactly `j.val` Down steps.

## References

* J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny, and A. R. Vindas Meléndez,
  *Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
  Article A44, pp. 1–18, Section 3, Proposition 2 and Theorem 7.
* A. Christensen, P. E. Harris, Z. Jones, M. Loving, A. Ramos Rodríguez, J. Rennie,
  and G. Rojas Kirby, *A Generalization of Parking Functions Allowing Backward Movement*,
  Electronic Journal of Combinatorics 27(1) (2020), Article P1.33, pp. 1–20, Theorem 1.3
  (the bounded-path correspondence cited in Proposition 2).
* Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats,
  *Lucky Cars and Lucky Spots in Parking Functions*, Journal of Integer Sequences 29 (2026),
  Article 26.1.1, pp. 1–18, Section 4, for the ordinary parking correspondence.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of descending $k$-Naples parking functions.** For natural numbers $n$ and $k$, this
is the number of $k$-Naples parking functions $\alpha = (a_1, \dots, a_n)$ of length $n$ (so
$a_i \in \{1, \dots, n\}$ for all $i$) that are descending, that is, weakly decreasing:
$a_1 \ge a_2 \ge \dots \ge a_n$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 2. -/
public def descendingNaplesCount (n k : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
    (∀ i j : Fin n, i ≤ j → α j ≤ α i) ∧ IsNaplesParkingFunction k α).card

/-- **Number of descending strictly $k$-Naples parking functions.** For natural numbers $n$ and
$k$, this is the number of preferences $\alpha = (a_1, \dots, a_n) \in \{1, \dots, n\}^n$ that
are descending ($a_1 \ge a_2 \ge \dots \ge a_n$), are $k$-Naples parking functions, and are not
$(k - 1)$-Naples parking functions. It is used for $k \ge 1$; for $k = 0$, where $k - 1$ is
read as $0$, the count is $0$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 4. -/
public def descendingStrictNaplesCount (n k : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
    (∀ i j : Fin n, i ≤ j → α j ≤ α i) ∧ IsNaplesParkingFunction k α ∧
      ¬ IsNaplesParkingFunction (k - 1) α).card

/-- **Height of a lattice path.** For a lattice path $p$ of $m$ steps, each an Up step $(1, 1)$
or a Down step $(1, -1)$, and a natural number $j$, the height of $p$ after $j$ steps is the
number of Up steps minus the number of Down steps among the first $\min(j, m)$ steps of $p$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3. -/
public def latticeHeight {m : ℕ} (p : Fin m → Bool) (j : ℕ) : ℤ :=
  ∑ i : Fin m, if i.val < j then (if p i then 1 else -1) else 0

/-- **$k$-Dyck path.** Let $n$ and $k$ be natural numbers. A lattice path of $2n$ steps, each
an Up step $(1, 1)$ or a Down step $(1, -1)$, is a $k$-Dyck path of semilength $n$ if its height
after all $2n$ steps is $0$, its height after its first $j$ steps is at least $-k$ for every
$j \le 2n$, and, when $n \ge 1$, its last step is a Down step.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3. -/
public def IsKDyckPath (n k : ℕ) (p : Fin (2 * n) → Bool) : Prop :=
  latticeHeight p (2 * n) = 0 ∧ (∀ j ≤ 2 * n, -(k : ℤ) ≤ latticeHeight p j) ∧
    ∀ i : Fin (2 * n), i.val + 1 = 2 * n → p i = false

public instance (n k : ℕ) : DecidablePred (IsKDyckPath n k) := fun p => by
  unfold IsKDyckPath
  infer_instance

end

namespace descendingNaplesCount_eq_card_kDyckPath

/-- The spots inspected by a car form an interval, regardless of the order of inspection. -/
private def reachable (n k a : ℕ) : Finset ℕ := Finset.Icc (max 1 (a - k)) n

private theorem spot_mem {n k a : ℕ} (occ : List ℕ) (ha : 1 ≤ a ∧ a ≤ n) :
    match naplesSpot n k occ a with
    | some s => s ∈ reachable n k a ∧ s ∉ occ
    | none => ∀ s ∈ reachable n k a, s ∈ occ := by
  unfold naplesSpot
  rw [ite_eq_right (not_not_intro ha)]
  by_cases hfree : a ∉ occ
  · rw [ite_eq_left hfree]
    exact ⟨Finset.mem_Icc.mpr ⟨max_le ha.1 (Nat.sub_le ..), ha.2⟩, hfree⟩
  · rw [ite_eq_right hfree]
    cases hb : ((List.range k).map fun j => a - (j + 1)).find?
        (fun s => decide (1 ≤ s ∧ s ∉ occ)) with
    | some s =>
      obtain ⟨hs, hfree⟩ : 1 ≤ s ∧ s ∉ occ := by simpa using List.find?_some hb
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hb)
      have := List.mem_range.mp hj
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hfree⟩
    | none =>
      cases hf : (List.range' (a + 1) (n - a)).find? (fun s => decide (s ∉ occ)) with
      | some s =>
        obtain ⟨i, hi, he⟩ := List.mem_range'.mp (List.mem_of_find?_eq_some hf)
        simp only [Nat.one_mul] at he
        exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simpa using List.find?_some hf⟩
      | none =>
        intro s hs
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hs
        by_cases he : s = a
        · simpa [he] using hfree
        by_cases hlt : s < a
        · have hm : s ∈ (List.range k).map (fun j => a - (j + 1)) :=
            List.mem_map.mpr ⟨a - s - 1, List.mem_range.mpr (by omega), by omega⟩
          simpa [show 1 ≤ s by omega] using List.find?_eq_none.mp hb s hm
        · have hm : s ∈ List.range' (a + 1) (n - a) :=
            List.mem_range'.mpr ⟨s - (a + 1), by omega, by simp; omega⟩
          simpa using List.find?_eq_none.mp hf s hm

/-- At each arrival all previously occupied spots lie in the current reachable interval.
The car succeeds precisely when their number is smaller than the size of that interval. -/
private theorem park_iff {n k m : ℕ} (α : Fin m → ℕ) (occ : List ℕ)
    (hvalid : ∀ i, 1 ≤ α i ∧ α i ≤ n) (hanti : Antitone α) (hnd : occ.Nodup)
    (hlen : occ.length + m = n) (hsub : ∀ i, occ.toFinset ⊆ reachable n k (α i)) :
    (naplesPark n k occ (List.ofFn α)).isSome ↔ ∀ i, α i + i.val ≤ m + k := by
  induction m generalizing occ with
  | zero => simp [naplesPark, List.ofFn_zero]
  | succ m ih =>
    rw [List.ofFn_succ, naplesPark]
    have hcard : occ.toFinset.card = occ.length := List.toFinset_card_of_nodup hnd
    have hsize : (reachable n k (α 0)).card = n + 1 - max 1 (α 0 - k) := Nat.card_Icc ..
    have hspec := spot_mem (k := k) occ (hvalid 0)
    cases hs : naplesSpot n k occ (α 0) with
    | none =>
      rw [hs] at hspec
      have heq := Finset.Subset.antisymm (hsub 0)
        (fun s h => List.mem_toFinset.mpr (hspec s h))
      have hfull := congrArg Finset.card heq
      simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff]
      intro h
      have := h (0 : Fin (m + 1))
      simp only [Fin.val_zero, Nat.add_zero] at this
      omega
    | some s =>
      rw [hs] at hspec
      obtain ⟨hmem, hfree⟩ := hspec
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hsub 0, fun h => hfree (List.mem_toFinset.mp (h ▸ hmem))⟩)
      have hzero : α 0 ≤ m + 1 + k := by omega
      have hnext (i : Fin m) : (s :: occ).toFinset ⊆ reachable n k (α i.succ) := by
        have hle := hanti (Fin.zero_le i.succ)
        have hsm := Finset.mem_Icc.mp hmem
        intro t ht
        rcases List.mem_cons.mp (List.mem_toFinset.mp ht) with rfl | ht
        · exact Finset.mem_Icc.mpr ⟨by omega, hsm.2⟩
        · exact hsub _ (List.mem_toFinset.mpr ht)
      rw [Option.bind_some, ih (fun i => α i.succ) _ (fun i => hvalid _)
        (fun _ _ h => hanti (Fin.succ_le_succ_iff.mpr h)) (hnd.cons hfree)
        (by simp; omega) hnext, Fin.forall_fin_succ]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      constructor
      · exact fun h => ⟨hzero, fun i => by have := h i; omega⟩
      · exact fun h i => by have := h.2 i; omega

private def upSteps {m : ℕ} (p : Fin m → Bool) := Finset.univ.filter fun t => p t = true

private theorem height_eq {m : ℕ} (p : Fin m → Bool) {j : ℕ} (hj : j ≤ m) :
    latticeHeight p j = 2 * (((upSteps p).filter fun t => t.val < j).card : ℤ) - j := by
  let pre := Finset.univ.filter fun t : Fin m => t.val < j
  have hlen : pre.card = j := by
    rcases lt_or_eq_of_le hj with hj | rfl
    · have he : pre = Finset.Iio (⟨j, hj⟩ : Fin m) := by
        ext i
        simp [pre, Fin.lt_def]
      rw [he, Fin.card_Iio]
    · simp [pre]
  have he : (upSteps p).filter (fun t => t.val < j) = pre.filter (fun t => p t = true) := by
    ext
    simp [pre, upSteps, and_comm]
  unfold latticeHeight
  rw [he, ← Finset.sum_filter, Finset.sum_ite]
  change (∑ _t ∈ pre.filter (fun t => p t = true), (1 : ℤ)) +
    (∑ _t ∈ pre.filter (fun t => ¬p t = true), (-1 : ℤ)) = _
  simp only [Finset.sum_const, Int.nsmul_eq_mul, Int.mul_one, Int.mul_neg]
  have := Finset.card_filter_add_card_filter_not (s := pre) (p := fun t => p t = true)
  omega

private def word {n : ℕ} (e : Fin n ↪o Fin (2 * n)) (t : Fin (2 * n)) : Bool :=
  decide (∃ i, e i = t)

private theorem upSteps_word {n : ℕ} (e : Fin n ↪o Fin (2 * n)) :
    upSteps (word e) = Finset.univ.map e.toEmbedding := by
  ext
  simp [upSteps, word]

private def before {n : ℕ} (e : Fin n ↪o Fin (2 * n)) (j : ℕ) :=
  Finset.univ.filter fun i => (e i).val < j

private theorem height_word {n : ℕ} (e : Fin n ↪o Fin (2 * n)) {j : ℕ} (hj : j ≤ 2 * n) :
    latticeHeight (word e) j = 2 * ((before e j).card : ℤ) - j := by
  rw [height_eq _ hj, upSteps_word, Finset.filter_map, Finset.card_map]
  rfl

private theorem before_up {n : ℕ} (e : Fin n ↪o Fin (2 * n)) (i : Fin n) :
    before e (e i).val = Finset.Iio i := by
  ext t
  change (_ ∈ Finset.univ.filter fun j => e j < e i) ↔ _
  simp

/-- The lowest height between successive Up steps is reached just before the next Up step.
After the final Up step the path descends to height zero. -/
private theorem word_iff {n k : ℕ} (e : Fin n ↪o Fin (2 * n)) :
    IsKDyckPath n k (word e) ↔
      (∀ i, (e i).val ≤ 2 * i.val + k) ∧ (∀ i, (e i).val + 1 < 2 * n) := by
  constructor
  · rintro ⟨_, heights, last⟩
    constructor
    · intro i
      have h := heights (e i).val (e i).isLt.le
      rw [height_word _ (e i).isLt.le, before_up, Fin.card_Iio] at h
      omega
    · intro i
      have h := (e i).isLt
      by_contra! hlast
      have := last (e i) (by omega)
      simp [word] at this
  · rintro ⟨hup, hend⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [height_word _ le_rfl]
      simp [before]
    · intro j hj
      rw [height_word _ hj]
      let q := (before e j).card
      by_cases hq : q < n
      · let i : Fin n := ⟨q, hq⟩
        have hnext : j ≤ (e i).val := by
          by_contra! hlt
          have hsub : Finset.Iic i ⊆ before e j := by
            intro t ht
            have := e.monotone (Finset.mem_Iic.mp ht)
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_lt this hlt⟩
          have h := Finset.card_le_card hsub
          rw [Fin.card_Iic] at h
          change q + 1 ≤ q at h
          omega
        have h := hup i
        change (e i).val ≤ 2 * q + k at h
        change -(k : ℤ) ≤ 2 * (q : ℤ) - j
        omega
      · change -(k : ℤ) ≤ 2 * (q : ℤ) - j
        omega
    · intro t ht
      simp only [word, decide_eq_false_iff_not]
      rintro ⟨i, rfl⟩
      have := hend i
      omega

/-- Sorting the Up positions of a balanced path recovers their unique increasing enumeration. -/
private theorem exists_word {n k : ℕ} {p : Fin (2 * n) → Bool} (hp : IsKDyckPath n k p) :
    ∃ e : Fin n ↪o Fin (2 * n), word e = p := by
  have hz := hp.1
  rw [height_eq p le_rfl] at hz
  simp at hz
  have hc : (upSteps p).card = n := by omega
  let e := (upSteps p).orderEmbOfFin hc
  refine ⟨e, funext fun t => Bool.eq_iff_iff.mpr ?_⟩
  have he : upSteps (word e) = upSteps p := by
    rw [upSteps_word, Finset.map_orderEmbOfFin_univ]
  simpa [upSteps] using (Finset.ext_iff.mp he t)

private theorem word_injective {n : ℕ} :
    Function.Injective (word (n := n)) := by
  intro e f h
  let s := upSteps (word f)
  have hc : s.card = n := by simp [s, upSteps_word]
  have hm (g : Fin n ↪o Fin (2 * n)) (hg : word g = word f) :
      g = s.orderEmbOfFin hc := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    change g i ∈ upSteps (word f)
    rw [← hg, upSteps_word]
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  exact (hm e h).trans (hm f rfl).symm

private def parkingSet (n k : ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
    (∀ i j : Fin n, i ≤ j → α j ≤ α i) ∧ IsNaplesParkingFunction k α

private structure Good {n : ℕ} (k : ℕ) (α : Fin n → ℕ) : Prop where
  valid : ∀ i, 1 ≤ α i ∧ α i ≤ n
  anti : Antitone α
  bound : ∀ i, α i + i.val ≤ n + k

private theorem mem_parkingSet {n k : ℕ} {α : Fin n → ℕ} :
    α ∈ parkingSet n k ↔ Good k α := by
  rw [parkingSet, Finset.mem_filter]
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, IsNaplesParkingFunction]
  constructor
  · rintro ⟨hv, ha, _, hs⟩
    have hanti : Antitone α := fun _ _ => ha _ _
    exact ⟨hv, hanti, (park_iff α [] hv hanti (by simp) (by simp) (by simp)).mp hs⟩
  · intro h
    exact ⟨h.valid, fun _ _ hij => h.anti hij, h.valid,
      (park_iff α [] h.valid h.anti (by simp) (by simp) (by simp)).mpr h.bound⟩

/-- Before Up step number `i` (zero-based), there are `i` Up steps and
`α i.rev - 1` Down steps. -/
private def encode {n k : ℕ} {α : Fin n → ℕ} (h : Good k α) : Fin n ↪o Fin (2 * n) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨i.val + (α i.rev - 1), by have := h.valid i.rev; omega⟩)
    (by
      intro i j hij
      have hle := h.anti (Fin.rev_le_rev.mpr hij.le)
      change i.val + (α i.rev - 1) < j.val + (α j.rev - 1)
      omega)

private theorem word_encode {n k : ℕ} {α : Fin n → ℕ} (h : Good k α) :
    IsKDyckPath n k (word (encode h)) := by
  apply (word_iff _).mpr
  constructor <;> intro i
  · have hb := h.bound i.rev
    simp only [Fin.val_rev] at hb
    change i.val + (α i.rev - 1) ≤ 2 * i.val + k
    omega
  · have hv := h.valid i.rev
    change i.val + (α i.rev - 1) + 1 < 2 * n
    omega

/-- Subtract the earlier Up steps from the position of an Up step to count earlier Down steps. -/
private def downs {n : ℕ} (e : Fin n ↪o Fin (2 * n)) (i : Fin n) := (e i).val - i.val

private theorem index_le {n : ℕ} (e : Fin n ↪o Fin (2 * n)) (i : Fin n) :
    i.val ≤ (e i).val := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih => exact lt_of_le_of_lt ih (e.strictMono i.castSucc_lt_succ)

private theorem downs_mono {n : ℕ} (e : Fin n ↪o Fin (2 * n)) : Monotone (downs e) := by
  cases n with
  | zero => exact fun i => i.elim0
  | succ n =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have h := e.strictMono i.castSucc_lt_succ
    simp only [downs, Fin.val_castSucc, Fin.val_succ]
    omega

private def decode {n : ℕ} (e : Fin n ↪o Fin (2 * n)) (i : Fin n) := downs e i.rev + 1

private theorem good_decode {n k : ℕ} (hn : 1 ≤ n) (e : Fin n ↪o Fin (2 * n))
    (h : IsKDyckPath n k (word e)) : Good k (decode e) := by
  obtain ⟨hup, hend⟩ := (word_iff _).mp h
  refine ⟨fun i => ⟨by simp [decode], ?_⟩, ?_, ?_⟩
  · let last : Fin n := ⟨n - 1, by omega⟩
    have hm := downs_mono e (show i.rev ≤ last by change i.rev.val ≤ n - 1; omega)
    have he := hend last
    change downs e i.rev ≤ (e last).val - (n - 1) at hm
    change downs e i.rev + 1 ≤ n
    omega
  · intro i j hij
    exact Nat.add_le_add_right (downs_mono e (Fin.rev_le_rev.mpr hij)) 1
  · intro i
    have hb := hup i.rev
    simp only [decode, downs, Fin.val_rev] at hb ⊢
    omega

private theorem decode_encode {n k : ℕ} {α : Fin n → ℕ} (h : Good k α) :
    decode (encode h) = α := by
  funext i
  have := h.valid i
  change i.rev.val + (α i.rev.rev - 1) - i.rev.val + 1 = α i
  rw [Fin.rev_rev]
  omega

private theorem encode_decode {n k : ℕ} (e : Fin n ↪o Fin (2 * n)) (h : Good k (decode e)) :
    encode h = e := by
  ext i
  change i.val + (downs e i.rev.rev + 1 - 1) = (e i).val
  simp [downs, index_le e i]

private theorem card_kDyckPath {n k : ℕ} (hn : 1 ≤ n) :
    descendingNaplesCount n k = (Finset.univ.filter (IsKDyckPath n k)).card := by
  change (parkingSet n k).card = _
  apply Finset.card_bij (fun α hα => word (encode (mem_parkingSet.mp hα)))
  · intro α hα
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, word_encode (mem_parkingSet.mp hα)⟩
  · intro α hα β hβ heq
    have he := congrArg decode (word_injective heq)
    simpa only [decode_encode] using he
  · intro p hp
    obtain ⟨e, rfl⟩ := exists_word (Finset.mem_filter.mp hp).2
    have hg := good_decode hn e (Finset.mem_filter.mp hp).2
    exact ⟨decode e, mem_parkingSet.mpr hg, congrArg word (encode_decode e _)⟩

private abbrev DecreasingParking (n : ℕ) :=
  {f : Fin n → Fin n // IsParkingFunction n f ∧ Antitone f}

private lemma good_zero_iff_parking {n : ℕ} (f : Fin n → Fin n) (hf : Antitone f) :
    Good 0 (fun i => (f i).val + 1) ↔ IsParkingFunction n f := by
  rw [IsParkingFunction, IsPartialParkingFunction]
  constructor
  · intro hg j
    have hsub : Finset.univ.filter (fun i => j ≤ f i) ⊆ Finset.Iic j.rev := by
      intro i hi
      have hji := Fin.le_def.mp (Finset.mem_filter.mp hi).2
      have hb := hg.bound i
      have hj := j.isLt
      exact Finset.mem_Iic.mpr (Fin.le_def.mpr (by rw [Fin.val_rev]; omega))
    refine (Finset.card_le_card hsub).trans_eq ?_
    rw [Fin.card_Iic, Fin.val_rev]
    have := j.isLt
    omega
  · intro hp
    refine ⟨fun i => ⟨by omega, by have := (f i).isLt; omega⟩,
      fun _ _ h => Nat.succ_le_succ (Fin.le_def.mp (hf h)), ?_⟩
    intro i
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun t => f i ≤ f t) := by
      intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf (Finset.mem_Iic.mp ht)⟩
    have h := (Finset.card_le_card hsub).trans (hp (f i))
    rw [Fin.card_Iic] at h
    omega

private def classicalParkingPath {n : ℕ} (f : DecreasingParking n) :
    {p : Fin (2 * n) → Bool // IsKDyckPath n 0 p} := by
  have hg := (good_zero_iff_parking f.1 f.2.2).mpr f.2.1
  exact ⟨word (encode hg), word_encode hg⟩

private noncomputable def classicalParkingPathEquiv {n : ℕ} (hn : 1 ≤ n) :
    DecreasingParking n ≃ {p : Fin (2 * n) → Bool // IsKDyckPath n 0 p} := by
  refine Equiv.ofBijective classicalParkingPath ⟨?_, ?_⟩
  · intro f g h
    have hw := congrArg Subtype.val h
    change word (encode ((good_zero_iff_parking f.1 f.2.2).mpr f.2.1)) =
      word (encode ((good_zero_iff_parking g.1 g.2.2).mpr g.2.1)) at hw
    have hd := congrArg decode (word_injective hw)
    rw [decode_encode, decode_encode] at hd
    exact Subtype.ext (funext fun i => Fin.ext (by have := congrFun hd i; omega))
  · rintro ⟨p, hp⟩
    obtain ⟨e, rfl⟩ := exists_word hp
    have hg := good_decode hn e hp
    let f (i : Fin n) : Fin n := ⟨downs e i.rev, Nat.lt_of_succ_le (hg.valid i).2⟩
    have hdec : (fun i => (f i).val + 1) = decode e := rfl
    have hgood : Good 0 (fun i => (f i).val + 1) := hdec ▸ hg
    have ha : Antitone f := fun _ _ h => by
      have hh := hgood.anti h
      exact Fin.le_def.mpr (Nat.succ_le_succ_iff.mp hh)
    refine ⟨⟨f, (good_zero_iff_parking f ha).mp hgood, ha⟩, Subtype.ext ?_⟩
    have he : encode hgood = e := encode_decode e hg
    exact congrArg word he

private lemma word_column_iff {n : ℕ} (e : Fin n ↪o Fin (2 * n)) (j : ℕ) :
    (∃ t : Fin (2 * n), word e t = true ∧
      (t.val : ℤ) - latticeHeight (word e) t.val = 2 * (j : ℤ)) ↔ ∃ i, downs e i = j := by
  have hcol (i : Fin n) : (e i).val - latticeHeight (word e) (e i).val =
      2 * (downs e i : ℤ) := by
    rw [height_word e (e i).isLt.le, before_up, Fin.card_Iio]
    have := index_le e i
    unfold downs
    omega
  constructor
  · rintro ⟨t, ht, hj⟩
    obtain ⟨i, rfl⟩ := of_decide_eq_true ht
    rw [hcol] at hj
    exact ⟨i, by omega⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e i, by simp [word], hcol i⟩

private lemma classicalParkingPath_column_iff {n : ℕ} (f : DecreasingParking n) (j : Fin n) :
    (∃ t : Fin (2 * n), (classicalParkingPath f).1 t = true ∧
      (t.val : ℤ) - latticeHeight (classicalParkingPath f).1 t.val = 2 * (j.val : ℤ)) ↔
      ∃ i, f.1 i = j := by
  let hg := (good_zero_iff_parking f.1 f.2.2).mpr f.2.1
  change (∃ t : Fin (2 * n), word (encode hg) t = true ∧
      (t.val : ℤ) - latticeHeight (word (encode hg)) t.val = 2 * (j.val : ℤ)) ↔ _
  rw [word_column_iff]
  have hd (i : Fin n) : downs (encode hg) i = (f.1 i.rev).val := by
    change i.val + ((f.1 i.rev).val + 1 - 1) - i.val = (f.1 i.rev).val
    omega
  simp only [hd]
  exact ⟨fun ⟨i, hi⟩ => ⟨i.rev, Fin.ext hi⟩, fun ⟨i, hi⟩ => ⟨i.rev, by simp [hi]⟩⟩

end descendingNaplesCount_eq_card_kDyckPath

open descendingNaplesCount_eq_card_kDyckPath in
/-- **Decreasing parking functions with a prescribed preferred spot and Dyck paths.** For
`j : Fin n`, the weakly decreasing parking functions of length `n` that contain preference `j`
correspond to paths of `2 * n` steps that stay nonnegative, end at height zero, end with a Down
step, and contain an Up step preceded by exactly `j.val` Down steps. If a step is at index `t`
with starting height `h`, the number of earlier Down steps is `(t - h) / 2`.

Source: Steve Butler et al., *Lucky Cars and Lucky Spots in Parking Functions*,
Journal of Integer Sequences 29 (2026), Article 26.1.1, Section 4. -/
public noncomputable def decreasingParkingPreferenceEquivPath {n : ℕ} (j : Fin n) :
    {f : {f : Fin n → Fin n // IsParkingFunction n f ∧ Antitone f} // ∃ i, f.1 i = j} ≃
      {p : {p : Fin (2 * n) → Bool // IsKDyckPath n 0 p} //
        ∃ t : Fin (2 * n), p.1 t = true ∧
          (t.val : ℤ) - latticeHeight p.1 t.val = 2 * (j.val : ℤ)} :=
  (classicalParkingPathEquiv (Nat.one_le_of_lt j.isLt)).subtypeEquiv fun f =>
    (classicalParkingPath_column_iff f j).symm

set_option linter.unusedVariables false in
open descendingNaplesCount_eq_card_kDyckPath in
/-- **Descending $k$-Naples parking functions and $k$-Dyck paths.** For all natural numbers
$n \ge 1$ and $k \ge 1$, the number of weakly decreasing $k$-Naples parking functions of length
$n$ equals the number of $k$-Dyck paths of length $n$: sequences of $2n$ Up and Down steps that
end at height $0$, never go below height $-k$, and end with a Down step.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 2 (citing Christensen et al., Theorem 1.3). -/
public theorem descendingNaplesCount_eq_card_kDyckPath {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) :
    descendingNaplesCount n k = (Finset.univ.filter (IsKDyckPath n k)).card := by
  exact card_kDyckPath hn

namespace descendingNaplesCount_eq_choose

open descendingNaplesCount_eq_card_kDyckPath

private def boundedWalks (m u k : ℕ) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun p => (upSteps p).card = u ∧ ∀ j ≤ m, -(k : ℤ) ≤ latticeHeight p j

private theorem mem_boundedWalks {m u k : ℕ} {p : Fin m → Bool} :
    p ∈ boundedWalks m u k ↔ (upSteps p).card = u ∧ ∀ j ≤ m, -(k : ℤ) ≤ latticeHeight p j := by
  simp [boundedWalks]

private theorem height_snoc {m : ℕ} (p : Fin m → Bool) (b : Bool) (j : ℕ) :
    latticeHeight (Fin.snoc p b) j = latticeHeight p j +
      (if m < j then (if b then 1 else -1) else 0) := by
  unfold latticeHeight
  rw [Fin.sum_univ_castSucc]
  simp

private theorem height_past_end {m : ℕ} (p : Fin m → Bool) :
    latticeHeight p (m + 1) = latticeHeight p m := by
  simp [latticeHeight, fun i : Fin m => i.isLt, fun i : Fin m => Nat.lt_succ_of_lt i.isLt]

private theorem height_end {m : ℕ} (p : Fin m → Bool) :
    latticeHeight p m = 2 * ((upSteps p).card : ℤ) - m := by
  rw [height_eq p le_rfl, Finset.filter_true_of_mem (fun i _ => i.isLt)]

private theorem upSteps_snoc_card {m : ℕ} (p : Fin m → Bool) (b : Bool) :
    (upSteps (Fin.snoc p b)).card = (upSteps p).card + b.toNat := by
  have h := height_end (Fin.snoc p b)
  rw [height_snoc, height_past_end, height_end p, ite_eq_left (Nat.lt_succ_self m)] at h
  cases b <;> simp at h ⊢ <;> omega

private theorem mem_boundedWalks_snoc {m u k : ℕ} (p : Fin m → Bool) (b : Bool)
    (h : m + 1 ≤ 2 * (u + b.toNat) + k) :
    Fin.snoc p b ∈ boundedWalks (m + 1) (u + b.toNat) k ↔ p ∈ boundedWalks m u k := by
  simp only [mem_boundedWalks, upSteps_snoc_card, Nat.add_right_cancel_iff]
  refine and_congr_right fun hu => ⟨?_, ?_⟩
  · intro ht j hj
    simpa [height_snoc, Nat.not_lt.mpr hj] using ht j (by omega)
  · intro ht j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · simpa [height_snoc, Nat.not_lt.mpr (Nat.le_of_lt_succ hj)] using
        ht j (Nat.le_of_lt_succ hj)
    · rw [height_eq _ le_rfl, Finset.filter_true_of_mem (fun i _ => i.isLt), upSteps_snoc_card, hu]
      omega

private theorem card_boundedWalks_last {m u k : ℕ} (b : Bool)
    (h : m + 1 ≤ 2 * (u + b.toNat) + k) :
    ((boundedWalks (m + 1) (u + b.toNat) k).filter fun p => p (Fin.last m) = b).card =
      (boundedWalks m u k).card := by
  symm
  apply Finset.card_bij (fun (p : Fin m → Bool) _ => @Fin.snoc m (fun _ => Bool) p b)
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(mem_boundedWalks_snoc p b h).mpr hp, Fin.snoc_last ..⟩
  · intro p _ q _ hpq
    exact @Fin.snoc_left_injective m (fun _ => Bool) b p q hpq
  · intro q hq
    obtain ⟨hwalk, hlast⟩ := Finset.mem_filter.mp hq
    have he : Fin.snoc (Fin.init q) b = q := by rw [← hlast, Fin.snoc_init_self]
    refine ⟨Fin.init q, (mem_boundedWalks_snoc (Fin.init q) b h).mp ?_, he⟩
    rwa [he]

private theorem card_boundedWalks_step {m u k : ℕ} (h : m + 1 ≤ 2 * (u + 1) + k) :
    (boundedWalks (m + 1) (u + 1) k).card =
      (boundedWalks m u k).card + (boundedWalks m (u + 1) k).card := by
  have h₁ := card_boundedWalks_last (m := m) (u := u) (k := k) true h
  have h₂ := card_boundedWalks_last (m := m) (u := u + 1) (k := k) false h
  change ((boundedWalks (m + 1) (u + 1) k).filter fun p => p (Fin.last m) = true).card = _ at h₁
  change ((boundedWalks (m + 1) (u + 1) k).filter fun p => p (Fin.last m) = false).card = _ at h₂
  rw [← h₁, ← h₂, ← Finset.card_filter_add_card_filter_not (p := fun p => p (Fin.last m) = true)]
  simp only [Bool.not_eq_true]

private theorem card_boundedWalks_empty {m u k : ℕ} (h : 2 * u + k < m) :
    (boundedWalks m u k).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hu, hl⟩ := mem_boundedWalks.mp hp
  have he := hl m le_rfl
  rw [height_eq p le_rfl, Finset.filter_true_of_mem (fun i _ => i.isLt), hu] at he
  omega

private theorem card_boundedWalks_all_up (m k : ℕ) : (boundedWalks m m k).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨fun _ => true, Finset.ext fun p => ?_⟩
  rw [mem_boundedWalks, Finset.mem_singleton]
  constructor
  · intro hp
    have he : upSteps p = Finset.univ :=
      Finset.eq_univ_of_card _ (hp.1.trans (Fintype.card_fin m).symm)
    funext i
    simpa [upSteps] using (show i ∈ upSteps p by simp [he])
  · rintro rfl
    refine ⟨by simp [upSteps], ?_⟩
    intro j _
    have h : 0 ≤ latticeHeight (fun _ : Fin m => true) j := by
      exact Finset.sum_nonneg fun i _ => by split <;> simp
    omega

private theorem card_boundedWalks_all_down {m k : ℕ} (h : m ≤ k) :
    (boundedWalks m 0 k).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨fun _ => false, Finset.ext fun p => ?_⟩
  rw [mem_boundedWalks, Finset.mem_singleton]
  constructor
  · intro hp
    have he := Finset.card_eq_zero.mp hp.1
    funext i
    simpa [upSteps] using (show i ∉ upSteps p by simp [he])
  · rintro rfl
    refine ⟨by simp [upSteps], ?_⟩
    intro j hj
    rw [height_eq _ hj]
    simp [upSteps]
    omega

/-- The ballot count, in additive form. The reflected binomial term satisfies the
same last-step recurrence as the total. At the boundary one unit below the floor,
there are no walks and the two binomial coefficients agree by symmetry. -/
private theorem card_boundedWalks_add_choose (u d k : ℕ) (h : d ≤ u + k + 1) :
    (boundedWalks (u + d) u k).card + Nat.choose (u + d) (u + k + 1) =
      Nat.choose (u + d) u := by
  induction hs : u + d using Nat.strong_induction_on generalizing u d with
  | ind m ih =>
    subst m
    by_cases hout : u + k < d
    · have hd : u + k + 1 = d := by omega
      rw [card_boundedWalks_empty (by omega), Nat.zero_add, hd, ← Nat.choose_symm_add]
    cases u with
    | zero =>
      simp only [Nat.zero_add]
      rw [card_boundedWalks_all_down (by omega), Nat.choose_eq_zero_of_lt (by omega),
        Nat.add_zero, Nat.choose_zero_right]
    | succ u =>
      cases d with
      | zero => simp [card_boundedWalks_all_up,
          Nat.choose_eq_zero_of_lt (n := u + 1) (k := u + 1 + k + 1) (by omega)]
      | succ d =>
        let m' := u + 1 + d
        have hm : u + 1 + (d + 1) = m' + 1 := by omega
        have hu : u + (d + 1) = m' := by omega
        have hup := ih (u + (d + 1)) (by omega) u (d + 1) (by omega) rfl
        have hdown := ih (u + 1 + d) (by omega) (u + 1) d (by omega) rfl
        rw [hu] at hup
        change (boundedWalks m' (u + 1) k).card + Nat.choose m' (u + 1 + k + 1) =
          Nat.choose m' (u + 1) at hdown
        rw [hm, card_boundedWalks_step (by omega), Nat.choose_succ_succ',
          show u + 1 + k + 1 = (u + k + 1) + 1 by omega, Nat.choose_succ_succ']
        simp only [show u + 1 + k = u + k + 1 by omega] at hdown ⊢
        omega

private theorem card_kDyckPath_add_choose {n k : ℕ} (hn : 1 ≤ n) :
    (Finset.univ.filter (IsKDyckPath n k)).card + Nat.choose (2 * n - 1) (n + k + 1) =
      Nat.choose (2 * n - 1) n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  let m := 2 * t + 1
  change (Finset.univ.filter (IsKDyckPath (t + 1) k)).card + Nat.choose m (t + 1 + k + 1) =
    Nat.choose m (t + 1)
  have he : Finset.univ.filter (IsKDyckPath (t + 1) k) =
      (boundedWalks (m + 1) (t + 1) k).filter fun p => p (Fin.last m) = false := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_boundedWalks, IsKDyckPath]
    change (_ ∧ _ ∧ (∀ i : Fin (m + 1), i.val + 1 = m + 1 → p i = false)) ↔ _
    rw [height_eq p le_rfl, Finset.filter_true_of_mem (fun i _ => i.isLt)]
    have hbal : 2 * ((upSteps p).card : ℤ) - (2 * (t + 1) : ℕ) = 0 ↔ (upSteps p).card = t + 1 := by
      push_cast
      omega
    rw [hbal, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h => h _ rfl, ?_⟩
    intro h i hi
    rwa [show i = Fin.last m from Fin.ext (by simp; omega)]
  have hlast := card_boundedWalks_last (m := m) (u := t + 1) (k := k) false
    (by change m + 1 ≤ 2 * (t + 1) + k; dsimp [m]; omega)
  change ((boundedWalks (m + 1) (t + 1) k).filter fun p => p (Fin.last m) = false).card = _ at hlast
  rw [he, hlast]
  have hm : m = (t + 1) + t := by dsimp [m]; omega
  rw [hm]
  exact card_boundedWalks_add_choose (t + 1) t k (by omega)

private theorem strict_add_count {n k : ℕ} :
    descendingStrictNaplesCount n k + descendingNaplesCount n (k - 1) =
      descendingNaplesCount n k := by
  have hsub : parkingSet n (k - 1) ⊆ parkingSet n k := fun α hα => by
    obtain ⟨hv, ha, hb⟩ := mem_parkingSet.mp hα
    exact mem_parkingSet.mpr ⟨hv, ha, fun i => (hb i).trans (by omega)⟩
  have he : ((Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun α =>
      (∀ i j : Fin n, i ≤ j → α j ≤ α i) ∧ IsNaplesParkingFunction k α ∧
        ¬ IsNaplesParkingFunction (k - 1) α) = parkingSet n k \ parkingSet n (k - 1) := by
    ext α
    simp only [Finset.mem_sdiff, parkingSet, Finset.mem_filter]
    tauto
  unfold descendingStrictNaplesCount descendingNaplesCount
  rw [he]
  exact Finset.card_sdiff_add_card_eq_card hsub

end descendingNaplesCount_eq_choose

open descendingNaplesCount_eq_choose descendingNaplesCount_eq_card_kDyckPath in
/-- **Counting descending $k$-Naples parking functions.** For all natural numbers $n \ge 1$ and
$k \ge 1$, the number of weakly decreasing $k$-Naples parking functions of length $n$ is
$\binom{2n-1}{n} - \binom{2n-1}{n+k+1}$, and the number of weakly decreasing strictly
$k$-Naples parking functions of length $n$ (those that are $k$-Naples but not $(k-1)$-Naples)
is $\frac{k+1}{n} \binom{2n}{n+k+1}$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Theorem 7. -/
public theorem descendingNaplesCount_eq_choose {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    descendingNaplesCount n k = Nat.choose (2 * n - 1) n - Nat.choose (2 * n - 1) (n + k + 1) ∧
      (descendingStrictNaplesCount n k : ℚ) =
        ((k : ℚ) + 1) / n * Nat.choose (2 * n) (n + k + 1)
 := by
  have hcount := card_kDyckPath_add_choose (n := n) (k := k) hn
  rw [← descendingNaplesCount_eq_card_kDyckPath hn hk] at hcount
  refine ⟨by omega, ?_⟩
  have hprev := card_kDyckPath_add_choose (n := n) (k := k - 1) hn
  rw [← card_kDyckPath hn, show n + (k - 1) + 1 = n + k by omega] at hprev
  have hs : descendingStrictNaplesCount n k + Nat.choose (2 * n - 1) (n + k + 1) =
      Nat.choose (2 * n - 1) (n + k) := by
    have := strict_add_count (n := n) (k := k)
    omega
  have hm : 2 * n - 1 + 1 = 2 * n := by omega
  have hpas := Nat.choose_succ_succ' (2 * n - 1) (n + k)
  have hmul := Nat.add_one_mul_choose_eq (2 * n - 1) (n + k)
  rw [hm] at hpas hmul
  have hsQ : (descendingStrictNaplesCount n k : ℚ) + (Nat.choose (2 * n - 1) (n + k + 1) : ℚ) =
      (Nat.choose (2 * n - 1) (n + k) : ℚ) := by exact_mod_cast hs
  have hpasQ : (Nat.choose (2 * n) (n + k + 1) : ℚ) =
      (Nat.choose (2 * n - 1) (n + k) : ℚ) + (Nat.choose (2 * n - 1) (n + k + 1) : ℚ) := by
    exact_mod_cast hpas
  have hmulQ : 2 * (n : ℚ) * (Nat.choose (2 * n - 1) (n + k) : ℚ) =
      (Nat.choose (2 * n) (n + k + 1) : ℚ) * (n + k + 1) := by exact_mod_cast hmul
  rw [div_mul_eq_mul_div, eq_div_iff (show (n : ℚ) ≠ 0 by exact_mod_cast (show n ≠ 0 by omega))]
  linear_combination (n : ℚ) * hsQ + hmulQ + (n : ℚ) * hpasQ

end MetaMathlibExt
