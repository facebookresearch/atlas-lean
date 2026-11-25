/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Combinatorics.Enumerative.KNaplesParking
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Fin.Basic

/-!
# Descending Naples parking functions and bounded Dyck paths

Descending parking preferences are encoded by the positions of the Up steps. This gives
`descendingNaplesCount_eq_card_kDyckPath`, equating the two counts.
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

end descendingNaplesCount_eq_card_kDyckPath

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

end MetaMathlibExt
