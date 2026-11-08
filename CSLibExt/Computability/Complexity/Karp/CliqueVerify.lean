/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.CliqueCorrect
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.BitOps
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith

/-!
# The NP verifier for CLIQUE, INDEPENDENT-SET and VERTEX-COVER

One verifier serves the three languages of `CSLibExt.Computability.Complexity.Karp.Clique`, with
a `Mode` choosing the pair condition (`Mode.ok`). A witness `w` chooses the vertices `i < n` with
`w[i] = true`; `kgCheck m x w` accepts iff `x` decodes to `(k, n, bits)` with one bit per pair,
`w` has at least `n` bits, exactly `k` of the first `n` are set, and every pair `{i, j}` meets the
condition.

* Pure part: `cliqueDec_iff`, `indSetDec_iff`, `vertexCoverDec_iff` characterize each language by
  `kgCheck` with witnesses no longer than the input (the characteristic vector of the vertex set,
  of length `n`), through Mathlib's `IsNClique`, `IsNIndepSet` and `IsVertexCover` on `toGraph`.
* Machine: `prog m`, a `TM2` component on six stacks over the alphabet `Sym` (bits as `Sym.bit`).
  It reads `k` and `n` in unary off `X` onto counters (`readU`), loads the first `n` witness bits
  onto `V` with bit `n - 1` on top, counting set bits against `k` (`loadS`), and then walks the
  rows: row `i` pops the vertices `n - 1, …, i + 1` off `V` onto `T`, pairing each with the next
  pair bit of `X` (the order of `pairs n`), then pops `i` itself and decides the row (`walkS`,
  `walkZ`); `back` restores `V` without `i`. With `V` empty, `X` must be empty too. `run`: it
  reaches `yes` iff `kgCheck m x w`, within `8 (|x| + |w| + 1)³` steps (quadratic in fact).
* The bridge between the two is `rowsOk`, the row-by-row form of the pair check
  (`rowsOk_eq`, `kgCheck_eq_rowsOk`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp.KGVerify

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin
open Cslib.Complexity.SatVerifier (Sym)

/-! ### The verifier as a pure function -/

/-- The three problems sharing the verifier. -/
inductive Mode | clique | indep | cover
  deriving DecidableEq

/-- `Mode` is finite. -/
instance Mode.instFintypeEnumFix : Fintype Mode where
  elems := ⟨↑[Mode.clique, .indep, .cover], by decide⟩
  complete := fun x => by cases x <;> decide

/-- The pairwise condition: bit of `{i, j}`, then whether `i` and `j` are chosen. -/
def Mode.ok : Mode → Bool → Bool → Bool → Bool
  | .clique, b, si, sj => !(si && sj) || b
  | .indep, b, si, sj => !(si && sj) || !b
  | .cover, b, si, sj => !b || si || sj

/-- The verifier: `w`'s first `n` bits choose the vertices. -/
def kgCheck (m : Mode) (x w : List Bool) : Bool :=
  match decodeKG x with
  | none => false
  | some (k, n, bits) => bits.length == (pairs n).length && n ≤ w.length &&
      (w.take n).count true == k &&
      ((pairs n).zip bits).all fun pb => m.ok pb.2 (w.getD pb.1.1 false) (w.getD pb.1.2 false)

/-- Vertex `i` alone settles every pair `{i, j}`: `i` unchosen (clique, independent set) or
chosen (cover). -/
def Mode.free : Mode → Bool → Bool
  | .cover, si => si
  | _, si => !si

/-- The pair condition when `i` does not settle it: bit `b`, whether `j` is chosen. -/
def Mode.sat : Mode → Bool → Bool → Bool
  | .clique, b, sj => !sj || b
  | .indep, b, sj => !sj || !b
  | .cover, b, sj => !b || sj

/-- The pair condition splits into the part `i` settles and the part left to `j`. -/
theorem Mode.ok_eq (m : Mode) (b si sj : Bool) : m.ok b si sj = (m.free si || m.sat b sj) := by
  cases m <;> cases b <;> cases si <;> cases sj <;> rfl

/-! ### The pair order -/

/-- Row `0` of `pairs (n + 1)`, then the pairs of `n` shifted by one. -/
theorem pairs_succ (n : ℕ) : pairs (n + 1) = (List.range n).reverse.map (fun j => (0, j + 1)) ++
    (pairs n).map fun p => (p.1 + 1, p.2 + 1) := by
  have hr : (0 :: (List.range n).map Nat.succ).reverse =
      (List.range n).reverse.map Nat.succ ++ [0] := by
    rw [List.reverse_cons, List.map_reverse]
  rw [pairs, pairs, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.map_flatMap,
    hr]
  congr 1
  · simp [List.filter_map, Function.comp_def]
  · exact List.flatMap_congr fun i _ => by simp [List.filter_map, Function.comp_def]

/-! ### The row-by-row check -/

/-- The chosen-flags of the two ends of each pair of `pairs s.length`, read off `s`. -/
def pairVals (s : List Bool) : List (Bool × Bool) :=
  (pairs s.length).map fun p => (s.getD p.1 false, s.getD p.2 false)

/-- Reading a list at every index in turn gives it back. -/
theorem map_getD_range (s : List Bool) : (List.range s.length).map (s.getD · false) = s := by
  refine List.ext_getElem (by simp) fun t h₁ h₂ => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- Row `0` of `a :: s` pairs `a` with the later vertices, last first. -/
theorem pairVals_cons (a : Bool) (s : List Bool) :
    pairVals (a :: s) = s.reverse.map (a, ·) ++ pairVals s := by
  rw [pairVals, List.length_cons, pairs_succ, List.map_append, List.map_map, List.map_map]
  congr 1
  conv_rhs => rw [← map_getD_range s]
  simp [List.map_reverse, Function.comp_def]

/-- What the machine checks, vertex by vertex: row `i` (vertex `s`, later vertices `rest`) takes
`rest.length` pair bits, met in the order of `rest.reverse`; then the rows of `rest`, and at the
end no bit may be left. -/
def rowsOk (m : Mode) : List Bool → List Bool → Bool
  | [], bs => bs.isEmpty
  | s :: rest, bs => decide (rest.length ≤ bs.length) &&
      (m.free s || (rest.reverse.zip bs).all fun p => m.sat p.2 p.1) &&
      rowsOk m rest (bs.drop rest.length)

/-- The row-by-row check is the pairwise check over `pairs`, with the bit count. -/
theorem rowsOk_eq (m : Mode) : ∀ (s bs : List Bool), rowsOk m s bs =
    (bs.length == (pairVals s).length &&
      ((pairVals s).zip bs).all fun q => m.ok q.2 q.1.1 q.1.2)
  | [], bs => by cases bs <;> simp [rowsOk, pairVals, pairs]
  | a :: s, bs => by
      rw [rowsOk, pairVals_cons, rowsOk_eq m s]
      by_cases h : s.length ≤ bs.length
      · have hz : (s.reverse.map (a, ·) ++ pairVals s).zip bs = (s.reverse.map (a, ·)).zip
            (bs.take s.length) ++ (pairVals s).zip (bs.drop s.length) := by
          rw [← List.zip_append (by simp [h]), List.take_append_drop]
        have hl : ((bs.drop s.length).length == (pairVals s).length) =
            (bs.length == (s.reverse.map (a, ·) ++ pairVals s).length) := by
          rw [Bool.eq_iff_iff]; simp; omega
        have hz' : s.reverse.zip bs = s.reverse.zip (bs.take s.length) := by
          rw [List.zip_eq_zip_take_min]
          simp [h, List.take_of_length_le (l := s.reverse) (i := s.length) (by simp)]
        rw [hz, List.all_append, ← hl, hz', List.zip_map_left, List.all_map]
        simp only [Function.comp_def, Prod.map, id, Mode.ok_eq, ← List.or_all_distrib_left]
        simp [h, Bool.and_left_comm]
      · have hl : (bs.length == (s.reverse.map (a, ·) ++ pairVals s).length) = false := by
          simp; omega
        rw [hl]
        simp [h]

/-- On a decodable instance with the right count, the verifier is the row-by-row check. -/
theorem kgCheck_eq_rowsOk {m : Mode} {x w : List Bool} {k n : ℕ} {bits : List Bool}
    (hx : decodeKG x = some (k, n, bits)) (hn : n ≤ w.length) (hk : (w.take n).count true = k) :
    kgCheck m x w = rowsOk m (w.take n) bits := by
  have hv : pairVals (w.take n) = (pairs n).map fun p => (w.getD p.1 false, w.getD p.2 false) := by
    rw [pairVals, List.length_take_of_le hn]
    refine List.map_congr_left fun p hp => ?_
    obtain ⟨h1, h2⟩ := mem_pairs.1 hp
    simp [List.getD_eq_getElem?_getD, show p.1 < n by omega, h2]
  rw [kgCheck, hx, rowsOk_eq, hv, List.length_map, List.zip_map_left, List.all_map]
  simp [hn, hk, Function.comp_def]

/-! ### Bridge to the graph languages -/

/-- With distinct keys, `lookup` finds the value paired with a key. -/
theorem lookup_of_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, (l.map Prod.fst).Nodup → (a, b) ∈ l →
      l.lookup a = some b
  | (a', b') :: l, a, b, hnd, hmem => by
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hmem with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        simp
      · have hm : a ∈ l.map Prod.fst := by simpa using List.mem_map_of_mem (f := Prod.fst) h
        have hne : (a == a') = false := beq_eq_false_iff_ne.2 fun e => hnd.1 (by simpa [e] using hm)
        simp [List.lookup_cons, hne, lookup_of_mem hnd.2 h]

/-- With one bit per pair, a check over `(pairs n).zip bits` is a check of `adjBits` on every
pair `i < j < n`. -/
theorem all_zip_pairs {n : ℕ} {bits : List Bool} (h : bits.length = (pairs n).length)
    (P : ℕ × ℕ → Bool → Bool) :
    ((pairs n).zip bits).all (fun pb => P pb.1 pb.2) = true ↔
      ∀ i j, i < j → j < n → P (i, j) (adjBits n bits i j) = true := by
  have hkeys : ((pairs n).zip bits).map Prod.fst = pairs n := List.map_fst_zip (by omega)
  have hlk : ∀ p b, (p, b) ∈ (pairs n).zip bits → adjBits n bits p.1 p.2 = b := by
    intro p b hpb
    obtain ⟨h1, -⟩ := mem_pairs.1 (List.of_mem_zip hpb).1
    rw [adjBits, min_eq_left h1.le, max_eq_right h1.le,
      lookup_of_mem (by rw [hkeys]; exact Karp.pairs_nodup n) hpb]
    rfl
  simp only [List.all_eq_true]
  constructor
  · intro hall i j hij hjn
    have hmem : (i, j) ∈ ((pairs n).zip bits).map Prod.fst := by
      rw [hkeys]; exact mem_pairs.2 ⟨hij, hjn⟩
    obtain ⟨⟨p, b⟩, hpb, hp⟩ := List.mem_map.1 hmem
    obtain rfl : p = (i, j) := hp
    have hb : adjBits n bits i j = b := hlk _ b hpb
    rw [hb]
    exact hall _ hpb
  · rintro hall ⟨p, b⟩ hpb
    obtain ⟨h1, h2⟩ := mem_pairs.1 (List.of_mem_zip hpb).1
    have := hall p.1 p.2 h1 h2
    rwa [hlk p b hpb] at this

/-- The verifier accepts iff `x` is an instance with one bit per pair, `w` has at least `n` bits,
`k` of the first `n` are set, and every pair meets the mode's condition. -/
theorem kgCheck_iff (m : Mode) (x w : List Bool) : kgCheck m x w = true ↔
    ∃ k n bits, x = encodeKG k n bits ∧ bits.length = (pairs n).length ∧ n ≤ w.length ∧
      (w.take n).count true = k ∧ ∀ i j, i < j → j < n →
        m.ok (adjBits n bits i j) (w.getD i false) (w.getD j false) = true := by
  constructor
  · intro h
    unfold kgCheck at h
    split at h
    · exact absurd h (by simp)
    · rename_i k n bits hx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hl, hn⟩, hk⟩, hall⟩ := h
      exact ⟨k, n, bits, decodeKG_eq_some_iff.1 hx, hl, hn, hk,
        (all_zip_pairs hl fun p b => m.ok b (w.getD p.1 false) (w.getD p.2 false)).1 hall⟩
  · rintro ⟨k, n, bits, rfl, hl, hn, hk, hall⟩
    rw [kgCheck, decodeKG_eq_some_iff.2 rfl]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨⟨hl, hn⟩, hk⟩,
      (all_zip_pairs hl fun p b => m.ok b (w.getD p.1 false) (w.getD p.2 false)).2 hall⟩

/-- The set bits of `List.ofFn f` count the indices where `f` holds. -/
theorem count_ofFn : ∀ {n : ℕ} (f : Fin n → Bool),
    (List.ofFn f).count true = (Finset.univ.filter fun i => f i = true).card
  | 0, f => by simp
  | n + 1, f => by
      rw [List.ofFn_succ, List.count_cons, count_ofFn, Finset.card_filter, Finset.card_filter,
        Fin.sum_univ_succ]
      cases f 0 <;> simp [add_comm]

/-- The first `n` bits of `w`, as a function on `Fin n`. -/
theorem take_eq_ofFn {n : ℕ} {w : List Bool} (hn : n ≤ w.length) :
    w.take n = List.ofFn fun i : Fin n => w.getD i false := by
  refine List.ext_getElem (by simp [hn]) fun t h₁ h₂ => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < w.length by
    simp at h₁; omega)]

/-- A vertex set meets the mode's condition on every pair `i < j`. -/
def SetOk (m : Mode) (n : ℕ) (bits : List Bool) (s : Finset (Fin n)) : Prop :=
  ∀ i j : Fin n, i < j → m.ok (adjBits n bits i j) (decide (i ∈ s)) (decide (j ∈ s)) = true

/-- An accepted witness chooses a vertex set of size `k` meeting the mode's condition. -/
theorem exists_setOk {m : Mode} {x w : List Bool} (h : kgCheck m x w = true) :
    ∃ k n bits, x = encodeKG k n bits ∧ bits.length = (pairs n).length ∧
      ∃ s : Finset (Fin n), s.card = k ∧ SetOk m n bits s := by
  obtain ⟨k, n, bits, rfl, hl, hn, hk, hall⟩ := (kgCheck_iff m x w).1 h
  refine ⟨k, n, bits, rfl, hl, Finset.univ.filter fun i : Fin n => w.getD i false = true, ?_,
    fun i j hij => ?_⟩
  · rw [← hk, take_eq_ofFn hn, count_ofFn]
  · have e : ∀ t : Fin n, decide (t ∈ Finset.univ.filter fun i : Fin n => w.getD i false = true) =
        w.getD t false := fun t => by simp
    rw [e, e]
    exact hall i j hij j.isLt

/-- The characteristic vector of a vertex set meeting the mode's condition is accepted. -/
theorem kgCheck_ofFn {m : Mode} {k n : ℕ} {bits : List Bool} (hl : bits.length = (pairs n).length)
    {s : Finset (Fin n)} (hs : s.card = k) (hok : SetOk m n bits s) :
    kgCheck m (encodeKG k n bits) (List.ofFn fun i : Fin n => decide (i ∈ s)) = true := by
  have hg : ∀ i (hi : i < n),
      (List.ofFn fun i : Fin n => decide (i ∈ s)).getD i false = decide (⟨i, hi⟩ ∈ s) := by
    intro i hi; simp [List.getD_eq_getElem?_getD, hi]
  refine (kgCheck_iff m _ _).2 ⟨k, n, bits, rfl, hl, by simp, ?_, fun i j hij hjn => ?_⟩
  · rw [List.take_of_length_le (by simp), count_ofFn, ← hs]
    congr 1; ext i; simp
  · rw [hg i (by omega), hg j hjn]
    exact hok ⟨i, by omega⟩ ⟨j, hjn⟩ hij

/-- A language `kgDec P` whose property is "some vertex set of size `k` meets the mode's
condition" is verified by `kgCheck m` with witnesses no longer than the input. -/
theorem kgDec_iff_exists (m : Mode) (P : ∀ n : ℕ, ℕ → SimpleGraph (Fin n) → Prop)
    (hP : ∀ n k bits, bits.length = (pairs n).length →
      (P n k (toGraph n bits) ↔ ∃ s : Finset (Fin n), s.card = k ∧ SetOk m n bits s))
    (x : List Bool) : kgDec P x = true ↔ ∃ w, w.length ≤ x.length ∧ kgCheck m x w = true := by
  simp only [kgDec, decide_eq_true_eq]
  constructor
  · rintro ⟨k, n, bits, rfl, hl, hPk⟩
    obtain ⟨s, hs, hok⟩ := (hP n k bits hl).1 hPk
    exact ⟨_, by simp [encodeKG]; omega, kgCheck_ofFn hl hs hok⟩
  · rintro ⟨w, -, hw⟩
    obtain ⟨k, n, bits, rfl, hl, s, hs, hok⟩ := exists_setOk hw
    exact ⟨k, n, bits, rfl, hl, (hP n k bits hl).2 ⟨s, hs, hok⟩⟩

/-- For a symmetric relation, the distinct pairs are checked by the pairs `i < j`. -/
theorem forall_ne_iff_lt {n : ℕ} {R : Fin n → Fin n → Prop} (hR : ∀ i j, R i j → R j i) :
    (∀ i j, i ≠ j → R i j) ↔ ∀ i j, i < j → R i j :=
  ⟨fun h i j hij => h i j hij.ne, fun h i j hij =>
    (lt_or_gt_of_ne hij).elim (h i j) fun hji => hR _ _ (h j i hji)⟩

/-- A `k`-clique is a `k`-set meeting the clique condition on every pair. -/
theorem clique_iff (n k : ℕ) (bits : List Bool) : (∃ s, (toGraph n bits).IsNClique k s) ↔
    ∃ s : Finset (Fin n), s.card = k ∧ SetOk .clique n bits s := by
  refine exists_congr fun s => ?_
  rw [SimpleGraph.isNClique_iff, and_comm]
  refine and_congr_right fun _ => ?_
  have h₁ : (toGraph n bits).IsClique (s : Set (Fin n)) ↔
      ∀ i j : Fin n, i ≠ j → i ∈ s → j ∈ s → adjBits n bits i j = true := by
    simp only [SimpleGraph.IsClique, Set.Pairwise, Finset.mem_coe, toGraph]
    exact ⟨fun h i j hij hi hj => (h hi hj hij).2, fun h i hi j hj hij => ⟨hij, h i j hij hi hj⟩⟩
  rw [h₁, forall_ne_iff_lt fun i j h hj hi => by rw [adjBits_comm]; exact h hi hj]
  refine forall₂_congr fun i j => forall_congr' fun _ => ?_
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [Mode.ok, hi, hj]

/-- A `k`-independent set is a `k`-set meeting the independence condition on every pair. -/
theorem indep_iff (n k : ℕ) (bits : List Bool) : (∃ s, (toGraph n bits).IsNIndepSet k s) ↔
    ∃ s : Finset (Fin n), s.card = k ∧ SetOk .indep n bits s := by
  refine exists_congr fun s => ?_
  rw [SimpleGraph.isNIndepSet_iff, and_comm]
  refine and_congr_right fun _ => ?_
  have h₁ : (toGraph n bits).IsIndepSet (s : Set (Fin n)) ↔
      ∀ i j : Fin n, i ≠ j → i ∈ s → j ∈ s → adjBits n bits i j = false := by
    simp only [SimpleGraph.IsIndepSet, Set.Pairwise, Finset.mem_coe, toGraph, not_and,
      Bool.not_eq_true]
    exact ⟨fun h i j hij hi hj => h hi hj hij hij, fun h i hi j hj hij _ => h i j hij hi hj⟩
  rw [h₁, forall_ne_iff_lt fun i j h hj hi => by rw [adjBits_comm]; exact h hi hj]
  refine forall₂_congr fun i j => forall_congr' fun _ => ?_
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [Mode.ok, hi, hj]

/-- A `k`-vertex cover is a `k`-set meeting the cover condition on every pair. -/
theorem cover_iff (n k : ℕ) (bits : List Bool) :
    (∃ s : Finset (Fin n), s.card = k ∧ (toGraph n bits).IsVertexCover (s : Set (Fin n))) ↔
      ∃ s : Finset (Fin n), s.card = k ∧ SetOk .cover n bits s := by
  refine exists_congr fun s => and_congr_right fun _ => ?_
  have h₁ : (toGraph n bits).IsVertexCover (s : Set (Fin n)) ↔
      ∀ i j : Fin n, i ≠ j → adjBits n bits i j = true → i ∈ s ∨ j ∈ s := by
    simp only [SimpleGraph.IsVertexCover, Finset.mem_coe, toGraph]
    exact ⟨fun h i j hij hb => h ⟨hij, hb⟩, fun h i j hij => h i j hij.1 hij.2⟩
  rw [h₁, forall_ne_iff_lt fun i j h hb => by rw [adjBits_comm] at hb; exact (h hb).symm]
  refine forall₂_congr fun i j => forall_congr' fun _ => ?_
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [Mode.ok, hi, hj]

/-- **CLIQUE is verified by `kgCheck .clique`**, with witnesses no longer than the input. -/
theorem cliqueDec_iff (x : List Bool) :
    cliqueDec x = true ↔ ∃ w, w.length ≤ x.length ∧ kgCheck .clique x w = true :=
  kgDec_iff_exists .clique _ (fun n k bits _ => clique_iff n k bits) x

/-- **INDEPENDENT-SET is verified by `kgCheck .indep`**, with witnesses no longer than the
input. -/
theorem indSetDec_iff (x : List Bool) :
    indSetDec x = true ↔ ∃ w, w.length ≤ x.length ∧ kgCheck .indep x w = true :=
  kgDec_iff_exists .indep _ (fun n k bits _ => indep_iff n k bits) x

/-- **VERTEX-COVER is verified by `kgCheck .cover`**, with witnesses no longer than the
input. -/
theorem vertexCoverDec_iff (x : List Bool) :
    vertexCoverDec x = true ↔ ∃ w, w.length ≤ x.length ∧ kgCheck .cover x w = true :=
  kgDec_iff_exists .cover _ (fun n k bits _ => cover_iff n k bits) x

/-! ### The machine -/

/-- Stacks: the input `X` and the witness `W`, the counters `C` (for `k`) and `N` (for `n`), the
vertex stack `V` and its scratch stack `T`. -/
inductive K | X | W | C | N | V | T
  deriving DecidableEq

/-- `K` is finite. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .W, .C, .N, .V, .T], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Labels: read `k`, read `n`, load the witness, walk a row (with the conjunction `c` of its
pair conditions so far), put the row back, accept, reject. -/
inductive Lab | rdK | rdN | load | walk (c : Bool) | back | yes | no
  deriving DecidableEq

/-- `Lab` is finite. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.rdK, .rdN, .load, .walk false, .walk true, .back, .yes, .no], by decide⟩
  complete := by rintro (_ | _ | _ | ⟨_ | _⟩ | _ | _ | _) <;> decide

/-- Statements of the verifier. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Sym) Lab Bool

/-- Read a unary number off `X` onto the counter `c`: a `true` adds a unit, the `false`
terminator moves on to `next`, an exhausted `X` rejects. -/
def readU (c : K) (self next : Lab) : Stmt :=
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop .X (fun _ o => bitOf Sym.bit? o) <| .branch id
      (.push c (fun _ => .bit true) (.goto fun _ => self)) (.goto fun _ => next)

/-- Load one witness bit per unit of `N` from `W` onto `V` (bit `n - 1` ends on top), taking a
unit off `C` per set bit. Rejects if `W` runs out or more than `k` bits are set; at the end `C`
must be empty. -/
def loadS : Stmt :=
  .pop .N (fun _ o => o.isSome) <| .branch id
    (.peek .W (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
      .pop .W (fun _ o => bitOf Sym.bit? o) <| .branch id
        (.push .V (fun _ => .bit true) <| .pop .C (fun _ o => o.isSome) <| .branch id
          (.goto fun _ => .load) (.goto fun _ => .no))
        (.push .V (fun _ => .bit false) <| .goto fun _ => .load))
    (.peek .C (fun _ o => o.isNone) <| .branch id (.goto fun _ => .walk true)
      (.goto fun _ => .no))

/-- The rest of a walk step, after popping the vertex bit `z`. If `V` is now empty, `z` is the
row's own vertex `i`: the row passes iff `i` settles it or `c` holds. Otherwise `z` is a later
vertex `j`: park it on `T` and fold the next pair bit of `X` into `c` (reject if `X` is out). -/
def walkZ (m : Mode) (c z : Bool) : Stmt :=
  .peek .V (fun _ o => o.isNone) <| .branch id
    (.goto fun _ => if m.free z || c then .back else .no) <|
  .push .T (fun _ => .bit z) <|
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
  .pop .X (fun _ o => bitOf Sym.bit? o) <| .branch id
    (.goto fun _ => .walk (c && m.sat true z)) (.goto fun _ => .walk (c && m.sat false z))

/-- A walk step: with `V` empty every row is done, and the verifier accepts iff no pair bit is
left on `X`; otherwise pop the top vertex bit and go on with `walkZ`. -/
def walkS (m : Mode) (c : Bool) : Stmt :=
  .peek .V (fun _ o => o.isNone) <| .branch id
    (.peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .yes) (.goto fun _ => .no)) <|
  .pop .V (fun _ o => bitOf Sym.bit? o) <| .branch id (walkZ m c true) (walkZ m c false)

/-- The verifier for mode `m`: parse `k` and `n`, load the witness, walk the rows. -/
def prog (m : Mode) : Lab → TM2.Stmt (fun _ : K => Sym) Lab Bool
  | .rdK => readU .C .rdK .rdN
  | .rdN => readU .N .rdN .load
  | .load => loadS
  | .walk c => walkS m c
  | .back => moveB .T .V Sym.bit? Sym.bit .back (.walk true)
  | .yes => .halt
  | .no => .halt

/-- The start label. -/
def start : Lab := .rdK

/-! ### Runs of the phases -/

/-- A step whose label is known: some state and stacks follow. -/
theorem run_one {M : Lab → Stmt} {l l' : Lab} {v : Bool} {S : ∀ _ : K, List Sym}
    (h : (TM2.stepAux (M l) v S).l = some l') :
    ∃ v' S', Run M 1 ⟨some l, v, S⟩ ⟨some l', v', S'⟩ :=
  ⟨_, _, Run.single (by rw [← h])⟩

section Phases

variable (m : Mode)

/-- `readU` on `k` in unary: `k + 1` steps to `next`, with `k` more units on the counter and
the rest of `X` left. -/
theorem readU_some {c : K} {self next : Lab} (hp : prog m self = readU c self next)
    (hc : c ≠ .X) : ∀ (k j : ℕ) (r : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      St .X = (List.replicate k true ++ false :: r).map Sym.bit → St c = cnt (Sym.bit true) j →
      ∃ v' S', Run (prog m) (k + 1) ⟨some self, v, St⟩ ⟨some next, v', S'⟩ ∧
        S' .X = r.map Sym.bit ∧ S' c = cnt (Sym.bit true) (k + j) ∧
        ∀ q, q ≠ .X → q ≠ c → S' q = St q := by
  intro k
  induction k with
  | zero =>
      intro j r v St hX hC
      simp only [List.replicate_zero, List.nil_append, List.map_cons] at hX
      refine ⟨false, update St .X (r.map Sym.bit), Run.single ?_, by simp, ?_,
        fun q hq _ => by simp [update_of_ne hq]⟩
      · simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?]
      · rw [update_of_ne hc, hC, zero_add]
  | succ k ih =>
      intro j r v St hX hC
      simp only [List.replicate_succ, List.cons_append, List.map_cons] at hX
      set St₁ := update (update St .X ((List.replicate k true ++ false :: r).map Sym.bit)) c
        (Sym.bit true :: St c) with hSt₁
      obtain ⟨v', S', hrun, hX', hC', hF'⟩ := ih (j + 1) r true St₁
        (by simp [hSt₁, update_of_ne hc.symm]) (by simp [hSt₁, hC, cnt_succ])
      refine ⟨v', S', Run.head ?_ hrun, hX', by rw [hC']; congr 1; omega,
        fun q h1 h2 => by rw [hF' q h1 h2, hSt₁, update_of_ne h2, update_of_ne h1]⟩
      simp [TM2.step, hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?, hSt₁, update_of_ne hc]

/-- `readU` on an unterminated unary prefix rejects. -/
theorem readU_none {c : K} {self next : Lab} (hp : prog m self = readU c self next)
    (hc : c ≠ .X) : ∀ (l : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
      readUnaryLength l = none → St .X = l.map Sym.bit →
      ∃ v' S', RunLe (prog m) (l.length + 1) ⟨some self, v, St⟩ ⟨some .no, v', S'⟩ := by
  intro l
  induction l with
  | nil =>
      intro v St _ hX
      obtain ⟨v', S', h⟩ := run_one (M := prog m) (l := self) (v := v) (S := St) (l' := .no)
        (by simp [hp, readU, TM2.stepAux, hX])
      exact ⟨v', S', h.le (by simp)⟩
  | cons b l ih =>
      intro v St hl hX
      cases b with
      | false => simp [readUnaryLength] at hl
      | true =>
          have hl' : readUnaryLength l = none := by simpa [readUnaryLength] using hl
          obtain ⟨v', S', h⟩ := ih true
            (update (update St .X (l.map Sym.bit)) c (Sym.bit true :: St c)) hl'
            (by simp [update_of_ne hc.symm])
          refine ⟨v', S', (((Run.single ?_).le le_rfl).trans h).mono (by simp; omega)⟩
          simp [hp, readU, TM2.stepAux, hX, bitOf, Sym.bit?, update_of_ne hc]

/-- The load phase: from counters `n` on `N` and `j` on `C`, the witness `w` on `W` and `acc` on
`V`, it reaches `walk true` if `w` has at least `n` bits, `j` of the first `n` set, and `no`
otherwise; on success the first `n` bits sit on `V`, last on top. -/
theorem load_run : ∀ (n : ℕ) (w acc : List Bool) (j : ℕ) (v : Bool) (St : ∀ _ : K, List Sym),
    St .N = cnt (Sym.bit true) n → St .W = w.map Sym.bit → St .C = cnt (Sym.bit true) j →
    St .V = acc.map Sym.bit →
    ∃ v' S', RunLe (prog m) (n + 1) ⟨some .load, v, St⟩
      ⟨some (if n ≤ w.length ∧ (w.take n).count true = j then .walk true else .no), v', S'⟩ ∧
      (n ≤ w.length ∧ (w.take n).count true = j →
        S' .V = ((w.take n).reverse ++ acc).map Sym.bit ∧ S' .X = St .X ∧ S' .T = St .T) := by
  intro n
  induction n with
  | zero =>
      intro w acc j v St hN hW hC hV
      cases j with
      | zero =>
          refine ⟨true, update St .N [], (Run.single ?_).le le_rfl,
            fun _ => ⟨by simp [hV], by simp, by simp⟩⟩
          simp [prog, loadS, TM2.stepAux, hN, hC]
      | succ j =>
          obtain ⟨v', S', h⟩ := run_one (M := prog m) (l := .load) (v := v) (S := St)
            (l' := .no) (by simp [prog, loadS, TM2.stepAux, hN, hC])
          exact ⟨v', S', by simpa using h.le le_rfl, fun h => by simp at h⟩
  | succ n ih =>
      intro w acc j v St hN hW hC hV
      cases w with
      | nil =>
          obtain ⟨v', S', h⟩ := run_one (M := prog m) (l := .load) (v := v) (S := St)
            (l' := .no) (by simp [prog, loadS, TM2.stepAux, hN, hW, cnt_succ])
          exact ⟨v', S', by simpa using h.le (by omega), fun h => by simp at h⟩
      | cons b w =>
          cases b with
          | true =>
              cases j with
              | zero =>
                  obtain ⟨v', S', h⟩ := run_one (M := prog m) (l := .load) (v := v) (S := St)
                    (l' := .no) (by simp [prog, loadS, TM2.stepAux, hN, hW, hC, cnt_succ, bitOf,
                      Sym.bit?])
                  exact ⟨v', S', by simpa using h.le (by omega), fun h => by simp at h⟩
              | succ j =>
                  set St₁ := update (update (update (update St .N (cnt (Sym.bit true) n)) .W
                    (w.map Sym.bit)) .V (Sym.bit true :: St .V)) .C (cnt (Sym.bit true) j)
                    with hSt₁
                  obtain ⟨v', S', hrun, hF⟩ := ih w (true :: acc) j true St₁ (by simp [hSt₁])
                    (by simp [hSt₁]) (by simp [hSt₁]) (by simp [hSt₁, hV])
                  have hstep : TM2.step (prog m) ⟨some .load, v, St⟩ =
                      some ⟨some .load, true, St₁⟩ := by
                    simp [TM2.step, prog, loadS, TM2.stepAux, hN, hW, hC, cnt_succ, bitOf,
                      Sym.bit?, hSt₁]
                  refine ⟨v', S', ?_, fun h => ?_⟩
                  · have := ((Run.head hstep (Run.zero _)).le le_rfl).trans hrun
                    simpa [List.count_cons, add_comm 1] using this.mono (by omega)
                  · obtain ⟨h1, h2, h3⟩ := hF (by simpa using h)
                    exact ⟨by simpa using h1, by simpa [hSt₁] using h2, by simpa [hSt₁] using h3⟩
          | false =>
              set St₁ := update (update (update St .N (cnt (Sym.bit true) n)) .W
                (w.map Sym.bit)) .V (Sym.bit false :: St .V) with hSt₁
              obtain ⟨v', S', hrun, hF⟩ := ih w (false :: acc) j false St₁ (by simp [hSt₁])
                (by simp [hSt₁]) (by simp [hSt₁, hC]) (by simp [hSt₁, hV])
              have hstep : TM2.step (prog m) ⟨some .load, v, St⟩ =
                  some ⟨some .load, false, St₁⟩ := by
                simp [TM2.step, prog, loadS, TM2.stepAux, hN, hW, cnt_succ, bitOf, Sym.bit?,
                  hSt₁]
              refine ⟨v', S', ?_, fun h => ?_⟩
              · have := ((Run.head hstep (Run.zero _)).le le_rfl).trans hrun
                simpa using this.mono (by omega)
              · obtain ⟨h1, h2, h3⟩ := hF (by simpa using h)
                exact ⟨by simpa using h1, by simpa [hSt₁] using h2, by simpa [hSt₁] using h3⟩

/-- The walk along one row: from `walk c` with the later vertices `zs` (as met) above the row's
own vertex `si` on `V` and the pair bits `bs` on `X`, it pairs `zs` with the first bits of `bs`,
parks `zs` on `T` and decides the row: `back` iff there are enough bits and `si` settles the row
or every pair condition holds (and `c` does). -/
theorem walkRow_run (si : Bool) : ∀ (zs : List Bool) (c : Bool) (bs : List Bool) (v : Bool)
    (St : ∀ _ : K, List Sym), St .V = (zs ++ [si]).map Sym.bit → St .X = bs.map Sym.bit →
    ∃ v' S', RunLe (prog m) (zs.length + 1) ⟨some (.walk c), v, St⟩
      ⟨some (if zs.length ≤ bs.length ∧
        (m.free si || (c && (zs.zip bs).all fun p => m.sat p.2 p.1)) = true
        then .back else .no), v', S'⟩ ∧
      (zs.length ≤ bs.length → S' .V = [] ∧ S' .T = zs.reverse.map Sym.bit ++ St .T ∧
        S' .X = (bs.drop zs.length).map Sym.bit) := by
  intro zs
  induction zs with
  | nil =>
      intro c bs v St hV hX
      refine ⟨true, update St .V [], (Run.single ?_).le le_rfl,
        fun _ => ⟨by simp, by simp, by simp [hX]⟩⟩
      cases si <;> simp [prog, walkS, walkZ, TM2.stepAux, hV, bitOf, Sym.bit?]
  | cons z zs ih =>
      intro c bs v St hV hX
      cases bs with
      | nil =>
          obtain ⟨v', S', h⟩ := run_one (M := prog m) (l := .walk c) (v := v) (S := St)
            (l' := .no) (by cases z <;> simp [prog, walkS, walkZ, TM2.stepAux, hV, hX, bitOf,
              Sym.bit?])
          exact ⟨v', S', by simpa using h.le (by omega), fun h => by simp at h⟩
      | cons b bs =>
          set St₁ := update (update (update St .V ((zs ++ [si]).map Sym.bit)) .T
            (Sym.bit z :: St .T)) .X (bs.map Sym.bit) with hSt₁
          obtain ⟨v', S', hrun, hF⟩ := ih (c && m.sat b z) bs b St₁ (by simp [hSt₁])
            (by simp [hSt₁])
          have hstep : TM2.step (prog m) ⟨some (.walk c), v, St⟩ =
              some ⟨some (.walk (c && m.sat b z)), b, St₁⟩ := by
            cases z <;> cases b <;>
              simp [TM2.step, prog, walkS, walkZ, TM2.stepAux, hV, hX, bitOf, Sym.bit?, hSt₁]
          refine ⟨v', S', ?_, fun h => ?_⟩
          · have := ((Run.head hstep (Run.zero _)).le le_rfl).trans hrun
            simpa [Bool.and_assoc] using this.mono (by simp; omega)
          · obtain ⟨h1, h2, h3⟩ := hF (by simpa using h)
            exact ⟨h1, by simp [h2, hSt₁], by simpa using h3⟩

/-- One row: the walk, then `back` restores the later vertices on `V`. -/
theorem row_run (si : Bool) (rest bs : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (hV : St .V = (rest.reverse ++ [si]).map Sym.bit) (hT : St .T = [])
    (hX : St .X = bs.map Sym.bit) :
    ∃ v' S', RunLe (prog m) (2 * rest.length + 2) ⟨some (.walk true), v, St⟩
      ⟨some (if rest.length ≤ bs.length ∧
        (m.free si || (rest.reverse.zip bs).all fun p => m.sat p.2 p.1) = true
        then .walk true else .no), v', S'⟩ ∧
      (rest.length ≤ bs.length ∧
        (m.free si || (rest.reverse.zip bs).all fun p => m.sat p.2 p.1) = true →
        S' .V = rest.reverse.map Sym.bit ∧ S' .T = [] ∧
          S' .X = (bs.drop rest.length).map Sym.bit) := by
  obtain ⟨v₁, S₁, h₁, hF₁⟩ := walkRow_run m si rest.reverse true bs v St hV hX
  simp only [List.length_reverse, Bool.true_and] at h₁ hF₁
  by_cases hc : rest.length ≤ bs.length ∧
      (m.free si || (rest.reverse.zip bs).all fun p => m.sat p.2 p.1) = true
  · rw [ite_eq_left hc] at h₁ ⊢
    obtain ⟨hV₁, hT₁, hX₁⟩ := hF₁ hc.1
    obtain ⟨v₂, S₂, h₂, hT₂, hV₂, hk₂⟩ := moveB_run (M := prog m) (self := .back)
      (next := .walk true) rfl (show K.T ≠ K.V by decide) rest (rest.map Sym.bit) [] v₁ S₁
      (by simp [hT₁, hT]) (by simp [IsBitBlock, Sym.bit?, Function.comp_def])
      (by simp [EndsBitBlock])
    refine ⟨v₂, S₂, (h₁.trans (h₂.le le_rfl)).mono (by omega), fun _ =>
      ⟨by simp [hV₂, hV₁, List.map_reverse], hT₂, ?_⟩⟩
    rw [hk₂ .X (by decide) (by decide), hX₁]
  · rw [ite_eq_right hc] at h₁ ⊢
    exact ⟨v₁, S₁, h₁.mono (by omega), fun h => absurd h hc⟩

/-- All rows: from `walk true` with the vertices `rs` on `V` (last on top), `T` empty and the
pair bits `bs` on `X`, the walk reaches `yes` iff `rowsOk m rs bs`. -/
theorem rows_run : ∀ (rs bs : List Bool) (v : Bool) (St : ∀ _ : K, List Sym),
    St .V = rs.reverse.map Sym.bit → St .T = [] → St .X = bs.map Sym.bit →
    ∃ v' S', RunLe (prog m) (rs.length * (2 * rs.length + 2) + 1) ⟨some (.walk true), v, St⟩
      ⟨some (if rowsOk m rs bs then .yes else .no), v', S'⟩
  | [], bs, v, St, hV, _, hX => by
      obtain ⟨v', S', h⟩ := run_one (M := prog m) (l := .walk true) (v := v) (S := St)
        (l' := if rowsOk m [] bs then .yes else .no)
        (by cases bs <;> simp [prog, walkS, TM2.stepAux, hV, hX, rowsOk])
      exact ⟨v', S', h.le (by simp)⟩
  | si :: rest, bs, v, St, hV, hT, hX => by
      obtain ⟨v₁, S₁, h₁, hF₁⟩ := row_run m si rest bs v St (by simpa using hV) hT hX
      by_cases hc : rest.length ≤ bs.length ∧
          (m.free si || (rest.reverse.zip bs).all fun p => m.sat p.2 p.1) = true
      · rw [ite_eq_left hc] at h₁
        obtain ⟨hV₁, hT₁, hX₁⟩ := hF₁ hc
        obtain ⟨v₂, S₂, h₂⟩ := rows_run rest (bs.drop rest.length) v₁ S₁ hV₁ hT₁ hX₁
        have e : rowsOk m (si :: rest) bs = rowsOk m rest (bs.drop rest.length) := by
          simp [rowsOk, hc.1, hc.2]
        refine ⟨v₂, S₂, ?_⟩
        rw [e]
        refine (h₁.trans h₂).mono ?_
        simp only [List.length_cons]
        nlinarith
      · rw [ite_eq_right hc] at h₁
        have e : rowsOk m (si :: rest) bs = false := by
          by_cases h : rest.length ≤ bs.length
          · have hX : (m.free si || (rest.reverse.zip bs).all fun p => m.sat p.2 p.1) = false :=
              Bool.eq_false_iff.2 fun hX => hc ⟨h, hX⟩
            simp only [rowsOk, hX, Bool.and_false, Bool.false_and]
          · simp [rowsOk, h]
        refine ⟨v₁, S₁, ?_⟩
        rw [e]
        refine h₁.mono ?_
        simp only [List.length_cons]
        nlinarith

end Phases

/-- **The verifier machine.** From `start` with `x` on `X`, `w` on `W` and the other stacks
empty, `prog m` reaches `yes` if `kgCheck m x w` and `no` otherwise, within
`8 (|x| + |w| + 1)³` steps. -/
theorem run (m : Mode) (x w : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (hX : St .X = x.map Sym.bit) (hW : St .W = w.map Sym.bit)
    (h0 : ∀ k, k ≠ .X → k ≠ .W → St k = []) :
    ∃ v' S', RunLe (prog m) (8 * (x.length + w.length + 1) ^ 3) ⟨some start, v, St⟩
      ⟨some (if kgCheck m x w then .yes else .no), v', S'⟩ := by
  set L := x.length + w.length + 1 with hL
  have hL3 : L * L ≤ L ^ 3 := by
    have : 1 ≤ L := by omega
    nlinarith
  cases hx : decodeKG x with
  | none =>
      have hk : kgCheck m x w = false := by simp [kgCheck, hx]
      rw [hk]
      cases h₁ : readUnaryLength x with
      | none =>
          obtain ⟨v', S', h⟩ := readU_none m (c := .C) (self := .rdK) (next := .rdN) rfl
            (by decide) x v St h₁ hX
          exact ⟨v', S', h.mono (by nlinarith)⟩
      | some p =>
          obtain ⟨k, r⟩ := p
          have h₂ : readUnaryLength r = none := by
            cases h : readUnaryLength r with
            | none => rfl
            | some q => simp [decodeKG, h₁, h] at hx
          have hx' := (readUnaryLength_eq_some_iff x k r).1 h₁
          obtain ⟨v₁, S₁, r₁, hX₁, -, -⟩ := readU_some m (c := .C) (self := .rdK)
            (next := .rdN) rfl (by decide) k 0 r v St (by rw [hX, hx'])
            (by simp [h0 .C (by decide) (by decide)])
          obtain ⟨v₂, S₂, r₂⟩ := readU_none m (c := .N) (self := .rdN) (next := .load) rfl
            (by decide) r v₁ S₁ h₂ hX₁
          refine ⟨v₂, S₂, ((r₁.le le_rfl).trans r₂).mono ?_⟩
          have : x.length = k + 1 + r.length := by rw [hx']; simp; omega
          nlinarith
  | some p =>
      obtain ⟨k, n, bits⟩ := p
      have hx' := decodeKG_eq_some_iff.1 hx
      obtain ⟨v₁, S₁, r₁, hX₁, hC₁, hF₁⟩ := readU_some m (c := .C) (self := .rdK)
        (next := .rdN) rfl (by decide) k 0 (List.replicate n true ++ false :: bits) v St
        (by rw [hX, hx', encodeKG]) (by simp [h0 .C (by decide) (by decide)])
      obtain ⟨v₂, S₂, r₂, hX₂, hN₂, hF₂⟩ := readU_some m (c := .N) (self := .rdN)
        (next := .load) rfl (by decide) n 0 bits v₁ S₁ hX₁
        (by rw [hF₁ .N (by decide) (by decide), h0 .N (by decide) (by decide)]; rfl)
      have hS : ∀ q, q ≠ .X → q ≠ .C → q ≠ .N → S₂ q = St q := fun q h1 h2 h3 => by
        rw [hF₂ q h1 h3, hF₁ q h1 h2]
      obtain ⟨v₃, S₃, r₃, hF₃⟩ := load_run m n w [] k v₂ S₂ (by simpa using hN₂)
        (by rw [hS .W (by decide) (by decide) (by decide), hW])
        (by rw [hF₂ .C (by decide) (by decide), hC₁]; simp)
        (by rw [hS .V (by decide) (by decide) (by decide), h0 .V (by decide) (by decide)]; rfl)
      have hxl : x.length = k + 1 + n + 1 + bits.length := by rw [hx', encodeKG]; simp; omega
      by_cases hc : n ≤ w.length ∧ (w.take n).count true = k
      · rw [ite_eq_left hc] at r₃
        obtain ⟨hV₃, hX₃, hT₃⟩ := hF₃ hc
        obtain ⟨v₄, S₄, r₄⟩ := rows_run m (w.take n) bits v₃ S₃ (by simpa using hV₃)
          (by rw [hT₃, hS .T (by decide) (by decide) (by decide), h0 .T (by decide) (by decide)])
          (by rw [hX₃, hX₂])
        rw [kgCheck_eq_rowsOk hx hc.1 hc.2]
        refine ⟨v₄, S₄, ((((r₁.le le_rfl).trans (r₂.le le_rfl)).trans r₃).trans r₄).mono ?_⟩
        rw [List.length_take_of_le hc.1]
        have hn : n ≤ L := by omega
        have hk : k ≤ L := by omega
        nlinarith
      · rw [ite_eq_right hc] at r₃
        have hk : kgCheck m x w = false := by
          rw [kgCheck, hx]
          simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, decide_eq_false_iff_not]
          by_cases hn : n ≤ w.length
          · exact Or.inl (Or.inr (fun h => hc ⟨hn, h⟩))
          · exact Or.inl (Or.inl (Or.inr hn))
        rw [hk]
        refine ⟨v₃, S₃, (((r₁.le le_rfl).trans (r₂.le le_rfl)).trans r₃).mono ?_⟩
        have hn : n ≤ L := by omega
        have hk : k ≤ L := by omega
        nlinarith

/-- Moved to `Cslib.Complexity.Karp.pairs_nodup` (`Karp.CliqueCorrect`). -/
@[deprecated Karp.pairs_nodup (since := "2026-10-15")]
theorem pairs_nodup (n : ℕ) : (pairs n).Nodup := Karp.pairs_nodup n

end Cslib.Complexity.Karp.KGVerify
