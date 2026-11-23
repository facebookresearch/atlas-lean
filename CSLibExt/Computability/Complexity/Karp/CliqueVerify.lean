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

/-- **Modes of the clique verifier.** A mode is one of three values, clique, independent set
and vertex cover, naming the three graph problems CLIQUE, INDEPENDENT-SET and VERTEX-COVER that
share one NP verifier. -/
inductive Mode | clique | indep | cover
  deriving DecidableEq

/-- `Mode` is finite. -/
instance Mode.instFintypeEnumFix : Fintype Mode where
  elems := ⟨↑[Mode.clique, .indep, .cover], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Pair condition of the clique verifier.** For a mode $m$, the adjacency bit $b$ of a vertex
pair $\{i, j\}$, and flags $s_i$, $s_j$ saying whether $i$ and $j$ are chosen, the pair
condition $\mathrm{ok}_m(b, s_i, s_j)$ is $\lnot(s_i \land s_j) \lor b$ for clique,
$\lnot(s_i \land s_j) \lor \lnot b$ for independent set, and $\lnot b \lor s_i \lor s_j$ for
vertex cover. -/
def Mode.ok : Mode → Bool → Bool → Bool → Bool
  | .clique, b, si, sj => !(si && sj) || b
  | .indep, b, si, sj => !(si && sj) || !b
  | .cover, b, si, sj => !b || si || sj

/-- **The verifier for CLIQUE, INDEPENDENT-SET and VERTEX-COVER.** For a mode $m$, an input
$x$ and a witness $w$ (bit lists), the verifier rejects if $x$ does not decode to a triple
$(k, n, \mathit{bits})$. Otherwise it accepts if and only if $\mathit{bits}$ has one bit per
pair $(i, j)$ with $i < j < n$, $w$ has at least $n$ bits, exactly $k$ of the first $n$ bits of
$w$ are set, and for every pair $(i, j)$, matched with its bit $b$ in the encoding order of the
pairs, the pair condition of $m$ holds for $b$, $w_i$ and $w_j$. So the first $n$ bits of $w$
choose the vertices. -/
def kgCheck (m : Mode) (x w : List Bool) : Bool :=
  match decodeKG x with
  | none => false
  | some (k, n, bits) => bits.length == (pairs n).length && n ≤ w.length &&
      (w.take n).count true == k &&
      ((pairs n).zip bits).all fun pb => m.ok pb.2 (w.getD pb.1.1 false) (w.getD pb.1.2 false)

/-- **Vertices that settle their pairs alone.** For a mode and the Boolean saying whether a
vertex $i$ is chosen, the result is true when $i$ alone settles the condition on every pair
$\{i, j\}$: in the clique and independent-set modes it is true exactly when $i$ is not chosen,
and in the vertex-cover mode exactly when $i$ is chosen. -/
def Mode.free : Mode → Bool → Bool
  | .cover, si => si
  | _, si => !si

/-- **The pair condition left to the later vertex.** For a mode $m$, a pair bit $b$ and a
flag $s_j$ saying whether vertex $j$ is chosen, $\mathrm{sat}_m(b, s_j)$ is
$\lnot s_j \lor b$ for clique, $\lnot s_j \lor \lnot b$ for independent set, and
$\lnot b \lor s_j$ for vertex cover.

It is the pair condition on $\{i, j\}$ when vertex $i$ does not settle it. -/
def Mode.sat : Mode → Bool → Bool → Bool
  | .clique, b, sj => !sj || b
  | .indep, b, sj => !sj || !b
  | .cover, b, sj => !b || sj

/-- **The pair condition splits by vertex.** For a mode $m$ and Booleans $b$, $s_i$, $s_j$, let
$\mathrm{ok}_m(b, s_i, s_j)$ be the pair condition of $m$: $\lnot(s_i \land s_j) \lor b$ for
clique, $\lnot(s_i \land s_j) \lor \lnot b$ for independent set and $\lnot b \lor s_i \lor s_j$
for vertex cover. Let $\mathrm{free}_m(s_i)$, the part that vertex $i$ alone settles, be
$\lnot s_i$ for clique and independent set and $s_i$ for vertex cover, and let
$\mathrm{sat}_m(b, s_j)$, the part left to $j$, be $\lnot s_j \lor b$ for clique,
$\lnot s_j \lor \lnot b$ for independent set and $\lnot b \lor s_j$ for vertex cover. Then for
every mode $m$ and all Booleans $b$, $s_i$, $s_j$, we have
$\mathrm{ok}_m(b, s_i, s_j) = \mathrm{free}_m(s_i) \lor \mathrm{sat}_m(b, s_j)$. -/
theorem Mode.ok_eq (m : Mode) (b si sj : Bool) : m.ok b si sj = (m.free si || m.sat b sj) := by
  cases m <;> cases b <;> cases si <;> cases sj <;> rfl

/-! ### The pair order -/

/-- **Vertex pairs in encoding order for one more vertex.** For a natural number $m$, write
$P(m)$ for the list of pairs $(i, j)$ of natural numbers with $i < j < m$, ordered by $i$
ascending and, for each $i$, by $j$ descending. Then for every natural number $n$, $P(n + 1)$ is
the list $(0, n), (0, n - 1), \dots, (0, 1)$ (empty when $n = 0$) followed by the pairs
$(i + 1, j + 1)$ for the pairs $(i, j)$ of $P(n)$, in the order of $P(n)$. -/
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

/-- **Chosen-flag pairs.** For a list $s = (s_0, \dots, s_{\ell - 1})$ of Booleans, the
chosen-flag pairs of $s$ are the pairs $(s_i, s_j)$, one for each vertex pair $(i, j)$ with
$i < j < \ell$, listed in the encoding order of the vertex pairs of $\ell$ vertices (rows $i$
ascending, within a row $j$ descending). -/
def pairVals (s : List Bool) : List (Bool × Bool) :=
  (pairs s.length).map fun p => (s.getD p.1 false, s.getD p.2 false)

/-- **Reading a list at every index.** For every list $s$ of Booleans of length $\ell$,
reading $s$ at the indices $0, 1, \dots, \ell - 1$ in turn (with default value false) gives
back $s$. -/
theorem map_getD_range (s : List Bool) : (List.range s.length).map (s.getD · false) = s := by
  refine List.ext_getElem (by simp) fun t h₁ h₂ => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- **Chosen-flag pairs of a list with a new head.** For a Boolean $a$ and a list
$s = (s_0, \dots, s_{\ell - 1})$ of Booleans, the chosen-flag pairs of the list
$(a, s_0, \dots, s_{\ell - 1})$ are $(a, s_{\ell - 1}), (a, s_{\ell - 2}), \dots, (a, s_0)$,
followed by the chosen-flag pairs of $s$. -/
theorem pairVals_cons (a : Bool) (s : List Bool) :
    pairVals (a :: s) = s.reverse.map (a, ·) ++ pairVals s := by
  rw [pairVals, List.length_cons, pairs_succ, List.map_append, List.map_map, List.map_map]
  congr 1
  conv_rhs => rw [← map_getD_range s]
  simp [List.map_reverse, Function.comp_def]

/-- **The row-by-row check of the clique verifier.** For a mode $m$, the row-by-row check of
a list of chosen-flags against a list $b$ of pair bits is defined by recursion on the flags.
For the empty list it holds iff $b$ is empty. For a flag $a$ followed by the flags $r$ of the
later vertices, write $\rho$ for the reverse of $r$: the check holds iff $|r| \le |b|$,
either $a$ is free for $m$ or $\mathrm{sat}_m(b_t, \rho_t)$ holds for every $t < |r|$
(indices from $0$), and the check of $r$ against $b$ with its first $|r|$ bits dropped holds.

This is what the machine checks, vertex by vertex; at the end no bit may be left. -/
def rowsOk (m : Mode) : List Bool → List Bool → Bool
  | [], bs => bs.isEmpty
  | s :: rest, bs => decide (rest.length ≤ bs.length) &&
      (m.free s || (rest.reverse.zip bs).all fun p => m.sat p.2 p.1) &&
      rowsOk m rest (bs.drop rest.length)

/-- **The row-by-row check is the pairwise check.** For every mode $m$ and all lists of bits
$s$ and $b$, the row-by-row check of $s$ against $b$ holds if and only if $b$ has exactly
one bit per pair $i < j < |s|$ and, listing these pairs in encoding order (rows $i$
ascending, within a row $j$ descending), the $t$-th pair $(i, j)$ and the $t$-th bit $b_t$
satisfy the pair condition $\mathrm{ok}_m(b_t, s_i, s_j)$ for every $t$. -/
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

/-- **The verifier as a row-by-row check.** Let $m$ be a mode and $x$, $w$ bit lists.
Suppose that $x$ decodes to $(k, n, \mathit{bits})$, that $w$ has at least $n$ bits, and that
exactly $k$ of the first $n$ bits of $w$ are set. Then the verifier for mode $m$ on input $x$
and witness $w$ returns the same value as the row-by-row check for mode $m$ of the first $n$
bits of $w$ against the pair bits $\mathit{bits}$. -/
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

/-- **Lookup in a list of pairs with distinct keys.** Let $l$ be a list of pairs whose keys lie
in a type with a lawful Boolean equality and are pairwise distinct. If $(a, b)$ occurs in $l$,
then looking up the key $a$ in $l$ returns $b$. -/
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

/-- **Checking each listed vertex pair against its bit.** Let $n$ be a natural number and $b$ a
list of bits with one bit per vertex pair, that is, with as many entries as the list of pairs
$(i, j)$ with $i < j < n$. Then for every Boolean predicate $P$ on a pair of natural numbers and
a bit, $P$ holds on every entry of the pair list zipped with $b$ (the $t$-th pair together with
the $t$-th bit of $b$) if and only if, for all natural numbers $i < j < n$, $P$ holds on the
pair $(i, j)$ together with the adjacency bit of $\{i, j\}$ in $b$. -/
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

/-- **Characterization of the CLIQUE verifier.** For a mode $m$ and bit lists $x$ and $w$, the
verifier for mode $m$ accepts input $x$ with witness $w$ if and only if there are $k$, $n$ and a
bit list $\mathit{bits}$ such that $x$ is the encoding of the instance $(k, n, \mathit{bits})$,
$\mathit{bits}$ has one bit per pair $(i, j)$ with $i < j < n$, $w$ has at least $n$ bits,
exactly $k$ of the first $n$ bits of $w$ are set, and for all $i < j < n$ the pair condition of
$m$ holds for the bit of the pair $\{i, j\}$ and the bits $w_i$ and $w_j$. -/
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

/-- **Counting the set bits of a list built from a function.** For every natural number $n$ and
every function $f$ from $\{0, \dots, n-1\}$ to the Booleans, the number of entries equal to
true in the list $f(0), f(1), \dots, f(n-1)$ equals the number of indices $i < n$ with $f(i)$
true. -/
theorem count_ofFn : ∀ {n : ℕ} (f : Fin n → Bool),
    (List.ofFn f).count true = (Finset.univ.filter fun i => f i = true).card
  | 0, f => by simp
  | n + 1, f => by
      rw [List.ofFn_succ, List.count_cons, count_ofFn, Finset.card_filter, Finset.card_filter,
        Fin.sum_univ_succ]
      cases f 0 <;> simp [add_comm]

/-- **The first $n$ bits of a list, read index by index.** If a bit list $w$ has length at
least $n$, then the first $n$ entries of $w$ form the list $(w_0, \dots, w_{n-1})$, where $w_i$
is the entry of $w$ at index $i$ (taken as false past the end of $w$). -/
theorem take_eq_ofFn {n : ℕ} {w : List Bool} (hn : n ≤ w.length) :
    w.take n = List.ofFn fun i : Fin n => w.getD i false := by
  refine List.ext_getElem (by simp [hn]) fun t h₁ h₂ => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < w.length by
    simp at h₁; omega)]

/-- **Vertex sets meeting a mode's pair condition.** For a mode $m$, a number $n$, a list of
pair bits and a set $s$ of vertices in $\{0, \dots, n - 1\}$, the set $s$ meets the condition
of $m$ when for all vertices $i < j$ the pair condition
$\mathrm{ok}_m(b_{ij}, [i \in s], [j \in s])$ holds, where $[i \in s]$ says whether $i$ is
chosen and $b_{ij}$ is the bit of the pair $\{i, j\}$: listing the pairs $i' < j' < n$ in
encoding order (rows $i'$ ascending, within a row $j'$ descending), the $t$-th bit of the list
belongs to the $t$-th pair, and $b_{ij}$ is false if the list has no bit for $\{i, j\}$. -/
def SetOk (m : Mode) (n : ℕ) (bits : List Bool) (s : Finset (Fin n)) : Prop :=
  ∀ i j : Fin n, i < j → m.ok (adjBits n bits i j) (decide (i ∈ s)) (decide (j ∈ s)) = true

/-- **An accepted input encodes an instance with a good vertex set.** Fix a mode (clique,
independent set or vertex cover) and bit strings $x$ and $w$. If the verifier in that mode
accepts the input $x$ with witness $w$, then there are natural numbers $k$ and $n$ and a list of
bits $b$ such that $x$ is the encoding of the instance $(k, n, b)$, $b$ has exactly one bit per
vertex pair $(i, j)$ with $i < j < n$, and some set of exactly $k$ of the vertices
$0, \dots, n-1$ meets the mode's pair condition on every pair $i < j$. -/
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

/-- **The characteristic vector of a good vertex set is accepted.** Let $m$ be a mode, $k$ and
$n$ natural numbers, let $\mathit{bits}$ be a bit list with one bit per pair $(i, j)$,
$i < j < n$, and let $s$ be a set of $k$ vertices of $\{0, \dots, n - 1\}$ that meets the pair
condition of $m$ on every pair $i < j$. Then the verifier for mode $m$ accepts the encoding of
$(k, n, \mathit{bits})$ with witness the characteristic vector of $s$: the list of $n$ bits whose
$i$-th bit is set if and only if $i \in s$. -/
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

/-- **Verifying a graph language defined by a vertex-set condition.** Let $m$ be a mode and
$P$ a property of a number $k$ and a graph on $n$ vertices. Suppose that for all $n$, $k$ and
every bit list $\mathit{bits}$ with one bit per pair $(i, j)$, $i < j < n$, the property $P$
holds for $k$ and the graph given by $\mathit{bits}$ exactly when some set of $k$ vertices meets
the pair condition of $m$ on every pair $i < j$. Then for every bit list $x$, $x$ belongs to
the language of instances satisfying $P$ if and only if the verifier for mode $m$ accepts $x$
with some witness $w$ of length $|w| \le |x|$. -/
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

/-- **Symmetric relations on increasing pairs.** Let $n$ be a natural number and $R$ a relation
on $\{0, \dots, n-1\}$ such that $R(i, j)$ implies $R(j, i)$. Then $R(i, j)$ holds for all
$i \ne j$ if and only if $R(i, j)$ holds for all $i < j$. -/
theorem forall_ne_iff_lt {n : ℕ} {R : Fin n → Fin n → Prop} (hR : ∀ i j, R i j → R j i) :
    (∀ i j, i ≠ j → R i j) ↔ ∀ i j, i < j → R i j :=
  ⟨fun h i j hij => h i j hij.ne, fun h i j hij =>
    (lt_or_gt_of_ne hij).elim (h i j) fun hji => hR _ _ (h j i hji)⟩

/-- **Cliques of the graph given by pair bits.** For natural numbers $n$ and $k$ and a list of
bits $b$, the graph on the vertices $0, \dots, n-1$ read off $b$ has a clique of exactly $k$
vertices if and only if there is a set $s$ of exactly $k$ of these vertices meeting the
clique-mode pair condition on every pair $i < j$: whenever $i$ and $j$ both lie in $s$, the
bit of the pair $\{i, j\}$ in $b$ is set. -/
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

/-- **Independent sets of the graph given by pair bits.** For natural numbers $n$ and $k$ and a
list of bits $b$, the graph on the vertices $0, \dots, n-1$ read off $b$ has an independent set
of exactly $k$ vertices if and only if there is a set $s$ of exactly $k$ of these vertices
meeting the independent-set-mode pair condition on every pair $i < j$: whenever $i$ and $j$ both
lie in $s$, the bit of the pair $\{i, j\}$ in $b$ is not set. -/
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

/-- **Vertex covers of the graph given by pair bits.** For natural numbers $n$ and $k$ and a list
of bits $b$, the graph on the vertices $0, \dots, n-1$ read off $b$ has a vertex cover of
exactly $k$ vertices if and only if there is a set $s$ of exactly $k$ of these vertices meeting
the cover-mode pair condition on every pair $i < j$: whenever the bit of the pair $\{i, j\}$ in
$b$ is set, $i$ or $j$ lies in $s$. -/
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

/-- **CLIQUE is verified with witnesses no longer than the input.** For every bit string $x$,
$x$ is in CLIQUE if and only if there is a bit string $w$ of length at most the length of $x$
such that the shared CLIQUE / INDEPENDENT-SET / VERTEX-COVER verifier, run in clique mode,
accepts the input $x$ with witness $w$. -/
theorem cliqueDec_iff (x : List Bool) :
    cliqueDec x = true ↔ ∃ w, w.length ≤ x.length ∧ kgCheck .clique x w = true :=
  kgDec_iff_exists .clique _ (fun n k bits _ => clique_iff n k bits) x

/-- **INDEPENDENT-SET is verified with witnesses no longer than the input.** For every bit string
$x$, $x$ is in INDEPENDENT-SET if and only if there is a bit string $w$ of length at most the
length of $x$ such that the shared CLIQUE / INDEPENDENT-SET / VERTEX-COVER verifier, run in
independent-set mode, accepts the input $x$ with witness $w$. -/
theorem indSetDec_iff (x : List Bool) :
    indSetDec x = true ↔ ∃ w, w.length ≤ x.length ∧ kgCheck .indep x w = true :=
  kgDec_iff_exists .indep _ (fun n k bits _ => indep_iff n k bits) x

/-- **VERTEX-COVER is verified by the clique verifier in cover mode.** A bit string $x$ is in
VERTEX-COVER if and only if there is a bit string $w$, no longer than $x$, such that the
clique-family verifier in vertex-cover mode accepts $x$ with witness $w$. -/
theorem vertexCoverDec_iff (x : List Bool) :
    vertexCoverDec x = true ↔ ∃ w, w.length ≤ x.length ∧ kgCheck .cover x w = true :=
  kgDec_iff_exists .cover _ (fun n k bits _ => cover_iff n k bits) x

/-! ### The machine -/

/-- **Stacks of the CLIQUE verifier.** The verifier machine for CLIQUE, INDEPENDENT-SET and
VERTEX-COVER, run on an instance with target size $k$ and $n$ vertices, has six stacks: the
input $X$, the witness $W$, the counter $C$ (holding $k$), the counter $N$ (holding $n$), the
vertex stack $V$ and its scratch stack $T$. -/
inductive K | X | W | C | N | V | T
  deriving DecidableEq

/-- `K` is finite. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .W, .C, .N, .V, .T], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Labels of the CLIQUE verifier.** On an instance with target size $k$ and $n$ vertices, the
verifier machine has the labels: read $k$, read $n$, load the witness, walk a row (carrying a bit
$c$, the conjunction of the row's pair conditions so far), put the row back, accept, and
reject. -/
inductive Lab | rdK | rdN | load | walk (c : Bool) | back | yes | no
  deriving DecidableEq

/-- `Lab` is finite. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.rdK, .rdN, .load, .walk false, .walk true, .back, .yes, .no], by decide⟩
  complete := by rintro (_ | _ | _ | ⟨_ | _⟩ | _ | _ | _) <;> decide

/-- **Statements of the clique verifier.** The statements of the verifier are those of a
multi-stack Turing machine (Mathlib's TM2 model) with the six stacks $X, W, C, N, V, T$, each
over the symbol alphabet of the SAT verifier, the verifier's labels, and one Boolean of local
state. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Sym) Lab Bool

/-- **The clique verifier's unary reader.** For a stack $c$ and labels $\ell$ (its own) and
$\ell'$ (the next), the unary reader onto $c$ is the verifier statement that inspects the
input stack $X$ and sets the state to whether $X$ is empty: if it is, it goes to the rejecting
label; otherwise it pops the top symbol of $X$ and sets the state to whether that symbol is
the bit $1$; if so, it pushes the bit $1$ onto $c$ and goes to $\ell$, while any other symbol
(normally the terminating $0$) sends it to $\ell'$.

Run from $\ell$, it reads a unary number off $X$ onto the counter $c$. -/
def readU (c : K) (self next : Lab) : Stmt :=
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
    .pop .X (fun _ o => bitOf Sym.bit? o) <| .branch id
      (.push c (fun _ => .bit true) (.goto fun _ => self)) (.goto fun _ => next)

/-- **Load step of the CLIQUE verifier.** The statement run at the load label. If the counter
$N$ is nonempty, it takes a unit off $N$, rejects if the witness stack $W$ is empty, and
otherwise pops the top of $W$ and pushes its bit (false for a non-bit symbol) onto the vertex
stack $V$; if that bit is set it also takes a unit off the counter $C$, rejecting if $C$ is
empty; then it returns to the load label. If $N$ is empty, it goes to the walk label with its
flag $c$ (the conjunction of the row's pair conditions so far) set to true when $C$ is empty,
and rejects otherwise.

Started from $n$ on $N$ and $k$ on $C$, it loads the first $n$ witness bits onto $V$, bit
$n - 1$ on top, and rejects if $W$ runs out or the number of set bits among them is not $k$. -/
def loadS : Stmt :=
  .pop .N (fun _ o => o.isSome) <| .branch id
    (.peek .W (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
      .pop .W (fun _ o => bitOf Sym.bit? o) <| .branch id
        (.push .V (fun _ => .bit true) <| .pop .C (fun _ o => o.isSome) <| .branch id
          (.goto fun _ => .load) (.goto fun _ => .no))
        (.push .V (fun _ => .bit false) <| .goto fun _ => .load))
    (.peek .C (fun _ o => o.isNone) <| .branch id (.goto fun _ => .walk true)
      (.goto fun _ => .no))

/-- **Rest of a walk step of the clique verifier.** Write $\mathrm{free}_m(s)$ for the condition
that, in mode $m$, a vertex with chosen-flag $s$ settles every pair of its row, and
$\mathrm{sat}_m(b', s')$ for the pair condition on pair bit $b'$ and later vertex flag $s'$. In
mode $m$ with row flag $c$, after a bit $z$ has been popped off the vertex stack $V$: if $V$ is
now empty, the machine moves to the put-back label when $\mathrm{free}_m(z)$ or $c$ holds, and to
the reject label otherwise. If $V$ is not empty, it pushes $z$ onto the scratch stack $T$; then
it moves to the reject label if the input stack $X$ is empty, and otherwise pops the top symbol
of $X$, reads it as a bit $b$ (a non-bit symbol reads as false), and moves to the walk label
with flag $c \wedge \mathrm{sat}_m(b, z)$. -/
def walkZ (m : Mode) (c z : Bool) : Stmt :=
  .peek .V (fun _ o => o.isNone) <| .branch id
    (.goto fun _ => if m.free z || c then .back else .no) <|
  .push .T (fun _ => .bit z) <|
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
  .pop .X (fun _ o => bitOf Sym.bit? o) <| .branch id
    (.goto fun _ => .walk (c && m.sat true z)) (.goto fun _ => .walk (c && m.sat false z))

/-- **Walk step of the clique verifier.** In mode $m$ with row flag $c$, the walk step looks at
the vertex stack $V$. If $V$ is empty, it moves to the accept label if the input stack $X$ is
empty and to the reject label otherwise. If $V$ is not empty, it pops the top symbol of $V$,
reads it as a bit $z$ (a non-bit symbol reads as false), and continues with the rest of the walk
step for $m$, $c$ and $z$. -/
def walkS (m : Mode) (c : Bool) : Stmt :=
  .peek .V (fun _ o => o.isNone) <| .branch id
    (.peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .yes) (.goto fun _ => .no)) <|
  .pop .V (fun _ o => bitOf Sym.bit? o) <| .branch id (walkZ m c true) (walkZ m c false)

/-- **Program of the clique verifier.** For a mode $m$ (clique, independent set or vertex
cover), the verifier program of mode $m$ assigns a statement to each label of the verifier: to
the label that reads the instance's target size $k$, the unary reader onto the counter $C$ with
own label this label and next label the label that reads the instance's number $n$ of vertices;
to the label that reads $n$, the unary reader onto the counter $N$ with own label this label and
next label the load label; to the load label, the load step; to the walk label with flag $c$,
the walk step of mode $m$ with flag $c$; to the put-back label, the bit-moving loop from the
scratch stack $T$ to the vertex stack $V$ that reads name-bit symbols as bits and writes each
bit $b$ as the name bit $b$, with own label the put-back label and next label the walk label
with flag true; and to the accept and reject labels, the statement that halts.

Run from the label that reads $k$, it parses $k$ and $n$, loads the witness and walks the
rows. -/
def prog (m : Mode) : Lab → TM2.Stmt (fun _ : K => Sym) Lab Bool
  | .rdK => readU .C .rdK .rdN
  | .rdN => readU .N .rdN .load
  | .load => loadS
  | .walk c => walkS m c
  | .back => moveB .T .V Sym.bit? Sym.bit .back (.walk true)
  | .yes => .halt
  | .no => .halt

/-- **Start label of the clique verifier.** The verifier for CLIQUE, INDEPENDENT-SET and
VERTEX-COVER starts at the label that reads the instance's size parameter $k$ (the number of
vertices to choose) in unary off the input stack $X$ onto the counter $C$. -/
def start : Lab := .rdK

/-! ### Runs of the phases -/

/-- **One step of a clique-verifier program to a known label.** Let $M$ be a program that
assigns a verifier statement to each label, $\ell$ and $\ell'$ labels, $v$ a state and $S$
stack contents. If executing the statement $M(\ell)$ from state $v$ and stacks $S$ ends at
label $\ell'$, then there are a state $v'$ and stack contents $S'$ such that $M$ runs in
exactly one step from label $\ell$ with state $v$ and stacks $S$ to label $\ell'$ with
state $v'$ and stacks $S'$. -/
theorem run_one {M : Lab → Stmt} {l l' : Lab} {v : Bool} {S : ∀ _ : K, List Sym}
    (h : (TM2.stepAux (M l) v S).l = some l') :
    ∃ v' S', Run M 1 ⟨some l, v, S⟩ ⟨some l', v', S'⟩ :=
  ⟨_, _, Run.single (by rw [← h])⟩

section Phases

variable (m : Mode)

/-- **The clique verifier's unary reader succeeds.** Let $m$ be a mode, $c$ a stack other
than the input stack $X$, and $\ell$, $\ell'$ labels such that the verifier program of
mode $m$ runs, at label $\ell$, the unary reader onto $c$ with own label $\ell$ and next
label $\ell'$. Let $k, j \in \mathbb{N}$, let $r$ be a list of bits, $v$ a state and $S$
stack contents in which $X$ holds, from the top, $k$ ones, then a zero, then the bits of
$r$, and $c$ holds exactly $j$ copies of the bit $1$. Then there are a state $v'$ and
stack contents $S'$ such that the program runs in exactly $k + 1$ steps from label $\ell$
with state $v$ and stacks $S$ to label $\ell'$ with state $v'$ and stacks $S'$, where in
$S'$ the stack $X$ holds the bits of $r$, the stack $c$ holds exactly $k + j$ copies of
the bit $1$, and every stack other than $X$ and $c$ is as in $S$. -/
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

/-- **Reading an unterminated unary number rejects.** Let $m$ be a mode, $c$ a stack other
than the input stack $X$, and $\lambda$, $\mu$ labels such that the verifier for $m$ runs at
$\lambda$ the unary reader onto $c$ that loops at $\lambda$ and exits to $\mu$. Let $l$ be a
list of Booleans from which no unary length can be read (it contains no false). Then for every
machine variable $v$ and all stack contents in which $X$ holds exactly the bits of $l$, the
verifier for $m$ goes from label $\lambda$ to the rejecting label no in at most $|l| + 1$
steps. -/
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

/-- **Run of the load phase.** Let $m$ be a mode, $n$ and $j$ natural numbers and $w$ and
$\mathit{acc}$ bit lists. Start the verifier for mode $m$ at the load label, in any internal
state, with $n$ in unary on the counter $N$, $j$ in unary on the counter $C$, $w$ on the witness
stack $W$ and $\mathit{acc}$ on the vertex stack $V$. Then within at most $n + 1$ steps the
machine reaches the walk label with its flag $c$ (the conjunction of the row's pair conditions
so far) set to true if $w$ has at least $n$ bits and exactly $j$ of its first $n$ bits are set,
and the reject label otherwise. In the first case $V$ then holds the first $n$ bits of $w$, bit
$n - 1$ on top, above $\mathit{acc}$, and the stacks $X$ and $T$ are unchanged. -/
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

/-- **Walking the pairs of one row of the clique verifier.** Let $m$ be a mode and $s$ a bit.
Let $z = (z_0, \dots, z_{r-1})$ and $b = (b_0, \dots, b_{q-1})$ be lists of bits, $c$ a bit, $v$
a state and $S$ stack contents in which the vertex stack $V$ holds, from the top, the name bits
$z_0, \dots, z_{r-1}$ followed by the name bit $s$, and the input stack $X$ holds, from the top,
the name bits $b_0, \dots, b_{q-1}$. Then there are a state $v'$ and stack contents $S'$ such
that within at most $r + 1$ steps the verifier program of mode $m$ goes from the walk label with
flag $c$, state $v$ and stacks $S$ to state $v'$ and stacks $S'$ at the put-back label if
$r \le q$ and either $\mathrm{free}_m(s)$ holds (a vertex with chosen-flag $s$ settles its pairs
alone) or both $c$ and $\mathrm{sat}_m(b_t, z_t)$ for every $t < r$ hold (the pair condition
left to the later vertex, with pair bit $b_t$ and later-vertex flag $z_t$), and at the reject
label otherwise. Moreover, if $r \le q$, then in $S'$ the stack $V$ is empty, the scratch stack
$T$ holds $z_{r-1}, \dots, z_0$ from the top above its contents in $S$, and $X$ holds, from the
top, $b_r, \dots, b_{q-1}$. -/
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

/-- **One row of the clique verifier's walk.** Let $m$ be a mode, $s_i$ a bit, $r$ and $b$
lists of bits, $v$ a state and $S$ stack contents in which the vertex stack $V$ holds, from
the top, the bits of the reverse $\rho$ of $r$ followed by $s_i$, the scratch stack $T$ is
empty, and the input stack $X$ holds the bits $b$. Call the row condition: $|r| \le |b|$,
and either $s_i$ is free for $m$ or $\mathrm{sat}_m(b_t, \rho_t)$ holds for every $t < |r|$
(indices from $0$). Then there are a state $v'$ and stack contents $S'$ such that within at
most $2|r| + 2$ steps the verifier program of mode $m$ goes from label walk(true) with
state $v$ and stacks $S$ to state $v'$ and stacks $S'$ at label walk(true) if the row
condition holds and at the rejecting label otherwise; and if the row condition holds, then
in $S'$ the stack $V$ holds the bits of $\rho$, $T$ is empty, and $X$ holds $b$ with its
first $|r|$ bits dropped. -/
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

/-- **All rows of the clique verifier's walk.** Let $m$ be a mode, $r$ and $b$ lists of
bits, $v$ a state and $S$ stack contents in which the vertex stack $V$ holds, from the top,
the bits of the reverse of $r$ (so the last entry of $r$ is on top), the scratch stack $T$
is empty, and the input stack $X$ holds the bits $b$. Then there are a state $v'$ and stack
contents $S'$ such that within at most $|r|(2|r| + 2) + 1$ steps the verifier program of
mode $m$ goes from label walk(true) with state $v$ and stacks $S$ to state $v'$ and stacks
$S'$ at the accepting label if the row-by-row check of $r$ against $b$ holds for $m$, and
at the rejecting label otherwise. -/
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

/-- **The verifier machine for clique, independent set and vertex cover.** Let $m$ be a
mode, $x$ and $w$ lists of bits, $v$ a state and $S$ stack contents in which the input
stack $X$ holds the bits of $x$, the witness stack $W$ holds the bits of $w$, and every other
stack is empty. Then there are a state $v'$ and stack contents $S'$ such that within at most
$8(|x| + |w| + 1)^3$ steps the verifier program of mode $m$ goes from the start label with
state $v$ and stacks $S$ to state $v'$ and stacks $S'$ at the accepting label if the
verifier check of mode $m$ accepts $x$ with witness $w$, and at the rejecting label
otherwise. -/
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
