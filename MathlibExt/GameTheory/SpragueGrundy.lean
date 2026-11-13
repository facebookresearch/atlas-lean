/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.WellFounded
import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MetaMathlibExt.SpragueGrundy

/-- **Impartial game.** An impartial game consists of a type of positions, a starting position,
for each position $p$ a finite set of positions reachable from $p$ in one move, and a rank
function assigning a natural number to each position such that every move strictly decreases the
rank: if $q$ is reachable from $p$ in one move, then $\mathrm{rank}(q) < \mathrm{rank}(p)$.

Because the move sets are finite and the rank strictly decreases along moves, every play
terminates and only finitely many positions are reachable from any position, even if the type of
positions is infinite or contains unreachable positions.
-/
structure ImpartialGame where
  Pos : Type
  eqDec : DecidableEq Pos
  moves : Pos → Finset Pos
  rank : Pos → ℕ
  rank_lt : ∀ p q, q ∈ moves p → rank q < rank p
  start : Pos

theorem wfRel (G : ImpartialGame) :
    WellFounded (fun a b => a ∈ G.moves b) := by
  refine Subrelation.wf ?_ (measure G.rank).wf
  intro a b h
  exact G.rank_lt b a h

/-- **P-positions.** In an impartial game $G$, the P-positions are defined by well-founded
recursion along moves: a position $p$ is a P-position if and only if no position reachable from
$p$ in one move is a P-position. Positions that are not P-positions are called N-positions.

Under normal play, where the player unable to move loses, the P-positions are exactly the
positions from which the player to move loses. -/
noncomputable def IsP (G : ImpartialGame) : G.Pos → Prop :=
  (wfRel G).fix fun p ih => ∀ q (h : q ∈ G.moves p), ¬ ih q h

/-- **Sum of impartial games.** The sum $G + H$ of two impartial games $G$ and $H$ is the
impartial game whose positions are the pairs $(a, b)$ of a position $a$ of $G$ and a position $b$
of $H$, and in which a move changes exactly one component: from $(a, b)$ one may move to
$(a', b)$ for any move from $a$ to $a'$ in $G$, or to $(a, b')$ for any move from $b$ to $b'$ in
$H$. Its starting position is the pair of the starting positions of $G$ and $H$, and the rank of
$(a, b)$ is the sum of the ranks of $a$ in $G$ and of $b$ in $H$. -/
noncomputable def gameSum (G H : ImpartialGame) : ImpartialGame :=
  letI := G.eqDec
  letI := H.eqDec
  { Pos := G.Pos × H.Pos
    eqDec := inferInstance
    moves := fun p =>
      (G.moves p.1).image (fun a => (a, p.2)) ∪
        (H.moves p.2).image (fun b => (p.1, b))
    rank := fun p => G.rank p.1 + H.rank p.2
    rank_lt := by
      intro p q h
      simp only [Finset.mem_union, Finset.mem_image] at h
      cases h with
      | inl h1 =>
        obtain ⟨a', ha', heq⟩ := h1
        change (a', p.2) = q at heq
        subst heq
        exact Nat.add_lt_add_right (G.rank_lt p.1 a' ha') _
      | inr h2 =>
        obtain ⟨b', hb', heq⟩ := h2
        change (p.1, b') = q at heq
        subst heq
        exact Nat.add_lt_add_left (H.rank_lt p.2 b' hb') _
    start := (G.start, H.start) }

/-- **Nim heap.** For a natural number $n$, the Nim heap of size $n$ is the impartial game whose
positions are $0, 1, \dots, n$, whose starting position is $n$, and in which a move from $k$ goes
to any $j < k$; the rank of a position is its value. -/
def nimHeap (n : ℕ) : ImpartialGame where
  Pos := Fin (n + 1)
  eqDec := inferInstance
  moves := fun k => Finset.univ.filter (fun j => j.val < k.val)
  rank := fun k => k.val
  rank_lt := by
    intro k j h
    simpa using h
  start := ⟨n, Nat.lt_succ_self n⟩

/-- **Equivalence of impartial games.** Two impartial games $G$ and $H$ are equivalent when no
third game tells them apart as summands: for every impartial game $K$, the starting position of
the sum $G + K$ is a P-position if and only if the starting position of the sum $H + K$ is a
P-position. The starting position of a sum is the pair of the starting positions of its summands. -/
noncomputable def Equiv (G H : ImpartialGame) : Prop :=
  ∀ K : ImpartialGame,
    IsP (gameSum G K) (G.start, K.start) ↔
      IsP (gameSum H K) (H.start, K.start)

/-- **Recursive characterization of P-positions.** In an impartial game $G$, a position $p$ is a
P-position if and only if every position reachable from $p$ in one move is not a P-position. -/
theorem isP_iff (G : ImpartialGame) (p : G.Pos) :
    IsP G p ↔ ∀ q (_ : q ∈ G.moves p), ¬ IsP G q := by
  unfold IsP
  rw [WellFounded.fix_eq]

private theorem exists_not_mem (s : Finset ℕ) : ∃ n, n ∉ s := by
  refine ⟨s.sup id + 1, fun h => ?_⟩
  have hle : id (s.sup id + 1) ≤ s.sup id := Finset.le_sup (f := id) h
  simp only [id_eq] at hle
  omega

private noncomputable def mex (s : Finset ℕ) : ℕ := Nat.find (exists_not_mem s)

private theorem mex_not_mem (s : Finset ℕ) : mex s ∉ s :=
  Nat.find_spec (exists_not_mem s)

private theorem mex_le_of_not_mem (s : Finset ℕ) {m : ℕ} (h : m ∉ s) : mex s ≤ m :=
  Nat.find_min' (exists_not_mem s) h

private theorem mem_of_lt_mex (s : Finset ℕ) {m : ℕ} (h : m < mex s) : m ∈ s := by
  by_contra hc
  exact absurd (mex_le_of_not_mem s hc) (not_le_of_gt h)

private theorem mex_empty : mex ∅ = 0 :=
  Nat.le_zero.mp (mex_le_of_not_mem _ (Finset.notMem_empty 0))

private theorem mex_range (n : ℕ) : mex (Finset.range n) = n := by
  apply Nat.le_antisymm
  · apply mex_le_of_not_mem
    rw [Finset.mem_range]
    exact Nat.lt_irrefl n
  · by_contra hle
    have hlt : mex (Finset.range n) < n := Nat.lt_of_not_ge hle
    have hmem : mex (Finset.range n) ∈ Finset.range n :=
      Finset.mem_range.mpr hlt
    exact mex_not_mem _ hmem

private noncomputable def grundy (G : ImpartialGame) : G.Pos → ℕ :=
  (wfRel G).fix fun p ih =>
    mex ((G.moves p).attach.image (fun x => ih x.val x.property))

private theorem grundy_eq (G : ImpartialGame) (p : G.Pos) :
    grundy G p =
      mex ((G.moves p).attach.image (fun x : { q // q ∈ G.moves p } => grundy G x.val)) := by
  unfold grundy
  rw [WellFounded.fix_eq]

private theorem exists_move_with_grundy (G : ImpartialGame) (p : G.Pos) {m : ℕ}
    (h : m < grundy G p) :
    ∃ q ∈ G.moves p, grundy G q = m := by
  have hmem : m ∈ ((G.moves p).attach.image
      (fun x : { q // q ∈ G.moves p } => grundy G x.val)) :=
    mem_of_lt_mex _ (grundy_eq G p ▸ h)
  rw [Finset.mem_image] at hmem
  obtain ⟨x, _, hxeq⟩ := hmem
  exact ⟨x.val, x.property, hxeq⟩

private theorem grundy_ne_of_mem (G : ImpartialGame) {p q : G.Pos}
    (h : q ∈ G.moves p) : grundy G q ≠ grundy G p := by
  intro heq
  have hmem : grundy G p ∈ ((G.moves p).attach.image
      (fun x : { qq // qq ∈ G.moves p } => grundy G x.val)) := by
    rw [← heq]
    exact Finset.mem_image.mpr ⟨⟨q, h⟩, Finset.mem_attach _ _, rfl⟩
  exact mex_not_mem _ (grundy_eq G p ▸ hmem)

private theorem nim_grundy_aux (n : ℕ) (v : ℕ) (k : Fin (n + 1)) (hk : k.val ≤ v) :
    grundy (nimHeap n) k = k.val := by
  induction v generalizing k with
  | zero =>
    have hk0 : k.val = 0 := by omega
    have him : ((nimHeap n).moves k).attach.image
        (fun x : { q // q ∈ (nimHeap n).moves k } => grundy (nimHeap n) x.val) =
        Finset.range k.val := by
      ext w
      simp only [Finset.mem_image, Finset.mem_attach, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨x, hx⟩
        have hmemFin : (x.val : Fin (n + 1)) ∈
            Finset.univ.filter (fun j : Fin (n + 1) => j.val < k.val) :=
          x.property
        have hmem := (Finset.mem_filter.mp hmemFin).2
        rw [hk0] at hmem
        exact absurd hmem (Nat.not_lt_zero _)
      · intro hw
        rw [hk0] at hw
        exact absurd hw (Nat.not_lt_zero _)
    have hge := grundy_eq (nimHeap n) k
    rw [hge, him, mex_range]
  | succ v ih =>
    have him : ((nimHeap n).moves k).attach.image
        (fun x : { q // q ∈ (nimHeap n).moves k } => grundy (nimHeap n) x.val) =
        Finset.range k.val := by
      ext w
      simp only [Finset.mem_image, Finset.mem_attach, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨x, hx⟩
        have hmemFin : (x.val : Fin (n + 1)) ∈
            Finset.univ.filter (fun j : Fin (n + 1) => j.val < k.val) :=
          x.property
        have hmem := (Finset.mem_filter.mp hmemFin).2
        have hlt : (x.val : Fin (n + 1)).val < v + 1 :=
          Nat.lt_of_lt_of_le hmem hk
        have hle : (x.val : Fin (n + 1)).val ≤ v :=
          Nat.le_of_lt_succ hlt
        have hgx : grundy (nimHeap n) (x.val : Fin (n + 1)) = (x.val : Fin (n + 1)).val :=
          ih (x.val : Fin (n + 1)) hle
        have hxw : (x.val : Fin (n + 1)).val = w := hgx.symm.trans hx
        rw [← hxw]
        exact hmem
      · intro hw
        have hkle : k.val ≤ n := Nat.le_of_lt_succ k.isLt
        have hlt : w < n + 1 := Nat.lt_of_lt_of_le hw (Nat.le_succ_of_le hkle)
        let j : Fin (n + 1) := ⟨w, hlt⟩
        have hmemFin : j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val < k.val) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        have hjmem : j ∈ (nimHeap n).moves k := hmemFin
        refine ⟨⟨j, hjmem⟩, ?_⟩
        have hle : (j : Fin (n + 1)).val ≤ v := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw hk)
        have hgj : grundy (nimHeap n) j = (j : Fin (n + 1)).val := ih j hle
        have hjw : (j : Fin (n + 1)).val = w := rfl
        rw [hjw] at hgj
        exact hgj
    have hge := grundy_eq (nimHeap n) k
    rw [hge, him, mex_range]

private theorem nim_grundy (n : ℕ) (k : Fin (n + 1)) :
    grundy (nimHeap n) k = k.val :=
  nim_grundy_aux n k.val k (Nat.le_refl _)

private theorem xor_eq_zero_iff {x y : ℕ} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have h2 : (x ^^^ y) ^^^ y = (0 : ℕ) ^^^ y := by rw [h]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at h2
    exact h2
  · intro h
    rw [h, Nat.xor_self]

private theorem sum_mem_left (G H : ImpartialGame) (a : G.Pos) (b : H.Pos)
    (a' : G.Pos) (h : a' ∈ G.moves a) :
    ((a', b) : (gameSum G H).Pos) ∈
      (gameSum G H).moves ((a, b) : (gameSum G H).Pos) := by
  let := G.eqDec
  let := H.eqDec
  change ((a', b) : G.Pos × H.Pos) ∈
    (G.moves a).image (fun a_1 => (a_1, b)) ∪
      (H.moves b).image (fun b_1 => (a, b_1))
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr ⟨a', h, rfl⟩

private theorem sum_mem_right (G H : ImpartialGame) (a : G.Pos) (b : H.Pos)
    (b' : H.Pos) (h : b' ∈ H.moves b) :
    ((a, b') : (gameSum G H).Pos) ∈
      (gameSum G H).moves ((a, b) : (gameSum G H).Pos) := by
  let := G.eqDec
  let := H.eqDec
  change ((a, b') : G.Pos × H.Pos) ∈
    (G.moves a).image (fun a_1 => (a_1, b)) ∪
      (H.moves b).image (fun b_1 => (a, b_1))
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨b', h, rfl⟩

private theorem sum_cases (G H : ImpartialGame) (a : G.Pos) (b : H.Pos)
    (q : (gameSum G H).Pos)
    (h : q ∈ (gameSum G H).moves ((a, b) : (gameSum G H).Pos)) :
    (∃ a', ∃ _ : a' ∈ G.moves a, q = ((a', b) : (gameSum G H).Pos)) ∨
      (∃ b', ∃ _ : b' ∈ H.moves b, q = ((a, b') : (gameSum G H).Pos)) := by
  let := (gameSum G H).eqDec
  have hdisj := Finset.mem_union.mp h
  cases hdisj with
  | inl hl =>
    obtain ⟨a', ha', heq⟩ := Finset.mem_image.mp hl
    exact Or.inl ⟨a', ha', heq.symm⟩
  | inr hr =>
    obtain ⟨b', hb', heq⟩ := Finset.mem_image.mp hr
    exact Or.inr ⟨b', hb', heq.symm⟩

private theorem IsP_sum_unfold (G H : ImpartialGame) (a : G.Pos) (b : H.Pos) :
    IsP (gameSum G H) ((a, b) : (gameSum G H).Pos) ↔
      ∀ q (_ : q ∈ (gameSum G H).moves ((a, b) : (gameSum G H).Pos)),
        ¬ IsP (gameSum G H) q :=
  isP_iff _ _

private theorem isP_sum_iff_aux (G H : ImpartialGame) (t : ℕ) (a : G.Pos) (b : H.Pos)
    (hle : G.rank a + H.rank b ≤ t) :
    IsP (gameSum G H) ((a, b) : (gameSum G H).Pos) ↔
      (grundy G a ^^^ grundy H b = 0) := by
  induction t generalizing a b with
  | zero =>
    have ha0 : G.rank a = 0 :=
      Nat.le_zero.mp (Nat.le_trans (Nat.le_add_right _ _) hle)
    have hb0 : H.rank b = 0 :=
      Nat.le_zero.mp (Nat.le_trans (Nat.le_add_left _ _) hle)
    have hemptyA : G.moves a = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hlt := G.rank_lt a x hx
      rw [ha0] at hlt
      exact absurd hlt (Nat.not_lt_zero _)
    have hemptyB : H.moves b = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hlt := H.rank_lt b x hx
      rw [hb0] at hlt
      exact absurd hlt (Nat.not_lt_zero _)
    have hsum_empty : (gameSum G H).moves ((a, b) : (gameSum G H).Pos) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro q hq
      have hc := sum_cases G H a b q hq
      cases hc with
      | inl hl =>
        obtain ⟨a', ha', -⟩ := hl
        rw [hemptyA] at ha'
        exact Finset.notMem_empty _ ha'
      | inr hr =>
        obtain ⟨b', hb', -⟩ := hr
        rw [hemptyB] at hb'
        exact Finset.notMem_empty _ hb'
    have hga : grundy G a = 0 := by
      have hge := grundy_eq G a
      rw [hemptyA] at hge
      have him : ((∅ : Finset G.Pos).attach.image
          (fun x : { q // q ∈ (∅ : Finset G.Pos) } => grundy G x.val)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        obtain ⟨x, _, -⟩ := Finset.mem_image.mp hy
        exact Finset.notMem_empty _ x.property
      rw [him, mex_empty] at hge
      exact hge
    have hgb : grundy H b = 0 := by
      have hge := grundy_eq H b
      rw [hemptyB] at hge
      have him : ((∅ : Finset H.Pos).attach.image
          (fun x : { q // q ∈ (∅ : Finset H.Pos) } => grundy H x.val)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        obtain ⟨x, _, -⟩ := Finset.mem_image.mp hy
        exact Finset.notMem_empty _ x.property
      rw [him, mex_empty] at hge
      exact hge
    have hl : IsP (gameSum G H) ((a, b) : (gameSum G H).Pos) := by
      rw [IsP_sum_unfold, hsum_empty]
      intro q hq
      exact absurd hq (Finset.notMem_empty q)
    have hr : grundy G a ^^^ grundy H b = 0 := by
      rw [hga, hgb, Nat.xor_self]
    exact iff_of_true hl hr
  | succ t ih =>
    rw [IsP_sum_unfold]
    constructor
    · intro hall
      by_contra hne
      have hxy : grundy G a ≠ grundy H b := by
        intro heq
        apply hne
        rw [heq, Nat.xor_self]
      have htri := lt_trichotomy (grundy G a) (grundy H b)
      cases htri with
      | inl hlt =>
        obtain ⟨b', hb', hgb⟩ := exists_move_with_grundy H b hlt
        have hq := sum_mem_right G H a b b' hb'
        have hlt2 : G.rank a + H.rank b' < G.rank a + H.rank b :=
          Nat.add_lt_add_left (H.rank_lt b b' hb') _
        have hle' : G.rank a + H.rank b' ≤ t :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt2 hle)
        have hi := ih a b' hle'
        have hxor0 : grundy G a ^^^ grundy H b' = 0 := by
          rw [hgb, Nat.xor_self]
        have hP : IsP (gameSum G H) ((a, b') : (gameSum G H).Pos) := hi.mpr hxor0
        exact hall _ hq hP
      | inr hrest =>
        cases hrest with
        | inl heq => exact hxy heq
        | inr hgt =>
          obtain ⟨a', ha', hga⟩ := exists_move_with_grundy G a hgt
          have hq := sum_mem_left G H a b a' ha'
          have hlt2 : G.rank a' + H.rank b < G.rank a + H.rank b :=
            Nat.add_lt_add_right (G.rank_lt a a' ha') _
          have hle' : G.rank a' + H.rank b ≤ t :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt2 hle)
          have hi := ih a' b hle'
          have hxor0 : grundy G a' ^^^ grundy H b = 0 := by
            rw [hga, Nat.xor_self]
          have hP : IsP (gameSum G H) ((a', b) : (gameSum G H).Pos) := hi.mpr hxor0
          exact hall _ hq hP
    · intro hxor q hq hP
      have hc := sum_cases G H a b q hq
      cases hc with
      | inl hl =>
        obtain ⟨a', ha', heq⟩ := hl
        have hlt2 : G.rank a' + H.rank b < G.rank a + H.rank b :=
          Nat.add_lt_add_right (G.rank_lt a a' ha') _
        have hle2 : G.rank a' + H.rank b ≤ t :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt2 hle)
        have hi := ih a' b hle2
        rw [heq] at hP
        have ha0 : grundy G a' ^^^ grundy H b = 0 := hi.mp hP
        have hea : grundy G a' = grundy H b := xor_eq_zero_iff.mp ha0
        have hxx : grundy G a = grundy H b := xor_eq_zero_iff.mp hxor
        have hne : grundy G a' ≠ grundy G a := grundy_ne_of_mem G ha'
        exact hne (hea.trans hxx.symm)
      | inr hr =>
        obtain ⟨b', hb', heq⟩ := hr
        have hlt2 : G.rank a + H.rank b' < G.rank a + H.rank b :=
          Nat.add_lt_add_left (H.rank_lt b b' hb') _
        have hle2 : G.rank a + H.rank b' ≤ t :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt2 hle)
        have hi := ih a b' hle2
        rw [heq] at hP
        have hb0 : grundy G a ^^^ grundy H b' = 0 := hi.mp hP
        have heb : grundy G a = grundy H b' := xor_eq_zero_iff.mp hb0
        have hxx : grundy G a = grundy H b := xor_eq_zero_iff.mp hxor
        have hne : grundy H b' ≠ grundy H b := grundy_ne_of_mem H hb'
        exact hne (heb.symm.trans hxx)

private theorem isP_sum_iff (G H : ImpartialGame) (a : G.Pos) (b : H.Pos) :
    IsP (gameSum G H) ((a, b) : (gameSum G H).Pos) ↔
      (grundy G a ^^^ grundy H b = 0) :=
  isP_sum_iff_aux G H _ a b (Nat.le_refl _)

/-- **Sprague–Grundy theorem.** Every impartial game $G$ is equivalent to a Nim heap: there is a
natural number $n$ such that $G$ is equivalent to the Nim heap of size $n$.

Source: Tanya Khovanova and Joshua Xiong, "Nim Fractals", Journal of Integer
Sequences 17 (2014), lines 101–105,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Khovanova/khova6.tex ;
complete SHA-256 `6f8be9d461ff98b5a7c878830eb169e69ba8dd7540948d9149527fdb5ca7783a`;
normalized span SHA-256 `2228effe253846e7f994ee9ae1695b5a830e5686148e5d9287d1b04eae55fec6`.
Its cited original references: Grundy, Eureka 2 (1939), 6–8, reprinted 27 (1964),
9–11; Sprague, Tôhoku Math. Journal 41 (1935–1936), 438–444.

Proves `Wanted` entry `sprague_grundy`.
-/
theorem sprague_grundy (G : ImpartialGame) :
    ∃ n : ℕ, Equiv G (nimHeap n) := by
  refine ⟨grundy G G.start, fun K => ?_⟩
  have hG := isP_sum_iff G K G.start K.start
  have hN := isP_sum_iff (nimHeap (grundy G G.start)) K
    ((nimHeap (grundy G G.start)).start) K.start
  have hnim : grundy (nimHeap (grundy G G.start))
      ((nimHeap (grundy G G.start)).start) = grundy G G.start := by
    have h := nim_grundy (grundy G G.start) ((nimHeap (grundy G G.start)).start)
    exact h
  rw [hnim] at hN
  exact hG.trans hN.symm

end MetaMathlibExt.SpragueGrundy
