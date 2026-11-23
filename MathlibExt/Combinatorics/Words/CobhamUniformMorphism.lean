/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import MathlibExt.Combinatorics.InfiniteWord.MorphicWord
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.Logic.Function.CompTypeclasses

@[expose] public section

/-!
# Cobham: `k`-automatic sequences are codings of prolongable `k`-uniform fixed points

The one-base characterization (stable ID
`jis_grounded_7ab6fb1531d4463cd12a1a80`). This is not the distinct two-base
periodicity theorem.

Provenance: Sunic, JIS VOL10,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Sunic/cubefree.tex>,
file SHA-256
`ef2bc04940dde383128c102334a4c332443a2124706971b1bcf3b50bd2fd5c9b`;
Stipulanti, JIS VOL21,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Stipulanti/stip8.tex>,
file SHA-256
`a535e42b1e5cfcbd668a44b952035dd8b647208ec35ddf93dfa245c04b1528c2`.
-/

section
namespace MetaMathlibExt

/-- **Value of a base-$k$ digit word, least significant digit first.** For a natural number $k$,
the value of a finite word $d_0 d_1 \cdots d_{m-1}$ of digits $d_i \in \{0, 1, \dots, k-1\}$ is
the natural number $\sum_{i < m} d_i k^i$, so the first digit is the least significant one; the
empty word has value $0$.

Source: Sunic selects least-significant-digit reading with tolerance of trailing
high-order zeros: lines 562-567 of `cubefree.tex`, span SHA-256
`e7c8c89ab0663ef3fe4e59fcb7a16bcf952104852337ffbdab1ed42fc6c20921`. -/
def baseWordValueLSD {k : Nat} (ds : List (Fin k)) : Nat :=
  ds.foldr (fun d acc => d.val + k * acc) 0

/-- **Automatic sequences via finite automata.** Let $k$ be a natural number and $B$ a finite
alphabet. A sequence $w : \mathbb{N} \to B$ is $k$-automatic when $k \ge 2$ and there is a
deterministic finite automaton with output, consisting of a nonempty finite set of states $Q$, an
initial state $s \in Q$, a transition map $\delta : Q \times \{0, 1, \dots, k-1\} \to Q$ and an
output map $\tau : Q \to B$, such that for every $n \in \mathbb{N}$ and every finite word
$d_0 d_1 \cdots d_{m-1}$ of digits in $\{0, 1, \dots, k-1\}$ with $\sum_{i < m} d_i k^i = n$, the
automaton started in $s$ and reading $d_0, d_1, \dots, d_{m-1}$ in this order (least significant
digit first) stops in a state $t$ with $\tau(t) = w(n)$.

Source: Sunic Definition 3, lines 556-560 of `cubefree.tex`, span SHA-256
`fd6739cecadd7bfc1b66a49c39db59b2a267e85abb0abf5556bac6b533f3330b`.
The universal clause over all representing words enforces tolerance of
trailing high-order zeros. -/
def IsKAutomaticSequence {B : Type} [Fintype B] (k : Nat) (w : Nat → B) : Prop :=
  2 ≤ k ∧
    ∃ q : Nat, 0 < q ∧
      ∃ start : Fin q,
        ∃ trans : Fin q → Fin k → Fin q,
          ∃ out : Fin q → B,
            ∀ n : Nat, ∀ ds : List (Fin k),
              baseWordValueLSD ds = n → out (ds.foldl trans start) = w n

/-- **Codings of prolongable uniform fixed points.** Let $k$ be a natural number and $B$ a finite
alphabet. A sequence $w : \mathbb{N} \to B$ is a coding of a prolongable $k$-uniform fixed point
when $k \ge 2$ and there are a nonempty finite alphabet $A$, a map $f$ sending each letter of $A$
to a word of length exactly $k$ over $A$, a letter $a \in A$ with $f(a) = a\alpha$ for some
nonempty word $\alpha$ over $A$, a sequence $u : \mathbb{N} \to A$ and a map $g : A \to B$ such
that $u(0) = a$, the letter of $f(u(n))$ at position $j$ (counted from $0$) is $u(kn + j)$ for
all $n \in \mathbb{N}$ and $j < k$, and $w(n) = g(u(n))$ for all $n \in \mathbb{N}$.

The conditions on $u$ say that $u$ begins with $a$ and is fixed by $f$ applied letter by letter.

Source: Sunic lines 569-584 state the equivalence and define prolongability and
uniformity (`cubefree.tex`, span SHA-256
`f618b2151d7a9680b94b6865bd471b1375fb23b387579b274c1e3174b9591763`);
Stipulanti lines 164-174 define morphism, coding, prolongability, and fixed
point (`stip8.tex`, span SHA-256
`cbafa712ca06a7c28b1c8cd9f5d425c3b6fc518d168a321d79aed28293c2d651`). -/
def IsCodingOfProlongableKUniformFixedPoint {B : Type} [Fintype B] (k : Nat)
    (w : Nat → B) : Prop :=
  2 ≤ k ∧
    ∃ q : Nat, 0 < q ∧
      ∃ f : Fin q → List (Fin q), (∀ a : Fin q, (f a).length = k) ∧
        ∃ a : Fin q, ∃ tl : List (Fin q), tl ≠ [] ∧ f a = a :: tl ∧
          ∃ u : Nat → Fin q, u 0 = a ∧
            (∀ n : Nat, ∀ j : Nat, j < k → (f (u n)).getD j a = u (k * n + j)) ∧
              ∃ g : Fin q → B, ∀ n : Nat, w n = g (u n)

/-- Canonical least-significant-digit-first expansion of `n` in base `k`. -/
private def repList {k : Nat} (hk : 2 ≤ k) : Nat → List (Fin k)
  | 0 => []
  | n + 1 => ⟨(n + 1) % k, Nat.mod_lt _ (by omega)⟩ :: repList hk ((n + 1) / k)
termination_by n => n
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) (by omega)

private theorem repVal {k : Nat} (hk : 2 ≤ k) (n : Nat) :
    baseWordValueLSD (repList hk n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; rw [repList.eq_1]; rfl
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
      have hmem : (m + 1) / k < m + 1 :=
        Nat.div_lt_self (Nat.succ_pos _) (by omega)
      rw [repList.eq_2 hk m]
      change _ + k * baseWordValueLSD (repList hk ((m + 1) / k)) = _
      rw [ih _ hmem]
      exact Nat.mod_add_div _ _

private theorem repCons {k : Nat} (hk : 2 ≤ k) (n j : Nat) (hj : j < k)
    (hne : k * n + j ≠ 0) :
    repList hk (k * n + j) = ⟨j, hj⟩ :: repList hk n := by
  have hk0 : 0 < k := by omega
  have hmod : (k * n + j) % k = j := by
    rw [add_comm (k * n) j, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hdiv : (k * n + j) / k = n := by
    rw [mul_comm k n, add_comm (n * k) j, Nat.add_mul_div_right j n hk0,
      Nat.div_eq_of_lt hj, zero_add]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have e1 : repList hk m.succ =
      ⟨m.succ % k, Nat.mod_lt _ (by omega)⟩ :: repList hk (m.succ / k) :=
    repList.eq_2 hk m
  rw [← hm] at e1
  rw [e1]
  simp only [hmod, hdiv]

/-- Composition of block maps along a digit word (least significant first). -/
private def morphComp {q k : Nat} (f : Fin q → List (Fin q)) (a : Fin q)
    (ds : List (Fin k)) : Fin q → Fin q :=
  ds.foldr (fun d F => (fun s => (f s).getD d.val a) ∘ F) id

/-- Automaton transition on function states for the backward direction. -/
private def autoTrans {q k q' : Nat} (f : Fin q → List (Fin q)) (a : Fin q)
    (e : (Fin q → Fin q) ≃ Fin q') : Fin q' → Fin k → Fin q' :=
  fun G d => e ((e.symm G) ∘ (fun s => (f s).getD d.val a))

private theorem morphComp_val {q k : Nat} (f : Fin q → List (Fin q)) (a : Fin q)
    (u : Nat → Fin q) (hu0 : u 0 = a)
    (hblock : ∀ n : Nat, ∀ j : Nat, j < k → (f (u n)).getD j a = u (k * n + j))
    (ds : List (Fin k)) :
    morphComp f a ds a = u (baseWordValueLSD ds) := by
  induction ds with
  | nil =>
    have hA : morphComp f a ([] : List (Fin k)) a = a := rfl
    have hB : baseWordValueLSD ([] : List (Fin k)) = 0 := rfl
    rw [hA, hB]; exact hu0.symm
  | cons d ds ih =>
    have h1 : baseWordValueLSD (d :: ds) = d.val + k * baseWordValueLSD ds := rfl
    change ((fun s => (f s).getD ↑d a) ∘ morphComp f a ds) a = _
    simp only [Function.comp_apply]
    rw [h1, ih, hblock _ _ d.is_lt, add_comm (k * baseWordValueLSD ds)]

private theorem foldlEq {q k q' : Nat} (f : Fin q → List (Fin q)) (a : Fin q)
    (e : (Fin q → Fin q) ≃ Fin q')
    (ds : List (Fin k)) (F : Fin q → Fin q) :
    ds.foldl (autoTrans f a e) (e F) = e (F ∘ morphComp f a ds) := by
  induction ds generalizing F with
  | nil => simp [morphComp]
  | cons d ds ih =>
    rw [List.foldl_cons]
    simp only [autoTrans]
    rw [Equiv.symm_apply_apply, ih]
    have hC : morphComp f a (d :: ds) =
        (fun s => (f s).getD ↑d a) ∘ morphComp f a ds := by
      simp only [morphComp, List.foldr_cons]
    rw [hC, Function.comp_assoc]

private theorem auto_of_morphic {B : Type} [Fintype B] {k : Nat} (w : Nat → B)
    (h : IsCodingOfProlongableKUniformFixedPoint k w) :
    IsKAutomaticSequence k w := by
  obtain ⟨hk, q, _hq, f, _hlen, a, _tl, _htl, _hfa, u, hu0, hblock, g, hg⟩ := h
  classical
  refine ⟨hk, Fintype.card (Fin q → Fin q), Fintype.card_pos_iff.mpr ⟨id⟩,
    Fintype.equivFin (Fin q → Fin q) id,
    autoTrans f a (Fintype.equivFin (Fin q → Fin q)),
    fun G => g ((Fintype.equivFin (Fin q → Fin q)).symm G a), ?_⟩
  intro n ds hds
  have hfold := foldlEq f a (Fintype.equivFin (Fin q → Fin q)) ds id
  have hC := morphComp_val f a u hu0 hblock ds
  rw [hds] at hC
  change g ((Fintype.equivFin (Fin q → Fin q)).symm
    (ds.foldl (autoTrans f a (Fintype.equivFin (Fin q → Fin q)))
      (Fintype.equivFin (Fin q → Fin q) id)) a) = w n
  simp only [hfold, Equiv.symm_apply_apply, Function.comp_apply, id_eq]
  rw [hC, hg n]



/-- Run an automaton from a given state along a digit word. -/
private def runFrom {q k : Nat} (trans : Fin q → Fin k → Fin q) (s : Fin q)
    (ds : List (Fin k)) : Fin q :=
  ds.foldl trans s

/-- Block map of a single digit. -/
private def transFn {q k : Nat} (trans : Fin q → Fin k → Fin q) (d : Fin k) :
    Fin q → Fin q :=
  fun s => trans s d

/-- Image of a function-state under one digit; `Option.none` is the fresh start. -/
private def imgAbove {q k : Nat} (trans : Fin q → Fin k → Fin q)
    (G : Option (Fin q → Fin q)) (d : Fin k) : Option (Fin q → Fin q) :=
  match G with
  | Option.none => if d.val = 0 then Option.none else Option.some (transFn trans d)
  | Option.some F => Option.some (F ∘ transFn trans d)

private theorem imgAbove_none {q k : Nat} (trans : Fin q → Fin k → Fin q)
    (d : Fin k) :
    imgAbove trans Option.none d =
      if d.val = 0 then Option.none else Option.some (transFn trans d) := rfl

private theorem imgAbove_some {q k : Nat} (trans : Fin q → Fin k → Fin q)
    (F : Fin q → Fin q) (d : Fin k) :
    imgAbove trans (Option.some F) d = Option.some (F ∘ transFn trans d) := rfl

/-- Morphism on coded states: `k` images, one per digit. -/
private def morphImg {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
    (e : Option (Fin q → Fin q) ≃ Fin q') : Fin q' → List (Fin q') :=
  fun G => List.ofFn (fun d : Fin k => e (imgAbove trans (e.symm G) d))

private theorem ofFn_getD {n : Nat} {α : Type} (f : Fin n → α) (j : Nat) (hj : j < n)
    (d : α) :
    (List.ofFn f).getD j d = f ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]



private theorem morphImg_eq {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
    (e : Option (Fin q → Fin q) ≃ Fin q') (G : Fin q') :
    morphImg trans e G =
      List.ofFn (fun d : Fin k => e (imgAbove trans (e.symm G) d)) := rfl

/-- Fixed point: fresh start at `0`, runs of canonical expansions elsewhere. -/
private def morphFix {q k q' : Nat} (trans : Fin q → Fin k → Fin q) (hk : 2 ≤ k)
    (e : Option (Fin q → Fin q) ≃ Fin q') : Nat → Fin q' :=
  fun n => e (if n = 0 then Option.none
    else Option.some (fun s => runFrom trans s (repList hk n)))

private theorem morphFix_zero {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
    (hk : 2 ≤ k) (e : Option (Fin q → Fin q) ≃ Fin q') :
    morphFix trans hk e 0 = e Option.none := rfl

private theorem morphFix_ne {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
    (hk : 2 ≤ k) (e : Option (Fin q → Fin q) ≃ Fin q') (n : Nat)
    (hne : n ≠ 0) :
    morphFix trans hk e n =
      e (Option.some (fun s => runFrom trans s (repList hk n))) := by
  simp only [morphFix, ite_eq_right hne]

/-- The block law for the constructed fixed point. -/
private theorem blockLaw {q k q' : Nat} (trans : Fin q → Fin k → Fin q) (hk : 2 ≤ k)
    (e : Option (Fin q → Fin q) ≃ Fin q') (n j : Nat) (hj : j < k) :
    (morphImg trans e (morphFix trans hk e n)).getD j (e Option.none)
      = morphFix trans hk e (k * n + j) := by
  have hget : (morphImg trans e (morphFix trans hk e n)).getD j (e Option.none)
      = e (imgAbove trans (e.symm (morphFix trans hk e n)) ⟨j, hj⟩) := by
    rw [morphImg_eq]
    exact ofFn_getD _ j hj _
  rw [hget]
  by_cases hn : n = 0
  · subst hn
    have hs : e.symm (morphFix trans hk e 0) = Option.none := by
      rw [morphFix_zero, Equiv.symm_apply_apply]
    rw [hs]
    by_cases hj0 : j = 0
    · subst hj0
      have hi : ∀ d : Fin k, d.val = 0 →
          imgAbove trans Option.none d = Option.none := by
        intro d hd
        rw [imgAbove_none, ite_eq_left hd]
      have hkj : k * 0 + 0 = 0 := by omega
      rw [hi _ rfl, hkj, morphFix_zero]
    · have hi2 : imgAbove trans Option.none ⟨j, hj⟩ =
          Option.some (transFn trans ⟨j, hj⟩) := by
        have hj0' : (⟨j, hj⟩ : Fin k).val ≠ 0 := hj0
        rw [imgAbove_none, ite_eq_right hj0']
      have hkj : k * 0 + j = j := by omega
      have hrep : repList hk j = [⟨j, hj⟩] := by
        have h0 : k * 0 + j ≠ 0 := by omega
        have h1 := repCons hk 0 j hj h0
        rw [hkj, repList.eq_1 hk] at h1
        exact h1
      rw [hi2, hkj, morphFix_ne trans hk e j hj0, hrep]
      apply congrArg e
      apply congrArg Option.some
      funext s
      rfl
  · have hs : e.symm (morphFix trans hk e n)
        = Option.some (fun s => runFrom trans s (repList hk n)) := by
      rw [morphFix_ne trans hk e n hn, Equiv.symm_apply_apply]
    rw [hs, imgAbove_some]
    have hne : k * n + j ≠ 0 := by
      intro hcon
      have hkn : k * n = 0 := by omega
      rcases Nat.mul_eq_zero.mp hkn with hk0 | hn0
      · omega
      · exact hn hn0
    rw [morphFix_ne trans hk e (k * n + j) hne, repCons hk n j hj hne]
    apply congrArg e
    apply congrArg Option.some
    funext s
    rfl

/-- The fresh start letter is prolongable. -/
private theorem morphImg_prol {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
    (hk : 2 ≤ k) (e : Option (Fin q → Fin q) ≃ Fin q') :
    ∃ tl : List (Fin q'), tl ≠ [] ∧
      morphImg trans e (e Option.none) = e Option.none :: tl := by
  have hL : (morphImg trans e (e Option.none)).length = k := by
    rw [morphImg_eq, List.length_ofFn]
  have hnil : morphImg trans e (e Option.none) ≠ [] := by
    rw [List.ne_nil_iff_length_pos, hL]
    omega
  refine ⟨(morphImg trans e (e Option.none)).tail, ?_, ?_⟩
  · rw [List.ne_nil_iff_length_pos, List.length_tail, hL]
    omega
  · have hhead : (morphImg trans e (e Option.none)).head hnil
        = e Option.none := by
      have h0 : ∀ d : Fin k, d.val = 0 →
          e (imgAbove trans Option.none d) = e Option.none := by
        intro d hd
        rw [imgAbove_none, ite_eq_left hd]
      have hnil' : List.ofFn
          (fun d : Fin k => e (imgAbove trans (e.symm (e Option.none)) d))
            ≠ [] := hnil
      have h1 : (morphImg trans e (e Option.none)).head hnil =
          (fun d : Fin k => e (imgAbove trans (e.symm (e Option.none)) d))
            ⟨0, by omega⟩ := List.head_ofFn hnil'
      rw [h1]
      change e (imgAbove trans (e.symm (e Option.none)) _) = e Option.none
      rw [Equiv.symm_apply_apply]
      exact h0 _ rfl
    have hcons := List.cons_head_tail hnil
    rw [hhead] at hcons
    exact hcons.symm

private theorem morphic_of_auto {B : Type} [Fintype B] {k : Nat} (w : Nat → B)
    (h : IsKAutomaticSequence k w) :
    IsCodingOfProlongableKUniformFixedPoint k w := by
  obtain ⟨hk, q, _hq, start, trans, out, hauto⟩ := h
  classical
  have hlen : ∀ G : Fin (Fintype.card (Option (Fin q → Fin q))),
      (morphImg trans (Fintype.equivFin (Option (Fin q → Fin q))) G).length
        = k := by
    intro G
    rw [morphImg_eq, List.length_ofFn]
  obtain ⟨tl, htl, hfa⟩ :=
    morphImg_prol trans hk (Fintype.equivFin (Option (Fin q → Fin q)))
  refine ⟨hk, Fintype.card (Option (Fin q → Fin q)),
    Fintype.card_pos_iff.mpr ⟨Option.none⟩,
    morphImg trans (Fintype.equivFin (Option (Fin q → Fin q))), hlen,
    Fintype.equivFin (Option (Fin q → Fin q)) Option.none, tl, htl, hfa,
    morphFix trans hk (Fintype.equivFin (Option (Fin q → Fin q))), ?_, ?_, ?_⟩
  · exact morphFix_zero trans hk _
  · intro n j hj
    exact blockLaw trans hk _ n j hj
  · refine ⟨fun G =>
        match (Fintype.equivFin (Option (Fin q → Fin q))).symm G with
        | Option.none => w 0
        | Option.some F => out (F start), ?_⟩
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [morphFix_zero]
      simp only [Equiv.symm_apply_apply]
    · rw [morphFix_ne trans hk _ n hn]
      simp only [Equiv.symm_apply_apply]
      show w n = out (runFrom trans start (repList hk n))
      exact (hauto n (repList hk n) (repVal hk n)).symm

set_option linter.unusedVariables false in
/-- **Cobham's characterization of automatic sequences.** Let $k \ge 2$ and let $B$ be a finite
alphabet. A sequence $w : \mathbb{N} \to B$ is $k$-automatic if and only if it is a coding of a
prolongable $k$-uniform fixed point.

Proves `Wanted` entry `cobham_automatic_iff_uniform_morphic`.

Source: Stipulanti lines 212-217 state the exact theorem (`stip8.tex`, span SHA-256
`f70b1a34e9a990c0d579ca451a899f834f58c1aecf4c2d30533e373da6b88854`); its
Cobham72 bibliography entry is line 1275, span SHA-256
`dbdcb42ca999b63fd976e953cd494b5d7a7e438a6bb245e621f52c5ebfac7636`.
-/
theorem cobham_automatic_iff_uniform_morphic {B : Type} [Fintype B]
    {k : Nat} (w : Nat → B) (hk : 2 ≤ k) :
    IsKAutomaticSequence k w ↔ IsCodingOfProlongableKUniformFixedPoint k w := by
  constructor
  · intro h
    exact morphic_of_auto w h
  · intro h
    exact auto_of_morphic w h

private theorem getElem?_flatMap_uniform {A : Type*} {k : Nat} {f : A → List A}
    (hlen : ∀ x, (f x).length = k) (l : List A) (m j : Nat) (hj : j < k) :
    (l.flatMap f)[k * m + j]? = l[m]?.bind fun x => (f x)[j]? := by
  induction l generalizing m with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons]
    cases m with
    | zero => simp [List.getElem?_append_left (hlen x ▸ hj)]
    | succ m =>
      rw [List.getElem?_append_right (by
          rw [hlen]; exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_right k (Nat.succ_pos m))),
        hlen, List.getElem?_cons_succ, ← ih]
      congr 1
      rw [Nat.mul_succ]
      omega

private theorem flatMap_map_range {q k : Nat} {f : Fin q → List (Fin q)} {a : Fin q}
    {u : Nat → Fin q} (hlen : ∀ x, (f x).length = k)
    (hblock : ∀ n j : Nat, j < k → (f (u n)).getD j a = u (k * n + j)) (m : Nat) :
    ((List.range m).map u).flatMap f = (List.range (k * m)).map u := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfu : f (u m) = (List.range k).map fun j => u (k * m + j) := by
      refine List.ext_getElem (by simp [hlen]) fun j h1 _ => ?_
      rw [← List.getD_eq_getElem _ a h1, hblock m j (hlen (u m) ▸ h1)]
      simp
    rw [List.range_succ, List.map_append, List.flatMap_append, ih, Nat.mul_succ, List.range_add,
      List.map_append, List.map_map]
    simp [hfu, Function.comp_def]

/-- **Uniform fixed-point codings via iterates of a uniform map.** Let $k \ge 2$ and let $B$
be a finite alphabet. A sequence $w : \mathbb{N} \to B$ is a coding of a prolongable $k$-uniform
fixed point if and only if there are a natural number $q$, a map $f$ sending each letter of the
alphabet $A = \{0, 1, \dots, q-1\}$ to a word of length exactly $k$ over $A$, a letter $a \in A$,
an infinite word $u$ over $A$ and a map $g : A \to B$ such that $f$ is prolongable at $a$, $u$ is
the limit of the iterates of $f$ at $a$, and $w(n) = g(u(n))$ for every $n \in \mathbb{N}$. -/
theorem isCodingOfProlongableKUniformFixedPoint_iff {B : Type} [Fintype B] {k : Nat}
    (w : Nat → B) (hk : 2 ≤ k) :
    IsCodingOfProlongableKUniformFixedPoint k w ↔
      ∃ q : Nat, ∃ f : Fin q → List (Fin q), (∀ x, (f x).length = k) ∧
        ∃ a : Fin q, ∃ u : Nat → Fin q, ∃ g : Fin q → B,
          IsPrefixPreserving f a ∧ IsOmegaLimit f a u ∧ ∀ n, w n = g (u n) := by
  constructor
  · rintro ⟨-, q, -, f, hlen, a, tl, htl, hfa, u, hu0, hblock, g, hg⟩
    have hL : ∀ n, morphIterate f n [a] = (List.range (k ^ n)).map u := by
      intro n
      induction n with
      | zero => simp [morphIterate, hu0]
      | succ n ih =>
        rw [morphIterate, ih, morphExtend, flatMap_map_range hlen hblock, pow_succ, mul_comm]
    refine ⟨q, f, hlen, a, u, g, ⟨tl, hfa, fun n => ?_⟩, ⟨fun M => ⟨M, ?_⟩, fun n i h => ?_⟩, hg⟩
    · rw [← List.length_pos_iff, morphIterate_length_of_uniform hlen]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) (List.length_pos_iff.2 htl)
    · rw [hL, List.length_map, List.length_range]
      exact (Nat.lt_pow_self hk).le
    · simp [hL]
  · rintro ⟨q, f, hlen, a, u, g, ⟨tl, hfa, -⟩, ⟨-, hlim⟩, hg⟩
    have hL : ∀ n, morphIterate f n [a] = (List.range (k ^ n)).map u := fun n =>
      List.ext_getElem (by simp [morphIterate_length_of_uniform hlen]) fun i h1 _ => by
        simp [← hlim n i h1]
    refine ⟨hk, q, Fin.pos a, f, hlen, a, tl, ?_, hfa, u, ?_, fun m j hj => ?_, g, hg⟩
    · rintro rfl
      have := hlen a
      simp [hfa] at this
      omega
    · simpa [morphIterate] using (hlim 0 0 (by simp [morphIterate])).symm
    · have hm : m < k ^ m := Nat.lt_pow_self hk
      have hkm : k * m + j < k ^ (m + 1) := by
        rw [pow_succ, Nat.mul_comm k m]
        calc m * k + j < m * k + k := Nat.add_lt_add_left hj _
          _ = (m + 1) * k := (Nat.succ_mul m k).symm
          _ ≤ k ^ m * k := Nat.mul_le_mul_right k hm
      have key := getElem?_flatMap_uniform hlen (morphIterate f m [a]) m j hj
      rw [← morphExtend, ← morphIterate, hL, hL] at key
      have hj' : (f (u m))[j]? = some (u (k * m + j)) := by simpa [hm, hkm] using key.symm
      rw [List.getD_eq_getElem?_getD, hj']
      rfl

/-- **Uniform fixed-point codings are morphic.** Let $k$ be a natural number and $B$ a finite
alphabet. If a sequence $w : \mathbb{N} \to B$ is a coding of a prolongable $k$-uniform fixed
point, then there are a natural number $q$, an infinite word $u$ over the alphabet
$A = \{0, 1, \dots, q-1\}$ and a map $g : A \to B$ such that $w$ is morphic with generator $u$
and coding $g$. -/
theorem IsCodingOfProlongableKUniformFixedPoint.exists_isMorphic {B : Type} [Fintype B]
    {k : Nat} {w : Nat → B} (h : IsCodingOfProlongableKUniformFixedPoint k w) :
    ∃ q : Nat, ∃ u : Nat → Fin q, ∃ g : Fin q → B, IsMorphic u g w := by
  obtain ⟨q, f, -, a, u, g, hpre, hlim, hg⟩ :=
    (isCodingOfProlongableKUniformFixedPoint_iff w h.1).1 h
  exact ⟨q, u, g, ⟨f, a, hpre, hlim⟩, hg⟩

/-- **Automatic sequences are morphic.** Let $k$ be a natural number and $B$ a finite alphabet.
If a sequence $w : \mathbb{N} \to B$ is $k$-automatic, then there are a natural number $q$, an
infinite word $u$ over the alphabet $A = \{0, 1, \dots, q-1\}$ and a map $g : A \to B$ such that
$w$ is morphic with generator $u$ and coding $g$. -/
theorem IsKAutomaticSequence.exists_isMorphic {B : Type} [Fintype B] {k : Nat} {w : Nat → B}
    (h : IsKAutomaticSequence k w) :
    ∃ q : Nat, ∃ u : Nat → Fin q, ∃ g : Fin q → B, IsMorphic u g w :=
  ((cobham_automatic_iff_uniform_morphic w h.1).1 h).exists_isMorphic

end MetaMathlibExt
