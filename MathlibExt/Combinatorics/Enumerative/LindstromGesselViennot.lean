/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

/-- First-occurrence split. -/
private theorem lgv_firstSplit {V : Type*} (l : List V) (v : V) (h : v ∈ l) :
    ∃ A B, l = A ++ v :: B ∧ ∀ u ∈ A, u ≠ v := by
  revert h
  induction l with
  | nil => intro h; simp at h
  | cons x xs ih =>
    intro h
    rw [List.mem_cons] at h
    rcases h with rfl | hmem
    · exact ⟨[], xs, rfl, by simp⟩
    · by_cases hx : x = v
      · subst hx
        exact ⟨[], xs, rfl, by simp⟩
      · obtain ⟨A, B, hAB, hfirst⟩ := ih hmem
        refine ⟨x :: A, B, by rw [hAB, List.cons_append], ?_⟩
        intro u hu
        rw [List.mem_cons] at hu
        rcases hu with hua | hu
        · rw [hua]; exact hx
        · exact hfirst u hu

/-- Uniqueness of first-occurrence splits. -/
private theorem lgv_firstSplit_unique {V : Type*} {v : V} {l A B A' B' : List V}
    (h : l = A ++ v :: B) (hA : ∀ u ∈ A, u ≠ v)
    (h' : l = A' ++ v :: B') (hA' : ∀ u ∈ A', u ≠ v) : A = A' ∧ B = B' := by
  revert l A' B B' h hA h' hA'
  induction A with
  | nil =>
    -- binders come back in creation order: l, B, A', B'
    intro l B A' B' h hA h' hA'
    cases A' with
    | nil =>
      have hBB : B = B' := by
        have h2 := h.symm.trans h'
        simpa using h2
      exact ⟨rfl, hBB⟩
    | cons a rest =>
      have hcc := h'.symm.trans h
      simp only [List.cons_append] at hcc
      have hcc2 : a = v ∧ rest ++ v :: B' = B := by simpa using hcc
      exact absurd hcc2.1 (hA' a (by simp))
  | cons a A ih =>
    intro l B A' B' h hA h' hA'
    cases A' with
    | nil =>
      have hcc := h.symm.trans h'
      simp only [List.cons_append] at hcc
      have hcc2 : a = v ∧ A ++ v :: B = B' := by simpa using hcc
      exact absurd hcc2.1 (hA a (by simp))
    | cons a' rest =>
      have hcc := h.symm.trans h'
      simp only [List.cons_append] at hcc
      have hcc2 : a = a' ∧ A ++ v :: B = rest ++ v :: B' := by simpa using hcc
      obtain ⟨haa, htail⟩ := hcc2
      subst haa
      obtain ⟨rfl, rfl⟩ := ih (l := A ++ v :: B) (B := B) (A' := rest) (B' := B') rfl
        (fun u hu => hA u (List.mem_cons_of_mem _ hu))
        htail
        (fun u hu => hA' u (List.mem_cons_of_mem _ hu))
      exact ⟨rfl, rfl⟩

/-- Ranks strictly increase before the split vertex. -/
private theorem lgv_rank_before {V : Type*} (E : V → V → Prop) (rank : V → ℕ)
    (hAcyc : ∀ u v, E u v → rank u < rank v)
    (A : List V) (v : V) (B : List V) (hchain : (A ++ v :: B).IsChain E) :
    ∀ u ∈ A, rank u < rank v := by
  revert hchain
  induction A with
  | nil => intro hchain u hu; simp at hu
  | cons a A ih =>
    intro hchain u hu
    simp only [List.cons_append] at hchain
    rw [List.isChain_cons] at hchain
    obtain ⟨hlink, htail⟩ := hchain
    rw [List.mem_cons] at hu
    rcases hu with hua | huA
    · rw [hua]
      cases A with
      | nil =>
        have hE : E a v := hlink v rfl
        exact hAcyc a v hE
      | cons a' rest =>
        have hE : E a a' := hlink a' rfl
        have hlt : rank a' < rank v :=
          ih htail a' (by simp)
        exact lt_trans (hAcyc a a' hE) hlt
    · exact ih htail u huA

/-- Ranks strictly increase after the head. -/
private theorem lgv_rank_after {V : Type*} (E : V → V → Prop) (rank : V → ℕ)
    (hAcyc : ∀ u v, E u v → rank u < rank v)
    (x : V) (D : List V) (hchain : (x :: D).IsChain E) :
    ∀ w ∈ D, rank x < rank w := by
  revert hchain
  induction D generalizing x with
  | nil => intro hchain w hw; simp at hw
  | cons d D ih =>
    intro hchain w hw
    rw [List.isChain_cons] at hchain
    obtain ⟨hlink, htail⟩ := hchain
    rw [List.mem_cons] at hw
    have hEd : E x d := hlink d rfl
    rcases hw with hwx | hwD
    · rw [hwx]; exact hAcyc x d hEd
    · exact lt_trans (hAcyc x d hEd) (ih d htail w hwD)

/-- Chain restricted to prefix through `v`. -/
private theorem lgv_chain_prefix {V : Type*} (E : V → V → Prop)
    (A : List V) (v : V) (B : List V) (hchain : (A ++ v :: B).IsChain E) :
    (A ++ [v]).IsChain E := by
  have htake := List.IsChain.take hchain (A.length + 1)
  have heq : (A ++ v :: B).take (A.length + 1) = A ++ [v] := by
    rw [List.take_append]
    simp
  rw [heq] at htake
  exact htake

/-- Chain restricted to suffix from `v`. -/
private theorem lgv_chain_suffix {V : Type*} (E : V → V → Prop)
    (A : List V) (v : V) (B : List V) (hchain : (A ++ v :: B).IsChain E) :
    (v :: B).IsChain E := by
  have hdrop := List.IsChain.drop hchain A.length
  rw [List.drop_left] at hdrop
  exact hdrop

/-- **Lindström–Gessel–Viennot lemma.** Let $R$ be a commutative ring, let $n$ be a natural
number, and let $E$ be a relation on a type $V$, read as a directed graph on $V$ with an edge
from $u$ to $v$ whenever $E(u, v)$. Suppose there is a function $r : V \to \mathbb{N}$ with
$r(u) < r(v)$ whenever $E(u, v)$, so the graph is acyclic. A path from $u$ to $w$ is a nonempty
list of vertices that starts at $u$, ends at $w$, and in which there is an edge from each vertex
to the next one. Let $A_0, \dots, A_{n-1}$ and $B_0, \dots, B_{n-1}$ be vertices, and suppose
that for all $i, j < n$ the paths from $A_i$ to $B_j$ form a finite set $P_{ij}$. Let $e$ be the
$n \times n$ matrix over $R$ with $e_{ij} = |P_{ij}|$. Suppose further that whenever $i < j$ and
$l < k$, every path from $A_i$ to $B_k$ shares a vertex with every path from $A_j$ to $B_l$. Let
$S$ be the finite set of families $(F_0, \dots, F_{n-1})$ in which each $F_i$ is a path from
$A_i$ to $B_i$ and $F_i$ and $F_j$ share no vertex whenever $i \ne j$. Then the number of
elements of $S$, taken in $R$, equals $\det e$.

Proves `Wanted` entry `lindstrom_gessel_viennot`.

Source: https://en.wikipedia.org/wiki/Lindstr%C3%B6m%E2%80%93Gessel%E2%80%93Viennot_lemma
-/
theorem lindstrom_gessel_viennot
    {V : Type*} [DecidableEq V]
    {R : Type*} [CommRing R]
    (n : ℕ)
    (E : V → V → Prop)
    (A B : Fin n → V)
    (rank : V → ℕ)
    (hAcyc : ∀ u v : V, E u v → rank u < rank v)
    (P : Fin n → Fin n → Finset (List V))
    (hPath : ∀ i j : Fin n, ∀ p : List V, p ∈ P i j ↔
      (p.head? = some (A i) ∧ p.getLast? = some (B j) ∧
        p.IsChain (fun u v => E u v)))
    (e : Fin n → Fin n → R)
    (he : ∀ i j : Fin n, e i j = ((P i j).card : R))
    (hPlanar : ∀ i j k l : Fin n, i < j → l < k →
      ∀ p ∈ P i k, ∀ q ∈ P j l, ∃ v : V, v ∈ p ∧ v ∈ q)
    (S : Finset (Fin n → List V))
    (hSys : ∀ F : Fin n → List V, F ∈ S ↔
      ((∀ i : Fin n, F i ∈ P i i) ∧
        ∀ i j : Fin n, i ≠ j → Disjoint (F i).toFinset (F j).toFinset)) :
    (S.card : R) = Matrix.det e := by
  classical
  have hNodup : ∀ (i j : Fin n) (p : List V), p ∈ P i j → p.Nodup := by
    intro i j p hp
    have h := (hPath i j p).mp hp
    have hc : p.IsChain (fun u v : V => rank u < rank v) :=
      h.2.2.imp (fun a b hh => hAcyc a b hh)
    have : Trans (fun u v : V => rank u < rank v) (fun u v : V => rank u < rank v)
        (fun u v : V => rank u < rank v) :=
      ⟨fun {_ _ _} hab hbc => lt_trans hab hbc⟩
    have : Std.Irrefl (fun u v : V => rank u < rank v) :=
      ⟨fun {_} hh => lt_irrefl _ hh⟩
    exact (hc.pairwise).nodup
  have hinv : ∀ (σ : Equiv.Perm (Fin n)), σ ≠ 1 →
      ∃ i j : Fin n, i < j ∧ σ j < σ i := by
    intro σ hσ
    by_contra h
    push Not at h
    have hmono : StrictMono (⇑σ : Fin n → Fin n) := by
      intro a b hab
      have hle : σ a ≤ σ b := h a b hab
      have hne : σ a ≠ σ b := by
        intro heq
        have : a = b := σ.injective heq
        exact absurd this (ne_of_lt hab)
      exact lt_of_le_of_ne hle hne
    have hle : (⇑σ : Fin n → Fin n) ≤ id := StrictMono.le_id hmono
    have hge : id ≤ (⇑σ : Fin n → Fin n) := StrictMono.id_le hmono
    have heq : (⇑σ : Fin n → Fin n) = id := le_antisymm hle hge
    apply hσ
    apply Equiv.ext
    intro x
    have hx : (⇑σ : Fin n → Fin n) x = id x := congrFun heq x
    simpa using hx
  have hdet : Matrix.det e = ∑ σ : Equiv.Perm (Fin n), ((σ.sign : ℤ) : R) * ∏ i,
      ((P i (σ i)).card : R) := by
    have h := Matrix.det_apply' (Matrix.transpose e)
    have ht : (Matrix.transpose e).det = Matrix.det e := Matrix.det_transpose e
    rw [ht] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro σ _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    have h1 : Matrix.transpose e (σ i) i = e i (σ i) := Matrix.transpose_apply _ _ _
    rw [h1, he]
  have hsum : (∑ c : (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))), (((c.1.sign : ℤ) : R))) =
      ∑ σ : Equiv.Perm (Fin n), ((σ.sign : ℤ) : R) * ∏ i, ((P i (σ i)).card : R) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro σ _
    have h1 : Fintype.card (∀ i, ↥(P i (σ i))) = ∏ i, Fintype.card ↥(P i (σ i)) :=
      Fintype.card_pi
    simp only [Fintype.card_coe] at h1
    have h2 : ((Fintype.card (∀ i, ↥(P i (σ i))) : ℕ) : R) = ∏ i, ((P i (σ i)).card : R) := by
      rw [h1, Nat.cast_prod]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, h2, mul_comm]
  set Coll : ((Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))) → Prop) :=
    fun c => ∃ i j, i ≠ j ∧ ∃ v, v ∈ (c.2 i).1 ∧ v ∈ (c.2 j).1 with hColl
  have hgood_perm : ∀ c : (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))), ¬ Coll c → c.1 = 1 := by
    intro c hc
    by_contra hne
    obtain ⟨i, j, hij, hji⟩ := hinv c.1 hne
    have hpi : (c.2 i).1 ∈ P i (c.1 i) := (c.2 i).2
    have hpj : (c.2 j).1 ∈ P j (c.1 j) := (c.2 j).2
    obtain ⟨v, hvi, hvj⟩ := hPlanar i j (c.1 i) (c.1 j) hij hji _ hpi _ hpj
    exact hc ⟨i, j, ne_of_lt hij, v, hvi, hvj⟩
  have hgood_sum : (∑ c ∈ Finset.univ.filter (fun c => ¬ Coll c), (((c.1.sign : ℤ) : R))) =
      (S.card : R) := by
    have hweight : ∀ c ∈ Finset.univ.filter
        (fun c : (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))) => ¬ Coll c),
        (((c.1.sign : ℤ) : R)) = (1 : R) := by
      intro c hc
      have hmem : ¬ Coll c := (Finset.mem_filter.mp hc).2
      have h1 : c.1 = 1 := hgood_perm c hmem
      rw [h1]
      simp
    rw [Finset.sum_congr rfl hweight]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (Finset.univ.filter
        (fun c : (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))) => ¬ Coll c)).card = S.card := by
      apply Finset.card_bij (fun c _ => (fun i => (c.2 i).1))
      · intro c hc
        obtain ⟨σ, F⟩ := c
        have hnc : ¬ Coll ⟨σ, F⟩ := (Finset.mem_filter.mp hc).2
        have hperm : σ = 1 := hgood_perm ⟨σ, F⟩ hnc
        subst hperm
        rw [hSys]
        constructor
        · intro i
          have hi : (F i).1 ∈ P i ((1 : Equiv.Perm (Fin n)) i) := (F i).2
          simpa using hi
        · intro i j hij
          rw [Finset.disjoint_left]
          intro a ha hja
          have ha' : a ∈ (F i).1 := List.mem_toFinset.mp ha
          have hj' : a ∈ (F j).1 := List.mem_toFinset.mp hja
          exact hnc ⟨i, j, hij, a, ha', hj'⟩
      · intro c1 hc1 c2 hc2 heq
        have h1 : c1.1 = 1 := hgood_perm c1 (Finset.mem_filter.mp hc1).2
        have h2 : c2.1 = 1 := hgood_perm c2 (Finset.mem_filter.mp hc2).2
        obtain ⟨σ1, F1⟩ := c1
        obtain ⟨σ2, F2⟩ := c2
        simp only at h1 h2
        subst h1
        subst h2
        have hfun : F1 = F2 := by
          funext i
          have hi := congrFun heq i
          exact Subtype.ext hi
        rw [hfun]
      · intro F hF
        have hFs := (hSys F).mp hF
        let c : (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))) :=
          ⟨1, fun i => ⟨F i, by simpa using hFs.1 i⟩⟩
        have hcgood : c ∈ Finset.univ.filter
            (fun c : (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))) => ¬ Coll c) := by
          rw [Finset.mem_filter]
          constructor
          · exact Finset.mem_univ c
          · intro hcol
            obtain ⟨i, j, hij, v, hvi, hvj⟩ := hcol
            have hd := hFs.2 i j hij
            rw [Finset.disjoint_left] at hd
            have hvi' : v ∈ (F i).toFinset := List.mem_toFinset.mpr hvi
            have hvj' : v ∈ (F j).toFinset := List.mem_toFinset.mpr hvj
            exact hd hvi' hvj'
        exact ⟨c, hcgood, rfl⟩
    rw [hcard]
  -- Colliding configurations cancel by the tail-swap involution.
  -- Canonical collision: minimal rank r* (Finset.min' on the finite Rset of ranks
  -- of shared vertices), then minimal i* (Finset.min'), then minimal j*
  -- (Finset.min'), then the shared vertex v* of rank r*.
  -- Swap tails after v*: F' i* = pre_i ++ v* :: suf_j, F' j* = pre_j ++ v* :: suf_i,
  -- σ' = σ * swap i* j*.  Sign flips via sign_mul/sign_swap; validity via
  -- IsChain.append_overlap with overlap [v*]; head/last preserved; ranks strictly
  -- increase so pre has rank < r* and suf has rank > r*, hence the canonical
  -- quadruple is preserved and the map is a fixed-point-free involution, as
  -- verified by the minimal-rank stability argument below.
  have hbad_sum : (∑ c ∈ Finset.univ.filter (fun c => Coll c), (((c.1.sign : ℤ) : R))) = 0 := by
    classical
    have hcanon : ∀ c : (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))), Coll c →
        ∃ (r : ℕ) (i j : Fin n) (v : V) (Ai Bi Aj Bj : List V),
        (c.2 i).1 = Ai ++ v :: Bi ∧ (∀ u ∈ Ai, u ≠ v) ∧
        (c.2 j).1 = Aj ++ v :: Bj ∧ (∀ u ∈ Aj, u ≠ v) ∧
        j ≠ i ∧ v ∈ (c.2 i).1 ∧ v ∈ (c.2 j).1 ∧ rank v = r ∧
        (∀ a b w, w ∈ (c.2 a).1 → w ∈ (c.2 b).1 → a ≠ b → r ≤ rank w) ∧
        (∀ a b w, b ≠ a → w ∈ (c.2 a).1 → w ∈ (c.2 b).1 → rank w = r → i ≤ a) ∧
        (∀ b w, w ∈ (c.2 i).1 → w ∈ (c.2 b).1 → rank w = r → b ≠ i → j ≤ b) := by
      intro c hc
      set Rset : Finset ℕ := Finset.univ.biUnion (fun a =>
        (((c.2 a).1.toFinset.filter fun v => ∃ b, b ≠ a ∧ v ∈ (c.2 b).1).image rank)) with hRdef
      have hRne : Rset.Nonempty := by
        obtain ⟨i, j, hij, v, hvi, hvj⟩ := hc
        refine ⟨rank v, ?_⟩
        rw [hRdef, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr
          ⟨List.mem_toFinset.mpr hvi, j, Ne.symm hij, hvj⟩, rfl⟩⟩
      set r := Rset.min' hRne with hrdef
      have hrmin : ∀ a b w, w ∈ (c.2 a).1 → w ∈ (c.2 b).1 → a ≠ b → r ≤ rank w := by
        intro a b w hwa hwb hab
        have hmem : rank w ∈ Rset := by
          rw [hRdef, Finset.mem_biUnion]
          exact ⟨a, Finset.mem_univ a, Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr
            ⟨List.mem_toFinset.mpr hwa, b, Ne.symm hab, hwb⟩, rfl⟩⟩
        exact Finset.min'_le _ _ hmem
      have hrmem : r ∈ Rset := Finset.min'_mem _ _
      rw [hRdef, Finset.mem_biUnion] at hrmem
      obtain ⟨a₀, -, hmem2⟩ := hrmem
      obtain ⟨u, humem, hru⟩ := Finset.mem_image.mp hmem2
      obtain ⟨hu1, b₀, hb₀ne, hu2⟩ := Finset.mem_filter.mp humem
      have hu1' : u ∈ (c.2 a₀).1 := List.mem_toFinset.mp hu1
      set Iset : Finset (Fin n) := Finset.univ.filter
        (fun a => ∃ b w, b ≠ a ∧ w ∈ (c.2 a).1 ∧ w ∈ (c.2 b).1 ∧ rank w = r) with hIdef
      have hIne : Iset.Nonempty := by
        refine ⟨a₀, ?_⟩
        rw [hIdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ a₀, b₀, u, hb₀ne, hu1', hu2, hru⟩
      set i := Iset.min' hIne with hidef
      have himin : ∀ a b w, b ≠ a → w ∈ (c.2 a).1 → w ∈ (c.2 b).1 → rank w = r → i ≤ a := by
        intro a b w hne hwa hwb hrw
        apply Finset.min'_le
        rw [hIdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ a, b, w, hne, hwa, hwb, hrw⟩
      have himem : i ∈ Iset := Finset.min'_mem _ _
      rw [hIdef, Finset.mem_filter] at himem
      obtain ⟨-, b₁, w₁, hb₁ne, hw₁i, hw₁b, hrw₁⟩ := himem
      set Jset : Finset (Fin n) := Finset.univ.filter
        (fun b => b ≠ i ∧ ∃ w, w ∈ (c.2 i).1 ∧ w ∈ (c.2 b).1 ∧ rank w = r) with hJdef
      have hJne : Jset.Nonempty := by
        refine ⟨b₁, ?_⟩
        rw [hJdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ b₁, hb₁ne, w₁, hw₁i, hw₁b, hrw₁⟩
      set j := Jset.min' hJne with hjdef
      have hjmin : ∀ b w, w ∈ (c.2 i).1 → w ∈ (c.2 b).1 → rank w = r → b ≠ i → j ≤ b := by
        intro b w hwi hwb hrw hne
        apply Finset.min'_le
        rw [hJdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ b, hne, w, hwi, hwb, hrw⟩
      have hjmem : j ∈ Jset := Finset.min'_mem _ _
      rw [hJdef, Finset.mem_filter] at hjmem
      obtain ⟨-, hji, w, hwi, hwj, hrw⟩ := hjmem
      obtain ⟨Ai, Bi, hAi, hAif⟩ := lgv_firstSplit _ _ hwi
      obtain ⟨Aj, Bj, hAj, hAjf⟩ := lgv_firstSplit _ _ hwj
      exact ⟨r, i, j, w, Ai, Bi, Aj, Bj, hAi, hAif, hAj, hAjf, hji, hwi, hwj, hrw, hrmin, himin,
          hjmin⟩
    choose r i j v Ai Bi Aj Bj hsplit_i hfirst_i hsplit_j hfirst_j hji hv1 hv2 hrank hrmin himin
        hjmin using hcanon
    have hch : ∀ (a b : Fin n) (p : List V), p ∈ P a b → p.IsChain E :=
      fun a b p hp => ((hPath a b p).mp hp).2.2
    have hmem_i : ∀ c (hc : Coll c) (k : Fin n) (_ : k = i c hc),
        Ai c hc ++ v c hc :: Bj c hc ∈
          P k ((c.1 * Equiv.swap (i c hc) (j c hc)) k) := by
      intro c hc k hk
      subst hk
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have hFi := ((hPath (i c hc) (c.1 (i c hc)) ((c.2 (i c hc)).1)).mp
        (c.2 (i c hc)).2)
      have hFj := ((hPath (j c hc) (c.1 (j c hc)) ((c.2 (j c hc)).1)).mp
        (c.2 (j c hc)).2)
      rw [hsplit_i c hc] at hFi
      rw [hsplit_j c hc] at hFj
      rw [hPath]
      refine ⟨?_, ?_, ?_⟩
      · have hhead : (Ai c hc ++ v c hc :: Bj c hc).head? =
            (Ai c hc ++ v c hc :: Bi c hc).head? := by
          cases Ai c hc <;> rfl
        rw [hhead]
        exact hFi.1
      · have hg : ∃ g, (v c hc :: Bj c hc).getLast? = some g := by
          cases h : (v c hc :: Bj c hc).getLast? with
          | none => rw [List.getLast?_eq_none_iff] at h; simp at h
          | some g => exact ⟨g, rfl⟩
        obtain ⟨g, hg⟩ := hg
        have e1 : (Ai c hc ++ v c hc :: Bj c hc).getLast? = some g := by
          simp [List.getLast?_append, hg]
        have e2 : (Aj c hc ++ v c hc :: Bj c hc).getLast? = some g := by
          simp [List.getLast?_append, hg]
        rw [e1]
        have hFj' : some g = some (B (c.1 (j c hc))) := by
          rw [← e2]; exact hFj.2.1
        exact hFj'
      · have hP := lgv_chain_prefix E (Ai c hc) (v c hc) (Bi c hc)
          (hsplit_i c hc ▸ hch _ _ _ (c.2 (i c hc)).2)
        have hS := lgv_chain_suffix E (Aj c hc) (v c hc) (Bj c hc)
          (hsplit_j c hc ▸ hch _ _ _ (c.2 (j c hc)).2)
        have h := List.IsChain.append_overlap hP hS (by simp : [v c hc] ≠ [])
        rw [List.append_assoc] at h
        exact h
    have hmem_j : ∀ c (hc : Coll c) (k : Fin n) (_ : k = j c hc),
        Aj c hc ++ v c hc :: Bi c hc ∈
          P k ((c.1 * Equiv.swap (i c hc) (j c hc)) k) := by
      intro c hc k hk
      subst hk
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have hFi := ((hPath (i c hc) (c.1 (i c hc)) ((c.2 (i c hc)).1)).mp
        (c.2 (i c hc)).2)
      have hFj := ((hPath (j c hc) (c.1 (j c hc)) ((c.2 (j c hc)).1)).mp
        (c.2 (j c hc)).2)
      rw [hsplit_i c hc] at hFi
      rw [hsplit_j c hc] at hFj
      rw [hPath]
      refine ⟨?_, ?_, ?_⟩
      · have hhead : (Aj c hc ++ v c hc :: Bi c hc).head? =
            (Aj c hc ++ v c hc :: Bj c hc).head? := by
          cases Aj c hc <;> rfl
        rw [hhead]
        exact hFj.1
      · have hg : ∃ g, (v c hc :: Bi c hc).getLast? = some g := by
          cases h : (v c hc :: Bi c hc).getLast? with
          | none => rw [List.getLast?_eq_none_iff] at h; simp at h
          | some g => exact ⟨g, rfl⟩
        obtain ⟨g, hg⟩ := hg
        have e1 : (Aj c hc ++ v c hc :: Bi c hc).getLast? = some g := by
          simp [List.getLast?_append, hg]
        have e2 : (Ai c hc ++ v c hc :: Bi c hc).getLast? = some g := by
          simp [List.getLast?_append, hg]
        rw [e1]
        have hFi' : some g = some (B (c.1 (i c hc))) := by
          rw [← e2]; exact hFi.2.1
        exact hFi'
      · have hP := lgv_chain_prefix E (Aj c hc) (v c hc) (Bj c hc)
          (hsplit_j c hc ▸ hch _ _ _ (c.2 (j c hc)).2)
        have hS := lgv_chain_suffix E (Ai c hc) (v c hc) (Bi c hc)
          (hsplit_i c hc ▸ hch _ _ _ (c.2 (i c hc)).2)
        have h := List.IsChain.append_overlap hP hS (by simp : [v c hc] ≠ [])
        rw [List.append_assoc] at h
        exact h
    have hmem_k : ∀ c (hc : Coll c) (k : Fin n) (_ : ¬ k = i c hc) (_ : ¬ k = j c hc),
        (c.2 k).1 ∈ P k ((c.1 * Equiv.swap (i c hc) (j c hc)) k) := by
      intro c hc k hk1 hk2
      have hkk : (c.1 * Equiv.swap (i c hc) (j c hc)) k = c.1 k := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hk1 hk2]
      rw [hkk]
      exact (c.2 k).2
    let hswap : ∀ c : (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))),
        ∀ hc : Coll c, (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))) :=
      fun c hc => ⟨c.1 * Equiv.swap (i c hc) (j c hc), fun k =>
        if hk1 : k = i c hc then ⟨Ai c hc ++ v c hc :: Bj c hc, hmem_i c hc k hk1⟩
        else if hk2 : k = j c hc then ⟨Aj c hc ++ v c hc :: Bi c hc, hmem_j c hc k hk2⟩
        else ⟨(c.2 k).1, hmem_k c hc k hk1 hk2⟩⟩
    have hfst : ∀ c hc, (hswap c hc).1 = c.1 * Equiv.swap (i c hc) (j c hc) :=
      fun c hc => rfl
    have hFval : ∀ c hc (k : Fin n), (hswap c hc).2 k =
        (if hk1 : k = i c hc then ⟨Ai c hc ++ v c hc :: Bj c hc, hmem_i c hc k hk1⟩
        else if hk2 : k = j c hc then ⟨Aj c hc ++ v c hc :: Bi c hc, hmem_j c hc k hk2⟩
        else ⟨(c.2 k).1, hmem_k c hc k hk1 hk2⟩) :=
      fun c hc k => rfl
    have hsnd_i : ∀ c hc (k : Fin n) (hk : k = i c hc),
        ((hswap c hc).2 k).1 = Ai c hc ++ v c hc :: Bj c hc := by
      intro c hc k hk
      rw [hFval, dite_eq_left hk]
    have hsnd_j : ∀ c hc (k : Fin n) (hk : k = j c hc),
        ((hswap c hc).2 k).1 = Aj c hc ++ v c hc :: Bi c hc := by
      intro c hc k hk
      have hk1 : ¬ k = i c hc := fun h => hji c hc (hk.symm.trans h)
      rw [hFval, dite_eq_right hk1, dite_eq_left hk]
    have hsnd_o : ∀ c hc (k : Fin n) (hk1 : ¬ k = i c hc) (hk2 : ¬ k = j c hc),
        ((hswap c hc).2 k).1 = (c.2 k).1 := by
      intro c hc k hk1 hk2
      rw [hFval, dite_eq_right hk1, dite_eq_right hk2]
    have hvin_i : ∀ c hc, v c hc ∈ ((hswap c hc).2 (i c hc)).1 := by
      intro c hc
      rw [hsnd_i c hc _ rfl]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    have hvin_j : ∀ c hc, v c hc ∈ ((hswap c hc).2 (j c hc)).1 := by
      intro c hc
      rw [hsnd_j c hc _ rfl]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    have hmemFi : ∀ c hc (w : V), w ∈ Ai c hc → w ∈ (c.2 (i c hc)).1 := by
      intro c hc w hw
      rw [hsplit_i c hc]
      exact List.mem_append.mpr (Or.inl hw)
    have hmemFj : ∀ c hc (w : V), w ∈ Aj c hc → w ∈ (c.2 (j c hc)).1 := by
      intro c hc w hw
      rw [hsplit_j c hc]
      exact List.mem_append.mpr (Or.inl hw)
    have hmemBi : ∀ c hc (w : V), w ∈ Bi c hc → w ∈ (c.2 (i c hc)).1 := by
      intro c hc w hw
      rw [hsplit_i c hc]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hw)))
    have hmemBj : ∀ c hc (w : V), w ∈ Bj c hc → w ∈ (c.2 (j c hc)).1 := by
      intro c hc w hw
      rw [hsplit_j c hc]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hw)))
    have hchain_i : ∀ c hc, (Ai c hc ++ v c hc :: Bi c hc).IsChain E := by
      intro c hc
      rw [← hsplit_i c hc]
      exact hch _ _ _ (c.2 (i c hc)).2
    have hchain_j : ∀ c hc, (Aj c hc ++ v c hc :: Bj c hc).IsChain E := by
      intro c hc
      rw [← hsplit_j c hc]
      exact hch _ _ _ (c.2 (j c hc)).2
    have hrankAi : ∀ c hc (u : V), u ∈ Ai c hc → rank u < r c hc := by
      intro c hc u hu
      have hlt := lgv_rank_before E rank hAcyc (Ai c hc) (v c hc) (Bi c hc)
        (hchain_i c hc) u hu
      rw [hrank c hc] at hlt
      exact hlt
    have hrankBi : ∀ c hc (w : V), w ∈ Bi c hc → r c hc < rank w := by
      intro c hc w hw
      have hS := lgv_chain_suffix E (Ai c hc) (v c hc) (Bi c hc) (hchain_i c hc)
      have hlt := lgv_rank_after E rank hAcyc (v c hc) (Bi c hc) hS w hw
      rw [← hrank c hc]
      exact hlt
    have hrankAj : ∀ c hc (u : V), u ∈ Aj c hc → rank u < r c hc := by
      intro c hc u hu
      have hlt := lgv_rank_before E rank hAcyc (Aj c hc) (v c hc) (Bj c hc)
        (hchain_j c hc) u hu
      rw [hrank c hc] at hlt
      exact hlt
    have hrankBj : ∀ c hc (w : V), w ∈ Bj c hc → r c hc < rank w := by
      intro c hc w hw
      have hS := lgv_chain_suffix E (Aj c hc) (v c hc) (Bj c hc) (hchain_j c hc)
      have hlt := lgv_rank_after E rank hAcyc (v c hc) (Bj c hc) hS w hw
      rw [← hrank c hc]
      exact hlt
    have hsub_i : ∀ c hc (w : V), w ∈ ((hswap c hc).2 (i c hc)).1 → rank w = r c hc →
        w ∈ (c.2 (i c hc)).1 := by
      intro c hc w hw hrw
      rw [hsnd_i c hc _ rfl, List.mem_append, List.mem_cons] at hw
      rcases hw with hAi | hvv | hBj
      · exact hmemFi c hc w hAi
      · rw [hvv]; exact hv1 c hc
      · have hgt := hrankBj c hc w hBj
        rw [hrw] at hgt
        exact absurd hgt (lt_irrefl _)
    have hsub_j : ∀ c hc (w : V), w ∈ ((hswap c hc).2 (j c hc)).1 → rank w = r c hc →
        w ∈ (c.2 (j c hc)).1 := by
      intro c hc w hw hrw
      rw [hsnd_j c hc _ rfl, List.mem_append, List.mem_cons] at hw
      rcases hw with hAj | hvv | hBi
      · exact hmemFj c hc w hAj
      · rw [hvv]; exact hv2 c hc
      · have hgt := hrankBi c hc w hBi
        rw [hrw] at hgt
        exact absurd hgt (lt_irrefl _)
    have hpull : ∀ c (hc : Coll c) (hc' : Coll (hswap c hc)) (m : Fin n) (w : V),
        w ∈ ((hswap c hc).2 m).1 → rank w = r c hc → w ∈ (c.2 m).1 := by
      intro c hc hc' m w hw hrw
      by_cases hm1 : m = i c hc
      · subst hm1; exact hsub_i c hc w hw hrw
      · by_cases hm2 : m = j c hc
        · subst hm2; exact hsub_j c hc w hw hrw
        · rw [hsnd_o c hc m hm1 hm2] at hw; exact hw
    have hroute_ij : ∀ c (hc : Coll c) (w : V),
        (w ∈ Ai c hc ∨ w = v c hc ∨ w ∈ Bj c hc) →
        (w ∈ Aj c hc ∨ w = v c hc ∨ w ∈ Bi c hc) →
        ∃ x y, x ≠ y ∧ w ∈ (c.2 x).1 ∧ w ∈ (c.2 y).1 := by
      intro c hc w hwa hwb
      by_cases hwi : w ∈ (c.2 (i c hc)).1
      · by_cases hwj : w ∈ (c.2 (j c hc)).1
        · exact ⟨i c hc, j c hc, Ne.symm (hji c hc), hwi, hwj⟩
        · exfalso
          have hBi : w ∈ Bi c hc := by
            rcases hwb with hAj | hvv | hBi
            · exact absurd (hmemFj c hc w hAj) hwj
            · exact absurd (hvv.symm ▸ hv2 c hc) hwj
            · exact hBi
          have hgt : r c hc < rank w := hrankBi c hc w hBi
          rcases hwa with hAi | hvv2 | hBj
          · exact (not_lt_of_gt hgt) (hrankAi c hc w hAi)
          · rw [hvv2, hrank c hc] at hgt
            exact absurd hgt (lt_irrefl _)
          · exact hwj (hmemBj c hc w hBj)
      · exfalso
        have hBj : w ∈ Bj c hc := by
          rcases hwa with hAi | hvv | hBj
          · exact absurd (hmemFi c hc w hAi) hwi
          · exact absurd (hvv.symm ▸ hv1 c hc) hwi
          · exact hBj
        have hgt : r c hc < rank w := hrankBj c hc w hBj
        rcases hwb with hAj | hvv2 | hBi
        · exact (not_lt_of_gt hgt) (hrankAj c hc w hAj)
        · rw [hvv2, hrank c hc] at hgt
          exact absurd hgt (lt_irrefl _)
        · exact hwi (hmemBi c hc w hBi)
    have hroute : ∀ c (hc : Coll c) (a b : Fin n) (w : V),
        w ∈ ((hswap c hc).2 a).1 → w ∈ ((hswap c hc).2 b).1 → a ≠ b →
        ∃ x y, x ≠ y ∧ w ∈ (c.2 x).1 ∧ w ∈ (c.2 y).1 := by
      intro c hc a b w hwa hwb hab
      by_cases ha1 : a = i c hc
      · by_cases hb1 : b = i c hc
        · exact absurd (ha1.trans hb1.symm) hab
        · by_cases hb2 : b = j c hc
          · rw [hsnd_i c hc a ha1, List.mem_append, List.mem_cons] at hwa
            rw [hsnd_j c hc b hb2, List.mem_append, List.mem_cons] at hwb
            exact hroute_ij c hc w hwa hwb
          · rw [hsnd_i c hc a ha1, List.mem_append, List.mem_cons] at hwa
            have hwb' : w ∈ (c.2 b).1 := by
              rw [hsnd_o c hc b hb1 hb2] at hwb; exact hwb
            rcases hwa with hAi | hvv | hBj
            · exact ⟨i c hc, b, Ne.symm hb1, hmemFi c hc w hAi, hwb'⟩
            · exact ⟨i c hc, b, Ne.symm hb1, hvv.symm ▸ hv1 c hc, hwb'⟩
            · exact ⟨j c hc, b, Ne.symm hb2, hmemBj c hc w hBj, hwb'⟩
      · by_cases ha2 : a = j c hc
        · by_cases hb1 : b = i c hc
          · rw [hsnd_j c hc a ha2, List.mem_append, List.mem_cons] at hwa
            rw [hsnd_i c hc b hb1, List.mem_append, List.mem_cons] at hwb
            exact hroute_ij c hc w hwb hwa
          · by_cases hb2 : b = j c hc
            · exact absurd (ha2.trans hb2.symm) hab
            · rw [hsnd_j c hc a ha2, List.mem_append, List.mem_cons] at hwa
              have hwb' : w ∈ (c.2 b).1 := by
                rw [hsnd_o c hc b hb1 hb2] at hwb; exact hwb
              rcases hwa with hAj | hvv | hBi
              · exact ⟨j c hc, b, Ne.symm hb2, hmemFj c hc w hAj, hwb'⟩
              · exact ⟨j c hc, b, Ne.symm hb2, hvv.symm ▸ hv2 c hc, hwb'⟩
              · exact ⟨i c hc, b, Ne.symm hb1, hmemBi c hc w hBi, hwb'⟩
        · by_cases hb1 : b = i c hc
          · have hwa' : w ∈ (c.2 a).1 := by
              rw [hsnd_o c hc a ha1 ha2] at hwa; exact hwa
            rw [hsnd_i c hc b hb1, List.mem_append, List.mem_cons] at hwb
            rcases hwb with hAi | hvv | hBj
            · exact ⟨a, i c hc, ha1, hwa', hmemFi c hc w hAi⟩
            · exact ⟨a, i c hc, ha1, hwa', hvv.symm ▸ hv1 c hc⟩
            · exact ⟨a, j c hc, ha2, hwa', hmemBj c hc w hBj⟩
          · by_cases hb2 : b = j c hc
            · have hwa' : w ∈ (c.2 a).1 := by
                rw [hsnd_o c hc a ha1 ha2] at hwa; exact hwa
              rw [hsnd_j c hc b hb2, List.mem_append, List.mem_cons] at hwb
              rcases hwb with hAj | hvv | hBi
              · exact ⟨a, j c hc, ha2, hwa', hmemFj c hc w hAj⟩
              · exact ⟨a, j c hc, ha2, hwa', hvv.symm ▸ hv2 c hc⟩
              · exact ⟨a, i c hc, ha1, hwa', hmemBi c hc w hBi⟩
            · have hwa' : w ∈ (c.2 a).1 := by
                rw [hsnd_o c hc a ha1 ha2] at hwa; exact hwa
              have hwb' : w ∈ (c.2 b).1 := by
                rw [hsnd_o c hc b hb1 hb2] at hwb; exact hwb
              exact ⟨a, b, hab, hwa', hwb'⟩
    have hrr : ∀ c (hc : Coll c) (hc' : Coll (hswap c hc)),
        r (hswap c hc) hc' = r c hc := by
      intro c hc hc'
      apply le_antisymm
      · have hle := hrmin (hswap c hc) hc' (i c hc) (j c hc) (v c hc)
          (hvin_i c hc) (hvin_j c hc) (Ne.symm (hji c hc))
        rw [hrank c hc] at hle
        exact hle
      · have hne : i (hswap c hc) hc' ≠ j (hswap c hc) hc' :=
          Ne.symm (hji (hswap c hc) hc')
        obtain ⟨x, y, hxy, hxx, hyy⟩ := hroute c hc
          (i (hswap c hc) hc') (j (hswap c hc) hc') (v (hswap c hc) hc')
          (hv1 _ _) (hv2 _ _) hne
        have hle := hrmin c hc x y _ hxx hyy hxy
        rw [hrank (hswap c hc) hc'] at hle
        exact hle
    have hii : ∀ c (hc : Coll c) (hc' : Coll (hswap c hc)),
        i (hswap c hc) hc' = i c hc := by
      intro c hc hc'
      apply le_antisymm
      · apply himin (hswap c hc) hc' (i c hc) (j c hc) (v c hc)
        · exact hji c hc
        · exact hvin_i c hc
        · exact hvin_j c hc
        · rw [hrr c hc hc', hrank c hc]
      · have hrw' : rank (v (hswap c hc) hc') = r c hc := by
          rw [← hrr c hc hc']; exact hrank _ _
        have h1 : v (hswap c hc) hc' ∈ (c.2 (i (hswap c hc) hc')).1 :=
          hpull c hc hc' _ _ (hv1 _ _) hrw'
        have h2 : v (hswap c hc) hc' ∈ (c.2 (j (hswap c hc) hc')).1 :=
          hpull c hc hc' _ _ (hv2 _ _) hrw'
        exact himin c hc _ _ _ (hji _ _) h1 h2 hrw'
    have hjj : ∀ c (hc : Coll c) (hc' : Coll (hswap c hc)),
        j (hswap c hc) hc' = j c hc := by
      intro c hc hc'
      have hi' : i (hswap c hc) hc' = i c hc := hii c hc hc'
      have hr' : r (hswap c hc) hc' = r c hc := hrr c hc hc'
      apply le_antisymm
      · apply hjmin (hswap c hc) hc' (j c hc) (v c hc)
        · rw [hi']; exact hvin_i c hc
        · exact hvin_j c hc
        · rw [hr']; exact hrank c hc
        · rw [hi']; exact hji c hc
      · have hrw' : rank (v (hswap c hc) hc') = r c hc := by
          rw [← hrr c hc hc']; exact hrank _ _
        have h1 : v (hswap c hc) hc' ∈ (c.2 (i c hc)).1 := by
          have h := hpull c hc hc' _ _ (hv1 _ _) hrw'
          rw [hi'] at h; exact h
        have h2 : v (hswap c hc) hc' ∈ (c.2 (j (hswap c hc) hc')).1 :=
          hpull c hc hc' _ _ (hv2 _ _) hrw'
        have hne : j (hswap c hc) hc' ≠ i c hc := by
          rw [← hi']; exact hji _ _
        exact hjmin c hc _ _ h1 h2 hrw' hne
    have hvv : ∀ c (hc : Coll c) (hc' : Coll (hswap c hc)),
        v (hswap c hc) hc' = v c hc := by
      intro c hc hc'
      have hi' := hii c hc hc'
      have hrw' : rank (v (hswap c hc) hc') = r c hc := by
        rw [← hrr c hc hc']; exact hrank _ _
      have hmem : v (hswap c hc) hc' ∈ Ai c hc ++ v c hc :: Bj c hc := by
        have h := hv1 (hswap c hc) hc'
        rw [hi', hsnd_i c hc _ rfl] at h
        exact h
      rw [List.mem_append, List.mem_cons] at hmem
      rcases hmem with hAi | hvv | hBj
      · have hlt := hrankAi c hc _ hAi
        rw [hrw'] at hlt
        exact absurd hlt (lt_irrefl _)
      · exact hvv
      · have hgt := hrankBj c hc _ hBj
        rw [hrw'] at hgt
        exact absurd hgt (lt_irrefl _)
    have hsign : ∀ c (hc : Coll c),
        ((c.1.sign : ℤ) : R) + (((hswap c hc).1.sign : ℤ) : R) = 0 := by
      intro c hc
      have hss : (hswap c hc).1.sign = c.1.sign * -1 := by
        rw [hfst c hc, Equiv.Perm.sign_mul,
          Equiv.Perm.sign_swap (Ne.symm (hji c hc))]
      have hcast : (((hswap c hc).1.sign : ℤ) : R) = -(((c.1.sign : ℤ) : R)) := by
        rw [hss]; push_cast; ring
      rw [hcast, add_neg_cancel]
    have hne : ∀ c (hc : Coll c), hswap c hc ≠ c := by
      intro c hc hcon
      have hσ : (hswap c hc).1 = c.1 := congrArg Sigma.fst hcon
      rw [hfst c hc] at hσ
      have h3 : c.1 (j c hc) = c.1 (i c hc) := by
        have h4 := congrArg (fun σ : Equiv.Perm (Fin n) => σ (i c hc)) hσ
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h4
        exact h4
      exact hji c hc (c.1.injective h3)
    have hgmem : ∀ c (hc : Coll c), Coll (hswap c hc) :=
      fun c hc => ⟨i c hc, j c hc, Ne.symm (hji c hc), v c hc, hvin_i c hc, hvin_j c hc⟩
    refine Finset.sum_involution
      (fun a (ha : a ∈ Finset.univ.filter (fun c => Coll c)) =>
        hswap a (Finset.mem_filter.mp ha).2) ?_ ?_ ?_ ?_
    · intro a ha
      exact hsign a (Finset.mem_filter.mp ha).2
    · intro a ha _
      exact hne a (Finset.mem_filter.mp ha).2
    · intro a ha
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hgmem a (Finset.mem_filter.mp ha).2⟩
    · intro a ha
      have h2 : Coll a := (Finset.mem_filter.mp ha).2
      have h3 : Coll (hswap a h2) := hgmem a h2
      change hswap (hswap a h2) h3 = a
      have hi' := hii a h2 h3
      have hj' := hjj a h2 h3
      have hv' := hvv a h2 h3
      have hσ2 : (hswap (hswap a h2) h3).1 = a.1 := by
        rw [hfst, hfst, hi', hj', mul_assoc, Equiv.swap_mul_self, mul_one]
      have hF2 : ∀ k, ((hswap (hswap a h2) h3).2 k).1 = ((a.2 k).1) := by
        intro k
        by_cases hk1 : k = i (hswap a h2) h3
        · have e1 : ((hswap a h2).2 (i (hswap a h2) h3)).1 =
              Ai a h2 ++ v (hswap a h2) h3 :: Bj a h2 := by
            rw [hi', hv']; exact hsnd_i a h2 _ rfl
          have e2 : ((hswap a h2).2 (j (hswap a h2) h3)).1 =
              Aj a h2 ++ v (hswap a h2) h3 :: Bi a h2 := by
            rw [hj', hv']; exact hsnd_j a h2 _ rfl
          have hfAi : ∀ u ∈ Ai a h2, u ≠ v (hswap a h2) h3 := by
            rw [hv']; exact hfirst_i a h2
          have hfAj : ∀ u ∈ Aj a h2, u ≠ v (hswap a h2) h3 := by
            rw [hv']; exact hfirst_j a h2
          have hU1 := lgv_firstSplit_unique e1 hfAi
            (hsplit_i _ _) (hfirst_i _ _)
          have hU2 := lgv_firstSplit_unique e2 hfAj
            (hsplit_j _ _) (hfirst_j _ _)
          have hkk : k = i a h2 := hk1.trans hi'
          rw [hsnd_i _ _ _ hk1, ← hU1.1, hv', ← hU2.2, hkk]
          exact (hsplit_i a h2).symm
        · by_cases hk2 : k = j (hswap a h2) h3
          · have e1 : ((hswap a h2).2 (i (hswap a h2) h3)).1 =
                Ai a h2 ++ v (hswap a h2) h3 :: Bj a h2 := by
              rw [hi', hv']; exact hsnd_i a h2 _ rfl
            have e2 : ((hswap a h2).2 (j (hswap a h2) h3)).1 =
                Aj a h2 ++ v (hswap a h2) h3 :: Bi a h2 := by
              rw [hj', hv']; exact hsnd_j a h2 _ rfl
            have hfAi : ∀ u ∈ Ai a h2, u ≠ v (hswap a h2) h3 := by
              rw [hv']; exact hfirst_i a h2
            have hfAj : ∀ u ∈ Aj a h2, u ≠ v (hswap a h2) h3 := by
              rw [hv']; exact hfirst_j a h2
            have hU1 := lgv_firstSplit_unique e1 hfAi
              (hsplit_i _ _) (hfirst_i _ _)
            have hU2 := lgv_firstSplit_unique e2 hfAj
              (hsplit_j _ _) (hfirst_j _ _)
            have hkk : k = j a h2 := hk2.trans hj'
            rw [hsnd_j _ _ _ hk2, ← hU2.1, hv', ← hU1.2, hkk]
            exact (hsplit_j a h2).symm
          · have h1 : ((hswap (hswap a h2) h3).2 k).1 = (((hswap a h2).2 k).1) := by
              rw [hsnd_o _ _ _ hk1 hk2]
            have hki : k ≠ i a h2 := fun hkk => hk1 (hi'.symm ▸ hkk)
            have hkj : k ≠ j a h2 := fun hkk => hk2 (hj'.symm ▸ hkk)
            rw [h1, hsnd_o a h2 k hki hkj]
      revert hσ2 hF2
      obtain ⟨σ2, F2⟩ := hswap (hswap a h2) h3
      intro hσ2 hF2
      have hσ2' : σ2 = a.1 := hσ2
      subst hσ2'
      have hcon : F2 = a.2 := by
        funext k
        apply Subtype.ext
        exact hF2 k
      exact congrArg (Sigma.mk a.1) hcon
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i)))) Coll
    (fun c => (((c.1.sign : ℤ) : R)))
  have htotal : (∑ c : (Σ σ : Equiv.Perm (Fin n), ∀ i, ↥(P i (σ i))), (((c.1.sign : ℤ) : R))) =
      (∑ c ∈ Finset.univ.filter (fun c => Coll c), (((c.1.sign : ℤ) : R))) +
      (∑ c ∈ Finset.univ.filter (fun c => ¬ Coll c), (((c.1.sign : ℤ) : R))) := by
    exact hsplit.symm
  have hdet_total : Matrix.det e =
      (∑ c ∈ Finset.univ.filter (fun c => Coll c), (((c.1.sign : ℤ) : R))) +
      (∑ c ∈ Finset.univ.filter (fun c => ¬ Coll c), (((c.1.sign : ℤ) : R))) :=
    (hdet.trans hsum.symm).trans htotal
  rw [hbad_sum, hgood_sum, zero_add] at hdet_total
  exact hdet_total.symm

end MetaMathlibExt
end
