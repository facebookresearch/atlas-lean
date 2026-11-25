/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.GlobalMarkov
public import CSLibExt.MachineLearning.GraphicalModels.MarkovRandomField

/-!
# The moralization criterion for d-separation

The *moral graph* of a set `A` of nodes of a Bayesian network is the
undirected graph on `A` obtained by marrying the parents of each node in
`A` and dropping all directions (Lauritzen). The moralization criterion
(Evans, APTS Causal Inference notes, Thm. 5.1) states that `Z`
d-separates `X` from `Y` if and only if `Z` separates `X` from `Y` in
the moral graph of the ancestral closure of `X ∪ Y ∪ Z`.

## Main definitions

* `BayesNet.ancestorsOf`: the ancestral closure `an(S)`, including `S`.
* `BayesNet.moralGraph`: the moral graph, on the full vertex type with
  vertices outside `A` isolated.

## Main results

* `BayesNet.dSeparated_iff_separatedBy_moralGraph`: the criterion, for
  pairwise disjoint `X`, `Y`, `Z`.
* `BayesNet.mem_ancestorsOf_of_isPath_not_blocked`: every vertex of an
  unblocked path lies in the ancestral closure (Evans, Prop. 5.1).
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α : Type*} {n : ℕ}

namespace BayesNet

variable (b : BayesNet α n)


/-- **Ancestors of a set of nodes** (including the set itself): `v` is an
ancestor of `S` when there is a directed path from `v` to a node of `S`
(zero steps allowed). Evans's `an(S)`. -/
def ancestorsOf (S : Set (Fin n)) : Set (Fin n) :=
  {v | ∃ s ∈ S, b.IsDescendant v s}

/-- Every node is an ancestor of itself, so `S ⊆ an(S)`. -/
theorem subset_ancestorsOf (S : Set (Fin n)) : S ⊆ b.ancestorsOf S := by
  intro v hv
  exact ⟨v, hv, Relation.ReflTransGen.refl⟩

/-- **Closure under parents**: an edge into `an(S)` comes from `an(S)`. -/
theorem ancestorsOf_edge_closed {S : Set (Fin n)} {i j : Fin n} (h : b.Edge i j) (hj : j ∈ b.ancestorsOf S) :
    i ∈ b.ancestorsOf S := by
  obtain ⟨s, hs, hjs⟩ := hj
  exact ⟨s, hs, Relation.ReflTransGen.head h hjs⟩

open Classical in
/-- `an(S)` as a finset is ancestral (parents-closed). -/
theorem isAncestral_ancestorsOf (S : Set (Fin n)) :
    b.IsAncestral (Finset.univ.filter fun v => v ∈ b.ancestorsOf S) := by
  intro i j h hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact b.ancestorsOf_edge_closed h hj

/-- **The moral graph on an ancestral vertex set `A`** (Lauritzen): distinct
`i, j ∈ A` are adjacent when they are adjacent in the skeleton of `b`, or
they are both parents of a common child in `A` (marrying parents, directions
dropped). Vertices outside `A` are isolated. -/
def moralGraph (A : Set (Fin n)) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ i ∈ A ∧ j ∈ A ∧ (b.Adj i j ∨ ∃ c ∈ A, b.Edge i c ∧ b.Edge j c)
  symm := ⟨by
    rintro i j ⟨hij, hi, hj, h⟩
    refine ⟨hij.symm, hj, hi, ?_⟩
    cases h with
    | inl h => exact Or.inl (Or.comm.mp h)
    | inr h =>
        obtain ⟨c, hc, h1, h2⟩ := h
        exact Or.inr ⟨c, hc, h2, h1⟩⟩
  loopless := ⟨by
    rintro i ⟨h, -⟩
    exact h rfl⟩

/-- Adjacency in the moral graph, unfolded. -/
theorem moralGraph_adj {A : Set (Fin n)} {i j : Fin n} :
    (b.moralGraph A).Adj i j ↔
      i ≠ j ∧ i ∈ A ∧ j ∈ A ∧ (b.Adj i j ∨ ∃ c ∈ A, b.Edge i c ∧ b.Edge j c) :=
  Iff.rfl

/-- **Every vertex of an open path lies in the ancestral closure** (Evans
Prop 5.1): if `p` is a path from `x` to `y` not blocked by `Z`, every vertex
of `p` is an ancestor of `{x, y} ∪ Z`. -/
theorem mem_ancestorsOf_of_isPath_not_blocked {x y : Fin n} {Z : Set (Fin n)}
    {p : List (Fin n)} (hp : b.IsPath x y p) (hb : ¬ b.PathBlocked Z p) {v : Fin n}
    (hv : v ∈ p) : v ∈ b.ancestorsOf ({x, y} ∪ Z) := by
  classical
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := hp
  have hne : p ≠ [] := by
    intro h
    simp [h] at hhead
  have hL : 0 < p.length := List.length_pos_iff_ne_nil.mpr hne
  have hx : p[0] = x := by
    rw [List.head?_eq_getElem?] at hhead
    obtain ⟨h0, hx⟩ := List.getElem_of_getElem? hhead
    exact hx
  have hlastlt : p.length - 1 < p.length := by omega
  have hy : p[p.length - 1] = y := by
    rw [List.getLast?_eq_getElem?] at hlast
    obtain ⟨h1, hy⟩ := List.getElem_of_getElem? hlast
    exact hy
  have hadj : ∀ (i : ℕ) (_ : i + 1 < p.length), b.Adj p[i] p[i + 1] :=
    List.isChain_iff_getElem.mp hchain
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
  have hunblocked : ∀ (i : ℕ) (h : i + 2 < p.length),
      ¬ b.BlockedAt Z p[i] p[i + 1] p[i + 2] := by
    intro i h hblk
    exact hb ⟨i, h, hblk⟩
  have hcoll : ∀ (i : ℕ) (h : i + 2 < p.length),
      b.Edge p[i] p[i + 1] → b.Edge p[i + 2] p[i + 1] →
      ∃ d, b.IsDescendant p[i + 1] d ∧ d ∈ Z := by
    intro i h e1 e2
    have hn := hunblocked i h
    simp only [BayesNet.BlockedAt] at hn
    have hnA : ¬ (b.Edge p[i] p[i + 1] ∧ b.Edge p[i + 2] p[i + 1] ∧
        ∀ d, b.IsDescendant p[i + 1] d → d ∉ Z) := fun h => hn (Or.inl h)
    by_contra hc
    push Not at hc
    exact hnA ⟨e1, e2, hc⟩
  have hright : ∀ (d k : ℕ) (hk : k < p.length) (hlt : k + d < p.length)
      (hall : ∀ (j : ℕ) (hj1 : k ≤ j) (hj2 : j + 1 < p.length)
        (hj3 : j < k + d), b.Edge p[j] p[j + 1]),
      Relation.ReflTransGen b.Edge p[k] p[k + d] := by
    intro d
    induction d with
    | zero =>
        intro k hk hlt hall
        simpa using
          (Relation.ReflTransGen.refl : Relation.ReflTransGen b.Edge p[k] p[k])
    | succ d ih =>
        intro k hk hlt hall
        have hmem1 : k + 1 < p.length := by omega
        have e0 : b.Edge p[k] p[k + 1] := hall k le_rfl hmem1 (by omega)
        have h1 : Relation.ReflTransGen b.Edge p[k + 1] p[k + (d + 1)] := by
          have hmem : k + 1 + d < p.length := by omega
          have hall' : ∀ (j : ℕ) (hj1 : k + 1 ≤ j) (hj2 : j + 1 < p.length)
              (hj3 : j < k + 1 + d), b.Edge p[j] p[j + 1] := by
            intro j hj1 hjlt hj2
            exact hall j (by omega) hjlt (by omega)
          have h := ih (k + 1) hmem1 hmem hall'
          have hcongr : p[k + 1 + d] = p[k + (d + 1)] := by congr 1; omega
          rwa [hcongr] at h
        exact Relation.ReflTransGen.head e0 h1
  have hleft : ∀ (d k : ℕ) (hk : k < p.length) (hle : d ≤ k)
      (hkd : k - d < p.length)
      (hall : ∀ (j : ℕ) (hj1 : k - d ≤ j) (hj2 : j < k)
        (hj3 : j + 1 < p.length), b.Edge p[j + 1] p[j]),
      Relation.ReflTransGen b.Edge p[k] p[k - d] := by
    intro d
    induction d with
    | zero =>
        intro k hk hle hkd hall
        simpa using
          (Relation.ReflTransGen.refl : Relation.ReflTransGen b.Edge p[k] p[k])
    | succ d ih =>
        intro k hk hle hkd hall
        have hkm1 : k - 1 < p.length := by omega
        have e0 : b.Edge p[k] p[k - 1] := by
          have h1 : k - (d + 1) ≤ k - 1 := by omega
          have h2 : k - 1 < k := by omega
          have h := hall (k - 1) h1 h2 (by omega)
          have hcongr : p[k - 1 + 1] = p[k] := by congr 1; omega
          rwa [hcongr] at h
        have h1 : Relation.ReflTransGen b.Edge p[k - 1] p[k - (d + 1)] := by
          have hle' : d ≤ k - 1 := by omega
          have hkd' : k - 1 - d < p.length := by omega
          have hall' : ∀ (j : ℕ) (hj1 : k - 1 - d ≤ j) (hj2 : j < k - 1)
              (hj3 : j + 1 < p.length), b.Edge p[j + 1] p[j] := by
            intro j hj1 hj2 hjlt
            exact hall j (by omega) (by omega) hjlt
          have h := ih (k - 1) hkm1 hle' hkd' hall'
          have hcongr : p[k - 1 - d] = p[k - (d + 1)] := by congr 1; omega
          rwa [hcongr] at h
        exact Relation.ReflTransGen.head e0 h1
  by_cases hall_right : ∀ (j : ℕ) (hj1 : k ≤ j) (hj2 : j + 1 < p.length),
      b.Edge p[j] p[j + 1]
  · have hlastlt : p.length - 1 < p.length := by omega
    have hRTC : Relation.ReflTransGen b.Edge p[k] p[p.length - 1] := by
      have hlen : k + (p.length - 1 - k) = p.length - 1 := by omega
      have hkd : k + (p.length - 1 - k) < p.length := by omega
      have hall' : ∀ (j : ℕ) (hj1 : k ≤ j) (hj2 : j + 1 < p.length)
          (hj3 : j < k + (p.length - 1 - k)), b.Edge p[j] p[j + 1] := by
        intro j hj1 hjlt hj2
        exact hall_right j hj1 hjlt
      have h := hright (p.length - 1 - k) k hk hkd hall'
      have hcongr : p[k + (p.length - 1 - k)] = p[p.length - 1] := by congr 1
      rwa [hcongr] at h
    refine ⟨y, Or.inl (by simp), ?_⟩
    rw [← hy]
    exact hRTC
  · have hexR : ∃ j, ∃ (_ : j + 1 < p.length),
        k ≤ j ∧ ¬ b.Edge p[j] p[j + 1] := by
      by_contra hc
      apply hall_right
      intro j hj1 hjlt
      by_contra hnc
      exact hc ⟨j, hjlt, hj1, hnc⟩
    obtain ⟨hjlt, hkj, hjn⟩ := Nat.find_spec hexR
    have hmin : ∀ (j' : ℕ) (hb : j' + 1 < p.length) (hle : k ≤ j')
        (hlt : j' < Nat.find hexR), b.Edge p[j'] p[j' + 1] := by
      intro j' hj'lt hj'1 hj'2
      by_contra hc
      have hle : Nat.find hexR ≤ j' := Nat.find_min' hexR ⟨hj'lt, hj'1, hc⟩
      omega
    have hRTCkj : Relation.ReflTransGen b.Edge p[k] p[Nat.find hexR] := by
      have hlen : k + (Nat.find hexR - k) = Nat.find hexR := by omega
      have hkd : k + (Nat.find hexR - k) < p.length := by omega
      have hall' : ∀ (j : ℕ) (hj1 : k ≤ j) (hj2 : j + 1 < p.length)
          (hj3 : j < k + (Nat.find hexR - k)), b.Edge p[j] p[j + 1] := by
        intro j hj1 hjlt hj2
        exact hmin j hjlt hj1 (by omega)
      have h := hright (Nat.find hexR - k) k hk hkd hall'
      have hcongr : p[k + (Nat.find hexR - k)] = p[Nat.find hexR] := by congr 1
      rwa [hcongr] at h
    have hadjfind : b.Edge p[Nat.find hexR + 1] p[Nat.find hexR] := by
      have h := hadj (Nat.find hexR) hjlt
      simp only [BayesNet.Adj] at h
      cases h with
      | inl h => exact absurd h hjn
      | inr h => exact h
    rcases eq_or_lt_of_le hkj with hkk | hkk
    · have hexS : ∃ t, ∀ (j : ℕ) (hj1 : t ≤ j) (hj2 : j < k)
          (hj3 : j + 1 < p.length), b.Edge p[j + 1] p[j] :=
        ⟨k, fun j h1 h2 _ => absurd h2 (by omega)⟩
      have hSspec : ∀ (j : ℕ) (hj1 : Nat.find hexS ≤ j) (hj2 : j < k)
          (hj3 : j + 1 < p.length), b.Edge p[j + 1] p[j] := Nat.find_spec hexS
      have hSmin : ∀ (t : ℕ), (∀ (j : ℕ) (hj1 : t ≤ j) (hj2 : j < k)
          (hj3 : j + 1 < p.length), b.Edge p[j + 1] p[j]) →
          Nat.find hexS ≤ t :=
        fun t ht => Nat.find_min' hexS ht
      have hsk : Nat.find hexS ≤ k :=
        hSmin k (fun j h1 h2 _ => absurd h2 (by omega))
      have hfindSlt : Nat.find hexS < p.length := by omega
      have hRTC : Relation.ReflTransGen b.Edge p[k] p[Nat.find hexS] := by
        have hlen : k - (k - Nat.find hexS) = Nat.find hexS := by omega
        have hkd : k - (k - Nat.find hexS) < p.length := by omega
        have hall' : ∀ (j : ℕ) (hj1 : k - (k - Nat.find hexS) ≤ j)
            (hj2 : j < k) (hj3 : j + 1 < p.length), b.Edge p[j + 1] p[j] := by
          intro j hj1 hj2 hjlt
          exact hSspec j (by omega) hj2 hjlt
        have h := hleft (k - Nat.find hexS) k hk (by omega) hkd hall'
        have hcongr : p[k - (k - Nat.find hexS)] = p[Nat.find hexS] := by congr 1
        rwa [hcongr] at h
      have hklen : k + 1 < p.length := by omega
      rcases Nat.eq_zero_or_pos (Nat.find hexS) with ht0 | htpos
      · have hcongr : p[Nat.find hexS] = p[0] := by congr 1
        rw [hcongr] at hRTC
        refine ⟨x, Or.inl (by simp), ?_⟩
        rw [← hx]
        exact hRTC
      · have hbadlt : Nat.find hexS - 1 + 1 < p.length := by omega
        have hbad : ¬ b.Edge p[Nat.find hexS - 1 + 1] p[Nat.find hexS - 1] := by
          intro hc
          have hS : ∀ (j : ℕ) (hj1 : Nat.find hexS - 1 ≤ j) (hj2 : j < k)
              (hj3 : j + 1 < p.length), b.Edge p[j + 1] p[j] := by
            intro j hj1 hj2 hjlt
            rcases eq_or_lt_of_le hj1 with hje | hjl
            · subst hje
              exact hc
            · exact hSspec j (by omega) hj2 hjlt
          have hle := hSmin _ hS
          omega
        have hbelow : b.Edge p[Nat.find hexS - 1] p[Nat.find hexS - 1 + 1] := by
          have hlt : Nat.find hexS - 1 + 1 < p.length := by omega
          have h := hadj (Nat.find hexS - 1) hlt
          simp only [BayesNet.Adj] at h
          cases h with
          | inl h => exact h
          | inr h => exact absurd h hbad
        have habovelt : Nat.find hexS + 1 < p.length := by omega
        have habove : b.Edge p[Nat.find hexS + 1] p[Nat.find hexS] := by
          rcases lt_or_eq_of_le hsk with hlt | heq
          · exact hSspec _ le_rfl hlt habovelt
          · have hc1 : p[Nat.find hexS + 1] = p[Nat.find hexR + 1] := by
              congr 1; omega
            have hc2 : p[Nat.find hexS] = p[Nat.find hexR] := by congr 1; omega
            rw [hc1, hc2]
            exact hadjfind
        have hi2 : Nat.find hexS - 1 + 2 < p.length := by omega
        have e2 : b.Edge p[Nat.find hexS - 1 + 2] p[Nat.find hexS - 1 + 1] := by
          have hc1 : p[Nat.find hexS - 1 + 2] = p[Nat.find hexS + 1] := by
            congr 1; omega
          have hc2 : p[Nat.find hexS - 1 + 1] = p[Nat.find hexS] := by
            congr 1; omega
          rw [hc1, hc2]
          exact habove
        obtain ⟨d, hdesc, hdZ⟩ := hcoll (Nat.find hexS - 1) hi2 hbelow e2
        have hdesc' : Relation.ReflTransGen b.Edge p[Nat.find hexS] d := by
          have hc : p[Nat.find hexS - 1 + 1] = p[Nat.find hexS] := by
            congr 1; omega
          rw [hc] at hdesc
          exact hdesc
        exact ⟨d, Or.inr hdZ, hRTC.trans hdesc'⟩
    · have hi2 : Nat.find hexR - 1 + 2 < p.length := by omega
      have e1 : b.Edge p[Nat.find hexR - 1] p[Nat.find hexR - 1 + 1] :=
        hmin _ (by omega) (by omega) (by omega)
      have e2 : b.Edge p[Nat.find hexR - 1 + 2] p[Nat.find hexR - 1 + 1] := by
        have hc1 : p[Nat.find hexR - 1 + 2] = p[Nat.find hexR + 1] := by
          congr 1; omega
        have hc2 : p[Nat.find hexR - 1 + 1] = p[Nat.find hexR] := by
          congr 1; omega
        rw [hc1, hc2]
        exact hadjfind
      obtain ⟨d, hdesc, hdZ⟩ := hcoll (Nat.find hexR - 1) hi2 e1 e2
      have hdesc' : Relation.ReflTransGen b.Edge p[Nat.find hexR] d := by
        have hc : p[Nat.find hexR - 1 + 1] = p[Nat.find hexR] := by
          congr 1; omega
        rw [hc] at hdesc
        exact hdesc
      exact ⟨d, Or.inr hdZ, hRTCkj.trans hdesc'⟩

/-- Chaining two lists over a shared boundary vertex. -/
private theorem isChain_append {r : Fin n → Fin n → Prop} {A B : List (Fin n)}
    {al bh : Fin n} (hA : A.IsChain r) (hB : B.IsChain r)
    (hAl : A.getLast? = some al) (hBh : B.head? = some bh) (hadj : r al bh) :
    (A ++ B).IsChain r := by
  have hlenA : 0 < A.length := by
    cases A with
    | nil => simp at hAl
    | cons _ _ => simp
  have hlenB : 0 < B.length := by
    cases B with
    | nil => simp at hBh
    | cons _ _ => simp
  have hal : A[A.length - 1] = al := by
    rw [List.getLast?_eq_getElem?] at hAl
    obtain ⟨_, h2⟩ := List.getElem_of_getElem? hAl
    exact h2
  have hbh : B[0] = bh := by
    rw [List.head?_eq_getElem?] at hBh
    obtain ⟨_, h2⟩ := List.getElem_of_getElem? hBh
    exact h2
  rw [List.isChain_iff_getElem]
  intro i hi
  have hlen : (A ++ B).length = A.length + B.length := List.length_append ..
  rw [hlen] at hi
  by_cases h1 : i + 1 < A.length
  · have e1 : (A ++ B)[i] = A[i] := List.getElem_append_left (by omega)
    have e2 : (A ++ B)[i + 1] = A[i + 1] := List.getElem_append_left h1
    rw [e1, e2]
    exact (List.isChain_iff_getElem.mp hA) i h1
  · by_cases h2 : i + 1 = A.length
    · have hiA : i < A.length := by omega
      have e1 : (A ++ B)[i] = al := by
        rw [List.getElem_append_left hiA]
        have hc : A[i] = A[A.length - 1] := by congr 1; omega
        rw [hc, hal]
      have e2 : (A ++ B)[i + 1] = bh := by
        have hge : A.length ≤ i + 1 := by omega
        rw [List.getElem_append_right hge]
        have hc : B[i + 1 - A.length] = B[0] := by congr 1; omega
        rw [hc, hbh]
      rw [e1, e2]
      exact hadj
    · have hge : A.length ≤ i := by omega
      have hge1 : A.length ≤ i + 1 := by omega
      have e1 : (A ++ B)[i] = B[i - A.length] := List.getElem_append_right hge
      have e2 : (A ++ B)[i + 1] = B[i - A.length + 1] := by
        rw [List.getElem_append_right hge1]
        congr 1
        omega
      rw [e1, e2]
      exact (List.isChain_iff_getElem.mp hB) _ (by omega)

/-- Vertices of a directed path as a list, from `u` to `v`. -/
private theorem exists_chain_of_reflTransGen {α : Type*} {n : ℕ} (b : BayesNet α n)
    {u v : Fin n} (h : Relation.ReflTransGen b.Edge u v) :
    ∃ D : List (Fin n), D.IsChain b.Edge ∧ D.head? = some u ∧ D.getLast? = some v ∧
      (∀ w ∈ D, Relation.ReflTransGen b.Edge u w) := by
  induction h with
  | refl =>
      refine ⟨[u], by simp, rfl, rfl, ?_⟩
      intro w hw
      simp at hw
      subst hw
      exact Relation.ReflTransGen.refl
  | @tail c d h1 h2 ih =>
      obtain ⟨D, hchain, hhead, hlast, hmem⟩ := ih
      refine ⟨D ++ [d], ?_, ?_, ?_, ?_⟩
      · have hlast' : D.getLast? = some c := hlast
        have hhead' : ([d] : List (Fin n)).head? = some d := rfl
        exact isChain_append hchain (by simp) hlast' hhead' h2
      · cases D with
        | nil =>
            simp at hhead
        | cons x l =>
            simp at hhead ⊢
            exact hhead
      · simp
      · intro w hw
        rw [List.mem_append] at hw
        rcases hw with hw | hw
        · exact hmem w hw
        · simp at hw
          subst hw
          exact Relation.ReflTransGen.tail h1 h2

/-- A reversed directed chain is a skeleton chain. -/
private theorem isChain_reverse_adj_of_edgeChain {D : List (Fin n)}
    (hchain : D.IsChain b.Edge) : D.reverse.IsChain b.Adj := by
  rw [List.isChain_reverse, List.isChain_iff_getElem]
  intro i hi
  exact Or.inr ((List.isChain_iff_getElem.mp hchain) i hi)

/-- Triples on a reversed directed chain point out of the middle vertex. -/
private theorem edge_out_of_reverse_edgeChain {D : List (Fin n)}
    (hchain : D.IsChain b.Edge) (i : ℕ) (hi : i + 2 < D.reverse.length) :
    b.Edge D.reverse[i + 1] D.reverse[i] := by
  have hlen : D.reverse.length = D.length := List.length_reverse ..
  have e1 : D.reverse[i] = D[D.length - 1 - i] :=
    List.getElem_reverse (by omega)
  have e2 : D.reverse[i + 1] = D[D.length - 1 - (i + 1)] :=
    List.getElem_reverse (by omega)
  rw [e1, e2]
  have hch := List.isChain_iff_getElem.mp hchain
  have hk : D.length - 1 - (i + 1) + 1 < D.length := by omega
  have h := hch _ hk
  have hc : D[D.length - 1 - (i + 1) + 1] = D[D.length - 1 - i] := by congr 1; omega
  rw [hc] at h
  exact h

/-- Middle vertices of a reversed chain lie on the chain. -/
private theorem mem_of_reverse_getElem {D : List (Fin n)} (i : ℕ)
    (hi : i < D.reverse.length) : D.reverse[i] ∈ D :=
  List.mem_reverse.mp (List.getElem_mem hi)

open Classical in
/-- Number of triples of `L` blocked by `Z`. -/
private noncomputable def blockedCount {α : Type*} {n : ℕ} (b : BayesNet α n)
    (Z : Set (Fin n)) : List (Fin n) → ℕ
  | [] => 0
  | [_] => 0
  | [_, _] => 0
  | a :: c :: e :: rest =>
      (if b.BlockedAt Z a c e then 1 else 0) + blockedCount b Z (c :: e :: rest)

open Classical in
/-- Blocked spanning triples of a list append. -/
private noncomputable def junctionCount {α : Type*} {n : ℕ} (b : BayesNet α n)
    (Z : Set (Fin n)) : List (Fin n) → List (Fin n) → ℕ
  | A, B =>
    match A.reverse, B with
    | y :: x :: _, b1 :: b2 :: _ =>
        (if b.BlockedAt Z x y b1 then 1 else 0) + (if b.BlockedAt Z y b1 b2 then 1 else 0)
    | [y], b1 :: b2 :: _ => if b.BlockedAt Z y b1 b2 then 1 else 0
    | y :: x :: _, [b1] => if b.BlockedAt Z x y b1 then 1 else 0
    | _, _ => 0

/-- The blocked count splits over appends, up to spanning triples. -/
private theorem blockedCount_append {α : Type*} {n : ℕ} (b : BayesNet α n)
    (Z : Set (Fin n)) (A B : List (Fin n)) :
    b.blockedCount Z (A ++ B) =
      b.blockedCount Z A + b.blockedCount Z B + b.junctionCount Z A B := by
  classical
  induction A with
  | nil => simp [blockedCount, junctionCount]
  | cons a A ih =>
      cases A with
      | nil =>
          cases B with
          | nil => simp [blockedCount, junctionCount]
          | cons b1 B =>
              cases B with
              | nil => simp [blockedCount, junctionCount]
              | cons b2 B' => simp [blockedCount, junctionCount]; ring
      | cons c A' =>
          cases A' with
          | nil =>
              cases B with
              | nil => simp [blockedCount, junctionCount]
              | cons b1 B =>
                  cases B with
                  | nil => simp [blockedCount, junctionCount]
                  | cons b2 B' => simp [blockedCount, junctionCount]; ring
          | cons e rest =>
              have hj : b.junctionCount Z (a :: c :: e :: rest) B =
                  b.junctionCount Z (c :: e :: rest) B := by
                cases hrev : (c :: e :: rest).reverse with
                | nil =>
                    exfalso
                    have hlen : (c :: e :: rest).length = 0 := by
                      have h := congrArg List.length hrev
                      rwa [List.length_reverse] at h
                    simp at hlen
                | cons y R =>
                    cases R with
                    | nil =>
                        exfalso
                        have hlen : (c :: e :: rest).length = 1 := by
                          have h := congrArg List.length hrev
                          rwa [List.length_reverse] at h
                        simp at hlen
                    | cons x R' =>
                        have hArev : (a :: c :: e :: rest).reverse =
                            y :: x :: (R' ++ [a]) := by
                          simp [List.reverse_cons, hrev]
                        cases B with
                        | nil => simp only [junctionCount, hArev, hrev]
                        | cons b1 B =>
                            cases B with
                            | nil => simp only [junctionCount, hArev, hrev]
                            | cons b2 B' => simp only [junctionCount, hArev, hrev]
              have eL : b.blockedCount Z ((a :: c :: e :: rest) ++ B) =
                  (if b.BlockedAt Z a c e then 1 else 0) +
                    b.blockedCount Z ((c :: e :: rest) ++ B) := by
                have happ : (a :: c :: e :: rest) ++ B = a :: c :: e :: (rest ++ B) := rfl
                rw [happ]
                rfl
              have eA : b.blockedCount Z (a :: c :: e :: rest) =
                  (if b.BlockedAt Z a c e then 1 else 0) +
                    b.blockedCount Z (c :: e :: rest) := rfl
              rw [eL, eA, ih, hj]
              omega

/-- A reversed directed chain avoiding `Z` has no blocked triples. -/
private theorem blockedCount_reverse_of_edgeChain {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {D : List (Fin n)} :
    D.IsChain b.Edge → (∀ v ∈ D, v ∉ Z) → b.blockedCount Z D.reverse = 0 := by
  classical
  induction D with
  | nil => intro _ _; simp [blockedCount]
  | cons x D ih =>
      intro hchain hZ
      cases D with
      | nil => simp [blockedCount]
      | cons y D' =>
          cases D' with
          | nil => simp [blockedCount]
          | cons z rest =>
              have hchain' : (y :: z :: rest).IsChain b.Edge :=
                List.IsChain.of_cons hchain
              have hZ' : ∀ v ∈ y :: z :: rest, v ∉ Z :=
                fun v hv => hZ v (List.mem_cons_of_mem x hv)
              have hIH := ih hchain' hZ'
              have happ : (x :: y :: z :: rest).reverse =
                  (y :: z :: rest).reverse ++ [x] := List.reverse_cons ..
              have hyz : b.Edge y z :=
                (List.isChain_iff_getElem.mp hchain') 0 (by simp)
              have hncoll : ¬ (b.Edge z y ∧ b.Edge x y) := by
                rintro ⟨hzy, -⟩
                obtain ⟨hlt1, _⟩ := hyz
                obtain ⟨hlt2, _⟩ := hzy
                omega
              have hyZ : y ∉ Z := hZ y (by simp)
              have hunblocked : ¬ b.BlockedAt Z z y x := by
                simp only [BayesNet.BlockedAt]
                rintro (⟨h1, h2, _⟩ | ⟨_, hyZ'⟩)
                · exact hncoll ⟨h1, h2⟩
                · exact hyZ hyZ'
              have hJ : b.junctionCount Z (y :: z :: rest).reverse [x] = 0 := by
                have hrev : ((y :: z :: rest).reverse).reverse = y :: z :: rest :=
                  List.reverse_reverse ..
                simp only [junctionCount, hrev]
                rw [ite_eq_right hunblocked]
              rw [happ, blockedCount_append _ _ _ _, hIH, hJ]
              simp [blockedCount]

/-- A blocked triple forces the blocked count to be positive. -/
private theorem blockedCount_ge_one_of_blockedAt {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T : List (Fin n)} {i : ℕ} :
    (hi : i + 2 < T.length) → b.BlockedAt Z T[i] T[i + 1] T[i + 2] →
      1 ≤ b.blockedCount Z T := by
  classical
  induction i generalizing T with
  | zero =>
      intro hi hblk
      cases T with
      | nil => simp at hi
      | cons a T' =>
          cases T' with
          | nil => simp at hi
          | cons c T'' =>
              cases T'' with
              | nil => simp at hi
              | cons e rest =>
                  have hblk' : b.BlockedAt Z a c e := hblk
                  have hcount : b.blockedCount Z (a :: c :: e :: rest) =
                      (if b.BlockedAt Z a c e then 1 else 0) +
                        b.blockedCount Z (c :: e :: rest) := rfl
                  rw [hcount, ite_eq_left hblk']
                  omega
  | succ i ih =>
      intro hi hblk
      cases T with
      | nil => simp at hi
      | cons a T' =>
          cases T' with
          | nil => simp at hi
          | cons c T'' =>
              cases T'' with
              | nil => simp at hi
              | cons e rest' =>
                  have hlen : (a :: c :: e :: rest').length =
                      (c :: e :: rest').length + 1 := rfl
                  have hb2 : i + 2 < (c :: e :: rest').length := by omega
                  have hblk' : b.BlockedAt Z (c :: e :: rest')[i] (c :: e :: rest')[i + 1]
                      (c :: e :: rest')[i + 2] := hblk
                  have hcount : b.blockedCount Z (a :: c :: e :: rest') =
                      (if b.BlockedAt Z a c e then 1 else 0) +
                        b.blockedCount Z (c :: e :: rest') := rfl
                  rw [hcount]
                  have hIH := ih (T := c :: e :: rest') (by omega) hblk'
                  omega

/-- A vertex of a directed chain ending at `s` reaches `s`. -/
private theorem reflTransGen_of_mem_edgeChain {α : Type*} {n : ℕ} (b : BayesNet α n)
    {D : List (Fin n)} {s w : Fin n}
    (hchain : D.IsChain b.Edge) (hlast : D.getLast? = some s) (hw : w ∈ D) :
    Relation.ReflTransGen b.Edge w s := by
  rw [List.getLast?_eq_getElem?] at hlast
  obtain ⟨_, hs⟩ := List.getElem_of_getElem? hlast
  subst hs
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hw
  have hch := List.isChain_iff_getElem.mp hchain
  have key : ∀ (d k : ℕ) (hk : k < D.length) (_ : k + d = D.length - 1),
      Relation.ReflTransGen b.Edge D[k] D[D.length - 1] := by
    intro d
    induction d with
    | zero =>
        intro k hk hd
        have hkk : k = D.length - 1 := by omega
        subst hkk
        exact Relation.ReflTransGen.refl
    | succ d ih =>
        intro k hk hd
        have e0 : b.Edge D[k] D[k + 1] := hch k (by omega)
        have h1 : Relation.ReflTransGen b.Edge D[k + 1] D[D.length - 1] :=
          ih (k + 1) (by omega) (by omega)
        exact Relation.ReflTransGen.head e0 h1
  exact key (D.length - 1 - k) k hk (by omega)

/-- A directed chain avoiding `Z` has no blocked triples. -/
private theorem blockedCount_of_edgeChain {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {D : List (Fin n)} :
    D.IsChain b.Edge → (∀ v ∈ D, v ∉ Z) → b.blockedCount Z D = 0 := by
  classical
  induction D with
  | nil => intro _ _; simp [blockedCount]
  | cons x D ih =>
      intro hchain hZ
      cases D with
      | nil => simp [blockedCount]
      | cons y D' =>
          cases D' with
          | nil => simp [blockedCount]
          | cons z rest =>
              have hchain' : (y :: z :: rest).IsChain b.Edge :=
                List.IsChain.of_cons hchain
              have hZ' : ∀ v ∈ y :: z :: rest, v ∉ Z :=
                fun v hv => hZ v (List.mem_cons_of_mem x hv)
              have hIH := ih hchain' hZ'
              have hyz : b.Edge y z :=
                (List.isChain_iff_getElem.mp hchain') 0 (by simp)
              have hncoll : ¬ (b.Edge x y ∧ b.Edge z y) := by
                rintro ⟨-, hzy⟩
                obtain ⟨hlt1, _⟩ := hyz
                obtain ⟨hlt2, _⟩ := hzy
                omega
              have hyZ : y ∉ Z := hZ y (by simp)
              have hunblocked : ¬ b.BlockedAt Z x y z := by
                simp only [BayesNet.BlockedAt]
                rintro (⟨h1, h2, _⟩ | ⟨_, hyZ'⟩)
                · exact hncoll ⟨h1, h2⟩
                · exact hyZ hyZ'
              have hcount : b.blockedCount Z (x :: y :: z :: rest) =
                  (if b.BlockedAt Z x y z then 1 else 0) +
                    b.blockedCount Z (y :: z :: rest) := rfl
              rw [hcount, ite_eq_right hunblocked, hIH]

/-- Splice out the loop between duplicate indices `i < j` of `T`. -/
private def splice {β : Type*} (T : List β) (i j : ℕ) : List β :=
  T.take (i + 1) ++ T.drop (j + 1)

/-- Length of a splice. -/
private theorem length_splice {β : Type*} (T : List β) (i j : ℕ)
    (hle : i + 1 ≤ T.length) :
    (splice T i j).length = i + 1 + (T.length - (j + 1)) := by
  rw [splice, List.length_append, List.length_take, List.length_drop,
    Nat.min_eq_left hle]

/-- Vertices before the splice point are unchanged. -/
private theorem getElem_splice_of_lt {β : Type*} (T : List β) (i j k : ℕ)
    (hk : k < i + 1) (hlen : k < T.length) (hlenS : k < (splice T i j).length) :
    (splice T i j)[k] = T[k] := by
  have h1 : k < (T.take (i + 1)).length := by
    rw [List.length_take]
    omega
  have hlenS' : k < (T.take (i + 1) ++ T.drop (j + 1)).length := hlenS
  show (T.take (i + 1) ++ T.drop (j + 1))[k] = T[k]
  rw [List.getElem_append_left h1, List.getElem_take]

/-- Vertices at and after the splice point shift past the removed segment. -/
private theorem getElem_splice_of_ge {β : Type*} (T : List β) (i j k : ℕ)
    (hk : i + 1 ≤ k) (hlen : k < (splice T i j).length)
    (hle : i + 1 ≤ T.length) (hlenT : (j + 1) + (k - (i + 1)) < T.length) :
    (splice T i j)[k] = T[(j + 1) + (k - (i + 1))] := by
  have htake : (T.take (i + 1)).length = i + 1 := by
    rw [List.length_take, Nat.min_eq_left hle]
  have hge : (T.take (i + 1)).length ≤ k := by omega
  have hlen' : k < (T.take (i + 1) ++ T.drop (j + 1)).length := hlen
  show (T.take (i + 1) ++ T.drop (j + 1))[k] = T[(j + 1) + (k - (i + 1))]
  rw [List.getElem_append_right hge, List.getElem_drop]
  congr 1
  omega

/-- A splice at duplicate indices keeps the chain property. -/
private theorem isChain_splice {n : ℕ} {r : Fin n → Fin n → Prop} {T : List (Fin n)}
    {i j : ℕ} (hchain : T.IsChain r) (hij : i < j) (hj : j + 1 < T.length)
    (hdup : T[i] = T[j]) : (splice T i j).IsChain r := by
  have hle : i + 1 ≤ T.length := by omega
  have hlen : (splice T i j).length = i + 1 + (T.length - (j + 1)) :=
    length_splice T i j hle
  have hch := List.isChain_iff_getElem.mp hchain
  rw [List.isChain_iff_getElem]
  intro k hk
  have hk' := hk
  rw [hlen] at hk'
  by_cases h1 : k + 1 < i + 1
  · have e1 : (splice T i j)[k] = T[k] :=
      getElem_splice_of_lt T i j k (by omega) (by omega) (by omega)
    have e2 : (splice T i j)[k + 1] = T[k + 1] :=
      getElem_splice_of_lt T i j (k + 1) h1 (by omega) hk
    rw [e1, e2]
    exact hch k (by omega)
  · by_cases h2 : k + 1 = i + 1
    · have hki : k = i := by omega
      subst k
      have e1 : (splice T i j)[i] = T[i] :=
        getElem_splice_of_lt T i j i (by omega) (by omega) (by omega)
      have e2 : (splice T i j)[i + 1] = T[(j + 1) + (i + 1 - (i + 1))] :=
        getElem_splice_of_ge T i j (i + 1) (by omega) hk hle (by omega)
      rw [e1, e2]
      have heq : T[(j + 1) + (i + 1 - (i + 1))] = T[j + 1] := by
        congr 1
        omega
      rw [heq, hdup]
      exact hch j hj
    · have hge : i + 1 ≤ k := by omega
      have e1 : (splice T i j)[k] = T[(j + 1) + (k - (i + 1))] :=
        getElem_splice_of_ge T i j k hge (by omega) hle (by omega)
      have e2 : (splice T i j)[k + 1] = T[(j + 1) + (k + 1 - (i + 1))] :=
        getElem_splice_of_ge T i j (k + 1) (by omega) (by omega) hle (by omega)
      rw [e1, e2]
      have heq : T[(j + 1) + (k + 1 - (i + 1))] = T[((j + 1) + (k - (i + 1))) + 1] := by
        congr 1
        omega
      rw [heq]
      exact hch _ (by omega)

/-- A splice keeps the first vertex. -/
private theorem head?_splice {n : ℕ} {T : List (Fin n)} {i j : ℕ}
    (hij : i < j) (hj : j + 1 < T.length) :
    (splice T i j).head? = T.head? := by
  have hle : i + 1 ≤ T.length := by omega
  have hlen : (splice T i j).length = i + 1 + (T.length - (j + 1)) :=
    length_splice T i j hle
  have hS : 0 < (splice T i j).length := by omega
  have hT : 0 < T.length := by omega
  rw [List.head?_eq_getElem?, List.head?_eq_getElem?,
    List.getElem?_eq_getElem hS, List.getElem?_eq_getElem hT]
  congr 1
  exact getElem_splice_of_lt T i j 0 (by omega) (by omega) (by omega)

/-- A splice keeps the last vertex. -/
private theorem getLast?_splice {n : ℕ} {T : List (Fin n)} {i j : ℕ}
    (hij : i < j) (hj : j + 1 < T.length) :
    (splice T i j).getLast? = T.getLast? := by
  have hle : i + 1 ≤ T.length := by omega
  have hlen : (splice T i j).length = i + 1 + (T.length - (j + 1)) :=
    length_splice T i j hle
  have hS : (splice T i j).length - 1 < (splice T i j).length := by omega
  have hT : T.length - 1 < T.length := by omega
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem hS, List.getElem?_eq_getElem hT]
  congr 1
  have e' := getElem_splice_of_ge T i j ((splice T i j).length - 1) (by omega) hS hle
    (by omega)
  have heq : T[(j + 1) + ((splice T i j).length - 1 - (i + 1))] = T[T.length - 1] := by
    congr 1
    omega
  rw [e', heq]

/-- A splice keeps vertices inside the ancestral closure. -/
private theorem mem_ancestorsOf_of_mem_splice {α : Type*} {n : ℕ} (b : BayesNet α n)
    {S : Set (Fin n)} {T : List (Fin n)} {i j : ℕ} {v : Fin n}
    (hA : ∀ v ∈ T, v ∈ b.ancestorsOf S) (hv : v ∈ splice T i j) :
    v ∈ b.ancestorsOf S := by
  rw [splice, List.mem_append] at hv
  rcases hv with hv | hv
  · exact hA v (List.mem_of_mem_take hv)
  · exact hA v (List.mem_of_mem_drop hv)

/-- A moral walk avoiding `Z` expands to a skeleton trail whose `Z`-members
are colliders. -/
private theorem exists_trail_of_moralWalk {α : Type*} {n : ℕ} (b : BayesNet α n)
    {X Y Z : Set (Fin n)} :
    ∀ {x y : Fin n} (w : (b.moralGraph (b.ancestorsOf (X ∪ Y ∪ Z))).Walk x y),
      x ∈ b.ancestorsOf (X ∪ Y ∪ Z) → (∀ v ∈ w.support, v ∉ Z) →
      ∃ T : List (Fin n), T.IsChain b.Adj ∧ T.head? = some x ∧ T.getLast? = some y ∧
        (∀ v ∈ T, v ∈ b.ancestorsOf (X ∪ Y ∪ Z)) ∧
        (∀ (i : ℕ) (hi : i + 2 < T.length), T[i + 1] ∈ Z →
          b.Edge T[i] T[i + 1] ∧ b.Edge T[i + 2] T[i + 1]) := by
  intro x y w
  induction w with
  | @nil u =>
      intro hxA havoid
      refine ⟨[u], by simp, rfl, rfl, ?_, ?_⟩
      · intro v hv
        simp at hv
        subst hv
        exact hxA
      · intro i hi _
        have hlen : ([u] : List (Fin n)).length = 1 := rfl
        omega
  | @cons u v w h rest ih =>
      intro hxA havoid
      have havoid' : ∀ v ∈ rest.support, v ∉ Z := by
        intro a ha
        apply havoid
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ ha
      rw [b.moralGraph_adj] at h
      obtain ⟨_hxm, _hxA', hmA, hsk | hmar⟩ := h
      · -- skeleton edge: prepend u
        obtain ⟨L, hchainL, hheadL, hlastL, hAL, htripleL⟩ := ih hmA havoid'
        cases L with
        | nil =>
            simp at hheadL
        | cons m L' =>
            simp at hheadL
            subst hheadL
            have hmZ : m ∉ Z := by
              apply havoid
              rw [SimpleGraph.Walk.support_cons]
              exact List.mem_cons_of_mem _ rest.start_mem_support
            refine ⟨u :: m :: L', ?_, rfl, ?_, ?_, ?_⟩
            · exact List.IsChain.cons hchainL (fun y hy => by
                simp at hy
                subst hy
                exact hsk)
            · simpa using hlastL
            · intro v hv
              simp only [List.mem_cons] at hv
              rcases hv with rfl | rfl | hv
              · exact hxA
              · exact hmA
              · exact hAL v (List.mem_cons_of_mem m hv)
            · intro i hi hmem
              cases i with
              | zero =>
                  exfalso
                  exact hmZ hmem
              | succ i =>
                  have hlen : (u :: m :: L').length = (m :: L').length + 1 := rfl
                  have hi' : i + 2 < (m :: L').length := by omega
                  have hmem' : (m :: L')[i + 1] ∈ Z := hmem
                  exact htripleL i hi' hmem'
      · -- marrying edge: route through the common child
        obtain ⟨c, hcA, hxc, hmc⟩ := hmar
        obtain ⟨L, hchainL, hheadL, hlastL, hAL, htripleL⟩ := ih hmA havoid'
        cases L with
        | nil =>
            simp at hheadL
        | cons m L' =>
            simp at hheadL
            subst hheadL
            have hmZ : m ∉ Z := by
              apply havoid
              rw [SimpleGraph.Walk.support_cons]
              exact List.mem_cons_of_mem _ rest.start_mem_support
            have hxcA : b.Adj u c := Or.inl hxc
            have hcmA : b.Adj c m := Or.inr hmc
            have hcL : (c :: m :: L').IsChain b.Adj :=
              List.IsChain.cons hchainL (fun y hy => by
                simp at hy
                subst hy
                exact hcmA)
            refine ⟨u :: c :: m :: L', ?_, rfl, ?_, ?_, ?_⟩
            · exact List.IsChain.cons hcL (fun y hy => by
                simp at hy
                subst hy
                exact hxcA)
            · simpa using hlastL
            · intro v hv
              simp only [List.mem_cons] at hv
              rcases hv with rfl | rfl | rfl | hv
              · exact hxA
              · exact hcA
              · exact hmA
              · exact hAL v (List.mem_cons_of_mem m hv)
            · intro i hi hmem
              cases i with
              | zero =>
                  exact ⟨hxc, hmc⟩
              | succ i =>
                  cases i with
                  | zero =>
                      exfalso
                      exact hmZ hmem
                  | succ i =>
                      have hlen : (u :: c :: m :: L').length =
                          (m :: L').length + 2 := rfl
                      have hi' : i + 2 < (m :: L').length := by omega
                      have hmem' : (m :: L')[i + 1] ∈ Z := hmem
                      exact htripleL i hi' hmem'

/-- A blocked triple of a trail with the triple property is a bad collider:
middle outside `Z`, both edges point in, no descendant in `Z`. -/
private theorem bad_collider_of_blockedAt {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T : List (Fin n)} {k : ℕ}
    (htriple : ∀ (i : ℕ) (_ : i + 2 < T.length), T[i + 1] ∈ Z →
      b.Edge T[i] T[i + 1] ∧ b.Edge T[i + 2] T[i + 1])
    (hk : k + 2 < T.length)
    (hblk : b.BlockedAt Z T[k] T[k + 1] T[k + 2]) :
    T[k + 1] ∉ Z ∧ b.Edge T[k] T[k + 1] ∧ b.Edge T[k + 2] T[k + 1] ∧
      (∀ d, b.IsDescendant T[k + 1] d → d ∉ Z) := by
  have hnotZ : T[k + 1] ∉ Z := by
    intro hmem
    obtain ⟨e1, e2⟩ := htriple k hk hmem
    have hself : b.IsDescendant T[k + 1] T[k + 1] := Relation.ReflTransGen.refl
    simp only [BayesNet.BlockedAt] at hblk
    rcases hblk with ⟨_, _, hno⟩ | ⟨hncoll, _⟩
    · exact hno _ hself hmem
    · exact hncoll ⟨e1, e2⟩
  simp only [BayesNet.BlockedAt] at hblk
  rcases hblk with ⟨e1, e2, hno⟩ | ⟨_, hmem⟩
  · exact ⟨hnotZ, e1, e2, hno⟩
  · exact absurd hmem hnotZ

/-- An ancestor with no descendant in `Z` reaches `X ∪ Y`. -/
private theorem exists_mem_union_of_ancestorsOf {α : Type*} {n : ℕ} (b : BayesNet α n)
    {X Y Z : Set (Fin n)} {c : Fin n}
    (hc : c ∈ b.ancestorsOf (X ∪ Y ∪ Z))
    (hno : ∀ d, b.IsDescendant c d → d ∉ Z) :
    ∃ s ∈ X ∪ Y, b.IsDescendant c s := by
  obtain ⟨s, hs, hds⟩ := hc
  have hsZn : s ∉ Z := hno s hds
  simp only [Set.mem_union] at hs
  rcases hs with hsXY | hsZ
  · exact ⟨s, hsXY, hds⟩
  · exact (hsZn hsZ).elim

/-- Zero blocked count means every triple is unblocked. -/
private theorem not_blockedAt_of_blockedCount_eq_zero {α : Type*} {n : ℕ}
    (b : BayesNet α n) {Z : Set (Fin n)} {T : List (Fin n)}
    (h0 : b.blockedCount Z T = 0) (i : ℕ) (hi : i + 2 < T.length) :
    ¬ b.BlockedAt Z T[i] T[i + 1] T[i + 2] := by
  intro hblk
  have hge := b.blockedCount_ge_one_of_blockedAt hi hblk
  omega

/-- Vertices reachable from a bad collider avoid `Z`. -/
private theorem not_mem_of_reachable_of_bad {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {c w : Fin n}
    (hno : ∀ d, b.IsDescendant c d → d ∉ Z)
    (hrw : Relation.ReflTransGen b.Edge c w) : w ∉ Z :=
  hno w hrw

/-- Vertices of a directed chain to `X ∪ Y` lie in the ancestral closure. -/
private theorem mem_ancestorsOf_of_mem_edgeChain {α : Type*} {n : ℕ} (b : BayesNet α n)
    {X Y Z : Set (Fin n)} {D : List (Fin n)} {s w : Fin n}
    (hchain : D.IsChain b.Edge) (hlast : D.getLast? = some s) (hw : w ∈ D)
    (hs : s ∈ X ∪ Y) : w ∈ b.ancestorsOf (X ∪ Y ∪ Z) := by
  have hrs : Relation.ReflTransGen b.Edge w s :=
    b.reflTransGen_of_mem_edgeChain hchain hlast hw
  exact ⟨s, Set.mem_union_left Z hs, hrs⟩

/-- A non-duplicate-free list has duplicate indices. -/
private theorem exists_dup_of_not_nodup {β : Type*} {T : List β} :
    ¬ T.Nodup → ∃ (i j : ℕ) (hij : i < j) (hj : j < T.length), T[i] = T[j] := by
  induction T with
  | nil =>
      intro h
      exact (h List.nodup_nil).elim
  | cons a l ih =>
      intro h
      rw [List.nodup_cons] at h
      by_cases ha : a ∈ l
      · obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp ha
        have h0 : 0 < (a :: l).length := by simp
        have hj1 : j + 1 < (a :: l).length := by simp; omega
        have hlt : 0 < j + 1 := by omega
        refine ⟨0, j + 1, hlt, hj1, ?_⟩
        have e0 : (a :: l)[0] = a := List.getElem_cons_zero a l h0
        have e1 : (a :: l)[j + 1] = l[j] := List.getElem_cons_succ a l j hj1
        rw [e0, e1]
        exact hjeq.symm
      · have hnodup : ¬ l.Nodup := by
          intro hnl
          exact h ⟨ha, hnl⟩
        obtain ⟨i, j, hij, hjlen, hdup⟩ := ih hnodup
        have hi1 : i + 1 < (a :: l).length := by simp; omega
        have hj1 : j + 1 < (a :: l).length := by simp; omega
        have hlt : i + 1 < j + 1 := by omega
        refine ⟨i + 1, j + 1, hlt, hj1, ?_⟩
        have e1 : (a :: l)[i + 1] = l[i] := List.getElem_cons_succ a l i hi1
        have e2 : (a :: l)[j + 1] = l[j] := List.getElem_cons_succ a l j hj1
        rw [e1, e2]
        exact hdup

/-- Dropping a prefix cannot increase the blocked count. -/
private theorem blockedCount_drop_le {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T : List (Fin n)} (m : ℕ) :
    b.blockedCount Z (T.drop m) ≤ b.blockedCount Z T := by
  induction m generalizing T with
  | zero =>
      rw [List.drop_zero]
  | succ m ih =>
      cases T with
      | nil => simp [blockedCount]
      | cons a l =>
          have htail : b.blockedCount Z l ≤ b.blockedCount Z (a :: l) := by
            classical
            cases l with
            | nil => simp [blockedCount]
            | cons y l' =>
                cases l' with
                | nil => simp [blockedCount]
                | cons z rest =>
                    have hc : b.blockedCount Z (a :: y :: z :: rest) =
                        (if b.BlockedAt Z a y z then 1 else 0) +
                          b.blockedCount Z (y :: z :: rest) := rfl
                    rw [hc]
                    omega
          have hdrop : (a :: l).drop (m + 1) = l.drop m := rfl
          rw [hdrop]
          exact Nat.le_trans (ih (T := l)) htail

/-- Surgery (X-side): chain and endpoints of `D.reverse ++ drop (k+2) T`. -/
private theorem surgery_chain_X {α : Type*} {n : ℕ} (b : BayesNet α n)
    {T D : List (Fin n)} {k : ℕ} {s x0 y0 : Fin n}
    (hchainT : T.IsChain b.Adj)
    (hheadT : T.head? = some x0) (hlastT : T.getLast? = some y0)
    (hk : k + 2 < T.length)
    (hchainD : D.IsChain b.Edge) (hheadD : D.head? = some T[k + 1])
    (hlastD : D.getLast? = some s) :
    (D.reverse ++ T.drop (k + 2)).IsChain b.Adj ∧
      (D.reverse ++ T.drop (k + 2)).head? = some s ∧
      (D.reverse ++ T.drop (k + 2)).getLast? = some y0 := by
  have hchT := List.isChain_iff_getElem.mp hchainT
  have hA : D.reverse.IsChain b.Adj := isChain_reverse_adj_of_edgeChain b hchainD
  have hB : (T.drop (k + 2)).IsChain b.Adj := hchainT.drop (k + 2)
  have hAl : D.reverse.getLast? = some T[k + 1] := by
    rw [List.getLast?_reverse, hheadD]
  have hBh : (T.drop (k + 2)).head? = some T[k + 2] := by
    rw [List.head?_drop, List.getElem?_eq_getElem hk]
  have hadj : b.Adj T[k + 1] T[k + 2] := hchT (k + 1) hk
  have hchain : (D.reverse ++ T.drop (k + 2)).IsChain b.Adj :=
    isChain_append hA hB hAl hBh hadj
  have hRhead : D.reverse.head? = some s := by
    rw [List.head?_reverse, hlastD]
  have hhead : (D.reverse ++ T.drop (k + 2)).head? = some s := by
    simp [List.head?_append, hRhead]
  have hBlast : (T.drop (k + 2)).getLast? = some y0 := by
    rw [List.getLast?_drop, ite_eq_right (by omega : ¬ T.length ≤ k + 2), hlastT]
  have hlast : (D.reverse ++ T.drop (k + 2)).getLast? = some y0 := by
    simp [List.getLast?_append, hBlast]
  exact ⟨hchain, hhead, hlast⟩

/-- Surgery (X-side): vertices stay in the ancestral closure. -/
private theorem surgery_mem_X {α : Type*} {n : ℕ} (b : BayesNet α n)
    {X Y Z : Set (Fin n)} {T D : List (Fin n)} {k : ℕ} {s : Fin n}
    {v : Fin n} (hAT : ∀ v ∈ T, v ∈ b.ancestorsOf (X ∪ Y ∪ Z))
    (hchainD : D.IsChain b.Edge) (hlastD : D.getLast? = some s)
    (hsX : s ∈ X) (hv : v ∈ D.reverse ++ T.drop (k + 2)) :
    v ∈ b.ancestorsOf (X ∪ Y ∪ Z) := by
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · have hwD : v ∈ D := List.mem_reverse.mp hv
    exact b.mem_ancestorsOf_of_mem_edgeChain hchainD hlastD hwD
      (Set.mem_union_left Y hsX)
  · exact hAT v (List.mem_of_mem_drop hv)

/-- Surgery (Y-side): chain and endpoints of `take (k+2) T ++ D.drop 1`. -/
private theorem surgery_chain_Y {α : Type*} {n : ℕ} (b : BayesNet α n)
    {T D : List (Fin n)} {k : ℕ} {s x0 y0 : Fin n}
    (hchainT : T.IsChain b.Adj)
    (hheadT : T.head? = some x0) (hlastT : T.getLast? = some y0)
    (hk : k + 2 < T.length)
    (hchainD : D.IsChain b.Edge) (hheadD : D.head? = some T[k + 1])
    (hlastD : D.getLast? = some s) (hlenD : 2 ≤ D.length) :
    (T.take (k + 2) ++ D.drop 1).IsChain b.Adj ∧
      (T.take (k + 2) ++ D.drop 1).head? = some x0 ∧
      (T.take (k + 2) ++ D.drop 1).getLast? = some s := by
  have hA : (T.take (k + 2)).IsChain b.Adj := hchainT.take (k + 2)
  have hB : (D.drop 1).IsChain b.Adj := by
    have hE : (D.drop 1).IsChain b.Edge := hchainD.drop 1
    rw [List.isChain_iff_getElem]
    intro i hi
    exact Or.inl ((List.isChain_iff_getElem.mp hE) i hi)
  have hAl : (T.take (k + 2)).getLast? = some T[k + 1] := by
    have hk1 : k + 1 < T.length := by omega
    have h1 : T[k + 2 - 1]? = some T[k + 1] := by
      have heq : k + 2 - 1 = k + 1 := by omega
      rw [heq]
      exact List.getElem?_eq_getElem hk1
    have htake := List.getLast?_take (i := k + 2) (l := T)
    rw [htake, ite_eq_right (by omega : ¬ k + 2 = 0), h1]
    rfl
  have hBh : (D.drop 1).head? = some D[1] := by
    rw [List.head?_drop]
    exact List.getElem?_eq_getElem (by omega : 1 < D.length)
  have hadj : b.Adj T[k + 1] D[1] := by
    have hchD := List.isChain_iff_getElem.mp hchainD
    have e0 : b.Edge D[0] D[1] := hchD 0 (by omega)
    have hD0 : D[0] = T[k + 1] := by
      rw [List.head?_eq_getElem?] at hheadD
      obtain ⟨_, hd⟩ := List.getElem_of_getElem? hheadD
      exact hd
    rw [hD0] at e0
    exact Or.inl e0
  have hchain : (T.take (k + 2) ++ D.drop 1).IsChain b.Adj :=
    isChain_append hA hB hAl hBh hadj
  have hAhead : (T.take (k + 2)).head? = some x0 := by
    rw [List.head?_take, ite_eq_right (by omega : ¬ k + 2 = 0), hheadT]
  have hhead : (T.take (k + 2) ++ D.drop 1).head? = some x0 := by
    simp [List.head?_append, hAhead]
  have hBlast : (D.drop 1).getLast? = some s := by
    rw [List.getLast?_drop, ite_eq_right (by omega : ¬ D.length ≤ 1), hlastD]
  have hlast : (T.take (k + 2) ++ D.drop 1).getLast? = some s := by
    rw [List.getLast?_append, hBlast]
    simp
  exact ⟨hchain, hhead, hlast⟩

/-- Directed edges are asymmetric by the topological order. -/
private theorem not_edge_of_reverse_edge {α : Type*} {n : ℕ} (b : BayesNet α n)
    {c d : Fin n} (h : b.Edge c d) : ¬ b.Edge d c := by
  rintro hrev
  obtain ⟨hlt1, _⟩ := h
  obtain ⟨hlt2, _⟩ := hrev
  omega

/-- A triple with middle outside `Z` and a missing incoming edge is unblocked. -/
private theorem not_blockedAt_of_missing_edge {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {u c w : Fin n}
    (hmiss : ¬ b.Edge u c ∨ ¬ b.Edge w c) (hcZ : c ∉ Z) :
    ¬ b.BlockedAt Z u c w := by
  simp only [BayesNet.BlockedAt]
  rintro (⟨h1, h2, _⟩ | ⟨_, hcZ'⟩)
  · rcases hmiss with h | h
    · exact h h1
    · exact h h2
  · exact hcZ hcZ'

/-- A tail never has larger blocked count than the whole list. -/
private theorem blockedCount_tail_le {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {a : Fin n} {L : List (Fin n)} :
    b.blockedCount Z L ≤ b.blockedCount Z (a :: L) := by
  classical
  cases L with
  | nil => simp [blockedCount]
  | cons y l' =>
      cases l' with
      | nil => simp [blockedCount]
      | cons z rest =>
          have hc : b.blockedCount Z (a :: y :: z :: rest) =
              (if b.BlockedAt Z a y z then 1 else 0) +
                b.blockedCount Z (y :: z :: rest) := rfl
          rw [hc]
          omega

/-- A blocked triple forces count above the suffix count plus one. -/
private theorem blockedCount_ge_drop_succ {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T : List (Fin n)} {k : ℕ}
    (hk : k + 2 < T.length)
    (hblk : b.BlockedAt Z T[k] T[k + 1] T[k + 2]) :
    b.blockedCount Z (T.drop (k + 2)) + 1 ≤ b.blockedCount Z T := by
  classical
  induction k generalizing T with
  | zero =>
      cases T with
      | nil => simp at hk
      | cons a l =>
          cases l with
          | nil => simp at hk
          | cons y l' =>
              cases l' with
              | nil => simp at hk
              | cons z rest =>
                  have hdrop : (a :: y :: z :: rest).drop (0 + 2) = z :: rest := rfl
                  have hc : b.blockedCount Z (a :: y :: z :: rest) =
                      (if b.BlockedAt Z a y z then 1 else 0) +
                        b.blockedCount Z (y :: z :: rest) := rfl
                  have htail := b.blockedCount_tail_le (Z := Z) (a := y) (L := z :: rest)
                  have hif : (if b.BlockedAt Z a y z then 1 else 0) = 1 :=
                    ite_eq_left hblk
                  rw [hdrop, hc, hif]
                  omega
  | succ k ih =>
      cases T with
      | nil => simp at hk
      | cons a l =>
          have hk' : k + 2 < l.length := by
            have hlen : (a :: l).length = l.length + 1 := rfl
            omega
          have hblk' : b.BlockedAt Z l[k] l[k + 1] l[k + 2] := hblk
          have hIH := ih (T := l) hk' hblk'
          have hdrop : (a :: l).drop (k + 1 + 2) = l.drop (k + 2) := rfl
          have htail := b.blockedCount_tail_le (Z := Z) (a := a) (L := l)
          rw [hdrop]
          omega

/-- Two blocked triples force count above the suffix count plus two. -/
private theorem blockedCount_ge_drop_add_two {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T : List (Fin n)} {k : ℕ}
    (hk : k + 3 < T.length)
    (hblk0 : b.BlockedAt Z T[k] T[k + 1] T[k + 2])
    (hblk1 : b.BlockedAt Z T[k + 1] T[k + 2] T[k + 3]) :
    b.blockedCount Z (T.drop (k + 2)) + 2 ≤ b.blockedCount Z T := by
  classical
  induction k generalizing T with
  | zero =>
      cases T with
      | nil => simp at hk
      | cons a l =>
          cases l with
          | nil => simp at hk
          | cons y l' =>
              cases l' with
              | nil => simp at hk
              | cons z l'' =>
                  cases l'' with
                  | nil => simp at hk
                  | cons w rest =>
                      have hdrop : (a :: y :: z :: w :: rest).drop (0 + 2) =
                          z :: w :: rest := rfl
                      have hc0 : b.blockedCount Z (a :: y :: z :: w :: rest) =
                          (if b.BlockedAt Z a y z then 1 else 0) +
                            b.blockedCount Z (y :: z :: w :: rest) := rfl
                      have hc1 : b.blockedCount Z (y :: z :: w :: rest) =
                          (if b.BlockedAt Z y z w then 1 else 0) +
                            b.blockedCount Z (z :: w :: rest) := rfl
                      have hif0 : (if b.BlockedAt Z a y z then 1 else 0) = 1 :=
                        ite_eq_left hblk0
                      have hif1 : (if b.BlockedAt Z y z w then 1 else 0) = 1 :=
                        ite_eq_left hblk1
                      rw [hdrop, hc0, hc1, hif0, hif1]
                      omega
  | succ k ih =>
      cases T with
      | nil => simp at hk
      | cons a l =>
          have hk' : k + 3 < l.length := by
            have hlen : (a :: l).length = l.length + 1 := rfl
            omega
          have hblk0' : b.BlockedAt Z l[k] l[k + 1] l[k + 2] := hblk0
          have hblk1' : b.BlockedAt Z l[k + 1] l[k + 2] l[k + 3] := hblk1
          have hIH := ih (T := l) hk' hblk0' hblk1'
          have hdrop : (a :: l).drop (k + 1 + 2) = l.drop (k + 2) := rfl
          have htail := b.blockedCount_tail_le (Z := Z) (a := a) (L := l)
          rw [hdrop]
          omega

/-- Surgery (X-side) strictly decreases the blocked count. -/
private theorem surgery_count_X {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T D : List (Fin n)} {k : ℕ} {s : Fin n}
    (hk : k + 2 < T.length)
    (hblk_bad : b.BlockedAt Z T[k] T[k + 1] T[k + 2])
    (hchainD : D.IsChain b.Edge) (hheadD : D.head? = some T[k + 1])
    (hDZ : ∀ v ∈ D, v ∉ Z) (hcZ : T[k + 1] ∉ Z) :
    b.blockedCount Z (D.reverse ++ T.drop (k + 2)) < b.blockedCount Z T := by
  classical
  have hcountR : b.blockedCount Z D.reverse = 0 :=
    b.blockedCount_reverse_of_edgeChain hchainD hDZ
  have happ := b.blockedCount_append Z D.reverse (T.drop (k + 2))
  have hBh : (T.drop (k + 2)).head? = some T[k + 2] := by
    rw [List.head?_drop, List.getElem?_eq_getElem hk]
  have hlenB : (T.drop (k + 2)).length = T.length - (k + 2) := List.length_drop
  have hL1 := b.blockedCount_ge_drop_succ hk hblk_bad
  cases D with
  | nil =>
      simp at hheadD
  | cons c0 D' =>
      have hc0 : c0 = T[k + 1] := by simpa using hheadD
      rw [hc0] at hchainD hDZ hcountR happ ⊢
      cases D' with
      | nil =>
          have hArev : ([T[k + 1]].reverse) = [T[k + 1]] := by simp
          cases hB : T.drop (k + 2) with
          | nil =>
              have hlen0 : (T.drop (k + 2)).length = 0 := by rw [hB]; rfl
              rw [hlenB] at hlen0
              omega
          | cons e B' =>
              cases B' with
              | nil =>
                  have hj : b.junctionCount Z [T[k + 1]] [e] = 0 := by
                    simp [junctionCount, hArev]
                  have hcountB : b.blockedCount Z [e] = 0 := by simp [blockedCount]
                  have hT' : [T[k + 1]].reverse ++ T.drop (k + 2) =
                      [T[k + 1]] ++ [e] := by rw [hArev, hB]
                  rw [hB] at happ hL1
                  rw [happ, hcountR, hcountB, hArev, hj] at ⊢
                  omega
              | cons nxt rest =>
                  have he : e = T[k + 2] := by
                    have h1 : some e = some T[k + 2] := by simp [← hBh, hB]
                    simpa using h1
                  have hBlen : 2 ≤ (T.drop (k + 2)).length := by rw [hB]; simp
                  have hk3 : k + 3 < T.length := by omega
                  have hnxt : nxt = T[k + 3] := by
                    have h1 : (T.drop (k + 2))[1] = T[k + 3] := by
                      have h := @List.getElem_drop (Fin n) T (k + 2) 1 (by omega)
                      simpa using h
                    have h2 : (T.drop (k + 2))[1] = nxt := by simp [hB]
                    rw [h2] at h1
                    exact h1
                  have hj : b.junctionCount Z [T[k + 1]] (e :: nxt :: rest) =
                      (if b.BlockedAt Z T[k + 1] T[k + 2] T[k + 3] then 1 else 0) := by
                    have h1 : b.junctionCount Z [T[k + 1]] (e :: nxt :: rest) =
                        (if b.BlockedAt Z T[k + 1] e nxt then 1 else 0) := by
                      simp [junctionCount, hArev]
                    rw [h1, he, hnxt]
                  by_cases h11 : b.BlockedAt Z T[k + 1] T[k + 2] T[k + 3]
                  · have hL2 := b.blockedCount_ge_drop_add_two hk3 hblk_bad h11
                    rw [hB] at happ hL2
                    rw [happ, hcountR, hArev, hj, ite_eq_left h11] at ⊢
                    omega
                  · rw [hB] at happ hL1
                    rw [happ, hcountR, hArev, hj, ite_eq_right h11] at ⊢
                    omega
      | cons d1 D'' =>
          have hchD := List.isChain_iff_getElem.mp hchainD
          have ecd : b.Edge T[k + 1] ((T[k + 1] :: d1 :: D'')[1]) := hchD 0 (by simp)
          have hD1 : (T[k + 1] :: d1 :: D'')[1] = d1 := by
            exact List.getElem_cons_succ _ _ 0 (by simp)
          rw [hD1] at ecd
          have hndc : ¬ b.Edge d1 T[k + 1] := b.not_edge_of_reverse_edge ecd
          have hunb1 : ∀ e, ¬ b.BlockedAt Z d1 T[k + 1] e :=
            fun e => b.not_blockedAt_of_missing_edge (Or.inl hndc) hcZ
          have hArev : (T[k + 1] :: d1 :: D'').reverse.reverse =
              T[k + 1] :: d1 :: D'' := List.reverse_reverse _
          cases hB : T.drop (k + 2) with
          | nil =>
              have hlen0 : (T.drop (k + 2)).length = 0 := by rw [hB]; rfl
              rw [hlenB] at hlen0
              omega
          | cons e B' =>
              cases B' with
              | nil =>
                  have hj : b.junctionCount Z (T[k + 1] :: d1 :: D'').reverse [e] = 0 := by
                    have h1 : b.junctionCount Z (T[k + 1] :: d1 :: D'').reverse [e] =
                        (if b.BlockedAt Z d1 T[k + 1] e then 1 else 0) := by
                      simp [junctionCount, hArev]
                    rw [h1, ite_eq_right (hunb1 e)]
                  have hcountB : b.blockedCount Z [e] = 0 := by simp [blockedCount]
                  rw [hB] at happ hL1
                  rw [happ, hcountR, hcountB, hj] at ⊢
                  omega
              | cons nxt rest =>
                  have he : e = T[k + 2] := by
                    have h1 : some e = some T[k + 2] := by simp [← hBh, hB]
                    simpa using h1
                  have hk3 : k + 3 < T.length := by
                    have hBlen : 2 ≤ (T.drop (k + 2)).length := by rw [hB]; simp
                    omega
                  have hnxt : nxt = T[k + 3] := by
                    have h1 : (T.drop (k + 2))[1] = T[k + 3] := by
                      have h := @List.getElem_drop (Fin n) T (k + 2) 1 (by omega)
                      simpa using h
                    have h2 : (T.drop (k + 2))[1] = nxt := by simp [hB]
                    rw [h2] at h1
                    exact h1
                  have hj : b.junctionCount Z (T[k + 1] :: d1 :: D'').reverse
                      (e :: nxt :: rest) =
                      (if b.BlockedAt Z T[k + 1] T[k + 2] T[k + 3] then 1 else 0) := by
                    have h1 : b.junctionCount Z (T[k + 1] :: d1 :: D'').reverse
                        (e :: nxt :: rest) =
                        (if b.BlockedAt Z d1 T[k + 1] e then 1 else 0) +
                          (if b.BlockedAt Z T[k + 1] e nxt then 1 else 0) := by
                      simp [junctionCount, hArev]
                    rw [h1, ite_eq_right (hunb1 e), he, hnxt]
                    simp
                  by_cases h11 : b.BlockedAt Z T[k + 1] T[k + 2] T[k + 3]
                  · have hL2 := b.blockedCount_ge_drop_add_two hk3 hblk_bad h11
                    rw [hB] at happ hL2
                    rw [happ, hcountR, hj, ite_eq_left h11] at ⊢
                    omega
                  · rw [hB] at happ hL1
                    rw [happ, hcountR, hj, ite_eq_right h11] at ⊢
                    omega

/-- Surgery (Y-side): vertices stay in the ancestral closure. -/
private theorem surgery_mem_Y {α : Type*} {n : ℕ} (b : BayesNet α n)
    {X Y Z : Set (Fin n)} {T D : List (Fin n)} {k : ℕ} {s : Fin n}
    {v : Fin n} (hAT : ∀ v ∈ T, v ∈ b.ancestorsOf (X ∪ Y ∪ Z))
    (hchainD : D.IsChain b.Edge) (hlastD : D.getLast? = some s)
    (hsY : s ∈ Y) (hv : v ∈ T.take (k + 2) ++ D.drop 1) :
    v ∈ b.ancestorsOf (X ∪ Y ∪ Z) := by
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · exact hAT v (List.mem_of_mem_take hv)
  · have hwD : v ∈ D := List.mem_of_mem_drop hv
    exact b.mem_ancestorsOf_of_mem_edgeChain hchainD hlastD hwD
      (Set.mem_union_right X hsY)

/-- Surgery (Y-side) strictly decreases the blocked count. -/
private theorem surgery_count_Y {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T D : List (Fin n)} {k : ℕ}
    (hk : k + 2 < T.length)
    (hblk_bad : b.BlockedAt Z T[k] T[k + 1] T[k + 2])
    (hchainD : D.IsChain b.Edge) (hheadD : D.head? = some T[k + 1])
    (hDZ : ∀ v ∈ D, v ∉ Z) (hcZ : T[k + 1] ∉ Z) :
    b.blockedCount Z (T.take (k + 2) ++ D.drop 1) < b.blockedCount Z T := by
  classical
  revert T hk hblk_bad hheadD hcZ
  induction k with
  | zero =>
      intro T hk hblk_bad hheadD hcZ
      cases T with
      | nil => simp at hk
      | cons a l =>
          cases l with
          | nil => simp at hk
          | cons c rest =>
              have htake : (a :: c :: rest).take (0 + 2) = [a, c] := rfl
              have h1 := b.blockedCount_ge_one_of_blockedAt (T := a :: c :: rest)
                (i := 0) hk hblk_bad
              cases D with
              | nil => simp at hheadD
              | cons c0 D' =>
                  have hc0 : c0 = c := by simpa using hheadD
                  rw [hc0] at hchainD hDZ hheadD ⊢
                  have hdrop : (c :: D').drop 1 = D' := rfl
                  cases D' with
                  | nil =>
                      have hT' : (a :: c :: rest).take (0 + 2) ++ (c :: []).drop 1 =
                          [a, c] := by simp [htake, hdrop]
                      have hcountB : b.blockedCount Z [a, c] = 0 := by
                        simp [blockedCount]
                      rw [hT', hcountB]
                      omega
                  | cons d1 D'' =>
                      have hT' : (a :: c :: rest).take (0 + 2) ++
                          (c :: d1 :: D'').drop 1 = a :: c :: d1 :: D'' := by
                        simp [htake, hdrop]
                      rw [hT']
                      have hcount : b.blockedCount Z (a :: c :: d1 :: D'') =
                          (if b.BlockedAt Z a c d1 then 1 else 0) +
                            b.blockedCount Z (c :: d1 :: D'') := rfl
                      rw [hcount]
                      have ecd : b.Edge c d1 := by
                        have h := (List.isChain_iff_getElem.mp hchainD) 0 (by simp)
                        simpa using h
                      have hndc : ¬ b.Edge d1 c := b.not_edge_of_reverse_edge ecd
                      have hunb : ¬ b.BlockedAt Z a c d1 :=
                        b.not_blockedAt_of_missing_edge (Or.inr hndc) hcZ
                      have hD0 : b.blockedCount Z (c :: d1 :: D'') = 0 :=
                        b.blockedCount_of_edgeChain hchainD hDZ
                      rw [ite_eq_right hunb, hD0]
                      omega
  | succ k ih =>
      intro T hk hblk_bad hheadD hcZ
      cases T with
      | nil => simp at hk
      | cons a l =>
          cases l with
          | nil =>
              have hlen : (a :: []).length = 1 := rfl
              omega
          | cons b1 m =>
              cases m with
              | nil =>
                  have hlen : (a :: b1 :: []).length = 2 := rfl
                  omega
              | cons c m' =>
                  have hlenT : (a :: b1 :: c :: m').length = m'.length + 3 := rfl
                  have hlenl : (b1 :: c :: m').length = m'.length + 2 := rfl
                  have hk' : k + 2 < (b1 :: c :: m').length := by omega
                  have hblk' : b.BlockedAt Z (b1 :: c :: m')[k]
                      (b1 :: c :: m')[k + 1] (b1 :: c :: m')[k + 2] := hblk_bad
                  have hheadD' : D.head? = some (b1 :: c :: m')[k + 1] := hheadD
                  have hcZ' : (b1 :: c :: m')[k + 1] ∉ Z := hcZ
                  have hIH := ih (T := b1 :: c :: m') hk' hblk' hheadD' hcZ'
                  have htakeS : (a :: b1 :: c :: m').take (k + 1 + 2) =
                      a :: (b1 :: c :: m').take (k + 2) := rfl
                  have htake2 : (b1 :: c :: m').take (k + 2) =
                      b1 :: c :: m'.take k := rfl
                  have hL : (b1 :: c :: m').take (k + 2) ++ D.drop 1 =
                      b1 :: c :: (m'.take k ++ D.drop 1) := by simp [htake2]
                  rw [hL] at hIH
                  have happ : (a :: (b1 :: c :: m').take (k + 2)) ++ D.drop 1 =
                      a :: ((b1 :: c :: m').take (k + 2) ++ D.drop 1) := rfl
                  rw [htakeS, happ, hL]
                  have hcL : b.blockedCount Z
                      (a :: b1 :: c :: (m'.take k ++ D.drop 1)) =
                      (if b.BlockedAt Z a b1 c then 1 else 0) +
                        b.blockedCount Z (b1 :: c :: (m'.take k ++ D.drop 1)) :=
                    rfl
                  have hcT : b.blockedCount Z (a :: b1 :: c :: m') =
                      (if b.BlockedAt Z a b1 c then 1 else 0) +
                        b.blockedCount Z (b1 :: c :: m') := rfl
                  rw [hcL, hcT]
                  omega

/-- Surgery (Y-side): the triple property is preserved. -/
private theorem surgery_triple_Y {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T D : List (Fin n)} {k : ℕ}
    (htripleT : ∀ (t : ℕ) (_ : t + 2 < T.length), T[t + 1] ∈ Z →
      b.Edge T[t] T[t + 1] ∧ b.Edge T[t + 2] T[t + 1])
    (hk : k + 2 < T.length)
    (hDZ : ∀ v ∈ D, v ∉ Z) (hcZ : T[k + 1] ∉ Z) :
    ∀ (t : ℕ) (_ : t + 2 < (T.take (k + 2) ++ D.drop 1).length),
      (T.take (k + 2) ++ D.drop 1)[t + 1] ∈ Z →
      b.Edge (T.take (k + 2) ++ D.drop 1)[t] (T.take (k + 2) ++ D.drop 1)[t + 1] ∧
        b.Edge (T.take (k + 2) ++ D.drop 1)[t + 2]
          (T.take (k + 2) ++ D.drop 1)[t + 1] := by
  have hkle : k + 2 ≤ T.length := by omega
  have htake_len : (T.take (k + 2)).length = k + 2 := by
    rw [List.length_take, Nat.min_eq_left hkle]
  have hlen : (T.take (k + 2) ++ D.drop 1).length =
      (k + 2) + (D.drop 1).length := by
    rw [List.length_append, htake_len]
  intro t ht hmem
  rw [hlen] at ht
  by_cases hA : t + 2 < k + 2
  · have h1 : t < (T.take (k + 2)).length := by omega
    have h2 : t + 1 < (T.take (k + 2)).length := by omega
    have h3 : t + 2 < (T.take (k + 2)).length := by omega
    have e0 : (T.take (k + 2) ++ D.drop 1)[t] = T[t] := by
      rw [List.getElem_append_left h1, List.getElem_take]
    have e1 : (T.take (k + 2) ++ D.drop 1)[t + 1] = T[t + 1] := by
      rw [List.getElem_append_left h2, List.getElem_take]
    have e2 : (T.take (k + 2) ++ D.drop 1)[t + 2] = T[t + 2] := by
      rw [List.getElem_append_left h3, List.getElem_take]
    rw [e1] at hmem
    rw [e0, e1, e2] at ⊢
    exact htripleT t (by omega) hmem
  · by_cases hB : k + 2 ≤ t
    · have e1 : (T.take (k + 2) ++ D.drop 1)[t + 1] =
          (D.drop 1)[t + 1 - (T.take (k + 2)).length] :=
        List.getElem_append_right (by omega)
      have hmemD : (D.drop 1)[t + 1 - (T.take (k + 2)).length] ∈ D := by
        apply List.mem_of_mem_drop
        apply List.getElem_mem
      rw [e1] at hmem
      exact (hDZ _ hmemD hmem).elim
    · have hspan : t + 1 = k + 1 ∨ t + 1 = k + 2 := by omega
      rcases hspan with hspan | hspan
      · have h2 : t + 1 < (T.take (k + 2)).length := by omega
        have e1 : (T.take (k + 2) ++ D.drop 1)[t + 1] = T[t + 1] := by
          rw [List.getElem_append_left h2, List.getElem_take]
        rw [e1] at hmem
        simp only [hspan] at hmem
        exact (hcZ hmem).elim
      · have e1 : (T.take (k + 2) ++ D.drop 1)[t + 1] =
            (D.drop 1)[t + 1 - (T.take (k + 2)).length] :=
          List.getElem_append_right (by omega)
        have hmemD : (D.drop 1)[t + 1 - (T.take (k + 2)).length] ∈ D := by
          apply List.mem_of_mem_drop
          apply List.getElem_mem
        rw [e1] at hmem
        exact (hDZ _ hmemD hmem).elim

/-- Surgery (X-side): the triple property is preserved. -/
private theorem surgery_triple_X {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T D : List (Fin n)} {k : ℕ}
    (htripleT : ∀ (t : ℕ) (_ : t + 2 < T.length), T[t + 1] ∈ Z →
      b.Edge T[t] T[t + 1] ∧ b.Edge T[t + 2] T[t + 1])
    (hk : k + 2 < T.length)
    (hheadD : D.head? = some T[k + 1])
    (hDZ : ∀ v ∈ D, v ∉ Z) :
    ∀ (t : ℕ) (_ : t + 2 < (D.reverse ++ T.drop (k + 2)).length),
      (D.reverse ++ T.drop (k + 2))[t + 1] ∈ Z →
      b.Edge (D.reverse ++ T.drop (k + 2))[t] (D.reverse ++ T.drop (k + 2))[t + 1] ∧
        b.Edge (D.reverse ++ T.drop (k + 2))[t + 2]
          (D.reverse ++ T.drop (k + 2))[t + 1] := by
  have hrev_len : D.reverse.length = D.length := List.length_reverse ..
  have hdrop_len : (T.drop (k + 2)).length = T.length - (k + 2) := List.length_drop
  have hlen : (D.reverse ++ T.drop (k + 2)).length =
      D.length + (T.length - (k + 2)) := by
    rw [List.length_append, hrev_len, hdrop_len]
  intro t ht hmem
  rw [hlen] at ht
  by_cases hA : t + 2 < D.length
  · have e1 : (D.reverse ++ T.drop (k + 2))[t + 1] = D.reverse[t + 1] :=
      List.getElem_append_left (by omega)
    have hmemD : D.reverse[t + 1] ∈ D :=
      List.mem_reverse.mp (List.getElem_mem (by omega))
    rw [e1] at hmem
    exact (hDZ _ hmemD hmem).elim
  · by_cases hB : D.length ≤ t
    · have e0 : (D.reverse ++ T.drop (k + 2))[t] = T[k + 2 + (t - D.length)] := by
        have hgr : D.reverse.length ≤ t := by omega
        rw [List.getElem_append_right hgr]
        have g := @List.getElem_drop (Fin n) T (k + 2) (t - D.reverse.length) (by omega)
        rw [g]
        congr 1
        omega
      have e1 : (D.reverse ++ T.drop (k + 2))[t + 1] =
          T[k + 2 + (t - D.length) + 1] := by
        have hgr : D.reverse.length ≤ t + 1 := by omega
        rw [List.getElem_append_right hgr]
        have g := @List.getElem_drop (Fin n) T (k + 2) (t + 1 - D.reverse.length) (by omega)
        rw [g]
        congr 1
        omega
      have e2 : (D.reverse ++ T.drop (k + 2))[t + 2] =
          T[k + 2 + (t - D.length) + 2] := by
        have hgr : D.reverse.length ≤ t + 2 := by omega
        rw [List.getElem_append_right hgr]
        have g := @List.getElem_drop (Fin n) T (k + 2) (t + 2 - D.reverse.length) (by omega)
        rw [g]
        congr 1
        omega
      rw [e1] at hmem
      rw [e0, e1, e2] at ⊢
      exact htripleT (k + 2 + (t - D.length)) (by omega) hmem
    · have hspan : D.length = t + 1 ∨ D.length = t + 2 := by omega
      rcases hspan with hr1 | hr2
      · have e0 : (D.reverse ++ T.drop (k + 2))[t] = D.reverse[t] :=
          List.getElem_append_left (by omega)
        have e1 : (D.reverse ++ T.drop (k + 2))[t + 1] = (T.drop (k + 2))[0] := by
          have hgr : D.reverse.length ≤ t + 1 := by omega
          rw [List.getElem_append_right hgr]
          congr 1
          omega
        have e2 : (D.reverse ++ T.drop (k + 2))[t + 2] = (T.drop (k + 2))[1] := by
          have hgr : D.reverse.length ≤ t + 2 := by omega
          rw [List.getElem_append_right hgr]
          congr 1
          omega
        have hB0 : (T.drop (k + 2))[0] = T[k + 2] := by
          have g := @List.getElem_drop (Fin n) T (k + 2) 0 (by omega)
          rw [g]
        have hB1 : (T.drop (k + 2))[1] = T[k + 3] := by
          have g := @List.getElem_drop (Fin n) T (k + 2) 1 (by omega)
          rw [g]
        have hD0 : D[0] = T[k + 1] := by
          rw [List.head?_eq_getElem?] at hheadD
          obtain ⟨_, hd⟩ := List.getElem_of_getElem? hheadD
          exact hd
        have hAt : D.reverse[t] = D[0] := by
          have g := List.getElem_reverse (l := D) (i := t) (by omega)
          rw [g]
          congr 1
          omega
        rw [e1, hB0] at hmem
        rw [e0, e1, e2, hAt, hD0, hB0, hB1] at ⊢
        exact htripleT (k + 1) (by omega) hmem
      · have e1 : (D.reverse ++ T.drop (k + 2))[t + 1] = D.reverse[t + 1] :=
          List.getElem_append_left (by omega)
        have hmemD : D.reverse[t + 1] ∈ D :=
          List.mem_reverse.mp (List.getElem_mem (by omega))
        rw [e1] at hmem
        exact (hDZ _ hmemD hmem).elim

/-- A splice at duplicate indices keeps the triple property. -/
private theorem triple_splice {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T : List (Fin n)} {i j : ℕ}
    (htriple : ∀ (t : ℕ) (_ : t + 2 < T.length), T[t + 1] ∈ Z →
      b.Edge T[t] T[t + 1] ∧ b.Edge T[t + 2] T[t + 1])
    (hij : i < j) (hj : j + 1 < T.length) (hdup : T[i] = T[j]) :
    ∀ (t : ℕ) (_ : t + 2 < (splice T i j).length), (splice T i j)[t + 1] ∈ Z →
      b.Edge (splice T i j)[t] (splice T i j)[t + 1] ∧
        b.Edge (splice T i j)[t + 2] (splice T i j)[t + 1] := by
  have hle : i + 1 ≤ T.length := by omega
  have hlen : (splice T i j).length = i + 1 + (T.length - (j + 1)) :=
    length_splice T i j hle
  intro t ht hmem
  have ht' := ht
  rw [hlen] at ht'
  by_cases h1 : t + 2 < i + 1
  · have e0 : (splice T i j)[t] = T[t] :=
      getElem_splice_of_lt T i j t (by omega) (by omega) (by omega)
    have e1 : (splice T i j)[t + 1] = T[t + 1] :=
      getElem_splice_of_lt T i j (t + 1) (by omega) (by omega) (by omega)
    have e2 : (splice T i j)[t + 2] = T[t + 2] :=
      getElem_splice_of_lt T i j (t + 2) (by omega) (by omega) (by omega)
    rw [e1] at hmem
    rw [e0, e1, e2] at ⊢
    exact htriple t (by omega) hmem
  · by_cases h2 : t + 2 = i + 1
    · have hBi : t + 1 = i := by omega
      have e0 : (splice T i j)[t] = T[t] :=
        getElem_splice_of_lt T i j t (by omega) (by omega) (by omega)
      have e1 : (splice T i j)[t + 1] = T[t + 1] :=
        getElem_splice_of_lt T i j (t + 1) (by omega) (by omega) (by omega)
      have e2 : (splice T i j)[t + 2] = T[j + 1] := by
        have h := getElem_splice_of_ge T i j (t + 2) (by omega) ht hle (by omega)
        rw [h]
        congr 1
        omega
      rw [e1] at hmem
      have hL := htriple t (by omega) hmem
      have hjj1 : j - 1 + 1 = j := by omega
      have eR1 : T[j - 1 + 1] = T[t + 1] := by
        simp only [hjj1, ← hdup, ← hBi]
      have hmemR : T[j - 1 + 1] ∈ Z := by
        rw [eR1]
        exact hmem
      have hR := htriple (j - 1) (by omega) hmemR
      have eR2 : T[j - 1 + 2] = T[j + 1] := by congr 1; omega
      rw [e0, e1, e2] at ⊢
      rw [eR2, eR1] at hR
      exact ⟨hL.1, hR.2⟩
    · by_cases h3 : t + 1 = i + 1
      · have hCi : t = i := by omega
        have e0 : (splice T i j)[t] = T[t] :=
          getElem_splice_of_lt T i j t (by omega) (by omega) (by omega)
        have e1 : (splice T i j)[t + 1] = T[j + 1] := by
          have h := getElem_splice_of_ge T i j (t + 1) (by omega) (by omega) hle
            (by omega)
          rw [h]
          congr 1
          omega
        have e2 : (splice T i j)[t + 2] = T[j + 2] := by
          have h := getElem_splice_of_ge T i j (t + 2) (by omega) (by omega) hle
            (by omega)
          rw [h]
          congr 1
          omega
        rw [e1] at hmem
        have hJ2 : j + 2 < T.length := by omega
        have hJ := htriple j hJ2 hmem
        rw [e0, e1, e2] at ⊢
        constructor
        · have het : T[t] = T[j] := by
            have h1 : t = i := by omega
            simp only [h1, hdup]
          rw [het]
          exact hJ.1
        · exact hJ.2
      · have hD : i + 1 ≤ t := by omega
        have e0 : (splice T i j)[t] = T[(j + 1) + (t - (i + 1))] :=
          getElem_splice_of_ge T i j t (by omega) (by omega) hle (by omega)
        have e1 : (splice T i j)[t + 1] = T[(j + 1) + (t + 1 - (i + 1))] :=
          getElem_splice_of_ge T i j (t + 1) (by omega) (by omega) hle (by omega)
        have e2 : (splice T i j)[t + 2] = T[(j + 1) + (t + 2 - (i + 1))] :=
          getElem_splice_of_ge T i j (t + 2) (by omega) (by omega) hle (by omega)
        have hs1 : (j + 1) + (t + 1 - (i + 1)) =
            ((j + 1) + (t - (i + 1))) + 1 := by omega
        have hs2 : (j + 1) + (t + 2 - (i + 1)) =
            ((j + 1) + (t - (i + 1))) + 2 := by omega
        rw [e1] at hmem
        simp only [hs1] at hmem
        have hsh : (j + 1) + (t - (i + 1)) + 2 < T.length := by omega
        have hS := htriple ((j + 1) + (t - (i + 1))) hsh hmem
        rw [e0, e1, e2] at ⊢
        simp only [hs1, hs2] at ⊢
        exact hS

/-- Forward edges propagate along an unblocked trail while every reached
vertex has no descendant in `Z`. -/
private theorem forward_edges_of_unblocked {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T : List (Fin n)} {t j : ℕ}
    (hch : ∀ (s : ℕ) (_ : s + 1 < T.length), b.Adj T[s] T[s + 1])
    (hunblocked : ∀ (s : ℕ) (_ : s + 2 < T.length),
      ¬ b.BlockedAt Z T[s] T[s + 1] T[s + 2])
    (htj : t + 1 < j) (hj : j + 1 < T.length)
    (hno : ∀ d, b.IsDescendant T[t + 1] d → d ∉ Z)
    (efirst : b.Edge T[t + 1] T[t + 2]) :
    ∀ (d : ℕ) (hle : t + 1 + d + 1 ≤ j),
      b.Edge T[t + 1 + d] T[t + 1 + d + 1] ∧
        Relation.ReflTransGen b.Edge T[t + 1] T[t + 1 + d + 1] := by
  intro d
  induction d with
  | zero =>
      intro hle
      have e0 : b.Edge T[t + 1] T[t + 2] := efirst
      have r0 : Relation.ReflTransGen b.Edge T[t + 1] T[t + 2] :=
        Relation.ReflTransGen.head e0 Relation.ReflTransGen.refl
      exact ⟨e0, r0⟩
  | succ d ih =>
      intro hle
      have hle' : t + 1 + d + 1 ≤ j := by omega
      obtain ⟨e_prev, rtc_prev⟩ := ih hle'
      have hTv : Relation.ReflTransGen b.Edge T[t + 1] T[t + 1 + d + 1] :=
        rtc_prev
      have hnodesc : ∀ dd, b.IsDescendant T[t + 1 + d + 1] dd → dd ∉ Z := by
        intro dd hdd
        exact hno dd (hTv.trans hdd)
      have hunb := hunblocked (t + 1 + d) (by omega)
      have hncoll2 : ¬ b.Edge T[t + 1 + d + 2] T[t + 1 + d + 1] := by
        intro hback
        exact hunb (Or.inl ⟨e_prev, hback, hnodesc⟩)
      have hadj := hch (t + 1 + d + 1) (by omega)
      have efwd : b.Edge T[t + 1 + d + 1] T[t + 1 + d + 2] := by
        simp only [BayesNet.Adj] at hadj
        rcases hadj with h | h
        · exact h
        · exact absurd h hncoll2
      have hstep : Relation.ReflTransGen b.Edge T[t + 1 + d + 1] T[t + 1 + d + 2] :=
        Relation.ReflTransGen.head efwd Relation.ReflTransGen.refl
      have rtc_new : Relation.ReflTransGen b.Edge T[t + 1] T[t + 1 + d + 2] :=
        Relation.ReflTransGen.trans hTv hstep
      exact ⟨efwd, rtc_new⟩

/-- Splicing preserves unblockedness: every triple of the splice is unblocked. -/
private theorem not_blockedAt_splice {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {T : List (Fin n)} {i j : ℕ}
    (hchain : T.IsChain b.Adj)
    (htriple : ∀ (t : ℕ) (_ : t + 2 < T.length), T[t + 1] ∈ Z →
      b.Edge T[t] T[t + 1] ∧ b.Edge T[t + 2] T[t + 1])
    (hunblocked : ∀ (t : ℕ) (_ : t + 2 < T.length),
      ¬ b.BlockedAt Z T[t] T[t + 1] T[t + 2])
    (hij : i < j) (hj : j + 1 < T.length) (hdup : T[i] = T[j]) :
    ∀ (t : ℕ) (_ : t + 2 < (splice T i j).length),
      ¬ b.BlockedAt Z (splice T i j)[t] (splice T i j)[t + 1]
        (splice T i j)[t + 2] := by
  have hle : i + 1 ≤ T.length := by omega
  have hlen : (splice T i j).length = i + 1 + (T.length - (j + 1)) :=
    length_splice T i j hle
  intro t ht hblk
  have ht' := ht
  rw [hlen] at ht'
  have hch := List.isChain_iff_getElem.mp hchain
  by_cases h1 : t + 2 < i + 1
  · have e0 : (splice T i j)[t] = T[t] :=
      getElem_splice_of_lt T i j t (by omega) (by omega) (by omega)
    have e1 : (splice T i j)[t + 1] = T[t + 1] :=
      getElem_splice_of_lt T i j (t + 1) (by omega) (by omega) (by omega)
    have e2 : (splice T i j)[t + 2] = T[t + 2] :=
      getElem_splice_of_lt T i j (t + 2) (by omega) (by omega) (by omega)
    rw [e0, e1, e2] at hblk
    exact hunblocked t (by omega) hblk
  · by_cases h2 : t + 2 = i + 1
    · have hBi : t + 1 = i := by omega
      have e0 : (splice T i j)[t] = T[t] :=
        getElem_splice_of_lt T i j t (by omega) (by omega) (by omega)
      have e1 : (splice T i j)[t + 1] = T[t + 1] :=
        getElem_splice_of_lt T i j (t + 1) (by omega) (by omega) (by omega)
      have e2 : (splice T i j)[t + 2] = T[j + 1] := by
        have h := getElem_splice_of_ge T i j (t + 2) (by omega) ht hle (by omega)
        rw [h]
        congr 1
        omega
      rw [e0, e1, e2] at hblk
      by_cases hvZ : T[t + 1] ∈ Z
      · obtain ⟨eL, -⟩ := htriple t (by omega) hvZ
        have hjj1 : j - 1 + 1 = j := by omega
        have eR1 : T[j - 1 + 1] = T[t + 1] := by
          simp only [hjj1, ← hdup, ← hBi]
        have hmemR : T[j - 1 + 1] ∈ Z := by
          rw [eR1]
          exact hvZ
        obtain ⟨-, eR0⟩ := htriple (j - 1) (by omega) hmemR
        have eR2 : T[j - 1 + 2] = T[j + 1] := by congr 1; omega
        rw [eR2, eR1] at eR0
        simp only [BayesNet.BlockedAt] at hblk
        rcases hblk with ⟨-, -, hno⟩ | ⟨hncoll, -⟩
        · exact hno _ Relation.ReflTransGen.refl hvZ
        · exact hncoll ⟨eL, eR0⟩
      · have hJcoll : b.Edge T[t] T[t + 1] ∧ b.Edge T[j + 1] T[t + 1] ∧
            (∀ d, b.IsDescendant T[t + 1] d → d ∉ Z) := by
          simp only [BayesNet.BlockedAt] at hblk
          rcases hblk with h | ⟨-, hmemZ⟩
          · exact h
          · exact absurd hmemZ hvZ
        obtain ⟨eL, eR, hno⟩ := hJcoll
        have hunb_t := hunblocked t (by omega)
        have hback_i : ¬ b.Edge T[t + 2] T[t + 1] := by
          intro hback
          exact hunb_t (Or.inl ⟨eL, hback, hno⟩)
        have hadj_i := hch (t + 1) (by omega)
        have fwd_i : b.Edge T[t + 1] T[t + 2] := by
          simp only [BayesNet.Adj] at hadj_i
          rcases hadj_i with h | h
          · exact h
          · exact absurd h hback_i
        have hjj1 : j - 1 + 1 = j := by omega
        have eR1 : T[j - 1 + 1] = T[t + 1] := by
          simp only [hjj1, ← hdup, ← hBi]
        have eR2 : T[j - 1 + 2] = T[j + 1] := by congr 1; omega
        have eM' : T[j - 1 + 1] = T[j] := by congr 1
        have hunb_j := hunblocked (j - 1) (by omega)
        have hback_j : ¬ b.Edge T[j - 1] T[j - 1 + 1] := by
          intro hback
          have eR' : b.Edge T[j - 1 + 2] T[j - 1 + 1] := by
            rw [eR2, eR1]
            exact eR
          have hno' : ∀ dd, b.IsDescendant T[j - 1 + 1] dd → dd ∉ Z := by
            intro dd hdd
            rw [eR1] at hdd
            exact hno dd hdd
          exact hunb_j (Or.inl ⟨hback, eR', hno'⟩)
        have hadj_j := hch (j - 1) (by omega)
        have fwd_j : b.Edge T[j] T[j - 1] := by
          simp only [BayesNet.Adj] at hadj_j
          rcases hadj_j with h | h
          · exact absurd h hback_j
          · rw [eM'] at h
            exact h
        have htj : t + 1 < j := by omega
        have key_fwd : ∀ (d : ℕ) (hle : t + 1 + d + 1 ≤ j),
            b.Edge T[t + 1 + d] T[t + 1 + d + 1] ∧
              Relation.ReflTransGen b.Edge T[t + 1] T[t + 1 + d + 1] :=
          forward_edges_of_unblocked b hch hunblocked htj hj hno fwd_i
        have hdle : t + 1 ≤ j - 1 := by omega
        have hd_le : t + 1 + (j - 1 - (t + 1)) + 1 ≤ j := by omega
        obtain ⟨eprop, -⟩ := key_fwd (j - 1 - (t + 1)) hd_le
        have hid1 : t + 1 + (j - 1 - (t + 1)) = j - 1 := by omega
        simp only [hid1, eM'] at eprop
        obtain ⟨hlt1, -⟩ := eprop
        obtain ⟨hlt2, -⟩ := fwd_j
        omega
    · by_cases h3 : t + 1 = i + 1
      · have e0 : (splice T i j)[t] = T[t] :=
          getElem_splice_of_lt T i j t (by omega) (by omega) (by omega)
        have e1 : (splice T i j)[t + 1] = T[j + 1] := by
          have h := getElem_splice_of_ge T i j (t + 1) (by omega) (by omega) hle
            (by omega)
          rw [h]
          congr 1
          omega
        have e2 : (splice T i j)[t + 2] = T[j + 2] := by
          have h := getElem_splice_of_ge T i j (t + 2) (by omega) (by omega) hle
            (by omega)
          rw [h]
          congr 1
          omega
        rw [e0, e1, e2] at hblk
        have het : T[t] = T[j] := by
          have h1 : t = i := by omega
          simp only [h1, hdup]
        rw [het] at hblk
        exact hunblocked j (by omega) hblk
      · have hD : i + 1 ≤ t := by omega
        have e0 : (splice T i j)[t] = T[(j + 1) + (t - (i + 1))] :=
          getElem_splice_of_ge T i j t (by omega) (by omega) hle (by omega)
        have e1 : (splice T i j)[t + 1] = T[(j + 1) + (t + 1 - (i + 1))] :=
          getElem_splice_of_ge T i j (t + 1) (by omega) (by omega) hle (by omega)
        have e2 : (splice T i j)[t + 2] = T[(j + 1) + (t + 2 - (i + 1))] :=
          getElem_splice_of_ge T i j (t + 2) (by omega) (by omega) hle (by omega)
        have hs1 : (j + 1) + (t + 1 - (i + 1)) =
            ((j + 1) + (t - (i + 1))) + 1 := by omega
        have hs2 : (j + 1) + (t + 2 - (i + 1)) =
            ((j + 1) + (t - (i + 1))) + 2 := by omega
        rw [e0, e1, e2] at hblk
        simp only [hs1, hs2] at hblk
        exact hunblocked ((j + 1) + (t - (i + 1))) (by omega) hblk

/-- An unblocked skeleton trail contains an unblocked path: splice out
duplicate loops, cutting at the end when the loop reaches it. -/
private theorem exists_isPath_of_unblocked {α : Type*} {n : ℕ} (b : BayesNet α n)
    {Z : Set (Fin n)} {x y : Fin n} (m : ℕ) :
    ∀ (T : List (Fin n)), T.IsChain b.Adj → T.head? = some x → T.getLast? = some y →
      (∀ (t : ℕ) (_ : t + 2 < T.length), T[t + 1] ∈ Z →
        b.Edge T[t] T[t + 1] ∧ b.Edge T[t + 2] T[t + 1]) →
      (∀ (t : ℕ) (_ : t + 2 < T.length),
        ¬ b.BlockedAt Z T[t] T[t + 1] T[t + 2]) →
      T.length ≤ m →
      ∃ p, b.IsPath x y p ∧ ¬ b.PathBlocked Z p := by
  induction m with
  | zero =>
      intro T hchain hhead hlast htriple hunblocked hlen
      have hnil : T = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil
      simp at hhead
  | succ m ih =>
      intro T hchain hhead hlast htriple hunblocked hlen
      by_cases hnodup : T.Nodup
      · refine ⟨T, ⟨hnodup, hchain, hhead, hlast⟩, ?_⟩
        rintro ⟨i, hi, hblk⟩
        exact hunblocked i hi hblk
      · obtain ⟨i, j, hij, hj, hdup⟩ := exists_dup_of_not_nodup hnodup
        by_cases hj1 : j + 1 < T.length
        · have hlenS : (splice T i j).length < T.length := by
            have hle : i + 1 ≤ T.length := by omega
            have h := length_splice T i j hle
            omega
          have hchainS : (splice T i j).IsChain b.Adj :=
            isChain_splice hchain hij hj1 hdup
          have hheadS : (splice T i j).head? = some x := by
            rw [head?_splice hij hj1]
            exact hhead
          have hlastS : (splice T i j).getLast? = some y := by
            rw [getLast?_splice hij hj1]
            exact hlast
          have htripleS := triple_splice b htriple hij hj1 hdup
          have hunblockedS :=
            not_blockedAt_splice b hchain htriple hunblocked hij hj1 hdup
          exact ih _ hchainS hheadS hlastS htripleS hunblockedS (by omega)
        · have hilen : i + 1 < T.length := by omega
          have hyj : T[j] = y := by
            have hlast' : T[T.length - 1] = y := by
              rw [List.getLast?_eq_getElem?] at hlast
              obtain ⟨_, h⟩ := List.getElem_of_getElem? hlast
              exact h
            have hjl : j = T.length - 1 := by omega
            simp only [hjl]
            exact hlast'
          have hiy : T[i] = y := by
            rw [hdup]
            exact hyj
          have hchainT : (T.take (i + 1)).IsChain b.Adj := hchain.take (i + 1)
          have hheadT : (T.take (i + 1)).head? = some x := by
            rw [List.head?_take, ite_eq_right (by omega : ¬ i + 1 = 0), hhead]
          have hlastT : (T.take (i + 1)).getLast? = some y := by
            have h1 : T[i + 1 - 1]? = some T[i] := by
              have heq : i + 1 - 1 = i := by omega
              rw [heq]
              exact List.getElem?_eq_getElem (by omega : i < T.length)
            have htake := List.getLast?_take (i := i + 1) (l := T)
            rw [htake, ite_eq_right (by omega : ¬ i + 1 = 0), h1, hiy]
            rfl
          have hlenT : (T.take (i + 1)).length ≤ T.length := by
            rw [List.length_take]
            exact Nat.min_le_right _ _
          have hunblockedT : ∀ (t : ℕ) (_ : t + 2 < (T.take (i + 1)).length),
              ¬ b.BlockedAt Z (T.take (i + 1))[t] (T.take (i + 1))[t + 1]
                (T.take (i + 1))[t + 2] := by
            intro t ht
            have htl : t + 2 < T.length := by omega
            rw [List.getElem_take, List.getElem_take, List.getElem_take]
            exact hunblocked t htl
          have htripleT : ∀ (t : ℕ) (_ : t + 2 < (T.take (i + 1)).length),
              (T.take (i + 1))[t + 1] ∈ Z →
              b.Edge (T.take (i + 1))[t] (T.take (i + 1))[t + 1] ∧
                b.Edge (T.take (i + 1))[t + 2] (T.take (i + 1))[t + 1] := by
            intro t ht hmem
            have htl : t + 2 < T.length := by omega
            rw [List.getElem_take] at hmem
            rw [List.getElem_take, List.getElem_take, List.getElem_take]
            exact htriple t htl hmem
          have htake_len : (T.take (i + 1)).length ≤ m := by
            have h1 : (T.take (i + 1)).length ≤ i + 1 := by
              rw [List.length_take]
              exact Nat.min_le_left _ _
            omega
          exact ih _ hchainT hheadT hlastT htripleT hunblockedT htake_len

/-- A skeleton trail with the triple property contains an unblocked path:
reroute bad colliders through their directed chains to `X ∪ Y`. -/
private theorem exists_isPath_of_trail {α : Type*} {n : ℕ} (b : BayesNet α n)
    {X Y Z : Set (Fin n)} (c : ℕ) :
    ∀ (T : List (Fin n)) (x y : Fin n), T.IsChain b.Adj → T.head? = some x →
      T.getLast? = some y → (∀ v ∈ T, v ∈ b.ancestorsOf (X ∪ Y ∪ Z)) →
      (∀ (t : ℕ) (_ : t + 2 < T.length), T[t + 1] ∈ Z →
        b.Edge T[t] T[t + 1] ∧ b.Edge T[t + 2] T[t + 1]) →
      x ∈ X → y ∈ Y → b.blockedCount Z T ≤ c →
      ∃ u ∈ X, ∃ v ∈ Y, ∃ p, b.IsPath u v p ∧ ¬ b.PathBlocked Z p := by
  induction c with
  | zero =>
      intro T x y hchain hhead hlast hA htriple hx hy hle
      have h0 : b.blockedCount Z T = 0 := by omega
      have hunblocked : ∀ (t : ℕ) (_ : t + 2 < T.length),
          ¬ b.BlockedAt Z T[t] T[t + 1] T[t + 2] :=
        fun t ht => b.not_blockedAt_of_blockedCount_eq_zero h0 t ht
      obtain ⟨p, hpath, hunblk⟩ := b.exists_isPath_of_unblocked T.length T hchain
        hhead hlast htriple hunblocked le_rfl
      exact ⟨x, hx, y, hy, p, hpath, hunblk⟩
  | succ c ih =>
      intro T x y hchain hhead hlast hA htriple hx hy hle
      by_cases hex : ∃ (t : ℕ) (_ : t + 2 < T.length),
        b.BlockedAt Z T[t] T[t + 1] T[t + 2]
      · obtain ⟨k, hk, hblk⟩ := hex
        obtain ⟨hcZ, _, _, hno⟩ := b.bad_collider_of_blockedAt htriple hk hblk
        have hcA : T[k + 1] ∈ b.ancestorsOf (X ∪ Y ∪ Z) :=
          hA _ (List.getElem_mem (show k + 1 < T.length by omega))
        obtain ⟨s, hsXY, hds⟩ := b.exists_mem_union_of_ancestorsOf hcA hno
        obtain ⟨D, hchainD, hheadD, hlastD, hmemD⟩ :=
          b.exists_chain_of_reflTransGen hds
        have hDZ : ∀ v ∈ D, v ∉ Z := fun v hv => hno v (hmemD v hv)
        rcases hsXY with hsX | hsY
        · obtain ⟨hchainY, hheadY, hlastY⟩ :=
            b.surgery_chain_X hchain hhead hlast hk hchainD hheadD hlastD
          have hAY : ∀ v ∈ D.reverse ++ T.drop (k + 2),
              v ∈ b.ancestorsOf (X ∪ Y ∪ Z) := by
            intro v hv
            exact b.surgery_mem_X hA hchainD hlastD hsX hv
          have htripleY := b.surgery_triple_X htriple hk hheadD hDZ
          have hltY := b.surgery_count_X (s := s) hk hblk hchainD hheadD hDZ hcZ
          exact ih _ s y hchainY hheadY hlastY hAY htripleY hsX hy (by omega)
        · by_cases hlenD : 2 ≤ D.length
          · obtain ⟨hchainY, hheadY, hlastY⟩ :=
              b.surgery_chain_Y hchain hhead hlast hk hchainD hheadD hlastD hlenD
            have hAY : ∀ v ∈ T.take (k + 2) ++ D.drop 1,
                v ∈ b.ancestorsOf (X ∪ Y ∪ Z) := by
              intro v hv
              exact b.surgery_mem_Y hA hchainD hlastD hsY hv
            have htripleY := b.surgery_triple_Y htriple hk hDZ hcZ
            have hltY := b.surgery_count_Y hk hblk hchainD hheadD hDZ hcZ
            exact ih _ x s hchainY hheadY hlastY hAY htripleY hx hsY (by omega)
          · have hne : D ≠ [] := by
              rintro rfl
              simp at hheadD
            have hDlen : D.length = 1 := by
              have h1 : 0 < D.length := List.length_pos_iff_ne_nil.mpr hne
              omega
            cases D with
            | nil => exact absurd rfl hne
            | cons c0 D' =>
                cases D' with
                | nil =>
                    have hc0 : c0 = T[k + 1] := by simpa using hheadD
                    have hs0 : c0 = s := by simpa using hlastD
                    have hdrop : (c0 :: []).drop 1 = [] := rfl
                    have hchainY :
                        (T.take (k + 2) ++ (c0 :: []).drop 1).IsChain b.Adj := by
                      rw [hdrop, List.append_nil]
                      exact hchain.take (k + 2)
                    have hheadY :
                        (T.take (k + 2) ++ (c0 :: []).drop 1).head? = some x := by
                      rw [hdrop, List.append_nil]
                      rw [List.head?_take, ite_eq_right (by omega : ¬ k + 2 = 0),
                        hhead]
                    have hlastY :
                        (T.take (k + 2) ++ (c0 :: []).drop 1).getLast? = some s := by
                      rw [hdrop, List.append_nil]
                      have hk1 : k + 1 < T.length := by omega
                      have h1 : T[k + 2 - 1]? = some T[k + 1] := by
                        have heq : k + 2 - 1 = k + 1 := by omega
                        rw [heq]
                        exact List.getElem?_eq_getElem hk1
                      have htake := List.getLast?_take (i := k + 2) (l := T)
                      have hcs : T[k + 1] = s := by
                        rw [← hc0]
                        exact hs0
                      rw [htake, ite_eq_right (by omega : ¬ k + 2 = 0), h1, hcs]
                      rfl
                    have hAY : ∀ v ∈ T.take (k + 2) ++ (c0 :: []).drop 1,
                        v ∈ b.ancestorsOf (X ∪ Y ∪ Z) := by
                      intro v hv
                      exact b.surgery_mem_Y hA hchainD hlastD hsY hv
                    have htripleY := b.surgery_triple_Y htriple hk hDZ hcZ
                    have hltY :=
                      b.surgery_count_Y hk hblk hchainD hheadD hDZ hcZ
                    exact ih _ x s hchainY hheadY hlastY hAY htripleY hx hsY
                      (by omega)
                | cons d1 D'' =>
                    exfalso
                    have h2 : 2 ≤ (c0 :: d1 :: D'').length := by simp
                    omega
      · push_neg at hex
        obtain ⟨p, hpath, hunblk⟩ := b.exists_isPath_of_unblocked T.length T hchain
          hhead hlast htriple hex le_rfl
        exact ⟨x, hx, y, hy, p, hpath, hunblk⟩

/-- **Moralization criterion, forward** (Evans Thm 5.1, =>): d-separation
implies separation in the moral graph of the ancestral closure. -/
theorem separatedBy_moralGraph_of_dSeparated {X Y Z : Set (Fin n)}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : b.DSeparated X Y Z) :
    (b.moralGraph (b.ancestorsOf (X ∪ Y ∪ Z))).SeparatedBy X Y Z := by
  intro a b_ ha hb w
  by_contra hcon
  have havoid : ∀ v ∈ w.support, v ∉ Z := fun v hv hmem => hcon ⟨v, hmem, hv⟩
  have hxA : a ∈ b.ancestorsOf (X ∪ Y ∪ Z) :=
    ⟨a, Set.mem_union_left Z (Set.mem_union_left Y ha),
      Relation.ReflTransGen.refl⟩
  obtain ⟨T, hchain, hhead, hlast, hA, htriple⟩ :=
    b.exists_trail_of_moralWalk w hxA havoid
  obtain ⟨u, hu, v, hv, p, hpath, hunblk⟩ :=
    b.exists_isPath_of_trail (b.blockedCount Z T) T a b_ hchain hhead hlast hA
      htriple ha hb le_rfl
  exact hunblk (h u hu v hv p hpath)

/-- Auxiliary: an unblocked skeleton chain yields a moral walk avoiding `Z`.
Single skeleton steps become moral edges; unblocked colliders are shortcut by
the marrying-parents edge. Proved by induction on the length bound. -/
private theorem exists_walk_avoiding_of_unblocked
    (Z A : Set (Fin n)) :
    ∀ (m : ℕ) (q : List (Fin n)) (x y : Fin n),
      q.length ≤ m →
      (∀ v ∈ q, v ∈ A) → q.Nodup → q.IsChain b.Adj →
      (∀ i (hi : i + 2 < q.length), ¬ b.BlockedAt Z q[i] q[i + 1] q[i + 2]) →
      q.head? = some x → q.getLast? = some y → x ∉ Z → y ∉ Z →
      ∃ w : (b.moralGraph A).Walk x y, ∀ v ∈ w.support, v ∉ Z := by
  intro m
  induction m with
  | zero =>
      intro q x y hlen _ _ _ _ hhead _ _ _
      cases q with
      | nil =>
          have h2 : (none : Option (Fin n)) = some x := hhead
          simp at h2
      | cons a l =>
          have hL : (a :: l).length = l.length + 1 := rfl
          omega
  | succ m ih =>
      intro q x y hlen hA hnodup hchain hunblocked hhead hlast hxZ hyZ
      cases q with
      | nil =>
          have h2 : (none : Option (Fin n)) = some x := hhead
          simp at h2
      | cons a l =>
          cases l with
          | nil =>
              have hax : a = x := by
                have h2 : some a = some x := hhead
                simpa using h2
              have hay : a = y := by
                have h2 : some a = some y := hlast
                simpa using h2
              subst hax
              subst hay
              refine ⟨SimpleGraph.Walk.nil, ?_⟩
              intro v hv
              rw [SimpleGraph.Walk.support_nil] at hv
              simp at hv
              subst hv
              exact hxZ
          | cons c d =>
              cases d with
              | nil =>
                  have hax : a = x := by
                    have h2 : some a = some x := hhead
                    simpa using h2
                  have hcy : c = y := by
                    have h2 : some c = some y := hlast
                    simpa using h2
                  subst hax
                  subst hcy
                  have hadj : b.Adj a c :=
                    List.isChain_iff_getElem.mp hchain 0 (by simp)
                  have hne : a ≠ c := by
                    rcases hadj with h | h
                    · obtain ⟨hlt, _⟩ := h
                      rintro rfl
                      omega
                    · obtain ⟨hlt, _⟩ := h
                      rintro rfl
                      omega
                  have haA : a ∈ A := hA a (by simp)
                  have hcA : c ∈ A := hA c (by simp)
                  have hmc : (b.moralGraph A).Adj a c :=
                    (b.moralGraph_adj).mpr ⟨hne, haA, hcA, Or.inl hadj⟩
                  refine ⟨SimpleGraph.Walk.cons hmc SimpleGraph.Walk.nil, ?_⟩
                  intro v hv
                  rw [SimpleGraph.Walk.support_cons,
                    SimpleGraph.Walk.support_nil] at hv
                  simp at hv
                  rcases hv with rfl | rfl
                  · exact hxZ
                  · exact hyZ
              | cons e f =>
                  have hax : a = x := by
                    have h2 : some a = some x := hhead
                    simpa using h2
                  subst hax
                  have hLq : (a :: c :: e :: f).length = f.length + 3 := rfl
                  have haA : a ∈ A := hA a (by simp)
                  have hcA : c ∈ A := hA c (by simp)
                  have heA : e ∈ A := hA e (by simp)
                  have hch := List.isChain_iff_getElem.mp hchain
                  have hadj0 : b.Adj a c := hch 0 (by omega)
                  have h0 : ¬ b.BlockedAt Z a c e := hunblocked 0 (by omega)
                  by_cases hcoll : b.Edge a c ∧ b.Edge e c
                  · -- collider at c: shortcut a — e, recurse on e :: f
                    have hane : a ≠ e := by
                      intro hcon
                      have hnotin := (List.nodup_cons.mp hnodup).1
                      apply hnotin
                      simp [hcon]
                    have hme : (b.moralGraph A).Adj a e :=
                      (b.moralGraph_adj).mpr
                        ⟨hane, haA, heA, Or.inr ⟨c, hcA, hcoll.1, hcoll.2⟩⟩
                    have hLf : (e :: f).length = f.length + 1 := rfl
                    have hlen'' : (e :: f).length ≤ m := by omega
                    have hA'' : ∀ v ∈ e :: f, v ∈ A := by
                      intro v hv
                      exact hA v
                        (List.mem_cons_of_mem a (List.mem_cons_of_mem c hv))
                    have hnodup'' : (e :: f).Nodup :=
                      (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).2
                    have hchain'' : (e :: f).IsChain b.Adj := by
                      rw [List.isChain_iff_getElem]
                      intro i hi
                      exact hch (i + 2) (by omega)
                    have hunblocked'' : ∀ i (hi : i + 2 < (e :: f).length),
                        ¬ b.BlockedAt Z (e :: f)[i] (e :: f)[i + 1]
                          (e :: f)[i + 2] := by
                      intro i hi
                      exact hunblocked (i + 2) (by omega)
                    have hlast'' : (e :: f).getLast? = some y := hlast
                    cases f with
                    | nil =>
                        have hey : e = y := by
                          have h2 : some e = some y := hlast
                          simpa using h2
                        have heZ : e ∉ Z := by
                          rw [hey]
                          exact hyZ
                        obtain ⟨w', hw'⟩ := ih (e :: []) e y hlen'' hA''
                          hnodup'' hchain'' hunblocked'' rfl hlast'' heZ hyZ
                        refine ⟨SimpleGraph.Walk.cons hme w', ?_⟩
                        intro v hv
                        rw [SimpleGraph.Walk.support_cons] at hv
                        simp at hv
                        rcases hv with rfl | hv'
                        · exact hxZ
                        · exact hw' v hv'
                    | cons g f' =>
                        have hLg : (g :: f').length = f'.length + 1 := rfl
                        have h1 : ¬ b.BlockedAt Z c e g :=
                          hunblocked 1 (by omega)
                        have hnc : ¬ (b.Edge c e ∧ b.Edge g e) := by
                          rintro ⟨hce, -⟩
                          obtain ⟨hlt1, _⟩ := hce
                          obtain ⟨hlt2, _⟩ := hcoll.2
                          omega
                        have heZ : e ∉ Z := by
                          intro heZ
                          exact h1 (Or.inr ⟨hnc, heZ⟩)
                        obtain ⟨w', hw'⟩ := ih (e :: g :: f') e y hlen'' hA''
                          hnodup'' hchain'' hunblocked'' rfl hlast'' heZ hyZ
                        refine ⟨SimpleGraph.Walk.cons hme w', ?_⟩
                        intro v hv
                        rw [SimpleGraph.Walk.support_cons] at hv
                        simp at hv
                        rcases hv with rfl | hv'
                        · exact hxZ
                        · exact hw' v hv'
                  · -- non-collider: step a — c, recurse on c :: e :: f
                    have hcZ : c ∉ Z := by
                      intro hcZ
                      exact h0 (Or.inr ⟨hcoll, hcZ⟩)
                    have hne : a ≠ c := by
                      rcases hadj0 with h | h
                      · obtain ⟨hlt, _⟩ := h
                        rintro rfl
                        omega
                      · obtain ⟨hlt, _⟩ := h
                        rintro rfl
                        omega
                    have hmc : (b.moralGraph A).Adj a c :=
                      (b.moralGraph_adj).mpr ⟨hne, haA, hcA, Or.inl hadj0⟩
                    have hLc : (c :: e :: f).length = f.length + 2 := rfl
                    have hlen' : (c :: e :: f).length ≤ m := by omega
                    have hA' : ∀ v ∈ c :: e :: f, v ∈ A := by
                      intro v hv
                      exact hA v (List.mem_cons_of_mem a hv)
                    have hnodup' : (c :: e :: f).Nodup :=
                      (List.nodup_cons.mp hnodup).2
                    have hchain' : (c :: e :: f).IsChain b.Adj := by
                      rw [List.isChain_iff_getElem]
                      intro i hi
                      exact hch (i + 1) (by omega)
                    have hunblocked' : ∀ i (hi : i + 2 < (c :: e :: f).length),
                        ¬ b.BlockedAt Z (c :: e :: f)[i] (c :: e :: f)[i + 1]
                          (c :: e :: f)[i + 2] := by
                      intro i hi
                      exact hunblocked (i + 1) (by omega)
                    have hlast' : (c :: e :: f).getLast? = some y := hlast
                    obtain ⟨w', hw'⟩ := ih (c :: e :: f) c y hlen' hA' hnodup'
                      hchain' hunblocked' rfl hlast' hcZ hyZ
                    refine ⟨SimpleGraph.Walk.cons hmc w', ?_⟩
                    intro v hv
                    rw [SimpleGraph.Walk.support_cons] at hv
                    simp at hv
                    rcases hv with rfl | hv'
                    · exact hxZ
                    · exact hw' v hv'

/-- **Moralization criterion, backward** (Evans Thm 5.1, <=): separation in
the moral graph of the ancestral closure implies d-separation. -/
theorem dSeparated_of_separatedBy_moralGraph {X Y Z : Set (Fin n)}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : (b.moralGraph (b.ancestorsOf (X ∪ Y ∪ Z))).SeparatedBy X Y Z) :
    b.DSeparated X Y Z := by
  intro x hx y hy p hp
  by_contra hb
  have hmem : ∀ v ∈ p, v ∈ b.ancestorsOf (X ∪ Y ∪ Z) := by
    intro v hv
    have h1 : v ∈ b.ancestorsOf ({x, y} ∪ Z) :=
      b.mem_ancestorsOf_of_isPath_not_blocked hp hb hv
    obtain ⟨s, hs, hds⟩ := h1
    refine ⟨s, ?_, hds⟩
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
    rcases hs with ((rfl | rfl) | hs)
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hy)
    · exact Or.inr hs
  have hxZ : x ∉ Z := Set.disjoint_left.mp hXZ hx
  have hyZ : y ∉ Z := Set.disjoint_left.mp hYZ hy
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := hp
  have hunblocked : ∀ i (hi : i + 2 < p.length),
      ¬ b.BlockedAt Z p[i] p[i + 1] p[i + 2] := by
    intro i hi hblk
    exact hb ⟨i, hi, hblk⟩
  obtain ⟨w, hw⟩ := exists_walk_avoiding_of_unblocked b Z
    (b.ancestorsOf (X ∪ Y ∪ Z)) p.length p x y le_rfl hmem hnodup hchain
    hunblocked hhead hlast hxZ hyZ
  obtain ⟨v, hvZ, hvsup⟩ := h hx hy w
  exact hw v hvsup hvZ

/-- **Moralization criterion** (Evans Thm 5.1): for disjoint `X Y Z`,
d-separation in the DAG is separation in the moral graph of the ancestral
closure `an(X ∪ Y ∪ Z)`. -/
theorem dSeparated_iff_separatedBy_moralGraph {X Y Z : Set (Fin n)}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    b.DSeparated X Y Z ↔
      (b.moralGraph (b.ancestorsOf (X ∪ Y ∪ Z))).SeparatedBy X Y Z := by
  exact ⟨b.separatedBy_moralGraph_of_dSeparated hXY hXZ hYZ,
    b.dSeparated_of_separatedBy_moralGraph hXY hXZ hYZ⟩

end BayesNet

end Cslib.MachineLearning.GraphicalModels
