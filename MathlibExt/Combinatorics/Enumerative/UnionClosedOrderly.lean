/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Multiset.Sort

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Lex
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Fin.Tuple.Take

@[expose] public section

namespace MetaMathlibExt

/-! # Orderly canonical prefixes of union-closed sets

This file proves that every nonempty initial segment of a canonical indexed family is canonical.
-/

/-- **Binary code of a subset.** For a natural number $n$ and a subset $A$ of
$\{0, 1, \dots, n-1\}$, the binary code of $A$ is the natural number
$b(A) = \sum_{i \in A} 2^i$. -/
public def binRep (n : ℕ) (A : Finset (Fin n)) : ℕ :=
  ∑ i ∈ A, 2 ^ (i : ℕ)

/-- **Set order.** For subsets $A$ and $B$ of $\{0, \dots, n-1\}$, $A$ precedes $B$ in the set
order, written $A < B$, if $|A| > |B|$, or $|A| = |B|$ and $b(A) < b(B)$, where
$b(A) = \sum_{i \in A} 2^i$ is the binary code of $A$. -/
public def setLT (n : ℕ) (A B : Finset (Fin n)) : Prop :=
  B.card < A.card ∨ (A.card = B.card ∧ binRep n A < binRep n B)

/-- **Sort key of a subset.** For a subset $A$ of $\{0, \dots, n-1\}$, the sort key of $A$ is
the natural number $(n - |A|) \cdot 2^n + b(A)$, where $b(A) = \sum_{i \in A} 2^i$ is the
binary code of $A$.

Since $b(A) < 2^n$, comparing sort keys as numbers agrees with the set order: larger sets come
first, and sets of the same size are ordered by binary code. -/
public def setKey (n : ℕ) (A : Finset (Fin n)) : ℕ :=
  (n - A.card) * 2 ^ n + binRep n A

/-- **String of a family.** For a family $U$ of subsets of $\{0, \dots, n-1\}$, the string
$s(U)$ is the list of the sort keys of the nonempty members of $U$, in increasing order. -/
public def famString (n : ℕ) (U : Finset (Finset (Fin n))) : List ℕ :=
  Multiset.sort ((U.filter (· ≠ ∅)).val.map (setKey n)) (· ≤ ·)

/-- **Permuted image of a family.** For a permutation $\sigma$ of $\{0, \dots, n-1\}$ and a
family $U$ of subsets of $\{0, \dots, n-1\}$, the permuted image $\sigma(U)$ is the family
$\{\sigma(A) : A \in U\}$, where $\sigma(A) = \{\sigma(a) : a \in A\}$. -/
public def permImage (n : ℕ) (σ : Equiv.Perm (Fin n))
    (U : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  U.image fun A => A.image ⇑σ

/-- **Union-closed family.** A family $U$ of subsets of $\{0, \dots, n-1\}$ is union-closed if
$A \cup B \in U$ for all $A, B \in U$. -/
public def IsUnionClosed (n : ℕ) (U : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ U, ∀ B ∈ U, A ∪ B ∈ U

/-- **Canonical family.** A family $U$ of subsets of $\{0, \dots, n-1\}$ is canonical, the
canonical representative of its isomorphism class, if for every permutation $\sigma$ of
$\{0, \dots, n-1\}$ the string $s(U)$ is lexicographically at most the string $s(\sigma(U))$
of the permuted family $\sigma(U)$. -/
public def IsCanonical (n : ℕ) (U : Finset (Finset (Fin n))) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), famString n U ≤ famString n (permImage n σ U)

private theorem orderly_binRep_lt_pow (n : ℕ) (A : Finset (Fin n)) :
    binRep n A < 2 ^ n := by
  unfold binRep
  calc
    (∑ i ∈ A, 2 ^ (i : ℕ)) ≤ ∑ i : Fin n, 2 ^ (i : ℕ) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ A)
    _ = ∑ i ∈ Finset.range n, 2 ^ i := Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) n
    _ < 2 ^ n := Nat.geomSum_lt (by omega) (by simp)

private theorem orderly_setLT_key_lt (n : ℕ) (A B : Finset (Fin n))
    (h : setLT n A B) : setKey n A < setKey n B := by
  rcases h with hcard | ⟨hcard, hbin⟩
  · have hAcard : A.card ≤ n := by simpa using Finset.card_le_univ A
    have hBcard : B.card < n := lt_of_lt_of_le hcard hAcard
    have hblocks : n - A.card < n - B.card := Nat.sub_lt_sub_left hBcard hcard
    unfold setKey
    calc
      (n - A.card) * 2 ^ n + binRep n A <
          (n - A.card) * 2 ^ n + 2 ^ n :=
        Nat.add_lt_add_left (orderly_binRep_lt_pow n A) _
      _ = (n - A.card + 1) * 2 ^ n := by rw [Nat.add_mul, one_mul]
      _ ≤ (n - B.card) * 2 ^ n :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hblocks)
      _ ≤ (n - B.card) * 2 ^ n + binRep n B := Nat.le_add_right _ _
  · unfold setKey
    rw [hcard]
    exact Nat.add_lt_add_left hbin _

/-- **The sort key encodes the set order.** For all subsets $A$ and $B$ of $\{0, \dots, n-1\}$,
$A < B$ in the set order if and only if the sort key of $A$ is less than the sort key of $B$. -/
public theorem setLT_iff_setKey_lt (n : ℕ) (A B : Finset (Fin n)) :
    setLT n A B ↔ setKey n A < setKey n B := by
  constructor
  · exact orderly_setLT_key_lt n A B
  · intro hkey
    by_cases hBA : B.card < A.card
    · exact Or.inl hBA
    · right
      have hAleB : A.card ≤ B.card := Nat.le_of_not_gt hBA
      have hnotAltB : ¬ A.card < B.card := by
        intro hAB
        have hAcard : A.card < n :=
          lt_of_lt_of_le hAB (by simpa using Finset.card_le_univ B)
        have hblocks : n - B.card < n - A.card :=
          Nat.sub_lt_sub_left hAcard hAB
        have hreverse : setKey n B < setKey n A := by
          unfold setKey
          calc
            (n - B.card) * 2 ^ n + binRep n B <
                (n - B.card) * 2 ^ n + 2 ^ n :=
              Nat.add_lt_add_left (orderly_binRep_lt_pow n B) _
            _ = (n - B.card + 1) * 2 ^ n := by rw [Nat.add_mul, one_mul]
            _ ≤ (n - A.card) * 2 ^ n :=
              Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hblocks)
            _ ≤ (n - A.card) * 2 ^ n + binRep n A := Nat.le_add_right _ _
        exact (not_lt_of_ge (Nat.le_of_lt hreverse)) hkey
      have hcard : A.card = B.card :=
        Nat.le_antisymm hAleB (Nat.le_of_not_gt hnotAltB)
      refine ⟨hcard, ?_⟩
      unfold setKey at hkey
      rw [hcard] at hkey
      exact Nat.add_lt_add_iff_left.mp hkey

private theorem orderly_famString_indexed (n q : ℕ) (A : Fin q → Finset (Fin n))
    (hne : ∀ i, A i ≠ ∅)
    (hkeys : StrictMono fun i => setKey n (A i)) :
    famString n (insert ∅ (Finset.image A Finset.univ)) =
      List.ofFn fun i => setKey n (A i) := by
  have hAinj : Function.Injective A := fun i j hij =>
    hkeys.injective (congrArg (setKey n) hij)
  let e : Fin q ↪ Finset (Fin n) := ⟨A, hAinj⟩
  have himage : Finset.image A Finset.univ = Finset.map e Finset.univ := by
    ext S
    simp [e]
  have hfilter :
      (insert ∅ (Finset.image A Finset.univ)).filter (· ≠ ∅) =
        Finset.image A Finset.univ := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h | him, hS⟩
      · exact (hS h).elim
      · exact him
    · rintro ⟨i, rfl⟩
      exact ⟨Or.inr ⟨i, rfl⟩, hne i⟩
  have hsorted :
      (List.ofFn fun i => setKey n (A i)).Pairwise (· ≤ ·) := by
    exact List.sortedLE_iff_pairwise.mp hkeys.sortedLT_ofFn.sortedLE
  unfold famString
  rw [hfilter, himage, Finset.map_val, Fin.univ_val_map]
  change Multiset.sort (Multiset.map (setKey n) (↑(List.ofFn A))) (· ≤ ·) = _
  change Multiset.sort (↑(List.map (setKey n) (List.ofFn A)) : Multiset ℕ) (· ≤ ·) = _
  rw [List.map_ofFn, Multiset.coe_sort]
  exact List.mergeSort_eq_self (· ≤ ·) hsorted

private theorem orderly_keys_strictMono (n k : ℕ) (A : Fin k → Finset (Fin n))
    (hlt : ∀ i j : Fin k, i < j → setLT n (A i) (A j)) :
    StrictMono fun i => setKey n (A i) := by
  intro i j hij
  exact orderly_setLT_key_lt n (A i) (A j) (hlt i j hij)

private theorem orderly_sort_cons (a : ℕ) (s : Multiset ℕ) :
    (a ::ₘ s).sort (· ≤ ·) = List.orderedInsert (· ≤ ·) a (s.sort (· ≤ ·)) := by
  refine List.Perm.eq_of_pairwise' (r := fun x y : ℕ => x ≤ y) ?_ ?_ ?_
  · exact Multiset.pairwise_sort (a ::ₘ s) (· ≤ ·)
  · exact (Multiset.pairwise_sort s (· ≤ ·)).orderedInsert a _
  · have hsort : ((a ::ₘ s).sort (· ≤ ·)).Perm (a :: s.sort (· ≤ ·)) := by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.sort_eq]
      change a ::ₘ s = a ::ₘ (↑(s.sort (· ≤ ·)) : Multiset ℕ)
      rw [Multiset.sort_eq]
    exact hsort.trans (List.perm_orderedInsert (· ≤ ·) a _).symm

private theorem orderly_sort_sublist {s t : Multiset ℕ} (h : s ≤ t) :
    (s.sort (· ≤ ·)).Sublist (t.sort (· ≤ ·)) := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  clear h
  induction u using Multiset.induction_on with
  | empty => simp
  | @cons a u ihu =>
      rw [Multiset.add_cons, orderly_sort_cons]
      exact ihu.trans (List.sublist_orderedInsert a _)

private theorem orderly_sort_sorted_eq (L : List ℕ) (h : L.Pairwise (· ≤ ·)) :
    (↑L : Multiset ℕ).sort (· ≤ ·) = L := by
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self (· ≤ ·) h

private theorem orderly_fin_index_le {p q : ℕ} (f : Fin p → Fin q)
    (hf : StrictMono f) (i : Fin p) : (i : ℕ) ≤ f i := by
  have h : ∀ r (hr : r < p), r ≤ (f ⟨r, hr⟩ : Fin q) := by
    intro r
    induction r with
    | zero =>
        intro
        omega
    | succ r ihr =>
        intro hr
        have hr' : r < p := by omega
        let j : Fin p := ⟨r, hr'⟩
        let j' : Fin p := ⟨r + 1, hr⟩
        have hjj : j < j' := by simp [j, j']
        have hmono := hf hjj
        have hind := ihr hr'
        change r ≤ (f j : Fin q) at hind
        change (f j : ℕ) < f j' at hmono
        change r + 1 ≤ (f j' : Fin q)
        omega
  exact h i i.isLt

private theorem orderly_sorted_sublist_get_le {K L : List ℕ} (hsub : K.Sublist L)
    (hsorted : L.Pairwise (· ≤ ·)) (i : Fin K.length) :
    L.get (Fin.castLE hsub.length_le i) ≤ K.get i := by
  obtain ⟨f, hget⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
  rw [hget i]
  have hindex : Fin.castLE hsub.length_le i ≤ f i := by
    apply Fin.mk_le_mk.mpr
    change (i : ℕ) ≤ (f i : Fin L.length)
    exact orderly_fin_index_le (fun j => f j) f.strictMono i
  rcases hindex.lt_or_eq with hlt | heq
  · exact hsorted.rel_get_of_lt hlt
  · rw [heq]

private theorem orderly_perm_famString_submultiset (n : ℕ) (σ : Equiv.Perm (Fin n))
    {P U : Finset (Finset (Fin n))} (h : P ⊆ U) :
    (↑(famString n (permImage n σ P)) : Multiset ℕ) ≤
      ↑(famString n (permImage n σ U)) := by
  unfold famString
  rw [Multiset.sort_eq, Multiset.sort_eq]
  apply Multiset.map_le_map
  rw [Finset.val_le_iff]
  apply Finset.filter_subset_filter
  unfold permImage
  exact Finset.image_subset_image h

private theorem orderly_list_le_of_forall₂ {K L : List ℕ}
    (h : List.Forall₂ (· ≤ ·) K L) : K ≤ L := by
  induction h with
  | nil => rfl
  | @cons a b K L hab _ ih =>
      rcases hab.lt_or_eq with hlt | heq
      · apply le_of_lt
        change List.Lex (· < ·) (a :: K) (b :: L)
        exact List.Lex.rel hlt
      · subst b
        exact List.cons_le_cons a ih

private theorem orderly_lex_append_of_length_eq {r : ℕ → ℕ → Prop} {K L : List ℕ}
    (h : List.Lex r K L) (hlen : K.length = L.length) (K' L' : List ℕ) :
    List.Lex r (K ++ K') (L ++ L') := by
  induction h generalizing K' L' with
  | nil => simp at hlen
  | rel hrel => exact List.Lex.rel hrel
  | cons hlex ih =>
      exact List.Lex.cons (ih (Nat.succ.inj hlen) K' L')

private theorem orderly_lt_append_of_length_eq {K L : List ℕ} (h : K < L)
    (hlen : K.length = L.length) (K' L' : List ℕ) : K ++ K' < L ++ L' := by
  change List.Lex (· < ·) K L at h
  change List.Lex (· < ·) (K ++ K') (L ++ L')
  exact orderly_lex_append_of_length_eq h hlen K' L'

private theorem orderly_lt_of_take_lt_take {K L : List ℕ} (m : ℕ)
    (hlen : K.length = L.length) (h : K.take m < L.take m) : K < L := by
  have htlen : (K.take m).length = (L.take m).length := by
    simp only [List.length_take, hlen]
  have happ :=
    orderly_lt_append_of_length_eq h htlen (K.drop m) (L.drop m)
  simpa only [List.take_append_drop] using happ

private theorem orderly_famString_length (n : ℕ) (U : Finset (Finset (Fin n))) :
    (famString n U).length = (U.filter (· ≠ ∅)).card := by
  unfold famString
  rw [Multiset.length_sort]
  exact Multiset.card_map (setKey n) _

private theorem orderly_famString_sorted (n : ℕ) (U : Finset (Finset (Fin n))) :
    (famString n U).Pairwise (· ≤ ·) := by
  unfold famString
  exact Multiset.pairwise_sort _ _

private theorem orderly_perm_famString_length (n : ℕ) (σ : Equiv.Perm (Fin n))
    (U : Finset (Finset (Fin n))) :
    (famString n (permImage n σ U)).length = (famString n U).length := by
  rw [orderly_famString_length, orderly_famString_length]
  have hfilter :
      (permImage n σ U).filter (· ≠ ∅) =
        Finset.image (fun A => A.image ⇑σ) (U.filter (· ≠ ∅)) := by
    ext S
    simp only [permImage, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨A, hAU, rfl⟩, hnonempty⟩
      refine ⟨A, ⟨hAU, ?_⟩, rfl⟩
      intro hA
      subst A
      simp at hnonempty
    · rintro ⟨A, ⟨hAU, hA⟩, rfl⟩
      refine ⟨⟨A, hAU, rfl⟩, ?_⟩
      simpa using hA
  rw [hfilter, Finset.card_image_of_injective]
  exact Finset.image_injective σ.injective

/-- **Prefixes of a sorted canonical family are canonical.** Let $A_1, \dots, A_k$ be nonempty
subsets of $\{0, \dots, n-1\}$ with $A_i < A_j$ in the set order whenever $i < j$, and suppose
the family $U = \{\emptyset, A_1, \dots, A_k\}$ is canonical. Then for every $m \le k$, including
$m = 0$, the family $\{\emptyset, A_1, \dots, A_m\}$ is canonical.

Neither union closure nor coverage of the universe is needed. -/
public theorem orderly_canonical_prefix_of_sorted
    (n k m : ℕ) (U : Finset (Finset (Fin n)))
    (A : Fin k → Finset (Fin n))
    (hmk : m ≤ k)
    (hU : U = insert ∅ (Finset.image A Finset.univ))
    (hne : ∀ i, A i ≠ ∅)
    (hlt : ∀ i j : Fin k, i < j → setLT n (A i) (A j))
    (hcan : IsCanonical n U) :
    IsCanonical n
      (insert ∅ (Finset.image (fun i : Fin m => A (Fin.castLE hmk i)) Finset.univ)) := by
  let B : Fin m → Finset (Fin n) := fun i => A (Fin.castLE hmk i)
  let P : Finset (Finset (Fin n)) := insert ∅ (Finset.image B Finset.univ)
  change IsCanonical n P
  have hkeysU : StrictMono fun i => setKey n (A i) :=
    orderly_keys_strictMono n k A hlt
  have hkeysP : StrictMono fun i => setKey n (B i) := by
    intro i j hij
    apply hkeysU
    exact Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hij)
  have hneP : ∀ i, B i ≠ ∅ := fun i => hne (Fin.castLE hmk i)
  have hstringU : famString n U = List.ofFn fun i => setKey n (A i) := by
    rw [hU]
    exact orderly_famString_indexed n k A hne hkeysU
  have hstringP : famString n P = List.ofFn fun i => setKey n (B i) := by
    exact orderly_famString_indexed n m B hneP hkeysP
  have hprefix : famString n P = (famString n U).take m := by
    rw [hstringP, hstringU]
    calc
      List.ofFn (fun i => setKey n (B i)) =
          List.ofFn (Fin.take m hmk fun i => setKey n (A i)) := by
        apply List.ofFn_inj.mpr
        funext i
        exact (Fin.take_apply m hmk (fun i => setKey n (A i)) i).symm
      _ = List.take m (List.ofFn fun i => setKey n (A i)) :=
        Fin.ofFn_take_eq_take_ofFn hmk (fun i => setKey n (A i))
  have hPsubU : P ⊆ U := by
    rw [hU]
    intro S hSP
    simp only [P, B, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
      true_and] at hSP ⊢
    rcases hSP with hS | ⟨i, hi⟩
    · exact Or.inl hS
    · exact Or.inr ⟨Fin.castLE hmk i, hi⟩
  have hlenU : (famString n U).length = k := by
    rw [hstringU, List.length_ofFn]
  have hlenP : (famString n P).length = m := by
    rw [hstringP, List.length_ofFn]
  intro σ
  by_contra hnot
  have hbad : famString n (permImage n σ P) < famString n P :=
    lt_of_not_ge hnot
  let K := famString n (permImage n σ P)
  let L := famString n (permImage n σ U)
  have hlenK : K.length = m := by
    dsimp [K]
    rw [orderly_perm_famString_length, hlenP]
  have hlenL : L.length = k := by
    dsimp [L]
    rw [orderly_perm_famString_length, hlenU]
  have hmulti : (↑K : Multiset ℕ) ≤ ↑L := by
    dsimp [K, L]
    exact orderly_perm_famString_submultiset n σ hPsubU
  have hsortedK : K.Pairwise (· ≤ ·) := by
    dsimp [K]
    exact orderly_famString_sorted n (permImage n σ P)
  have hsortedL : L.Pairwise (· ≤ ·) := by
    dsimp [L]
    exact orderly_famString_sorted n (permImage n σ U)
  have hsub : K.Sublist L := by
    have hs := orderly_sort_sublist hmulti
    rw [orderly_sort_sorted_eq K hsortedK, orderly_sort_sorted_eq L hsortedL] at hs
    exact hs
  have hmL : m ≤ L.length := by omega
  have htlen : (L.take m).length = K.length := by
    rw [List.length_take, Nat.min_eq_left hmL, hlenK]
  have htakeForall : List.Forall₂ (· ≤ ·) (L.take m) K := by
    apply List.forall₂_of_length_eq_of_get htlen
    intro i hiTake hiK
    have horder :=
      orderly_sorted_sublist_get_le hsub hsortedL (⟨i, hiK⟩ : Fin K.length)
    simpa only [List.get_eq_getElem, List.getElem_take, Fin.val_castLE] using horder
  have htakeLe : L.take m ≤ K := orderly_list_le_of_forall₂ htakeForall
  change K < famString n P at hbad
  rw [hprefix] at hbad
  have htakeLt : L.take m < (famString n U).take m :=
    lt_of_le_of_lt htakeLe hbad
  have hlenFull : L.length = (famString n U).length := by
    dsimp [L]
    exact orderly_perm_famString_length n σ U
  have hfullLt : L < famString n U :=
    orderly_lt_of_take_lt_take m hlenFull htakeLt
  have hcanonical : famString n U ≤ L := by
    dsimp [L]
    exact hcan σ
  exact (not_lt_of_ge hcanonical) hfullLt

/--
**Orderly generation of union-closed families.** Let $n$, $k$ and $m$ be natural numbers with
$1 \le m \le k$, and let $A_1, \dots, A_k$ be nonempty subsets of $\Omega_n = \{0, \dots, n-1\}$
with $A_i < A_j$ in the set order whenever $i < j$. Suppose the family
$U = \{\emptyset, A_1, \dots, A_k\}$ is union-closed, every element of $\Omega_n$ lies in some
member of $U$, $U \ne \{\Omega_n, \emptyset\}$, and $U$ is canonical. Then the prefix family
$\{\emptyset, A_1, \dots, A_m\}$ is canonical.

The hypotheses that $U$ is union-closed, covers $\Omega_n$ and differs from
$\{\Omega_n, \emptyset\}$ are not used in the proof. The string of $U$ lists the sort keys of
$A_1, \dots, A_k$ in order, so the string of the prefix family is a prefix of it, and a
permutation that made the prefix family's string smaller would make the string of $U$ smaller.

Proves `Wanted` entry `orderly_canonical_prefix`.

Source: Gunnar Brinkmann and Robin Deklerck, "Generation of Union-Closed Sets and Moore
Families", Journal of Integer Sequences 21 (2018), Article 18.1.7, Theorem `thm:orderly`,
source lines 275–281, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Brinkmann/brink6.tex>.
-/
public theorem orderly_canonical_prefix
    (n k m : ℕ) (U : Finset (Finset (Fin n)))
    (A : Fin k → Finset (Fin n))
    (_hm : 1 ≤ m) (hmk : m ≤ k)
    (hU : U = insert ∅ (Finset.image A Finset.univ))
    (hne : ∀ i, A i ≠ ∅)
    (hlt : ∀ i j : Fin k, i < j → setLT n (A i) (A j))
    (_hbase : U ≠ {Finset.univ, ∅})
    (_hcov : ∀ i : Fin n, ∃ A₀ ∈ U, i ∈ A₀)
    (_huc : IsUnionClosed n U)
    (hcan : IsCanonical n U) :
    IsCanonical n
      (insert ∅ (Finset.image (fun i : Fin m => A (Fin.castLE hmk i)) Finset.univ)) :=
  orderly_canonical_prefix_of_sorted n k m U A hmk hU hne hlt hcan

end MetaMathlibExt
