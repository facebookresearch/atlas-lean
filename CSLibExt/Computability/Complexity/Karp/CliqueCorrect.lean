/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Clique
public import CSLibExt.Computability.Complexity.DenseToBinary

/-!
# Correctness of Karp's reductions SAT ≤ CLIQUE ≤ INDEPENDENT-SET ≤ VERTEX-COVER

The three reductions of `CSLibExt.Computability.Complexity.Karp.Clique` preserve membership:

* `satDec_eq_cliqueDec_reduceClique`: a CNF formula `φ` is satisfiable iff Karp's graph on its
  literal occurrences has a clique of `φ.length` vertices (Karp 1972; Sipser, *Introduction to the
  Theory of Computation*, Thm. 7.32, whose proof for 3SAT works for any CNF). A satisfying
  assignment picks one true occurrence per clause; conversely a clique of that size meets every
  clause exactly once (occurrences in one clause are not adjacent), and setting the variables of
  its positive occurrences true satisfies every clause (adjacent occurrences are not
  complementary). An empty clause has no vertex, so neither side holds.
* `cliqueDec_eq_indSetDec_flipKG`: complementing the pair bits complements the graph
  (`toGraph_map_not`), and a clique of `G` is an independent set of `Gᶜ`.
* `indSetDec_eq_vertexCoverDec_isToVc`: a set is independent iff its complement is a vertex cover,
  and the complement of a `k`-set of `Fin n` has `n - k` elements.

Supporting API: the instance codec (`decodeKG_encodeKG`, `decodeKG_eq_some_iff`, `encodeKG_inj`),
the pair list (`mem_pairs`, `length_pairs`), the pair bits (`adjBits_eq_getElem`, `adjBits_comm`),
and `noKG` as a no-instance of all three languages.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-! ### The instance codec -/

@[simp] theorem decodeKG_encodeKG (k n : ℕ) (bits : List Bool) :
    decodeKG (encodeKG k n bits) = some (k, n, bits) := by
  simp [decodeKG, encodeKG]

theorem decodeKG_eq_some_iff {x : List Bool} {k n : ℕ} {bits : List Bool} :
    decodeKG x = some (k, n, bits) ↔ x = encodeKG k n bits := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeKG_encodeKG k n bits⟩
  unfold decodeKG at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨k', r⟩, h1, h2⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨⟨n', bits'⟩, h2, rfl, rfl, rfl⟩ := h2
  rw [readUnaryLength_eq_some_iff] at h1 h2
  rw [h1, h2]
  rfl

theorem encodeKG_inj {k n k' n' : ℕ} {bits bits' : List Bool}
    (h : encodeKG k n bits = encodeKG k' n' bits') : k = k' ∧ n = n' ∧ bits = bits' := by
  simpa using congrArg decodeKG h

theorem kgDec_encodeKG_eq_true {P : ∀ n : ℕ, ℕ → SimpleGraph (Fin n) → Prop} {k n : ℕ}
    {bits : List Bool} :
    kgDec P (encodeKG k n bits) = true ↔
      bits.length = (pairs n).length ∧ P n k (toGraph n bits) := by
  simp only [kgDec, decide_eq_true_eq]
  constructor
  · rintro ⟨k', n', bits', h, hlen, hP⟩
    obtain ⟨rfl, rfl, rfl⟩ := encodeKG_inj h
    exact ⟨hlen, hP⟩
  · rintro ⟨hlen, hP⟩
    exact ⟨k, n, bits, rfl, hlen, hP⟩

/-- Input that does not parse as two unary numbers is rejected. -/
theorem kgDec_of_decodeKG_eq_none {P : ∀ n : ℕ, ℕ → SimpleGraph (Fin n) → Prop}
    {x : List Bool} (h : decodeKG x = none) : kgDec P x = false := by
  simp only [kgDec, decide_eq_false_iff_not]
  rintro ⟨k, n, bits, rfl, -⟩
  simp at h

theorem kgDec_noKG {P : ∀ n : ℕ, ℕ → SimpleGraph (Fin n) → Prop}
    (hP : ∀ G, ¬P 0 1 G) : kgDec P noKG = false := by
  rw [Bool.eq_false_iff, ne_eq, noKG, kgDec_encodeKG_eq_true]
  exact fun h => hP _ h.2

/-- No finset of `Fin 0` has one element. -/
private theorem card_ne_one_fin_zero (s : Finset (Fin 0)) : s.card ≠ 1 := by
  simp [Finset.eq_empty_of_isEmpty s]

theorem cliqueDec_noKG : cliqueDec noKG = false :=
  kgDec_noKG fun _ ⟨s, hs⟩ => card_ne_one_fin_zero s hs.card_eq

theorem indSetDec_noKG : indSetDec noKG = false :=
  kgDec_noKG fun _ ⟨s, hs⟩ => card_ne_one_fin_zero s hs.card_eq

theorem vertexCoverDec_noKG : vertexCoverDec noKG = false :=
  kgDec_noKG fun _ ⟨s, hs, _⟩ => card_ne_one_fin_zero s hs

/-! ### Pairs and pair bits -/

@[simp] theorem mem_pairs {n i j : ℕ} : (i, j) ∈ pairs n ↔ i < j ∧ j < n := by
  simp [pairs]
  omega

/-- Row `i` of `pairs n` has `n - 1 - i` pairs. -/
private theorem length_row (n i : ℕ) :
    ((List.range n).reverse.filter (i < ·)).length = n - 1 - i := by
  rw [← List.countP_eq_length_filter, List.countP_reverse]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : i < n <;> simp [h] <;> omega

theorem length_pairs_succ (n : ℕ) : (pairs (n + 1)).length = (pairs n).length + n := by
  simp only [pairs, List.length_flatMap, List.length_map, length_row]
  rw [List.sum_range_succ, List.map_congr_left (g := fun i => (n - 1 - i) + 1)
    (fun i hi => by simp at hi; omega), List.sum_map_add]
  simp

theorem two_mul_length_pairs (n : ℕ) : 2 * (pairs n).length = n * (n - 1) := by
  induction n with
  | zero => simp [pairs]
  | succ n ih =>
    rw [length_pairs_succ, mul_add, ih, Nat.add_sub_cancel]
    cases n with
    | zero => rfl
    | succ m =>
      simp only [Nat.add_sub_cancel, Nat.mul_succ, Nat.succ_mul]
      omega

theorem length_pairs (n : ℕ) : (pairs n).length = n * (n - 1) / 2 := by
  rw [← two_mul_length_pairs]
  omega

/-- No pair is listed twice (rows have distinct first components). -/
theorem pairs_nodup (n : ℕ) : (pairs n).Nodup := by
  rw [pairs, List.nodup_flatMap]
  refine ⟨fun i _ => List.Nodup.map (Prod.mk_right_injective i)
    ((List.nodup_reverse.2 List.nodup_range).filter _), ?_⟩
  refine List.nodup_range.imp fun {i j} hij p hp hp' => hij ?_
  simp only [List.mem_map] at hp hp'
  obtain ⟨a, -, rfl⟩ := hp
  obtain ⟨b, -, hb⟩ := hp'
  exact (Prod.mk.inj hb).1.symm

/-- Looking up a key of `l` in `l` zipped with a list at least as long finds the entry at the
key's index. -/
private theorem lookup_zip_of_mem {α β : Type*} [BEq α] [LawfulBEq α] {l : List α} {bs : List β}
    {a : α} (ha : a ∈ l) (hlen : l.length ≤ bs.length) :
    (l.zip bs).lookup a =
      some (bs[l.idxOf a]'(lt_of_lt_of_le (List.idxOf_lt_length_of_mem ha) hlen)) := by
  induction l generalizing bs with
  | nil => simp at ha
  | cons b l ih =>
    cases bs with
    | nil => simp at hlen
    | cons c bs =>
      by_cases hab : a = b
      · subst hab
        simp
      · have ha' : a ∈ l := by simpa [hab] using ha
        have hba : (b == a) = false := by simpa using Ne.symm hab
        simp only [List.zip_cons_cons, List.lookup_cons, beq_false_of_ne hab, List.idxOf_cons,
          hba]
        simpa using ih ha' (by simpa using hlen)

theorem adjBits_comm (n : ℕ) (bits : List Bool) (i j : ℕ) :
    adjBits n bits i j = adjBits n bits j i := by
  rw [adjBits, adjBits, min_comm, max_comm]

/-- On a valid instance, the bit of a pair `i < j < n` is the bit at the pair's index. -/
theorem adjBits_eq_getElem {n : ℕ} {bits : List Bool} {i j : ℕ}
    (h : bits.length = (pairs n).length) (hij : i < j) (hj : j < n) :
    adjBits n bits i j = bits[(pairs n).idxOf (i, j)]'(by
      rw [h]; exact List.idxOf_lt_length_of_mem (mem_pairs.2 ⟨hij, hj⟩)) := by
  rw [adjBits, min_eq_left hij.le, max_eq_right hij.le,
    lookup_zip_of_mem (mem_pairs.2 ⟨hij, hj⟩) h.ge]
  rfl

theorem adjBits_map_not {n : ℕ} {bits : List Bool} {i j : ℕ}
    (h : bits.length = (pairs n).length) (hij : i ≠ j) (hi : i < n) (hj : j < n) :
    adjBits n (bits.map not) i j = !adjBits n bits i j := by
  have hm : (bits.map not).length = (pairs n).length := by simpa using h
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · rw [adjBits_eq_getElem hm hlt hj, adjBits_eq_getElem h hlt hj, List.getElem_map]
  · rw [adjBits_comm, adjBits_comm n bits, adjBits_eq_getElem hm hgt hi,
      adjBits_eq_getElem h hgt hi, List.getElem_map]

/-- Bits computed pairwise by `f` give `f` back on each pair. -/
theorem adjBits_map_pairs {n i j : ℕ} (f : ℕ × ℕ → Bool) (hij : i < j) (hj : j < n) :
    adjBits n ((pairs n).map f) i j = f (i, j) := by
  rw [adjBits_eq_getElem (by simp) hij hj, List.getElem_map, List.getElem_idxOf]

/-- Complementing the bits of a valid instance complements its graph. -/
theorem toGraph_map_not {n : ℕ} {bits : List Bool} (h : bits.length = (pairs n).length) :
    toGraph n (bits.map not) = (toGraph n bits)ᶜ := by
  ext i j
  by_cases hij : i = j
  · simp [hij]
  · have := adjBits_map_not h (Fin.val_ne_of_ne hij) i.2 j.2
    simp [toGraph, hij, this]

/-! ### CLIQUE ≤ INDEPENDENT-SET -/

theorem cliqueDec_eq_indSetDec_flipKG (x : List Bool) : cliqueDec x = indSetDec (flipKG x) := by
  unfold flipKG
  split
  next k n bits h =>
    rw [decodeKG_eq_some_iff] at h
    subst h
    rw [Bool.eq_iff_iff, cliqueDec, indSetDec, kgDec_encodeKG_eq_true, kgDec_encodeKG_eq_true,
      List.length_map]
    refine and_congr_right fun hlen => ?_
    simp only [toGraph_map_not hlen, SimpleGraph.isNIndepSet_compl]
  next h => rw [cliqueDec, kgDec_of_decodeKG_eq_none h, indSetDec_noKG]

/-! ### INDEPENDENT-SET ≤ VERTEX-COVER -/

/-- `G` has an independent set of `k ≤ n` vertices iff it has a vertex cover of `n - k`. -/
theorem exists_isNIndepSet_iff_exists_isVertexCover {n k : ℕ} (G : SimpleGraph (Fin n))
    (hk : k ≤ n) : (∃ s, G.IsNIndepSet k s) ↔
      ∃ s : Finset (Fin n), s.card = n - k ∧ G.IsVertexCover (s : Set (Fin n)) := by
  classical
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨sᶜ, by rw [Finset.card_compl, Fintype.card_fin, hs.card_eq], ?_⟩
    rw [Finset.coe_compl, SimpleGraph.isVertexCover_compl]
    exact hs.isIndepSet
  · rintro ⟨t, ht, hcov⟩
    refine ⟨tᶜ, ⟨?_, ?_⟩⟩
    · rw [Finset.coe_compl, SimpleGraph.isIndepSet_compl_iff_isVertexCover]
      exact hcov
    · rw [Finset.card_compl, Fintype.card_fin, ht]
      omega

theorem indSetDec_eq_vertexCoverDec_isToVc (x : List Bool) :
    indSetDec x = vertexCoverDec (isToVc x) := by
  unfold isToVc
  split
  next k n bits h =>
    rw [decodeKG_eq_some_iff] at h
    subst h
    split_ifs with hkn
    · rw [Bool.eq_iff_iff, indSetDec, vertexCoverDec, kgDec_encodeKG_eq_true,
        kgDec_encodeKG_eq_true]
      exact and_congr_right fun _ => exists_isNIndepSet_iff_exists_isVertexCover _ hkn
    · rw [vertexCoverDec_noKG, indSetDec, Bool.eq_false_iff, ne_eq, kgDec_encodeKG_eq_true]
      rintro ⟨-, s, hs⟩
      have := hs.card_eq ▸ Finset.card_le_univ s
      simp only [Fintype.card_fin] at this
      omega
  next h => rw [indSetDec, kgDec_of_decodeKG_eq_none h, vertexCoverDec_noKG]

/-! ### SAT ≤ CLIQUE -/

theorem mem_occs {p : ℕ × ℕ × Bool} {φ : CNF} :
    p ∈ occs φ ↔ ∃ h : p.1 < φ.length, p.2 ∈ φ[p.1] := by
  rcases p with ⟨c, l⟩
  simp only [occs, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨C, c'⟩, hq, a, ha, heq⟩
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff] at hq
    obtain ⟨hc', hC⟩ := hq
    simp only [Prod.mk.injEq] at heq ha hC hc'
    obtain ⟨rfl, h2⟩ := heq
    subst hC
    exact ⟨hc', by rwa [← h2]⟩
  · rintro ⟨h, hl⟩
    exact ⟨(φ[c], c), List.mem_zipIdx_iff_getElem?.2 (by simp), l, hl, rfl⟩

theorem occAdj_eq_true {o o' : ℕ × ℕ × Bool} :
    occAdj o o' = true ↔ o.1 ≠ o'.1 ∧ (o.2.1 = o'.2.1 → o.2.2 = o'.2.2) := by
  simp [occAdj, imp_iff_not_or]

theorem occAdj_comm (o o' : ℕ × ℕ × Bool) : occAdj o o' = occAdj o' o := by
  rw [Bool.eq_iff_iff, occAdj_eq_true, occAdj_eq_true]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨Ne.symm h1, fun h => (h2 h.symm).symm⟩

/-- Adjacency in Karp's graph is `occAdj` on distinct occurrences. -/
theorem toGraph_cliqueBits_adj {φ : CNF} {i j : Fin (occs φ).length} :
    (toGraph _ (cliqueBits φ)).Adj i j ↔ i ≠ j ∧ occAdj (occs φ)[i] (occs φ)[j] = true := by
  simp only [toGraph, cliqueBits, ne_eq, and_congr_right_iff]
  intro hij
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
  · rw [adjBits_map_pairs _ hlt j.2]
    simp
  · rw [adjBits_comm, adjBits_map_pairs _ hgt i.2, occAdj_comm]
    simp

/-- Karp's correctness: `φ` is satisfiable iff its graph has a clique of `φ.length` vertices. -/
theorem cnfSat_iff_exists_isNClique (φ : CNF) :
    CNFSat φ ↔ ∃ s, (toGraph (occs φ).length (cliqueBits φ)).IsNClique φ.length s := by
  classical
  constructor
  · rintro ⟨v, hv⟩
    -- One true occurrence per clause.
    have hpick : ∀ c : Fin φ.length, ∃ i : Fin (occs φ).length,
        (occs φ)[i].1 = c ∧ v (occs φ)[i].2.1 = (occs φ)[i].2.2 := by
      intro c
      obtain ⟨x, b, hxb, hvx⟩ := hv φ[c] (List.getElem_mem _)
      obtain ⟨i, hi, hieq⟩ :=
        List.mem_iff_getElem.1 ((mem_occs (p := (c.1, x, b))).2 ⟨c.2, hxb⟩)
      exact ⟨⟨i, hi⟩, by simp [hieq], by simpa [hieq] using hvx⟩
    choose g hg1 hg2 using hpick
    have hinj : Function.Injective g := fun c c' h => Fin.ext (by rw [← hg1 c, ← hg1 c', h])
    refine ⟨Finset.univ.image g, ⟨?_, by rw [Finset.card_image_of_injective _ hinj]; simp⟩⟩
    intro a ha b hb hab
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨c', rfl⟩ := hb
    have hcc : (c : ℕ) ≠ c' := fun h => hab (by rw [Fin.ext h])
    refine toGraph_cliqueBits_adj.2 ⟨hab, occAdj_eq_true.2 ⟨by rwa [hg1, hg1], fun h => ?_⟩⟩
    rw [← hg2, ← hg2, h]
  · rintro ⟨s, hs⟩
    have hcl : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (occs φ)[i].1 ≠ (occs φ)[j].1 ∧
        ((occs φ)[i].2.1 = (occs φ)[j].2.1 → (occs φ)[i].2.2 = (occs φ)[j].2.2) :=
      fun i hi j hj hij =>
        occAdj_eq_true.1 (toGraph_cliqueBits_adj.1 (hs.isClique hi hj hij)).2
    have hlt : ∀ i : Fin (occs φ).length, (occs φ)[i].1 < φ.length := fun i =>
      (mem_occs.1 (List.getElem_mem (l := occs φ) i.2)).1
    -- The clique meets every clause: its clause indices are distinct and there are `m` of them.
    have himage : s.image (fun i => (occs φ)[i].1) = Finset.range φ.length := by
      apply Finset.eq_of_subset_of_card_le
      · intro c hc
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
        exact Finset.mem_range.2 (hlt i)
      · rw [Finset.card_image_of_injOn, hs.card_eq, Finset.card_range]
        intro i hi j hj h
        by_contra hne
        exact (hcl i hi j hj hne).1 h
    -- A variable is true iff it occurs positively in the clique.
    refine ⟨fun x => decide (∃ i ∈ s, (occs φ)[i].2 = (x, true)), fun C hC => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.1 hC
    obtain ⟨i, hi, hic⟩ := Finset.mem_image.1 (himage ▸ Finset.mem_range.2 hc)
    obtain ⟨_, hmem⟩ := mem_occs.1 (List.getElem_mem (l := occs φ) i.2)
    refine ⟨(occs φ)[i].2.1, (occs φ)[i].2.2, by subst hic; exact hmem, ?_⟩
    cases hb : (occs φ)[i].2.2
    · simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro j hj hjeq
      have hj2 : (occs φ)[j].2.2 = true := by rw [hjeq]
      have hij : i ≠ j := by
        rintro rfl
        simp only [Fin.getElem_fin] at hj2 hb
        simp [hj2] at hb
      have := (hcl i hi j hj hij).2 (by rw [hjeq])
      simp only [Fin.getElem_fin] at this hj2 hb
      rw [hb, hj2] at this
      simp at this
    · simp only [decide_eq_true_eq]
      exact ⟨i, hi, Prod.ext rfl hb⟩

@[simp] theorem reduceClique_encodeCNF (φ : CNF) : reduceClique (encodeCNF φ) = toClique φ := by
  simp [reduceClique]

theorem satDec_eq_cliqueDec_reduceClique (x : List Bool) :
    satDec x = cliqueDec (reduceClique x) := by
  unfold reduceClique
  split
  next φ h =>
    rw [decodeCNF_eq_some_iff] at h
    subst h
    rw [Bool.eq_iff_iff, DenseSAT.ToBinary.satDec_encodeCNF, toClique, cliqueDec,
      kgDec_encodeKG_eq_true, cnfSat_iff_exists_isNClique]
    simp [cliqueBits]
  next h => rw [DenseSAT.ToBinary.satDec_of_decodeCNF_eq_none h, cliqueDec_noKG]

/-- Moved to `DenseSAT.ToBinary.satDec_of_decodeCNF_eq_none` (`DenseToBinary`). -/
@[deprecated DenseSAT.ToBinary.satDec_of_decodeCNF_eq_none (since := "2026-10-15")]
theorem satDec_of_decodeCNF_eq_none {x : List Bool} (h : decodeCNF x = none) :
    satDec x = false :=
  DenseSAT.ToBinary.satDec_of_decodeCNF_eq_none h

end Cslib.Complexity.Karp
