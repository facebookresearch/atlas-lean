/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Sum
import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound

/-!
# Monochromatic clique packings

The Burr–Erdős–Spencer theorem gives the sharp leftover for monochromatic clique packings in
large two-colourings. The upper bound reserves a large monochromatic clique, and the lower
bound extends a colouring that fails the Ramsey property at one less than the Ramsey number.

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/MonochromaticCliquePartitionLeftoverErdosProblem1015Wanted.lean`:

Source: T. F. Bloom, Erdős Problems, Problem #1015, https://www.erdosproblems.com/1015 (status
SOLVED). UnsolvedMath record UM-30007126 (`EP-1015`), dataset ulamai/UnsolvedMath v1.8.0.

A two-colouring of the edges of `K_n` is a graph `G` on `Fin n` (red edges those of `G`, blue
edges those of `Gᶜ`), and a monochromatic `K_k` is a `k`-clique of `G` or of `Gᶜ`. As the page
notes, the question is meant for `n` sufficiently large depending on `t` (called `k` here), so the
least leftover depends on `n`; Burr, Erdős and Spencer call it `f(n, k)`. The page records their
answer as `R(t, t - 1) + x(t, n)` with `n + 1 ≡ R(t, t - 1) + x (mod t)`; Theorem 6 of the paper
reads `r(k, k - 1) - 1 + rem(n - r(k, k - 1) + 1, k)`, so the page drops the `- 1` (the page's
value is never congruent to `n` modulo `t`, while a leftover always is; for `t = 3` and `n ≡ 1
(mod 3)` it gives `5` against Moon's `f(3) = 4`). This module states Theorem 6 as printed in the
paper, with `r(k, k - 1)` the MathlibExt Ramsey number `SimpleGraph.graphRamsey k (k - 1)`, for
every `k ≥ 2` (for `k = 2` the value is `n mod 2`). The two follow-up questions are not stated:
their negative answers follow from Theorem 6 and the exponential growth of `r(t, t - 1)`, a step
the page does not record. formal-conjectures has no statement of this problem.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticCliquePartitionLeftoverErdosProblem1015Wanted

open SimpleGraph

/-- **Monochromatic clique packings.** Let $n$ and $k$ be natural numbers, and view a simple
graph $G$ on the vertex set $\{0, 1, \dots, n - 1\}$ as a two-colouring of the edges of the
complete graph $K_n$: the edges of $G$ are red and the edges of its complement $G^c$ are blue.
A finite family $P$ of sets of vertices is a monochromatic $k$-clique packing for $G$ when the
sets in $P$ are pairwise disjoint and each of them is a $k$-clique of $G$ or a $k$-clique of
$G^c$, that is, a set of exactly $k$ vertices spanning a monochromatic copy of $K_k$. -/
def IsMonochromaticCliquePacking {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (P : Finset (Finset (Fin n))) : Prop :=
  (P : Set (Finset (Fin n))).PairwiseDisjoint id ∧ ∀ S ∈ P, G.IsNClique k S ∨ Gᶜ.IsNClique k S

/-- **Burr–Erdős–Spencer leftover value.** For natural numbers $k$ and $n$, let $r = R(k, k - 1)$
be the classical two-colour Ramsey number. The leftover value is
$r - 1 + \big((n + 1 - r) \bmod k\big)$, where subtraction is truncated at $0$ (in particular
$n + 1 - r$ is read as $0$ when $n + 1 \le r$) and $a \bmod 0 = a$.

For $k \ge 2$ and large $n$, Burr, Erdős and Spencer showed that this is the least number of
vertices that vertex-disjoint monochromatic copies of $K_k$ can be guaranteed to leave uncovered
in every two-colouring of the edges of $K_n$. -/
noncomputable def leftoverValue (k n : ℕ) : ℕ :=
  graphRamsey k (k - 1) - 1 + (n + 1 - graphRamsey k (k - 1)) % k

/-- **Erdős Problem 1015 in the Burr–Erdős–Spencer form.** This is the statement that for every
natural number $k \ge 2$ there is $n_0$ such that for every $n \ge n_0$ the following holds. Let
$r = R(k, k - 1)$ be the classical two-colour Ramsey number and let
$L = r - 1 + \big((n + 1 - r) \bmod k\big)$, where $n + 1 - r$ is read as $0$ if it is negative.
View a simple graph $G$ on $n$ vertices as a two-colouring of the edges of $K_n$, with the edges
of $G$ red and those of its complement $G^c$ blue. Then every such colouring admits a
monochromatic $k$-clique packing, that is, a finite family of pairwise disjoint sets of vertices,
each a $k$-clique of $G$ or of $G^c$, leaving at most $L$ vertices uncovered; and some colouring
admits no such packing leaving fewer than $L$ vertices uncovered. In other words, for these $n$
the least number $f(n, k)$ such that every two-colouring of $K_n$ admits such a packing leaving at
most $f(n, k)$ vertices uncovered equals $L$. -/
def monochromaticCliquePartitionLeftover : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (∀ G : SimpleGraph (Fin n), ∃ P, IsMonochromaticCliquePacking G k P ∧
        n - k * P.card ≤ leftoverValue k n) ∧
    ∃ G : SimpleGraph (Fin n), ∀ P, IsMonochromaticCliquePacking G k P →
        leftoverValue k n ≤ n - k * P.card

private theorem isNClique_map_comap_iff {α β : Type*} (G : SimpleGraph β) (e : α ↪ β)
    {k : ℕ} {S : Finset α} : (G.comap e).IsNClique k S ↔ G.IsNClique k (S.map e) := by
  simp only [isNClique_iff, Finset.card_map]
  refine and_congr ⟨?_, ?_⟩ Iff.rfl
  · intro h _ hx _ hy hne
    obtain ⟨x, hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y, hy', rfl⟩ := Finset.mem_map.mp hy
    exact h hx' hy' (fun he => hne (congrArg e he))
  · intro h x hx y hy hne
    exact h (Finset.mem_map_of_mem e hx) (Finset.mem_map_of_mem e hy) (e.injective.ne hne)

private theorem comap_compl {α β : Type*} (G : SimpleGraph β) (e : α ↪ β) :
    Gᶜ.comap e = (G.comap e)ᶜ := by
  ext x y
  simp [e.injective.ne_iff]

open Finset MathlibExt.Combinatorics.RamseyErdosLowerBound

private theorem ramsey_on {n s t b : ℕ} (h : classicalRamsey s t b)
    (G : SimpleGraph (Fin n)) {U : Finset (Fin n)} (hU : b ≤ U.card) :
    (∃ S ⊆ U, G.IsNClique s S) ∨ ∃ S ⊆ U, Gᶜ.IsNClique t S := by
  let e₀ := (equivFinOfCardEq (rfl : U.card = U.card)).symm.toEmbedding
  let e : Fin U.card ↪ Fin n := e₀.trans (.subtype (· ∈ U))
  have liftClique (H : SimpleGraph (Fin n)) {l : ℕ} (hc :
      (completeGraph (Fin l)).IsContained (H.comap e)) : ∃ S ⊆ U, H.IsNClique l S := by
    obtain ⟨f⟩ := hc
    refine ⟨(univ.map f.toEmbedding).map e, ?_, (isNClique_map_comap_iff H e).1 ?_⟩
    · intro x hx
      obtain ⟨y, -, rfl⟩ := mem_map.1 hx
      exact (e₀ y).property
    · simpa only [Fintype.card_fin] using isNClique_map_copy_top f
  rcases classicalRamsey_mono hU h (G.comap e) with hc | hc
  · exact Or.inl (liftClique G hc)
  · rw [← comap_compl] at hc
    exact Or.inr (liftClique Gᶜ hc)

private theorem ramsey_at_minimum (s t : ℕ) : classicalRamsey s t (graphRamsey s t) :=
  Nat.sInf_mem (s := {N | classicalRamsey s t N}) (exists_classicalRamsey s t)

private abbrev IsMonoClique {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (S : Finset (Fin n)) :=
  G.IsNClique k S ∨ Gᶜ.IsNClique k S

private theorem mono_card {n k : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (h : IsMonoClique G k S) : S.card = k :=
  h.elim IsNClique.card_eq IsNClique.card_eq

private theorem packing_card {n k : ℕ} {G : SimpleGraph (Fin n)} {P : Finset (Finset (Fin n))}
    (hP : IsMonochromaticCliquePacking G k P) : (P.biUnion id).card = k * P.card := by
  rw [card_biUnion hP.1]
  calc
    ∑ S ∈ P, S.card = ∑ _S ∈ P, k := sum_congr rfl (fun S hS => mono_card (hP.2 S hS))
    _ = k * P.card := by simp [Nat.mul_comm]

private theorem packing_union {n k : ℕ} {G : SimpleGraph (Fin n)}
    {P Q : Finset (Finset (Fin n))} (hP : IsMonochromaticCliquePacking G k P)
    (hQ : IsMonochromaticCliquePacking G k Q) (hPQ : Disjoint (P.biUnion id) (Q.biUnion id)) :
    IsMonochromaticCliquePacking G k (P ∪ Q) := by
  refine ⟨?_, fun S hS => (mem_union.1 hS).elim (hP.2 S) (hQ.2 S)⟩
  rw [coe_union]
  exact hP.1.union hQ.1 fun _ hS _ hT _ =>
    hPQ.mono (subset_biUnion_of_mem id hS) (subset_biUnion_of_mem id hT)

/-- A packing removes exactly the vertices in `U \ T` and leaves `T`. -/
private structure PacksTo {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (U T : Finset (Fin n)) : Prop where
  subset : T ⊆ U
  exists_packing : ∃ P, IsMonochromaticCliquePacking G k P ∧ P.biUnion id = U \ T

private theorem PacksTo.refl {n k : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) :
    PacksTo G k U U :=
  ⟨Subset.rfl, ∅, ⟨by simp, by simp⟩, by simp⟩

private theorem PacksTo.trans {n k : ℕ} {G : SimpleGraph (Fin n)} {U T W : Finset (Fin n)}
    (h₁ : PacksTo G k U T) (h₂ : PacksTo G k T W) : PacksTo G k U W := by
  obtain ⟨P, hP, hPe⟩ := h₁.exists_packing
  obtain ⟨Q, hQ, hQe⟩ := h₂.exists_packing
  have hd : Disjoint (P.biUnion id) (Q.biUnion id) := by
    rw [hPe, hQe]
    exact sdiff_disjoint.mono_right sdiff_subset
  refine ⟨h₂.subset.trans h₁.subset, P ∪ Q, packing_union hP hQ hd, ?_⟩
  rw [union_biUnion, hPe, hQe, sdiff_union_sdiff_cancel h₁.subset h₂.subset]

private theorem PacksTo.remove {n k : ℕ} {G : SimpleGraph (Fin n)} {U S : Finset (Fin n)}
    (hSU : S ⊆ U) (hS : IsMonoClique G k S) : PacksTo G k U (U \ S) := by
  refine ⟨sdiff_subset, {S}, ⟨by simp, ?_⟩, ?_⟩
  · simpa only [mem_singleton, forall_eq] using hS
  · simp [Finset.sdiff_sdiff_eq_self hSU]

private theorem PacksTo.union_right {n k : ℕ} {G : SimpleGraph (Fin n)} {U T D : Finset (Fin n)}
    (h : PacksTo G k U T) (hd : Disjoint U D) : PacksTo G k (U ∪ D) (T ∪ D) := by
  obtain ⟨P, hP, hPe⟩ := h.exists_packing
  refine ⟨union_subset_union h.subset Subset.rfl, P, hP, ?_⟩
  rw [hPe]
  ext x
  simp only [mem_sdiff, mem_union]
  have hxd : x ∈ U → x ∉ D := fun hx => Finset.disjoint_left.1 hd hx
  tauto

-- Repeatedly remove one clique whenever the current set reaches the given threshold.
private theorem pack_below {n k b : ℕ} {G : SimpleGraph (Fin n)} (hk : 0 < k)
    {U : Finset (Fin n)}
    (step : ∀ T ⊆ U, b ≤ T.card → ∃ S ⊆ T, IsMonoClique G k S) :
    ∃ T, PacksTo G k U T ∧ T.card < b := by
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    by_cases hU : U.card < b
    · exact ⟨U, PacksTo.refl G U, hU⟩
    · obtain ⟨S, hSU, hS⟩ := step U Subset.rfl (Nat.le_of_not_gt hU)
      have hne : S.Nonempty := card_pos.1 ((mono_card hS).symm ▸ hk)
      obtain ⟨T, hT, hTb⟩ := ih (U \ S) (sdiff_ssubset hSU hne)
        (fun V hV => step V (hV.trans sdiff_subset))
      exact ⟨T, (PacksTo.remove hSU hS).trans hT, hTb⟩

private theorem extend_clique {n k : ℕ} {H : SimpleGraph (Fin n)} (hk : 0 < k)
    {x : Fin n} {S : Finset (Fin n)} (hS : H.IsNClique (k - 1) S) (hx : x ∉ S)
    (hadj : ∀ y ∈ S, H.Adj x y) : H.IsNClique k (insert x S) := by
  constructor
  · rw [coe_insert]
    exact (isClique_insert_of_notMem hx).2 ⟨hS.isClique, hadj⟩
  · rw [card_insert_of_notMem hx, hS.card_eq]
    omega

-- With a red reserve, cover a vertex outside it using either a red extension or Ramsey's theorem.
private theorem clique_meeting_residual {n k : ℕ} (hk : 2 ≤ k) {G : SimpleGraph (Fin n)}
    {C B : Finset (Fin n)} (hC : G.IsClique C) (hd : Disjoint C B) (hsize : k * k < C.card)
    (hB : graphRamsey k (k - 1) ≤ B.card) :
    ∃ S ⊆ C ∪ B, IsMonoClique G k S ∧ (B ∩ S).Nonempty := by
  classical
  let neighbors (x : Fin n) := C.filter (G.Adj x)
  by_cases hred : ∃ x ∈ B, k - 1 ≤ (neighbors x).card
  · obtain ⟨x, hxB, hx⟩ := hred
    obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq hx
    have hSC : S ⊆ C := hS.trans (filter_subset _ _)
    have hxS : x ∉ S := fun h => Finset.disjoint_left.1 hd (hSC h) hxB
    refine ⟨insert x S, ?_, Or.inl (extend_clique (by omega) ⟨hC.subset hSC, hcard⟩ hxS ?_),
      ⟨x, mem_inter.2 ⟨hxB, mem_insert_self _ _⟩⟩⟩
    · exact insert_subset (mem_union_right _ hxB) (hSC.trans subset_union_left)
    · exact fun y hy => (mem_filter.1 (hS hy)).2
  · rcases ramsey_on (ramsey_at_minimum k (k - 1)) G hB with ⟨S, hS, hredS⟩ | ⟨T, hT, hblue⟩
    · obtain ⟨x, hx⟩ := card_pos.1 (show 0 < S.card by rw [hredS.card_eq]; omega)
      exact ⟨S, hS.trans subset_union_right, Or.inl hredS, ⟨x, mem_inter.2 ⟨hS hx, hx⟩⟩⟩
    -- The blue clique forbids at most `k * k` vertices of the reserve as possible extensions.
    have hforbidden : (T.biUnion neighbors).card ≤ k * k := by
      calc
        (T.biUnion neighbors).card ≤ ∑ x ∈ T, (neighbors x).card := card_biUnion_le
        _ ≤ ∑ _x ∈ T, k := by
          refine sum_le_sum fun x hx => ?_
          have hl : ¬ k - 1 ≤ (neighbors x).card := fun h => hred ⟨x, hT hx, h⟩
          omega
        _ = T.card * k := by simp
        _ ≤ k * k := Nat.mul_le_mul_right k (by rw [hblue.card_eq]; omega)
    obtain ⟨y, hyC, hy⟩ := exists_mem_notMem_of_card_lt_card (hforbidden.trans_lt hsize)
    have hyT : y ∉ T := fun hyT => Finset.disjoint_left.1 hd hyC (hT hyT)
    have hblueAdj : ∀ x ∈ T, Gᶜ.Adj y x := by
      intro x hx
      refine (compl_adj G y x).2 ⟨fun he => hyT (he.symm ▸ hx), fun h => hy ?_⟩
      exact mem_biUnion.2 ⟨x, hx, mem_filter.2 ⟨hyC, h.symm⟩⟩
    obtain ⟨x, hx⟩ := card_pos.1 (show 0 < T.card by rw [hblue.card_eq]; omega)
    exact ⟨insert y T, insert_subset (mem_union_left _ hyC) (hT.trans subset_union_right),
      Or.inr (extend_clique (by omega) hblue hyT hblueAdj),
      ⟨x, mem_inter.2 ⟨hT hx, mem_insert_of_mem hx⟩⟩⟩

-- Each step reduces the residual set and spends at most `k` vertices of the reserve.
private theorem pack_with_reserve {n k : ℕ} (hk : 2 ≤ k) {G : SimpleGraph (Fin n)}
    {C B : Finset (Fin n)} (hC : G.IsClique C) (hd : Disjoint C B)
    (hsize : k * k + 1 + k * B.card ≤ C.card) :
    ∃ T, PacksTo G k (C ∪ B) T ∧ T.card < graphRamsey k (k - 1) - 1 + k := by
  induction B using Finset.strongInductionOn generalizing C with
  | _ B ih =>
    by_cases hB : B.card < graphRamsey k (k - 1)
    · obtain ⟨C', hC', hC'k⟩ := pack_below (k := k) (by omega) (G := G) (U := C) (b := k)
        (fun T hTC hkT => by
          obtain ⟨S, hST, hSk⟩ := exists_subset_card_eq hkT
          exact ⟨S, hST, Or.inl ⟨hC.subset (hST.trans hTC), hSk⟩⟩)
      refine ⟨C' ∪ B, hC'.union_right hd, ?_⟩
      have := card_union_le C' B
      omega
    · obtain ⟨S, hSsub, hS, x, hx⟩ :=
        clique_meeting_residual hk hC hd (by omega) (Nat.le_of_not_gt hB)
      have hBx := (mem_inter.1 hx).1
      have hSx := (mem_inter.1 hx).2
      have hlt : B \ S ⊂ B := Finset.ssubset_iff_subset_ne.2
        ⟨sdiff_subset, fun he => (mem_sdiff.1 (he.symm ▸ hBx)).2 hSx⟩
      have hmul := Nat.mul_le_mul_left k (show (B \ S).card + 1 ≤ B.card from card_lt_card hlt)
      rw [Nat.mul_add, Nat.mul_one] at hmul
      have hcost : C.card ≤ (C \ S).card + k := by
        rw [← mono_card hS]
        refine (card_le_card (show C ⊆ (C \ S) ∪ S from ?_)).trans (card_union_le _ _)
        intro y hy
        by_cases hyS : y ∈ S
        · exact mem_union_right _ hyS
        · exact mem_union_left _ (mem_sdiff.2 ⟨hy, hyS⟩)
      obtain ⟨T, hT, hTc⟩ := ih (B \ S) hlt (C := C \ S) (hC.subset sdiff_subset)
        (hd.mono sdiff_subset sdiff_subset) (by omega)
      have hstep : PacksTo G k (C ∪ B) ((C \ S) ∪ (B \ S)) := by
        rw [← sup_sdiff]
        exact PacksTo.remove hSsub hS
      exact ⟨T, hstep.trans hT, hTc⟩

private theorem upper_of_monochromatic_reserve {n k : ℕ} (hk : 2 ≤ k) {G : SimpleGraph (Fin n)}
    {C : Finset (Fin n)} (hC : G.IsNClique (k * k + 1 + k * graphRamsey k k) C) :
    ∃ T, PacksTo G k univ T ∧ T.card < graphRamsey k (k - 1) - 1 + k := by
  obtain ⟨B, hP, hB⟩ := pack_below (k := k) (by omega) (G := G) (U := univ \ C)
    (b := graphRamsey k k)
    (fun _ _ hT => by
      rcases ramsey_on (ramsey_at_minimum k k) G hT with ⟨S, hS, hc⟩ | ⟨S, hS, hc⟩
      · exact ⟨S, hS, Or.inl hc⟩
      · exact ⟨S, hS, Or.inr hc⟩)
  have hinit := hP.union_right (D := C) sdiff_disjoint
  rw [sdiff_union_of_subset (subset_univ C), union_comm B C] at hinit
  have hsize : k * k + 1 + k * B.card ≤ C.card := by
    rw [hC.card_eq]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left k (Nat.le_of_lt hB)) _
  obtain ⟨T, hT, hTc⟩ := pack_with_reserve hk hC.isClique
    (Finset.disjoint_sdiff.mono_right hP.subset) hsize
  exact ⟨T, hinit.trans hT, hTc⟩

private theorem PacksTo.of_compl {n k : ℕ} {G : SimpleGraph (Fin n)} {U T : Finset (Fin n)}
    (h : PacksTo Gᶜ k U T) : PacksTo G k U T := by
  obtain ⟨P, hP, hPe⟩ := h.exists_packing
  refine ⟨h.subset, P, ⟨hP.1, fun S hS => ?_⟩, hPe⟩
  simpa only [compl_compl, or_comm] using hP.2 S hS

private theorem ramsey_obstruction {k : ℕ} (hk : 2 ≤ k) :
    0 < graphRamsey k (k - 1) ∧
      ∃ H : SimpleGraph (Fin (graphRamsey k (k - 1) - 1)),
        H.CliqueFree k ∧ Hᶜ.CliqueFree (k - 1) := by
  have hzero : ¬ classicalRamsey k (k - 1) 0 := by
    intro h
    rcases h ⊥ with hc | hc
    · exact Fin.elim0 (hc.some ⟨0, by omega⟩)
    · exact Fin.elim0 (hc.some ⟨0, by omega⟩)
  have hr : 0 < graphRamsey k (k - 1) := Nat.pos_of_ne_zero fun he =>
    hzero (he ▸ ramsey_at_minimum k (k - 1))
  have hf : ¬ classicalRamsey k (k - 1) (graphRamsey k (k - 1) - 1) := by
    intro h
    have hle : graphRamsey k (k - 1) ≤ graphRamsey k (k - 1) - 1 :=
      Nat.sInf_le (s := {N | classicalRamsey k (k - 1) N}) h
    omega
  unfold classicalRamsey at hf
  simp only [not_forall, not_or] at hf
  obtain ⟨H, hred, hblue⟩ := hf
  exact ⟨hr, H, fun _ h => hred ((not_cliqueFree_iff_top_isContained k).1 h.not_cliqueFree),
    fun _ h => hblue ((not_cliqueFree_iff_top_isContained (k - 1)).1 h.not_cliqueFree)⟩

-- Take the disjoint red sum of the Ramsey obstruction and a complete graph.
-- Red cliques cannot cross the two parts, and a blue clique uses at most one vertex on the right.
private theorem sum_clique_avoids_left {α β : Type*} {k : ℕ} {H : SimpleGraph α}
    (hred : H.CliqueFree k) (hblue : Hᶜ.CliqueFree (k - 1)) {S : Finset (α ⊕ β)}
    (hS : (H ⊕g (⊤ : SimpleGraph β)).IsNClique k S ∨ (H ⊕g (⊤ : SimpleGraph β))ᶜ.IsNClique k S) :
    S.toLeft = ∅ := by
  classical
  rcases hS with hS | hS
  · by_contra hne
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
    have hR : S.toRight = ∅ := eq_empty_iff_forall_notMem.2 fun y hy =>
      not_adj_sum_inl_inr x y (hS.isClique (mem_toLeft.1 hx) (mem_toRight.1 hy) (by simp))
    apply hred S.toLeft
    refine ⟨?_, by simpa [hR, hS.card_eq] using card_toLeft_add_card_toRight (u := S)⟩
    intro a ha b hb hab
    exact sum_adj_inl.1 (hS.isClique (mem_toLeft.1 ha) (mem_toLeft.1 hb) (Sum.inl_injective.ne hab))
  · exfalso
    have hR : S.toRight.card ≤ 1 := card_le_one_iff.2 fun {a b} ha hb => by
      by_contra hne
      have h := hS.isClique (mem_toRight.1 ha) (mem_toRight.1 hb) (Sum.inr_injective.ne hne)
      exact (compl_adj _ _ _).1 h |>.2 (sum_adj_inr.2 ((top_adj a b).2 hne))
    have hsum := card_toLeft_add_card_toRight (u := S)
    rw [hS.card_eq] at hsum
    obtain ⟨T, hT, hTk⟩ := exists_subset_card_eq (show k - 1 ≤ S.toLeft.card by omega)
    refine hblue T ⟨?_, hTk⟩
    intro a ha b hb hab
    have h := hS.isClique (mem_toLeft.1 (hT ha)) (mem_toLeft.1 (hT hb)) (Sum.inl_injective.ne hab)
    exact (compl_adj H a b).2 ⟨hab, fun hadj => ((compl_adj _ _ _).1 h).2 (sum_adj_inl.2 hadj)⟩

private theorem packing_bound_of_obstruction {n m k : ℕ} (hm : m ≤ n)
    {H : SimpleGraph (Fin m)} (hred : H.CliqueFree k) (hblue : Hᶜ.CliqueFree (k - 1)) :
    ∃ G : SimpleGraph (Fin n), ∀ P, IsMonochromaticCliquePacking G k P → k * P.card ≤ n - m := by
  let J := H ⊕g (⊤ : SimpleGraph (Fin (n - m)))
  let e : Fin n ≃ Fin m ⊕ Fin (n - m) := (finSumFinEquiv.trans (finCongr (by omega))).symm
  refine ⟨J.comap e, fun P hP => ?_⟩
  let A : Finset (Fin m ⊕ Fin (n - m)) := (univ : Finset (Fin (n - m))).map .inr
  have hsub : (P.biUnion id).map e.toEmbedding ⊆ A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    obtain ⟨S, hS, hyS⟩ := mem_biUnion.1 hy
    have hclique : J.IsNClique k (S.map e.toEmbedding) ∨ Jᶜ.IsNClique k (S.map e.toEmbedding) := by
      rcases hP.2 S hS with hc | hc
      · exact Or.inl ((isNClique_map_comap_iff J e.toEmbedding).1 hc)
      · exact Or.inr ((isNClique_map_comap_iff Jᶜ e.toEmbedding).1 (by rwa [comap_compl]))
    have hleft := sum_clique_avoids_left hred hblue hclique
    exact (subset_map_inr.2 ⟨hleft, subset_univ _⟩) (mem_map_of_mem e.toEmbedding hyS)
  simpa [A, packing_card hP] using card_le_card hsub

/-- **Burr–Erdős–Spencer theorem on monochromatic clique packings.** For every natural number
$k \ge 2$ there is $n_0$ such that for every $n \ge n_0$ the following holds. Let
$r = R(k, k - 1)$ be the classical two-colour Ramsey number and let
$L = r - 1 + \big((n + 1 - r) \bmod k\big)$, where $n + 1 - r$ is read as $0$ if it is negative.
View a simple graph $G$ on $n$ vertices as a two-colouring of the edges of $K_n$, with the edges
of $G$ red and those of its complement $G^c$ blue. Then every such colouring admits a finite
family of pairwise disjoint sets of vertices, each a $k$-clique of $G$ or of $G^c$, that leaves at
most $L$ vertices uncovered; and some colouring admits no such family leaving fewer than $L$
vertices uncovered.

Source: T. F. Bloom,
Erdős Problems, Problem #1015, https://www.erdosproblems.com/1015 (status SOLVED); resolution: S.
A. Burr, P. Erdős and J. H. Spencer, Ramsey theorems for multiple copies of graphs, Trans. Amer.
Math. Soc. 209 (1975), 87-99, §5, Theorem 6: if k is given, then for sufficiently large n, f(n, k)
= r(k, k - 1) - 1 + rem(n - r(k, k - 1) + 1, k), where f(n, k) is the minimal integer such that
any two-coloring of K_n admits vertex-disjoint monochromatic K_k with at most f(n, k) points left
over; erdosproblems.com/1015 lists the problem as solved citing this paper,
https://users.renyi.hu/~p_erdos/1975-35.pdf.
-/
public theorem monochromaticCliquePartitionLeftover_holds :
    monochromaticCliquePartitionLeftover := by
  intro k hk
  have hk₀ : 0 < k := by omega
  let r := graphRamsey k (k - 1)
  let m := r - 1
  let M := k * k + 1 + k * graphRamsey k k
  obtain ⟨hr, H, hred, hblue⟩ := ramsey_obstruction hk
  refine ⟨max r (graphRamsey M M), fun n hn => ?_⟩
  have hrn : r ≤ n := (le_max_left _ _).trans hn
  have hmn : m ≤ n := (Nat.sub_le _ _).trans hrn
  have hM : graphRamsey M M ≤ (univ : Finset (Fin n)).card := by
    simpa using (le_max_right r (graphRamsey M M)).trans hn
  have hsub : n + 1 - r = n - m := by dsimp [m]; omega
  have hvalue : leftoverValue k n + k * ((n - m) / k) = n := by
    change m + (n + 1 - r) % k + k * ((n - m) / k) = n
    rw [hsub]
    have := Nat.mod_add_div (n - m) k
    omega
  constructor
  · intro G
    have hupper : ∃ T, PacksTo G k univ T ∧ T.card < m + k := by
      rcases ramsey_on (ramsey_at_minimum M M) G hM with ⟨C, _, hC⟩ | ⟨C, _, hC⟩
      · exact upper_of_monochromatic_reserve hk hC
      · obtain ⟨T, hT, hTk⟩ := upper_of_monochromatic_reserve hk hC
        exact ⟨T, hT.of_compl, hTk⟩
    obtain ⟨T, hT, hTk⟩ := hupper
    obtain ⟨P, hP, hPe⟩ := hT.exists_packing
    refine ⟨P, hP, ?_⟩
    have hcard := packing_card hP
    rw [hPe, card_sdiff_of_subset hT.subset, card_univ, Fintype.card_fin] at hcard
    have hTn : T.card ≤ n := by simpa using card_le_card hT.subset
    have hdiv : (n - m) / k < P.card + 1 := by
      apply (Nat.div_lt_iff_lt_mul hk₀).2
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm P.card k]
      omega
    have := Nat.mul_le_mul_left k (show (n - m) / k ≤ P.card by omega)
    omega
  · obtain ⟨G, hG⟩ := packing_bound_of_obstruction hmn hred hblue
    refine ⟨G, fun P hP => ?_⟩
    have hdiv : P.card ≤ (n - m) / k :=
      (Nat.le_div_iff_mul_le hk₀).2 (by rw [Nat.mul_comm]; exact hG P hP)
    have := Nat.mul_le_mul_left k hdiv
    omega

end MathlibExt.Combinatorics.MonochromaticCliquePartitionLeftoverErdosProblem1015Wanted
