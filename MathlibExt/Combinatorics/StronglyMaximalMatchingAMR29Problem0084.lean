/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Strongly maximal matchings in hypergraphs with bounded edges (EGRES open problem)

EGRES Open, Strongly maximal matchings: is it true that if all the hyperedges of a hypergraph `H`
have size at most `k` for some `k ∈ ℕ`, then `H` admits a strongly maximal matching?

Hollom and Randall Shaw construct a `3`-uniform hypergraph with no strongly maximal matching,
refuting the claim. The proof below follows their argument: an unbounded hypergraph on `ℕ`
whose edges satisfy `|e| = min e` has no strongly maximal matching, and a gadget replacing
each such edge by edges of size at most `3` simulates it.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.StronglyMaximalMatchingAMR29Problem0084Wanted

/-!
Source: EGRES Open (Egerváry Research Group), list of open problems, Strongly maximal matchings,
https://oldlemon.cs.elte.hu/egres/open/Strongly_maximal_matchings. UnsolvedMath record UM-03000084
(`AMR-029-0084`), dataset ulamai/UnsolvedMath v1.8.0.

A hypergraph on a vertex type `V` is a set `E` of finite edges (`Finset V`); `V` and `E` may be
infinite. A matching is a set of pairwise disjoint edges, and it is strongly maximal if `|M' \ M| ≤
|M \ M'|` (cardinals) for every matching `M'`, the definition of Hollom and Randall Shaw
(Introduction), which their abstract says resolves the questions of Aharoni and others listed by
EGRES.
-/

/-- **Matching in a hypergraph.** For a hypergraph on a vertex set $V$ whose edges form a set $E$
of finite subsets of $V$, a set $M$ is a matching when $M \subseteq E$ and any two distinct
members of $M$ are disjoint. -/
def IsMatching {V : Type} (E M : Set (Finset V)) : Prop :=
  M ⊆ E ∧ M.Pairwise Disjoint

/-- **Strongly maximal matching.** For a hypergraph with edge set $E$, a set $M$ is a strongly
maximal matching (Aharoni) when $M$ is a matching of $E$ and every matching $M'$ of $E$
satisfies $|M' \setminus M| \le |M \setminus M'|$, comparing the cardinalities as cardinal
numbers. -/
def IsStronglyMaximal {V : Type} (E M : Set (Finset V)) : Prop :=
  IsMatching E M ∧ ∀ M', IsMatching E M' → Cardinal.mk ↥(M' \ M) ≤ Cardinal.mk ↥(M \ M')

/-- **Strongly maximal matchings in hypergraphs with bounded edges.** The statement that for
every vertex set $V$ and every set $E$ of finite subsets of $V$ such that some natural number $k$
bounds the number of elements of every edge in $E$, the hypergraph with edge set $E$ has a
strongly maximal matching.

This is the claim from the EGRES list of open problems; it has since been refuted. -/
def boundedEdgesStronglyMaximalMatching : Prop :=
  ∀ (V : Type) (E : Set (Finset V)) (k : ℕ), (∀ e ∈ E, e.card ≤ k) →
    ∃ M, IsStronglyMaximal E M

/-- The edges of the unbounded hypergraph of Hollom and Randall Shaw (Theorem 1.8): the finite
subsets `e` of `ℕ` whose cardinality equals their least element. -/
private def starEdges : Set (Finset ℕ) :=
  {e | ∃ m, m ∈ e ∧ e.card = m ∧ ∀ x ∈ e, m ≤ x}

/-- The least element of an edge of `starEdges`: for such an edge it equals the
cardinality, since the cardinality equals the least element by definition. -/
private def starMin (e : Finset ℕ) : ℕ := e.card

private theorem starMin_spec {e : Finset ℕ} (he : e ∈ starEdges) :
    starMin e ∈ e ∧ e.card = starMin e ∧ ∀ x ∈ e, starMin e ≤ x := by
  obtain ⟨m, hm, hcard, hmin⟩ := he
  refine ⟨?_, rfl, ?_⟩
  · rw [starMin, hcard]; exact hm
  · intro x hx
    rw [starMin, hcard]; exact hmin x hx

private theorem starMin_card {e : Finset ℕ} (he : e ∈ starEdges) :
    e.card = starMin e :=
  (starMin_spec he).2.1

private theorem starMin_mem {e : Finset ℕ} (he : e ∈ starEdges) : starMin e ∈ e :=
  (starMin_spec he).1

/-- Distinct edges of a matching in `starEdges` have distinct least elements. -/
private theorem starMin_injOn {M : Set (Finset ℕ)} (hM : IsMatching starEdges M) :
    Set.InjOn starMin M := by
  intro e₁ he₁ e₂ he₂ h
  by_contra hne
  have hdis := hM.2 he₁ he₂ hne
  rw [Finset.disjoint_left] at hdis
  exact hdis (starMin_mem (hM.1 he₁)) (h ▸ starMin_mem (hM.1 he₂))

/-- Only finitely many edges of a matching in `starEdges` have least element below a bound. -/
private theorem finite_starMin_lt {M : Set (Finset ℕ)} (hM : IsMatching starEdges M)
    (B : ℕ) : (M ∩ starMin ⁻¹' Finset.range B).Finite := by
  apply Set.Finite.of_injOn (f := starMin) (t := Finset.range B)
  · intro x hx
    exact Finset.mem_coe.mpr hx.2
  · exact (starMin_injOn hM).mono (fun _ hx ↦ hx.1)
  · exact Set.finite_coe_iff.mpr (Finset.finite_toSet _)

private theorem exists_starMin_ge {M : Set (Finset ℕ)} (hM : IsMatching starEdges M)
    (hinf : M.Infinite) (B : ℕ) : ∃ e ∈ M, B ≤ starMin e := by
  by_contra h
  have hlt : ∀ e ∈ M, starMin e < B := by
    intro e he
    by_contra hc
    exact h ⟨e, he, Nat.le_of_not_gt hc⟩
  have hsub : M ⊆ M ∩ starMin ⁻¹' Finset.range B := by
    intro e he
    exact ⟨he, Finset.mem_range.mpr (hlt e he)⟩
  exact hinf ((finite_starMin_lt hM B).subset hsub)

private theorem star_improvement_of_finite {M : Set (Finset ℕ)}
    (hM : IsMatching starEdges M) (hfin : M.Finite) :
    ∃ N, IsMatching starEdges N ∧ (N \ M).Finite ∧ (M \ N).Finite ∧
      (M \ N).ncard < (N \ M).ncard := by
  classical
  let S : Finset (Finset ℕ) := hfin.toFinset
  let U : Finset ℕ := S.biUnion id
  let n : ℕ := U.sup id + 1
  let F : Finset ℕ := Finset.Icc n (2 * n - 1)
  have hU : ∀ x ∈ U, x < n := by
    intro x hx
    have : x ≤ U.sup id := Finset.le_sup (f := id) hx
    simp only [n] at this ⊢
    omega
  have hn : 1 ≤ n := by simp [n]
  have hFmem : F ∈ starEdges := by
    refine ⟨n, ?_, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.le_refl _, by omega⟩
    · rw [show F.card = (2 * n - 1) + 1 - n from Nat.card_Icc n (2 * n - 1)]
      omega
    · intro x hx; simp only [F, Finset.mem_Icc] at hx; exact hx.1
  have hFsub : ∀ e ∈ M, Disjoint F e := by
    intro e he
    rw [Finset.disjoint_left]
    intro x hxF hxe
    have hxU : x ∈ U := by
      apply Finset.mem_biUnion.mpr
      exact ⟨e, by simp [S, hfin.mem_toFinset.mpr he], hxe⟩
    exact absurd (hU x hxU) (not_lt_of_ge (by
      simp only [F, Finset.mem_Icc] at hxF; exact hxF.1))
  have hFnot : F ∉ M := by
    intro hFM
    have hxU : n ∈ U := by
      apply Finset.mem_biUnion.mpr
      exact ⟨F, by simp [S, hfin.mem_toFinset.mpr hFM],
        Finset.mem_Icc.mpr ⟨Nat.le_refl _, by omega⟩⟩
    exact absurd (hU n hxU) (lt_irrefl n)
  refine ⟨insert F M, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e he
    rcases Set.mem_insert_iff.mp he with rfl | heM
    · exact hFmem
    · exact hM.1 heM
  · intro a ha b hb hab
    rcases Set.mem_insert_iff.mp ha with rfl | haM <;>
      rcases Set.mem_insert_iff.mp hb with rfl | hbM
    · exact absurd rfl hab
    · exact hFsub b hbM
    · exact (hFsub a haM).symm
    · exact hM.2 haM hbM hab
  · rw [show insert F M \ M = {F} by ext x; simp [hFnot]]
    exact Set.finite_singleton F
  · rw [show M \ insert F M = ∅ by
      exact Set.eq_empty_of_forall_notMem fun x hx ↦
        hx.2 (Set.mem_insert_of_mem F hx.1)]
    exact Set.finite_empty
  · rw [show insert F M \ M = {F} by ext x; simp [hFnot],
      show M \ insert F M = ∅ by
        exact Set.eq_empty_of_forall_notMem fun x hx ↦
          hx.2 (Set.mem_insert_of_mem F hx.1)]
    simp

private theorem star_improvement_of_infinite {M : Set (Finset ℕ)}
    (hM : IsMatching starEdges M) (hinf : M.Infinite) :
    ∃ N, IsMatching starEdges N ∧ (N \ M).Finite ∧ (M \ N).Finite ∧
      (M \ N).ncard < (N \ M).ncard := by
  classical
  obtain ⟨E1, hE1M, hE1card⟩ := exists_starMin_ge hM hinf 3
  have hE1spec := starMin_spec (hM.1 hE1M)
  have hstar1 : starMin E1 = E1.card := rfl
  have hE1card3 : 3 ≤ E1.card := by omega
  -- The three smallest elements of `E1`.
  have hE1ne : (E1.erase (starMin E1)).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem (starMin_mem (hM.1 hE1M))]
    omega)
  set v2 := (E1.erase (starMin E1)).min' hE1ne with hv2def
  have hv2mem : v2 ∈ E1.erase (starMin E1) := Finset.min'_mem _ _
  have hv2inE1 : v2 ∈ E1 := (Finset.mem_erase.mp hv2mem).2
  have hv2ne : v2 ≠ starMin E1 := (Finset.mem_erase.mp hv2mem).1
  have hv1ltv2 : starMin E1 < v2 := by
    have hle := hE1spec.2.2 v2 hv2inE1
    omega
  have hE1bne : (E1.erase (starMin E1) |>.erase v2).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hv2mem, Finset.card_erase_of_mem
      (starMin_mem (hM.1 hE1M))]
    omega)
  set v3 := (E1.erase (starMin E1) |>.erase v2).min' hE1bne with hv3def
  have hv3mem : v3 ∈ (E1.erase (starMin E1)).erase v2 := Finset.min'_mem _ _
  have hv3inE1a : v3 ∈ E1.erase (starMin E1) := (Finset.mem_erase.mp hv3mem).2
  have hv3inE1 : v3 ∈ E1 := (Finset.mem_erase.mp hv3inE1a).2
  have hv3ne2 : v3 ≠ v2 := (Finset.mem_erase.mp hv3mem).1
  have hv2ltv3 : v2 < v3 := by
    have hle : v2 ≤ v3 := Finset.min'_le _ _ hv3inE1a
    omega
  have hge3 : ∀ x ∈ E1, x = starMin E1 ∨ x = v2 ∨ v3 ≤ x := by
    intro x hx
    by_cases h1 : x = starMin E1
    · exact Or.inl h1
    · by_cases h2 : x = v2
      · exact Or.inr (Or.inl h2)
      · have hx2 : x ∈ (E1.erase (starMin E1)).erase v2 := by
          rw [Finset.mem_erase]
          exact ⟨h2, Finset.mem_erase.mpr ⟨h1, hx⟩⟩
        exact Or.inr (Or.inr (Finset.min'_le _ _ hx2))
  -- A second edge of `M` with large least element.
  obtain ⟨E2, hE2M, hE2ge⟩ := exists_starMin_ge hM hinf (v2 + v3)
  have hE2spec := starMin_spec (hM.1 hE2M)
  have hstar2 : starMin E2 = E2.card := rfl
  have hE2ne : E2 ≠ E1 := by
    intro h
    rw [h] at hE2ge
    omega
  have hdis12 : Disjoint E1 E2 := hM.2 hE1M hE2M (fun h ↦ hE2ne h.symm)
  -- The three replacement edges, chosen inside `E1 ∪ E2`.
  obtain ⟨S3, hS3sub, hS3card⟩ :=
    Finset.exists_subset_card_eq (s := E2) (n := v3 - 1) (by omega)
  let F3 : Finset ℕ := insert v3 S3
  have hv3notS3 : v3 ∉ S3 := fun h ↦
    Finset.disjoint_left.mp hdis12 hv3inE1 (hS3sub h)
  have hF3card : F3.card = v3 := by
    rw [Finset.card_insert_of_notMem hv3notS3, hS3card]
    omega
  have hF3star : F3 ∈ starEdges := by
    refine ⟨v3, Finset.mem_insert_self _ _, hF3card, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact Nat.le_refl _
    · have := hE2spec.2.2 x (hS3sub hxS)
      omega
  have hF3subU : F3 ⊆ E1 ∪ E2 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact Finset.mem_union_left _ hv3inE1
    · exact Finset.mem_union_right _ (hS3sub hxS)
  obtain ⟨S2, hS2sub, hS2card⟩ :=
    Finset.exists_subset_card_eq (s := E2 \ S3) (n := v2 - 1) (by
      rw [Finset.card_sdiff_of_subset hS3sub, hS3card]
      omega)
  let F2 : Finset ℕ := insert v2 S2
  have hv2notS2 : v2 ∉ S2 := fun h ↦
    Finset.disjoint_left.mp hdis12 hv2inE1 (Finset.mem_sdiff.mp (hS2sub h)).1
  have hF2card : F2.card = v2 := by
    rw [Finset.card_insert_of_notMem hv2notS2, hS2card]
    omega
  have hF2star : F2 ∈ starEdges := by
    refine ⟨v2, Finset.mem_insert_self _ _, hF2card, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact Nat.le_refl _
    · have := hE2spec.2.2 x (Finset.mem_sdiff.mp (hS2sub hxS)).1
      omega
  have hF2subU : F2 ⊆ E1 ∪ E2 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact Finset.mem_union_left _ hv2inE1
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mp (hS2sub hxS)).1
  have hdis23 : Disjoint F2 F3 := by
    rw [Finset.disjoint_left]
    intro x hxF2 hxF3
    rcases Finset.mem_insert.mp hxF2 with rfl | hxS2
    · rcases Finset.mem_insert.mp hxF3 with h | hxS3
      · exact hv3ne2 h.symm
      · exact Finset.disjoint_left.mp hdis12 hv2inE1 (hS3sub hxS3)
    · have hxE2 : x ∈ E2 := (Finset.mem_sdiff.mp (hS2sub hxS2)).1
      rcases Finset.mem_insert.mp hxF3 with rfl | hxS3
      · exact Finset.disjoint_left.mp hdis12 hv3inE1 hxE2
      · exact (Finset.mem_sdiff.mp (hS2sub hxS2)).2 hxS3
  have hF23subU : F2 ∪ F3 ⊆ E1 ∪ E2 := Finset.union_subset hF2subU hF3subU
  have hcardU : (E1 ∪ E2).card = E1.card + E2.card :=
    Finset.card_union_of_disjoint hdis12
  have hcardF23 : (F2 ∪ F3).card = v2 + v3 := by
    rw [Finset.card_union_of_disjoint hdis23, hF2card, hF3card]
  have hv1notF23 : starMin E1 ∉ F2 ∪ F3 := by
    intro h
    rcases Finset.mem_union.mp h with hF2 | hF3
    · rcases Finset.mem_insert.mp hF2 with hEq | hS
      · exact hv2ne hEq.symm
      · exact Finset.disjoint_left.mp hdis12 (starMin_mem (hM.1 hE1M))
          (Finset.mem_sdiff.mp (hS2sub hS)).1
    · rcases Finset.mem_insert.mp hF3 with hEq | hS
      · exact absurd hEq (by omega)
      · exact Finset.disjoint_left.mp hdis12 (starMin_mem (hM.1 hE1M)) (hS3sub hS)
  obtain ⟨S1, hS1sub, hS1card⟩ :=
    Finset.exists_subset_card_eq
      (s := (E1 ∪ E2) \ insert (starMin E1) (F2 ∪ F3)) (n := starMin E1 - 1) (by
      have hsub : insert (starMin E1) (F2 ∪ F3) ⊆ E1 ∪ E2 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxU
        · exact Finset.mem_union_left _ (starMin_mem (hM.1 hE1M))
        · exact hF23subU hxU
      rw [Finset.card_sdiff_of_subset hsub, hcardU, Finset.card_insert_of_notMem hv1notF23,
        hcardF23, hstar1]
      omega)
  let F1 : Finset ℕ := insert (starMin E1) S1
  have hv1notS1 : starMin E1 ∉ S1 := fun h ↦
    (Finset.mem_sdiff.mp (hS1sub h)).2 (Finset.mem_insert_self _ _)
  have hF1card : F1.card = starMin E1 := by
    rw [Finset.card_insert_of_notMem hv1notS1, hS1card]
    have : 1 ≤ starMin E1 := by omega
    omega
  have hF1star : F1 ∈ starEdges := by
    refine ⟨starMin E1, Finset.mem_insert_self _ _, hF1card, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact Nat.le_refl _
    · have hxU := (Finset.mem_sdiff.mp (hS1sub hxS)).1
      rcases Finset.mem_union.mp hxU with hxE1 | hxE2
      · exact hE1spec.2.2 x hxE1
      · have := hE2spec.2.2 x hxE2
        omega
  have hF1subU : F1 ⊆ E1 ∪ E2 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact Finset.mem_union_left _ (starMin_mem (hM.1 hE1M))
    · exact (Finset.mem_sdiff.mp (hS1sub hxS)).1
  have hdisF12 : Disjoint F1 F2 := by
    rw [Finset.disjoint_left]
    intro x hxF1 hxF2
    rcases Finset.mem_insert.mp hxF1 with rfl | hxS1
    · exact hv1notF23 (Finset.mem_union_left _ hxF2)
    · exact (Finset.mem_sdiff.mp (hS1sub hxS1)).2
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ hxF2))
  have hdisF13 : Disjoint F1 F3 := by
    rw [Finset.disjoint_left]
    intro x hxF1 hxF3
    rcases Finset.mem_insert.mp hxF1 with rfl | hxS1
    · exact hv1notF23 (Finset.mem_union_right _ hxF3)
    · exact (Finset.mem_sdiff.mp (hS1sub hxS1)).2
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ hxF3))
  have hv2inF2 : v2 ∈ F2 := Finset.mem_insert_self _ _
  have hv3inF3 : v3 ∈ F3 := Finset.mem_insert_self _ _
  have hv2notF1 : v2 ∉ F1 :=
    Finset.disjoint_left.mp hdisF12.symm hv2inF2
  have hv3notF2 : v3 ∉ F2 :=
    Finset.disjoint_left.mp hdis23.symm hv3inF3
  have hv2notF3 : v2 ∉ F3 := by
    intro h
    rcases Finset.mem_insert.mp h with hEq | hS
    · exact hv3ne2 hEq.symm
    · exact Finset.disjoint_left.mp hdis12 hv2inE1 (hS3sub hS)
  -- The replacement edges are not in `M`: each meets `E1`.
  have hnotMem : ∀ {f : Finset ℕ} {v : ℕ}, f ≠ E1 → v ∈ f → v ∈ E1 → f ∉ M := by
    intro f v hne hmem hvE1 hfm
    exact Finset.disjoint_left.mp (hM.2 hfm hE1M hne) hmem hvE1
  have hF1ne : F1 ≠ E1 := by
    intro hEq
    exact hv2notF1 (hEq ▸ hv2inE1)
  have hF1not : F1 ∉ M :=
    hnotMem hF1ne (Finset.mem_insert_self _ _) (starMin_mem (hM.1 hE1M))
  have hF2ne : F2 ≠ E1 := by
    intro hEq
    obtain ⟨x, hxS2⟩ : (S2).Nonempty := Finset.card_pos.mp (by
      rw [hS2card]; omega)
    have hxE2 : x ∈ E2 := (Finset.mem_sdiff.mp (hS2sub hxS2)).1
    exact Finset.disjoint_left.mp hdis12 (hEq ▸ Finset.mem_insert_of_mem hxS2) hxE2
  have hF2not : F2 ∉ M := hnotMem hF2ne hv2inF2 hv2inE1
  have hF3ne : F3 ≠ E1 := by
    intro hEq
    obtain ⟨x, hxS3⟩ : (S3).Nonempty := Finset.card_pos.mp (by
      rw [hS3card]; omega)
    have hxE2 : x ∈ E2 := hS3sub hxS3
    exact Finset.disjoint_left.mp hdis12 (hEq ▸ Finset.mem_insert_of_mem hxS3) hxE2
  have hF3not : F3 ∉ M := hnotMem hF3ne hv3inF3 hv3inE1
  have hdisU : ∀ {a f : Finset ℕ}, a ∈ M → a ≠ E1 → a ≠ E2 → f ⊆ E1 ∪ E2 →
      Disjoint a f := by
    intro a f ha h1 h2 hsub
    rw [Finset.disjoint_left]
    intro x hxa hxf
    rcases Finset.mem_union.mp (hsub hxf) with hxE1 | hxE2
    · exact Finset.disjoint_left.mp (hM.2 ha hE1M h1) hxa hxE1
    · exact Finset.disjoint_left.mp (hM.2 ha hE2M h2) hxa hxE2
  have hne12 : ∀ {a : Finset ℕ}, a ∉ ({E1, E2} : Set (Finset ℕ)) → a ≠ E1 ∧ a ≠ E2 := by
    intro a ha
    refine ⟨fun h ↦ ha (Set.mem_insert_iff.mpr (Or.inl h)),
      fun h ↦ ha (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h)))⟩
  refine ⟨(M \ {E1, E2}) ∪ {F1, F2, F3}, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e he
    rcases he with heM | heF
    · exact hM.1 heM.1
    · rcases heF with rfl | rfl | rfl
      · exact hF1star
      · exact hF2star
      · exact hF3star
  · intro a ha b hb hab
    rcases ha with ⟨haM, ha12⟩ | haF <;>
      rcases hb with ⟨hbM, hb12⟩ | hbF
    · exact hM.2 haM hbM hab
    · rcases hbF with rfl | rfl | rfl
      · exact hdisU haM (hne12 ha12).1 (hne12 ha12).2 hF1subU
      · exact hdisU haM (hne12 ha12).1 (hne12 ha12).2 hF2subU
      · exact hdisU haM (hne12 ha12).1 (hne12 ha12).2 hF3subU
    · rcases haF with rfl | rfl | rfl
      · exact (hdisU hbM (hne12 hb12).1 (hne12 hb12).2 hF1subU).symm
      · exact (hdisU hbM (hne12 hb12).1 (hne12 hb12).2 hF2subU).symm
      · exact (hdisU hbM (hne12 hb12).1 (hne12 hb12).2 hF3subU).symm
    · rcases haF with rfl | rfl | rfl <;> rcases hbF with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact hdisF12
      · exact hdisF13
      · exact hdisF12.symm
      · exact absurd rfl hab
      · exact hdis23
      · exact hdisF13.symm
      · exact hdis23.symm
      · exact absurd rfl hab
  · apply Set.Finite.subset (s := (({F1, F2, F3} : Finset (Finset ℕ)) : Set (Finset ℕ)))
    · exact Finset.finite_toSet _
    · intro x hx
      rcases hx.1 with heM | heF
      · exact absurd heM.1 hx.2
      · rcases heF with rfl | rfl | rfl <;> simp
  · apply Set.Finite.subset (s := (({E1, E2} : Finset (Finset ℕ)) : Set (Finset ℕ)))
    · exact Finset.finite_toSet _
    · intro x hx
      by_cases h12 : x = E1 ∨ x = E2
      · rcases h12 with rfl | rfl <;> simp
      · exfalso
        exact hx.2 (Set.mem_union_left _ ⟨hx.1, h12⟩)
  · have hMN : M \ ((M \ {E1, E2}) ∪ {F1, F2, F3}) = {E1, E2} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · intro hx
        by_cases h12 : x = E1 ∨ x = E2
        · exact h12
        · exfalso
          exact hx.2 (Or.inl ⟨hx.1, h12⟩)
      · intro hx
        rcases hx with rfl | rfl
        · refine ⟨hE1M, ?_⟩
          rintro (⟨_, hnot⟩ | hF | hF | hF)
          · exact hnot (Or.inl rfl)
          · exact hF1not (hF ▸ hE1M)
          · exact hF2not (hF ▸ hE1M)
          · exact hF3not (hF ▸ hE1M)
        · refine ⟨hE2M, ?_⟩
          rintro (⟨_, hnot⟩ | hF | hF | hF)
          · exact hnot (Or.inr rfl)
          · exact hF1not (hF ▸ hE2M)
          · exact hF2not (hF ▸ hE2M)
          · exact hF3not (hF ▸ hE2M)
    have hNM : ((M \ {E1, E2}) ∪ {F1, F2, F3}) \ M = {F1, F2, F3} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · intro hx
        rcases hx.1 with ⟨hxM, _⟩ | hxF
        · exact absurd hxM hx.2
        · exact hxF
      · intro hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨Or.inr (Or.inl rfl), hF1not⟩
        · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hF2not⟩
        · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hF3not⟩
    rw [hMN, hNM, Set.ncard_pair hE2ne.symm]
    have hF12 : F1 ≠ F2 := fun h ↦ hv2notF1 (h ▸ hv2inF2)
    have hv3notF1 : v3 ∉ F1 := Finset.disjoint_left.mp hdisF13.symm hv3inF3
    have hF13 : F1 ≠ F3 := fun h ↦ hv3notF1 (h ▸ hv3inF3)
    have hF23 : F2 ≠ F3 := fun h ↦ hv3notF2 (h ▸ hv3inF3)
    rw [show ({F1, F2, F3} : Set (Finset ℕ)) = insert F1 {F2, F3} from rfl,
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hF12, hF13⟩) (by simp),
      Set.ncard_pair hF23]
    omega

private theorem star_improvement {M : Set (Finset ℕ)} (hM : IsMatching starEdges M) :
    ∃ N, IsMatching starEdges N ∧ (N \ M).Finite ∧ (M \ N).Finite ∧
      (M \ N).ncard < (N \ M).ncard := by
  by_cases hfin : M.Finite
  · exact star_improvement_of_finite hM hfin
  · exact star_improvement_of_infinite hM hfin


/-- The vertex type of the gadget hypergraph: the original vertices of `ℕ`, together with a
pair of new vertices for every edge `e` of the unbounded hypergraph and every `x ∈ e`. -/
private abbrev GadgetV := ℕ ⊕ (Finset ℕ × ℕ × Bool)

/-- A new gadget vertex: the vertex of sign `b` attached to `x` in the gadget on `e`. -/
private def gadgetVertex (e : Finset ℕ) (x : ℕ) (b : Bool) : GadgetV := Sum.inr (e, x, b)

/-- An outer edge of the gadget on `e` at `x`: the original vertex `x` together with its two
gadget vertices. -/
private def outerEdge (e : Finset ℕ) (x : ℕ) : Finset GadgetV :=
  {Sum.inl x, gadgetVertex e x true, gadgetVertex e x false}

/-- An inner edge of the gadget on `e` between consecutive elements `x < y` of `e`. -/
private def innerEdge (e : Finset ℕ) (x y : ℕ) : Finset GadgetV :=
  {gadgetVertex e x true, gadgetVertex e y false}

/-- `y` is the immediate successor of `x` in `e`. -/
private def isSucc (e : Finset ℕ) (x y : ℕ) : Prop :=
  x ∈ e ∧ y ∈ e ∧ x < y ∧ ∀ z ∈ e, x < z → y ≤ z

/-- The outer edges of the gadget on `e`. -/
private def outerSet (e : Finset ℕ) : Set (Finset GadgetV) :=
  {f | ∃ x ∈ e, f = outerEdge e x}

/-- The inner edges of the gadget on `e`. -/
private def innerSet (e : Finset ℕ) : Set (Finset GadgetV) :=
  {f | ∃ x y, isSucc e x y ∧ f = innerEdge e x y}

/-- All edges of the gadget on `e`. -/
private def gadgetEdges (e : Finset ℕ) : Set (Finset GadgetV) :=
  outerSet e ∪ innerSet e

/-- The edge set of the gadget hypergraph: the union of the gadgets on all edges of
`starEdges`. -/
private def gadgetEdgeSet : Set (Finset GadgetV) :=
  ⋃ e ∈ starEdges, gadgetEdges e

private theorem gadgetVertex_inj {e e' : Finset ℕ} {x x' : ℕ} {b b' : Bool}
    (h : gadgetVertex e x b = gadgetVertex e' x' b') : e = e' ∧ x = x' ∧ b = b' := by
  simp only [gadgetVertex, Sum.inr.injEq, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

private theorem gadgetVertex_ne_inl {e : Finset ℕ} {x v : ℕ} {b : Bool} :
    gadgetVertex e x b ≠ Sum.inl v := by
  simp [gadgetVertex]

private theorem outerEdge_card_le (e : Finset ℕ) (x : ℕ) : (outerEdge e x).card ≤ 3 := by
  have h2 : ({gadgetVertex e x true, gadgetVertex e x false} : Finset GadgetV).card ≤ 2 := by
    calc ({gadgetVertex e x true, gadgetVertex e x false} : Finset GadgetV).card
        ≤ ({gadgetVertex e x true} : Finset GadgetV).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  calc (outerEdge e x).card
      ≤ ({gadgetVertex e x true, gadgetVertex e x false} : Finset GadgetV).card + 1 := by
        rw [outerEdge]; exact Finset.card_insert_le _ _
    _ ≤ 3 := by omega

private theorem innerEdge_card_le (e : Finset ℕ) (x y : ℕ) : (innerEdge e x y).card ≤ 3 := by
  rw [innerEdge]
  calc ({gadgetVertex e x true, gadgetVertex e y false} : Finset GadgetV).card
      ≤ ({gadgetVertex e x true} : Finset GadgetV).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp
    _ ≤ 3 := by omega

private theorem gadgetEdges_finite (e : Finset ℕ) : (gadgetEdges e).Finite := by
  apply Set.Finite.subset (s := ((e.image (outerEdge e) ∪
    (e ×ˢ e).image (fun p ↦ innerEdge e p.1 p.2) : Finset (Finset GadgetV)) : Set _))
  · exact Finset.finite_toSet _
  · intro f hf
    rcases hf with ⟨x, hx, rfl⟩ | ⟨x, y, ⟨hx, hy, _, _⟩, rfl⟩
    · exact Finset.mem_coe.mpr (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    · exact Finset.mem_coe.mpr (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩))

private theorem outer_mem_gadget {e : Finset ℕ} {x : ℕ} (hx : x ∈ e) :
    outerEdge e x ∈ gadgetEdges e :=
  Set.mem_union_left _ ⟨x, hx, rfl⟩

private theorem inner_mem_gadget {e : Finset ℕ} {x y : ℕ} (h : isSucc e x y) :
    innerEdge e x y ∈ gadgetEdges e :=
  Set.mem_union_right _ ⟨x, y, h, rfl⟩

private theorem outer_subset_gadget {e : Finset ℕ} : outerSet e ⊆ gadgetEdges e :=
  fun _ hf ↦ Set.mem_union_left _ hf

private theorem inner_subset_gadget {e : Finset ℕ} : innerSet e ⊆ gadgetEdges e :=
  fun _ hf ↦ Set.mem_union_right _ hf

private theorem gadget_mem_edgeSet {e : Finset ℕ} (he : e ∈ starEdges)
    {f : Finset GadgetV} (hf : f ∈ gadgetEdges e) : f ∈ gadgetEdgeSet :=
  Set.mem_biUnion he hf

/-- An edge of one gadget that contains a gadget vertex of another gadget determines the
gadget. -/
private theorem gadget_of_vertex {e e' : Finset ℕ} {f : Finset GadgetV}
    (hf : f ∈ gadgetEdges e') {x : ℕ} {b : Bool} (hv : gadgetVertex e x b ∈ f) : e = e' := by
  rcases hf with ⟨x', hx', rfl⟩ | ⟨x', y', _, rfl⟩
  · simp only [outerEdge, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv
    · exact absurd hv gadgetVertex_ne_inl
    · exact (gadgetVertex_inj hv).1
    · exact (gadgetVertex_inj hv).1
  · simp only [innerEdge, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · exact (gadgetVertex_inj hv).1
    · exact (gadgetVertex_inj hv).1

/-- Distinct gadgets have disjoint edge sets. -/
private theorem gadgetEdges_disjoint {e e' : Finset ℕ} (hne : e ≠ e') :
    Disjoint (gadgetEdges e) (gadgetEdges e') := by
  rw [Set.disjoint_left]
  rintro f hf hf'
  rcases hf with ⟨x, hx, rfl⟩ | ⟨x, y, ⟨hx, _, _, _⟩, rfl⟩
  · exact hne (gadget_of_vertex hf'
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  · exact hne (gadget_of_vertex hf' (Finset.mem_insert_self _ _))

/-- If an edge of a gadget contains an original vertex, it is the outer edge at that
vertex. -/
private theorem inl_mem_gadget {e : Finset ℕ} {f : Finset GadgetV} {w : ℕ}
    (hf : f ∈ gadgetEdges e) (hw : Sum.inl w ∈ f) : f = outerEdge e w ∧ w ∈ e := by
  rcases hf with ⟨x, hx, rfl⟩ | ⟨x, y, ⟨hx, hy, hxy, _⟩, rfl⟩
  · simp only [outerEdge, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw
    · rw [Sum.inl.injEq] at hw; exact ⟨by rw [hw], hw ▸ hx⟩
    · exact absurd hw (by simp [gadgetVertex])
    · exact absurd hw (by simp [gadgetVertex])
  · simp only [innerEdge, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw <;> exact absurd hw (by simp [gadgetVertex])


/-- Every gadget edge contains exactly one `+` vertex, with a unique index in `e`. -/
private theorem plus_exists {e : Finset ℕ} {f : Finset GadgetV} (hf : f ∈ gadgetEdges e) :
    ∃ x ∈ e, gadgetVertex e x true ∈ f ∧ ∀ x' ∈ e, gadgetVertex e x' true ∈ f → x' = x := by
  rcases hf with ⟨x, hx, rfl⟩ | ⟨x, y, ⟨hx, hy, _, _⟩, rfl⟩
  · refine ⟨x, hx, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
    intro x' _ hmem
    simp only [outerEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact absurd h (by simp [gadgetVertex])
    · exact (gadgetVertex_inj h).2.1
    · exact absurd (gadgetVertex_inj h).2.2 (by simp)
  · refine ⟨x, hx, Finset.mem_insert_self _ _, ?_⟩
    intro x' _ hmem
    simp only [innerEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact (gadgetVertex_inj h).2.1
    · exact absurd (gadgetVertex_inj h).2.2 (by simp)

/-- Every gadget edge contains exactly one `-` vertex, with a unique index in `e`. -/
private theorem minus_exists {e : Finset ℕ} {f : Finset GadgetV} (hf : f ∈ gadgetEdges e) :
    ∃ x ∈ e, gadgetVertex e x false ∈ f ∧ ∀ x' ∈ e, gadgetVertex e x' false ∈ f → x' = x := by
  rcases hf with ⟨x, hx, rfl⟩ | ⟨x, y, ⟨hx, hy, _, _⟩, rfl⟩
  · refine ⟨x, hx, Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
    intro x' _ hmem
    simp only [outerEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact absurd h (by simp [gadgetVertex])
    · exact absurd (gadgetVertex_inj h).2.2 (by simp)
    · exact (gadgetVertex_inj h).2.1
  · refine ⟨y, hy, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
    intro x' _ hmem
    simp only [innerEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact absurd (gadgetVertex_inj h).2.2 (by simp)
    · exact (gadgetVertex_inj h).2.1

/-- The index of the `+` vertex of a gadget edge. -/
private noncomputable def plusIdx (e : Finset ℕ) (f : Finset GadgetV) : ℕ :=
  if h : ∃ x ∈ e, gadgetVertex e x true ∈ f then Classical.choose h else 0

/-- The index of the `-` vertex of a gadget edge. -/
private noncomputable def minusIdx (e : Finset ℕ) (f : Finset GadgetV) : ℕ :=
  if h : ∃ x ∈ e, gadgetVertex e x false ∈ f then Classical.choose h else 0

private theorem plusIdx_spec {e : Finset ℕ} {f : Finset GadgetV} (hf : f ∈ gadgetEdges e) :
    plusIdx e f ∈ e ∧ gadgetVertex e (plusIdx e f) true ∈ f ∧
      ∀ x' ∈ e, gadgetVertex e x' true ∈ f → x' = plusIdx e f := by
  obtain ⟨x, hx, hmem, huniq⟩ := plus_exists hf
  have hex : ∃ x ∈ e, gadgetVertex e x true ∈ f := ⟨x, hx, hmem⟩
  have hdef : plusIdx e f = Classical.choose hex := dite_eq_left hex
  have hspec := Classical.choose_spec hex
  rw [hdef]
  refine ⟨hspec.1, hspec.2, fun x' hx' hmem' ↦ ?_⟩
  exact (huniq x' hx' hmem').trans (huniq _ hspec.1 hspec.2).symm

private theorem minusIdx_spec {e : Finset ℕ} {f : Finset GadgetV} (hf : f ∈ gadgetEdges e) :
    minusIdx e f ∈ e ∧ gadgetVertex e (minusIdx e f) false ∈ f ∧
      ∀ x' ∈ e, gadgetVertex e x' false ∈ f → x' = minusIdx e f := by
  obtain ⟨x, hx, hmem, huniq⟩ := minus_exists hf
  have hex : ∃ x ∈ e, gadgetVertex e x false ∈ f := ⟨x, hx, hmem⟩
  have hdef : minusIdx e f = Classical.choose hex := dite_eq_left hex
  have hspec := Classical.choose_spec hex
  rw [hdef]
  refine ⟨hspec.1, hspec.2, fun x' hx' hmem' ↦ ?_⟩
  exact (huniq x' hx' hmem').trans (huniq _ hspec.1 hspec.2).symm

/-- The `+` and `-` indices of an edge of a gadget are ordered, and are either equal (an
outer edge) or consecutive (an inner edge). -/
private theorem plus_le_minus_or_succ {e : Finset ℕ} {f : Finset GadgetV}
    (hf : f ∈ gadgetEdges e) :
    plusIdx e f ≤ minusIdx e f ∧
      (plusIdx e f = minusIdx e f ∨ isSucc e (plusIdx e f) (minusIdx e f)) := by
  have hp := plusIdx_spec hf
  have hm := minusIdx_spec hf
  rcases hf with ⟨x, hx, rfl⟩ | ⟨x, y, hsucc, rfl⟩
  · have hplus : plusIdx e (outerEdge e x) = x :=
      (hp.2.2 x hx (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))).symm
    have hminus : minusIdx e (outerEdge e x) = x :=
      (hm.2.2 x hx (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))).symm
    rw [hplus, hminus]
    exact ⟨Nat.le_refl _, Or.inl rfl⟩
  · have hplus : plusIdx e (innerEdge e x y) = x :=
      (hp.2.2 x hsucc.1 (Finset.mem_insert_self _ _)).symm
    have hminus : minusIdx e (innerEdge e x y) = y :=
      (hm.2.2 y hsucc.2.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).symm
    rw [hplus, hminus]
    exact ⟨hsucc.2.2.1.le, Or.inr hsucc⟩


private theorem plusIdx_injOn {e : Finset ℕ} {A : Set (Finset GadgetV)}
    (hA : A ⊆ gadgetEdges e) (hpair : A.Pairwise Disjoint) :
    Set.InjOn (plusIdx e) A := by
  intro f hf g hg hfg
  by_contra hne
  have hdis := hpair hf hg hne
  have hmemf := (plusIdx_spec (hA hf)).2.1
  have hmemg := (plusIdx_spec (hA hg)).2.1
  rw [← hfg] at hmemg
  exact Finset.disjoint_left.mp hdis hmemf hmemg

private theorem minusIdx_injOn {e : Finset ℕ} {A : Set (Finset GadgetV)}
    (hA : A ⊆ gadgetEdges e) (hpair : A.Pairwise Disjoint) :
    Set.InjOn (minusIdx e) A := by
  intro f hf g hg hfg
  by_contra hne
  have hdis := hpair hf hg hne
  have hmemf := (minusIdx_spec (hA hf)).2.1
  have hmemg := (minusIdx_spec (hA hg)).2.1
  rw [← hfg] at hmemg
  exact Finset.disjoint_left.mp hdis hmemf hmemg

private theorem succ_right_unique {e : Finset ℕ} {x y y' : ℕ}
    (h1 : isSucc e x y) (h2 : isSucc e x y') : y = y' :=
  le_antisymm (h1.2.2.2 y' h2.2.1 h2.2.2.1) (h2.2.2.2 y h1.2.1 h1.2.2.1)

private theorem succ_left_unique {e : Finset ℕ} {x x' y : ℕ}
    (h1 : isSucc e x y) (h2 : isSucc e x' y) : x = x' := by
  rcases lt_trichotomy x x' with h | h | h
  · have hy : y ≤ x' := h1.2.2.2 x' h2.1 h
    have hx'y : x' < y := h2.2.2.1
    omega
  · exact h
  · have hy : y ≤ x := h2.2.2.2 x h1.1 h
    have hxy : x < y := h1.2.2.1
    omega

private theorem inner_disjoint {e : Finset ℕ} {f g : Finset GadgetV}
    (hf : f ∈ innerSet e) (hg : g ∈ innerSet e) (hne : f ≠ g) : Disjoint f g := by
  obtain ⟨x, y, hsucc, rfl⟩ := hf
  obtain ⟨x', y', hsucc', rfl⟩ := hg
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  simp only [innerEdge, Finset.mem_insert, Finset.mem_singleton] at hv1 hv2
  rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
  · have heq := h1.symm.trans h2
    have hxx : x = x' := (gadgetVertex_inj heq).2.1
    have hyy : y = y' := succ_right_unique hsucc (hxx ▸ hsucc')
    exact hne (by rw [hxx, hyy])
  · have heq := h1.symm.trans h2
    exact absurd (gadgetVertex_inj heq).2.2 (by simp)
  · have heq := h1.symm.trans h2
    exact absurd (gadgetVertex_inj heq).2.2 (by simp)
  · have heq := h1.symm.trans h2
    have hyy : y = y' := (gadgetVertex_inj heq).2.1
    have hxx : x = x' := succ_left_unique hsucc (hyy ▸ hsucc')
    exact hne (by rw [hxx, hyy])

private theorem outer_disjoint {e : Finset ℕ} {f g : Finset GadgetV}
    (hf : f ∈ outerSet e) (hg : g ∈ outerSet e) (hne : f ≠ g) : Disjoint f g := by
  obtain ⟨x, hx, rfl⟩ := hf
  obtain ⟨y, hy, rfl⟩ := hg
  have hxy : x ≠ y := fun h ↦ hne (by rw [h])
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  simp only [outerEdge, Finset.mem_insert, Finset.mem_singleton] at hv1 hv2
  rcases hv1 with h1 | h1 | h1 <;> rcases hv2 with h2 | h2 | h2 <;>
    (have heq := h1.symm.trans h2; simp_all [gadgetVertex])

private theorem inner_outer_disjoint (e : Finset ℕ) :
    Disjoint (innerSet e) (outerSet e) := by
  rw [Set.disjoint_left]
  rintro f hf hg
  obtain ⟨x, y, hsucc, rfl⟩ := hf
  obtain ⟨w, hw, heq⟩ := hg
  have hmem : Sum.inl w ∈ innerEdge e x y := by
    rw [heq]
    exact Finset.mem_insert_self _ _
  simp only [innerEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h <;> exact absurd h (by simp [gadgetVertex])

private theorem outerSet_ncard (e : Finset ℕ) : (outerSet e).ncard = e.card := by
  have himg : outerSet e = outerEdge e '' (e : Set ℕ) := by
    ext f
    simp only [outerSet, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  have hinj : Set.InjOn (outerEdge e) (e : Set ℕ) := by
    intro x _ y _ h
    have hmem : Sum.inl x ∈ outerEdge e y := h ▸ Finset.mem_insert_self _ _
    simp only [outerEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · exact Sum.inl.inj h1
    · exact absurd h1 (by simp [gadgetVertex])
    · exact absurd h1 (by simp [gadgetVertex])
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset]

private theorem exists_pred {e : Finset ℕ} (he : e ∈ starEdges) {y : ℕ} (hy : y ∈ e)
    (hyne : y ≠ starMin e) : ∃ x, isSucc e x y := by
  have hylt : starMin e < y :=
    lt_of_le_of_ne ((starMin_spec he).2.2 y hy) (Ne.symm hyne)
  let S := e.filter (· < y)
  have hSne : S.Nonempty :=
    ⟨starMin e, Finset.mem_filter.mpr ⟨starMin_mem he, hylt⟩⟩
  have hmax := Finset.mem_filter.mp (Finset.max'_mem S hSne)
  refine ⟨S.max' hSne, hmax.1, hy, hmax.2, ?_⟩
  intro z hz hxz
  by_contra hzy
  have hzy' : z < y := lt_of_not_ge hzy
  have hzS : z ∈ S := Finset.mem_filter.mpr ⟨hz, hzy'⟩
  have hle : z ≤ S.max' hSne := Finset.le_max' _ _ hzS
  omega

private theorem innerSet_ncard_le {e : Finset ℕ} (he : e ∈ starEdges) :
    (innerSet e).ncard ≤ e.card - 1 := by
  have hpair : (innerSet e).Pairwise Disjoint :=
    fun _ hf _ hg hne ↦ inner_disjoint hf hg hne
  have hle := Set.ncard_le_ncard_of_injOn (f := minusIdx e) (s := innerSet e)
    (t := ((e.erase (starMin e) : Finset ℕ) : Set ℕ)) (fun f hf ↦ ?_)
    (minusIdx_injOn inner_subset_gadget hpair) (Finset.finite_toSet _)
  · rw [Set.ncard_coe_finset, Finset.card_erase_of_mem (starMin_mem he)] at hle
    exact hle
  · obtain ⟨x, y, hsucc, rfl⟩ := hf
    have hminus : minusIdx e (innerEdge e x y) = y :=
      ((minusIdx_spec (inner_mem_gadget hsucc)).2.2 y hsucc.2.1
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).symm
    rw [hminus]
    have hle1 : starMin e ≤ x := (starMin_spec he).2.2 x hsucc.1
    have hxy : x < y := hsucc.2.2.1
    refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨by omega, hsucc.2.1⟩)

private theorem innerSet_ncard_ge {e : Finset ℕ} (he : e ∈ starEdges) :
    e.card - 1 ≤ (innerSet e).ncard := by
  classical
  let pred : ℕ → ℕ := fun y ↦
    if h : ∃ x, isSucc e x y then Classical.choose h else 0
  have pred_spec : ∀ y ∈ (e.erase (starMin e) : Finset ℕ), isSucc e (pred y) y := by
    intro y hy
    have hyE : y ∈ e := (Finset.mem_erase.mp hy).2
    have hyne : y ≠ starMin e := (Finset.mem_erase.mp hy).1
    have hex := exists_pred he hyE hyne
    have hdef : pred y = Classical.choose hex := by
      change (if h : ∃ x, isSucc e x y then Classical.choose h else 0) = Classical.choose hex
      exact dite_eq_left hex
    rw [hdef]
    exact Classical.choose_spec hex
  have hinj : Set.InjOn (fun y ↦ innerEdge e (pred y) y)
      ((e.erase (starMin e) : Finset ℕ) : Set ℕ) := by
    intro y1 hy1 y2 hy2 heq
    have h1 : innerEdge e (pred y1) y1 ∈ innerSet e :=
      ⟨pred y1, y1, pred_spec y1 hy1, rfl⟩
    have h2 : innerEdge e (pred y2) y2 ∈ innerSet e :=
      ⟨pred y2, y2, pred_spec y2 hy2, rfl⟩
    have hm1 := minusIdx_spec (inner_subset_gadget h1)
    have hm2 := minusIdx_spec (inner_subset_gadget h2)
    have e1 : minusIdx e (innerEdge e (pred y1) y1) = y1 :=
      ((hm1.2.2 y1 (pred_spec y1 hy1).2.1
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).symm)
    have e2 : minusIdx e (innerEdge e (pred y2) y2) = y2 :=
      ((hm2.2.2 y2 (pred_spec y2 hy2).2.1
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).symm)
    have heq' : innerEdge e (pred y1) y1 = innerEdge e (pred y2) y2 := heq
    rw [heq'] at e1
    exact (e2.symm.trans e1).symm
  have hle := Set.ncard_le_ncard_of_injOn (f := fun y ↦ innerEdge e (pred y) y)
    (s := ((e.erase (starMin e) : Finset ℕ) : Set ℕ)) (t := innerSet e)
    (fun y _ ↦ ⟨pred y, y, pred_spec y ‹y ∈ ↑(e.erase (starMin e))›, rfl⟩) hinj
    ((gadgetEdges_finite e).subset inner_subset_gadget)
  rw [Set.ncard_coe_finset, Finset.card_erase_of_mem (starMin_mem he)] at hle
  exact hle

private theorem innerSet_ncard {e : Finset ℕ} (he : e ∈ starEdges) :
    (innerSet e).ncard = e.card - 1 :=
  le_antisymm (innerSet_ncard_le he) (innerSet_ncard_ge he)


private theorem gadget_size_le {e : Finset ℕ} {A : Set (Finset GadgetV)}
    (hA : A ⊆ gadgetEdges e) (hpair : A.Pairwise Disjoint) :
    A.ncard ≤ e.card := by
  have hle := Set.ncard_le_ncard_of_injOn (f := plusIdx e) (s := A) (t := (e : Set ℕ))
    (fun f hf ↦ Finset.mem_coe.mpr (plusIdx_spec (hA hf)).1)
    (plusIdx_injOn hA hpair) (Finset.finite_toSet e)
  rwa [Set.ncard_coe_finset] at hle

private theorem gadget_classify {e : Finset ℕ} {A : Set (Finset GadgetV)}
    (hA : A ⊆ gadgetEdges e) (hpair : A.Pairwise Disjoint)
    (hcard : A.ncard = e.card) : A = outerSet e := by
  have hsub : A ⊆ outerSet e := by
    intro f hfA
    by_contra hfout
    rcases hA hfA with hfO | hfI
    · exact hfout hfO
    · obtain ⟨x, y, hsucc, rfl⟩ := hfI
      have hxy : x < y := hsucc.2.2.1
      set I : Finset GadgetV := innerEdge e x y with hIdef
      have hfI : I ∈ A := hfA
      -- The rest of `A` injects into `e` with `x` and `y` removed.
      have hgt_of_not : ∀ g ∈ A \ {I}, ¬ plusIdx e g < x → y < minusIdx e g := by
        intro g hg hnot
        have hgA : g ∈ A := hg.1
        have hgne : g ≠ I := fun h ↦ hg.2 (Set.mem_singleton_iff.mpr h)
        have hp := plusIdx_spec (hA hgA)
        have hm := minusIdx_spec (hA hgA)
        have hord := plus_le_minus_or_succ (hA hgA)
        have hne : plusIdx e g ≠ x := by
          intro hEq
          have hdis := hpair hgA hfI hgne
          have hmemg : gadgetVertex e x true ∈ g := hEq ▸ hp.2.1
          have hmemI : gadgetVertex e x true ∈ I := Finset.mem_insert_self _ _
          exact Finset.disjoint_left.mp hdis hmemg hmemI
        have hgt : x < minusIdx e g := by
          have hle1 : plusIdx e g ≤ minusIdx e g := hord.1
          have hgtx : x < plusIdx e g := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)
          omega
        have hle2 : y ≤ minusIdx e g := hsucc.2.2.2 _ hm.1 hgt
        have hney : minusIdx e g ≠ y := by
          intro hEq
          have hdis := hpair hgA hfI hgne
          have hmemg : gadgetVertex e y false ∈ g := hEq ▸ hm.2.1
          have hmemI : gadgetVertex e y false ∈ I :=
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          exact Finset.disjoint_left.mp hdis hmemg hmemI
        omega
      let ψ : Finset GadgetV → ℕ := fun g ↦
        if plusIdx e g < x then plusIdx e g else minusIdx e g
      have hmaps : ∀ g ∈ A \ {I}, ψ g ∈ ((e.erase x).erase y : Finset ℕ) := by
        intro g hg
        have hgA : g ∈ A := hg.1
        have hp := plusIdx_spec (hA hgA)
        have hm := minusIdx_spec (hA hgA)
        by_cases hlt : plusIdx e g < x
        · have hψ : ψ g = plusIdx e g := dite_eq_left hlt
          rw [hψ]
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hp.1⟩⟩
          · omega
          · omega
        · have hψ : ψ g = minusIdx e g := dite_eq_right hlt
          have hgt := hgt_of_not g hg hlt
          rw [hψ]
          refine Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega, hm.1⟩⟩
      have hinj : Set.InjOn ψ (A \ {I}) := by
        intro g1 hg1 g2 hg2 heq
        by_cases h1 : plusIdx e g1 < x
        · by_cases h2 : plusIdx e g2 < x
          · have e1 : ψ g1 = plusIdx e g1 := dite_eq_left h1
            have e2 : ψ g2 = plusIdx e g2 := dite_eq_left h2
            rw [e1, e2] at heq
            exact plusIdx_injOn hA hpair hg1.1 hg2.1 heq
          · have e1 : ψ g1 = plusIdx e g1 := dite_eq_left h1
            have e2 : ψ g2 = minusIdx e g2 := dite_eq_right h2
            have hgt := hgt_of_not g2 hg2 h2
            rw [e1, e2] at heq
            omega
        · by_cases h2 : plusIdx e g2 < x
          · have e1 : ψ g1 = minusIdx e g1 := dite_eq_right h1
            have e2 : ψ g2 = plusIdx e g2 := dite_eq_left h2
            have hgt := hgt_of_not g1 hg1 h1
            rw [e1, e2] at heq
            omega
          · have e1 : ψ g1 = minusIdx e g1 := dite_eq_right h1
            have e2 : ψ g2 = minusIdx e g2 := dite_eq_right h2
            rw [e1, e2] at heq
            exact minusIdx_injOn hA hpair hg1.1 hg2.1 heq
      have hcount := Set.ncard_le_ncard_of_injOn (f := ψ) (s := A \ {I})
        (t := (((e.erase x).erase y : Finset ℕ) : Set ℕ)) (fun g hg ↦
          Finset.mem_coe.mpr (hmaps g hg)) hinj (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at hcount
      have hEcard : ((e.erase x).erase y).card = e.card - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr
          ⟨by omega, hsucc.2.1⟩), Finset.card_erase_of_mem hsucc.1]
        omega
      have hAfin : A.Finite := (gadgetEdges_finite e).subset hA
      have hTfin : (A \ {I}).Finite := hAfin.sdiff
      have hnotmem : I ∉ A \ {I} := fun h ↦ h.2 (Set.mem_singleton_iff.mpr rfl)
      have hAeq : insert I (A \ {I}) = A := by
        ext g
        simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
        constructor
        · rintro (rfl | ⟨hgA, -⟩) <;> assumption
        · intro hgA
          by_cases hgi : g = I
          · exact Or.inl hgi
          · exact Or.inr ⟨hgA, hgi⟩
      have hAT : A.ncard = (A \ {I}).ncard + 1 := by
        conv_lhs => rw [← hAeq]
        rw [Set.ncard_insert_of_notMem hnotmem hTfin]
      have hcard2 : 2 ≤ e.card := by
        have hsub2 : ({x, y} : Finset ℕ) ⊆ e := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hsucc.1
          · exact hsucc.2.1
        have h2 : ({x, y} : Finset ℕ).card = 2 := by
          rw [Finset.card_insert_of_notMem
              (fun h ↦ hxy.ne (Finset.mem_singleton.mp h)), Finset.card_singleton]
        have hle := Finset.card_le_card hsub2
        omega
      omega
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [outerSet_ncard, hcard])
    ((gadgetEdges_finite e).subset outer_subset_gadget)


private theorem ncard_le_of_cardinal_le {s t : Set (Finset GadgetV)}
    (hs : s.Finite) (ht : t.Finite) (h : Cardinal.mk ↥s ≤ Cardinal.mk ↥t) :
    s.ncard ≤ t.ncard := by
  have e1 : (s.ncard : Cardinal) = Cardinal.mk ↥s := Set.cast_ncard hs
  have e2 : (t.ncard : Cardinal) = Cardinal.mk ↥t := Set.cast_ncard ht
  rw [← e1, ← e2] at h
  exact_mod_cast h

/-- An edge of the gadget hypergraph containing a gadget vertex of the gadget on `e`,
which is not an outer edge of that gadget, is an inner edge of it. -/
private theorem mem_inner_of_gadgetVertex {e : Finset ℕ} {a : Finset GadgetV}
    (ha : a ∈ gadgetEdgeSet) {x : ℕ} {b : Bool} (hv : gadgetVertex e x b ∈ a)
    (hao : a ∉ outerSet e) : a ∈ innerSet e := by
  obtain ⟨e', he', hae'⟩ := Set.mem_iUnion₂.mp ha
  have heq : e = e' := gadget_of_vertex hae' hv
  subst heq
  rcases hae' with haO | haI
  · exact absurd haO hao
  · exact haI

/-- If `M` is strongly maximal, every gadget contributes at least `|e| - 1` edges: otherwise
the inner edges improve it. -/
private theorem gadget_lower {M : Set (Finset GadgetV)}
    (hM : IsStronglyMaximal gadgetEdgeSet M) {e : Finset ℕ} (he : e ∈ starEdges) :
    e.card - 1 ≤ (M ∩ gadgetEdges e).ncard := by
  by_contra hlt
  push Not at hlt
  set N : Set (Finset GadgetV) := (M \ outerSet e) ∪ innerSet e with hNdef
  have hNsub : N ⊆ gadgetEdgeSet := by
    intro f hf
    rcases hf with hfM | hfI
    · exact hM.1.1 hfM.1
    · exact gadget_mem_edgeSet he (inner_subset_gadget hfI)
  have hNpair : N.Pairwise Disjoint := by
    intro a ha b hb hab
    rcases ha with ⟨haM, haO⟩ | haI <;> rcases hb with ⟨hbM, hbO⟩ | hbI
    · exact hM.1.2 haM hbM hab
    · rw [Finset.disjoint_left]
      intro v hva hvb
      obtain ⟨x, y, hsucc, rfl⟩ := hbI
      simp only [innerEdge, Finset.mem_insert, Finset.mem_singleton] at hvb
      rcases hvb with hv | hv
      · rw [hv] at hva
        exact Finset.disjoint_left.mp (inner_disjoint
          (mem_inner_of_gadgetVertex (hM.1.1 haM) hva haO) ⟨x, y, hsucc, rfl⟩ hab)
          hva (Finset.mem_insert_self _ _)
      · rw [hv] at hva
        exact Finset.disjoint_left.mp (inner_disjoint
          (mem_inner_of_gadgetVertex (hM.1.1 haM) hva haO) ⟨x, y, hsucc, rfl⟩ hab)
          hva (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · rw [Finset.disjoint_left]
      intro v hva hvb
      obtain ⟨x, y, hsucc, rfl⟩ := haI
      simp only [innerEdge, Finset.mem_insert, Finset.mem_singleton] at hva
      rcases hva with hv | hv
      · rw [hv] at hvb
        exact Finset.disjoint_left.mp (inner_disjoint ⟨x, y, hsucc, rfl⟩
          (mem_inner_of_gadgetVertex (hM.1.1 hbM) hvb hbO) hab)
          (Finset.mem_insert_self _ _) hvb
      · rw [hv] at hvb
        exact Finset.disjoint_left.mp (inner_disjoint ⟨x, y, hsucc, rfl⟩
          (mem_inner_of_gadgetVertex (hM.1.1 hbM) hvb hbO) hab)
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hvb
    · exact inner_disjoint haI hbI hab
  have hNM : N \ M = innerSet e \ M := by
    ext f
    constructor
    · intro hf
      rcases hf.1 with hfM | hfI
      · exact absurd hfM.1 hf.2
      · exact ⟨hfI, hf.2⟩
    · intro hf
      exact ⟨Or.inr hf.1, hf.2⟩
  have hMN : M \ N = M ∩ outerSet e := by
    ext f
    constructor
    · intro hf
      refine ⟨hf.1, ?_⟩
      by_contra hfO
      exact hf.2 (Or.inl ⟨hf.1, hfO⟩)
    · intro hf
      refine ⟨hf.1, ?_⟩
      rintro (hfM | hfI)
      · exact hfM.2 hf.2
      · exact Set.disjoint_left.mp (inner_outer_disjoint e) hfI hf.2
  have hsplit : (M ∩ gadgetEdges e).ncard =
      (M ∩ innerSet e).ncard + (M ∩ outerSet e).ncard := by
    have hunion : M ∩ gadgetEdges e = (M ∩ innerSet e) ∪ (M ∩ outerSet e) := by
      ext f
      simp only [Set.mem_inter_iff, Set.mem_union, gadgetEdges]
      constructor
      · rintro ⟨hfM, hfO | hfI⟩
        · exact Or.inr ⟨hfM, hfO⟩
        · exact Or.inl ⟨hfM, hfI⟩
      · rintro (⟨hfM, hfI⟩ | ⟨hfM, hfO⟩)
        · exact ⟨hfM, Or.inr hfI⟩
        · exact ⟨hfM, Or.inl hfO⟩
    have hdisj : Disjoint (M ∩ innerSet e) (M ∩ outerSet e) :=
      Set.disjoint_left.mpr fun f hf1 hf2 ↦
        Set.disjoint_left.mp (inner_outer_disjoint e) hf1.2 hf2.2
    have hfin1 : (M ∩ innerSet e).Finite :=
      (gadgetEdges_finite e).subset (fun f hf ↦ inner_subset_gadget hf.2)
    have hfin2 : (M ∩ outerSet e).Finite :=
      (gadgetEdges_finite e).subset (fun f hf ↦ outer_subset_gadget hf.2)
    rw [hunion]
    exact Set.ncard_union_eq hdisj hfin1 hfin2
  have hinner : (innerSet e).ncard = e.card - 1 := innerSet_ncard he
  have hsdiff : (innerSet e \ M).ncard =
      (innerSet e).ncard - (M ∩ innerSet e).ncard := by
    have heq : innerSet e \ M = innerSet e \ (M ∩ innerSet e) := by
      ext f
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h ↦ h2 h.1⟩
      · rintro ⟨h1, h⟩
        exact ⟨h1, fun hm ↦ h ⟨hm, h1⟩⟩
    rw [heq, Set.ncard_sdiff Set.inter_subset_right
      ((gadgetEdges_finite e).subset (fun f hf ↦ inner_subset_gadget hf.2))]
  have hNfin : (N \ M).Finite :=
    ((gadgetEdges_finite e).subset inner_subset_gadget).subset (by
      intro f hf
      rw [hNM] at hf
      exact hf.1)
  have hMfin : (M \ N).Finite :=
    ((gadgetEdges_finite e).subset outer_subset_gadget).subset (by
      intro f hf
      rw [hMN] at hf
      exact hf.2)
  have hle := ncard_le_of_cardinal_le hNfin hMfin (hM.2 N ⟨hNsub, hNpair⟩)
  rw [hNM, hMN, hsdiff, hinner] at hle
  have ha_le : (M ∩ innerSet e).ncard ≤ (innerSet e).ncard :=
    Set.ncard_le_ncard Set.inter_subset_right
      ((gadgetEdges_finite e).subset inner_subset_gadget)
  omega


private theorem exists_gadget_of_mem {f : Finset GadgetV} (hf : f ∈ gadgetEdgeSet) :
    ∃ e ∈ starEdges, f ∈ gadgetEdges e := by
  obtain ⟨e, he, hf⟩ := Set.mem_iUnion₂.mp hf
  exact ⟨e, he, hf⟩

/-- The choice of gadget edges for `e` in the proof that the gadget hypergraph has no
strongly maximal matching: the outer edges for edges gained by the improved matching of
`starEdges`, the inner edges for edges lost or affected by it, and the old matching's edges
elsewhere. -/
private noncomputable def choiceSet (M : Set (Finset GadgetV)) (Mstar Nstar Aff : Set (Finset ℕ))
    (e : Finset ℕ) : Set (Finset GadgetV) := by
  classical
  exact if e ∈ Nstar \ Mstar then outerSet e
    else if e ∈ Mstar \ Nstar then innerSet e
    else if e ∈ Aff then innerSet e
    else M ∩ gadgetEdges e

private theorem choiceSet_of_gain {M : Set (Finset GadgetV)} {Mstar Nstar Aff : Set (Finset ℕ)}
    {e : Finset ℕ} (h : e ∈ Nstar \ Mstar) :
    choiceSet M Mstar Nstar Aff e = outerSet e :=
  dite_eq_left h

private theorem choiceSet_of_loss {M : Set (Finset GadgetV)} {Mstar Nstar Aff : Set (Finset ℕ)}
    {e : Finset ℕ} (h1 : e ∉ Nstar \ Mstar) (h2 : e ∈ Mstar \ Nstar) :
    choiceSet M Mstar Nstar Aff e = innerSet e := by
  unfold choiceSet
  rw [ite_eq_right h1, ite_eq_left h2]

private theorem choiceSet_of_aff {M : Set (Finset GadgetV)} {Mstar Nstar Aff : Set (Finset ℕ)}
    {e : Finset ℕ} (h1 : e ∉ Nstar \ Mstar) (h2 : e ∉ Mstar \ Nstar) (h3 : e ∈ Aff) :
    choiceSet M Mstar Nstar Aff e = innerSet e := by
  unfold choiceSet
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]

private theorem choiceSet_of_other {M : Set (Finset GadgetV)} {Mstar Nstar Aff : Set (Finset ℕ)}
    {e : Finset ℕ} (h1 : e ∉ Nstar \ Mstar) (h2 : e ∉ Mstar \ Nstar) (h3 : e ∉ Aff) :
    choiceSet M Mstar Nstar Aff e = M ∩ gadgetEdges e := by
  unfold choiceSet
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

private theorem choiceSet_subset_gadget {M : Set (Finset GadgetV)}
    {Mstar Nstar Aff : Set (Finset ℕ)}
    {e : Finset ℕ} :
    choiceSet M Mstar Nstar Aff e ⊆ gadgetEdges e := by
  by_cases h1 : e ∈ Nstar \ Mstar
  · rw [choiceSet_of_gain h1]; exact outer_subset_gadget
  · by_cases h2 : e ∈ Mstar \ Nstar
    · rw [choiceSet_of_loss h1 h2]; exact inner_subset_gadget
    · by_cases h3 : e ∈ Aff
      · rw [choiceSet_of_aff h1 h2 h3]; exact inner_subset_gadget
      · rw [choiceSet_of_other h1 h2 h3]; exact Set.inter_subset_right

private theorem choiceSet_pairwise {M : Set (Finset GadgetV)}
    (hM : IsMatching gadgetEdgeSet M) {Mstar Nstar Aff : Set (Finset ℕ)}
    {e : Finset ℕ} : (choiceSet M Mstar Nstar Aff e).Pairwise Disjoint := by
  by_cases h1 : e ∈ Nstar \ Mstar
  · rw [choiceSet_of_gain h1]
    exact fun _ hf _ hg hne ↦ outer_disjoint hf hg hne
  · by_cases h2 : e ∈ Mstar \ Nstar
    · rw [choiceSet_of_loss h1 h2]
      exact fun _ hf _ hg hne ↦ inner_disjoint hf hg hne
    · by_cases h3 : e ∈ Aff
      · rw [choiceSet_of_aff h1 h2 h3]
        exact fun _ hf _ hg hne ↦ inner_disjoint hf hg hne
      · rw [choiceSet_of_other h1 h2 h3]
        exact fun _ hf _ hg hne ↦ hM.2 hf.1 hg.1 hne

/-- If an edge chosen for a gadget contains an original vertex, then either the gadget was
gained by the improved matching, or the edge is an old matching edge and the gadget was not
affected. -/
private theorem choice_inl_cases {M : Set (Finset GadgetV)} {Mstar Nstar Aff : Set (Finset ℕ)}
    {e : Finset ℕ} {f : Finset GadgetV} (hf : f ∈ choiceSet M Mstar Nstar Aff e) {w : ℕ}
    (hw : Sum.inl w ∈ f) :
    (e ∈ Nstar \ Mstar) ∨
      (f ∈ M ∧ e ∉ Aff ∧ e ∉ Nstar \ Mstar ∧ e ∉ Mstar \ Nstar) := by
  have hnotI : f ∉ innerSet e := by
    intro hfI
    obtain ⟨x, y, -, rfl⟩ := hfI
    simp only [innerEdge, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h | h <;> exact absurd h (by simp [gadgetVertex])
  by_cases h1 : e ∈ Nstar \ Mstar
  · exact Or.inl h1
  · by_cases h2 : e ∈ Mstar \ Nstar
    · rw [choiceSet_of_loss h1 h2] at hf
      exact absurd hf hnotI
    · by_cases h3 : e ∈ Aff
      · rw [choiceSet_of_aff h1 h2 h3] at hf
        exact absurd hf hnotI
      · rw [choiceSet_of_other h1 h2 h3] at hf
        exact Or.inr ⟨hf.1, h3, h1, h2⟩

private theorem ncard_biUnion_eq_sum {T : Finset (Finset ℕ)}
    {P : Finset ℕ → Set (Finset GadgetV)}
    (hfin : ∀ e ∈ T, (P e).Finite)
    (hdisj : ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → Disjoint (P e) (P e')) :
    (⋃ e ∈ (T : Set (Finset ℕ)), P e).ncard = ∑ e ∈ T, (P e).ncard := by
  induction T using Finset.induction with
  | empty => simp
  | @insert a T ha ih =>
    have hfin' : ∀ e ∈ T, (P e).Finite := fun e he ↦ hfin e (Finset.mem_insert_of_mem he)
    have hdisj' : ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → Disjoint (P e) (P e') :=
      fun e he e' he' hne ↦ hdisj e (Finset.mem_insert_of_mem he) e'
        (Finset.mem_insert_of_mem he') hne
    have hdis : Disjoint (P a) (⋃ e ∈ (T : Set (Finset ℕ)), P e) := by
      rw [Set.disjoint_left]
      rintro f hf hfU
      obtain ⟨e, heT, hfe⟩ := Set.mem_iUnion₂.mp hfU
      exact Set.disjoint_left.mp
        (hdisj a (Finset.mem_insert_self _ _) e (Finset.mem_insert_of_mem heT)
          (fun h ↦ ha (h ▸ heT))) hf hfe
    rw [Finset.coe_insert, Set.biUnion_insert, Set.ncard_union_eq hdis
      (hfin a (Finset.mem_insert_self _ _))
      (Set.Finite.biUnion (Finset.finite_toSet T) hfin'), ih hfin' hdisj',
      Finset.sum_insert ha]


private theorem gadget_no_strongly_maximal : ¬ ∃ M, IsStronglyMaximal gadgetEdgeSet M := by
  classical
  rintro ⟨M, hM⟩
  set Mstar : Set (Finset ℕ) :=
    {e | e ∈ starEdges ∧ M ∩ gadgetEdges e = outerSet e} with hMstarDef
  have hMstar_sub : Mstar ⊆ starEdges := fun e he ↦ he.1
  have hpairG : ∀ e, (M ∩ gadgetEdges e).Pairwise Disjoint :=
    fun e a ha b hb hab ↦ hM.1.2 ha.1 hb.1 hab
  have hcard_ge : ∀ e ∈ starEdges,
      e.card - 1 ≤ (M ∩ gadgetEdges e).ncard ∧ (M ∩ gadgetEdges e).ncard ≤ e.card :=
    fun e he ↦ ⟨gadget_lower hM he, gadget_size_le Set.inter_subset_right (hpairG e)⟩
  have hcard_pos : ∀ e ∈ starEdges, 1 ≤ e.card :=
    fun e he ↦ Finset.card_pos.mpr ⟨starMin e, starMin_mem he⟩
  have hclass : ∀ e ∈ starEdges, (M ∩ gadgetEdges e).ncard = e.card ∨
      (M ∩ gadgetEdges e).ncard = e.card - 1 := by
    intro e he
    have ⟨hlo, hhi⟩ := hcard_ge e he
    have hpos := hcard_pos e he
    omega
  have hMstar_iff : ∀ e ∈ starEdges,
      e ∈ Mstar ↔ (M ∩ gadgetEdges e).ncard = e.card := by
    intro e he
    constructor
    · intro h
      rw [h.2, outerSet_ncard]
    · intro h
      exact ⟨he, gadget_classify Set.inter_subset_right (hpairG e) h⟩
  have hMstar_match : IsMatching starEdges Mstar := by
    refine ⟨hMstar_sub, ?_⟩
    intro e1 he1 e2 he2 hne
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    have ho1 : outerEdge e1 v ∈ M := by
      have hmem : outerEdge e1 v ∈ outerSet e1 := ⟨v, hv1, rfl⟩
      rw [← he1.2] at hmem
      exact hmem.1
    have ho2 : outerEdge e2 v ∈ M := by
      have hmem : outerEdge e2 v ∈ outerSet e2 := ⟨v, hv2, rfl⟩
      rw [← he2.2] at hmem
      exact hmem.1
    have hne2 : outerEdge e1 v ≠ outerEdge e2 v := by
      intro hEq
      apply hne
      have hmem : outerEdge e1 v ∈ gadgetEdges e2 := by
        rw [hEq]
        exact outer_mem_gadget hv2
      exact gadget_of_vertex hmem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    exact Finset.disjoint_left.mp (hM.1.2 ho1 ho2 hne2)
      (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
  obtain ⟨Nstar, hNstar, hNfin1, hNfin2, hcount⟩ := star_improvement hMstar_match
  set Aff : Set (Finset ℕ) :=
    {e | ∃ f ∈ Nstar \ Mstar, ∃ v ∈ f, v ∈ e ∧ outerEdge e v ∈ M} with hAffDef
  have haff_star : ∀ e ∈ Aff, e ∈ starEdges := by
    intro e heAff
    obtain ⟨f, hf, v, hvf, hve, hout⟩ := heAff
    obtain ⟨e', he', hmem⟩ := exists_gadget_of_mem (hM.1.1 hout)
    have heq : e = e' := gadget_of_vertex hmem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    rw [heq]
    exact he'
  have hAff_fin : Aff.Finite := by
    have hUfin : (⋃ f ∈ Nstar \ Mstar, (f : Set ℕ)).Finite :=
      Set.Finite.biUnion hNfin1 (fun f _ ↦ Finset.finite_toSet f)
    have hsub : ∀ v : ℕ, ({e | outerEdge e v ∈ M} : Set (Finset ℕ)).Subsingleton := by
      intro v e1 he1 e2 he2
      by_contra hne
      have hne2 : outerEdge e1 v ≠ outerEdge e2 v := by
        intro hEq
        apply hne
        obtain ⟨e', he', hmem⟩ := exists_gadget_of_mem (hM.1.1 he2)
        have h1 : e1 = e' := gadget_of_vertex (by rwa [← hEq] at hmem)
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have h2 : e2 = e' := gadget_of_vertex hmem
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        exact h1.trans h2.symm
      exact Finset.disjoint_left.mp (hM.1.2 he1 he2 hne2)
        (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
    apply Set.Finite.subset
      (s := ⋃ v ∈ ⋃ f ∈ Nstar \ Mstar, (f : Set ℕ), {e | outerEdge e v ∈ M})
    · exact Set.Finite.biUnion hUfin (fun v _ ↦ (hsub v).finite)
    · intro e heAff
      obtain ⟨f, hf, v, hvf, hve, hout⟩ := heAff
      apply Set.mem_biUnion _ hout
      exact Set.mem_biUnion hf (Finset.mem_coe.mpr hvf)
  have haff_not_Mstar : ∀ e ∈ Aff, e ∉ Mstar \ Nstar → e ∉ Mstar := by
    intro e heAff hnot hMstar
    have heStar : e ∈ starEdges := haff_star e heAff
    obtain ⟨f, hf, v, hvf, hve, hout⟩ := heAff
    by_cases heN : e ∈ Nstar
    · have hne : e ≠ f := fun hEq ↦ hf.2 (hEq ▸ hMstar)
      have hdis := hNstar.2 heN hf.1 hne
      exact Finset.disjoint_left.mp hdis hve hvf
    · exact hnot ⟨hMstar, heN⟩
  set N : Set (Finset GadgetV) := ⋃ e ∈ starEdges, choiceSet M Mstar Nstar Aff e with hNdef
  have hNG : ∀ e ∈ starEdges, N ∩ gadgetEdges e = choiceSet M Mstar Nstar Aff e := by
    intro e he
    ext f
    constructor
    · intro hf
      obtain ⟨e', he', hf'⟩ := Set.mem_iUnion₂.mp hf.1
      have heq : e' = e := by
        by_contra hne
        exact Set.disjoint_left.mp (gadgetEdges_disjoint hne)
          (choiceSet_subset_gadget hf') hf.2
      subst heq
      exact hf'
    · intro hf
      exact ⟨Set.mem_biUnion he hf, choiceSet_subset_gadget hf⟩
  have hNsub : N ⊆ gadgetEdgeSet := by
    intro f hf
    obtain ⟨e, he, hf'⟩ := Set.mem_iUnion₂.mp hf
    exact gadget_mem_edgeSet he (choiceSet_subset_gadget hf')
  have hNpair : N.Pairwise Disjoint := by
    intro f hf g hg hne
    obtain ⟨ef, hef, hff⟩ := Set.mem_iUnion₂.mp hf
    obtain ⟨eg, heg, hfg⟩ := Set.mem_iUnion₂.mp hg
    by_cases heq : ef = eg
    · subst heq
      exact choiceSet_pairwise hM.1 hff hfg hne
    · by_contra hdis
      rw [Finset.not_disjoint_iff] at hdis
      obtain ⟨v, hvf, hvg⟩ := hdis
      cases v with
      | inl w =>
        rcases choice_inl_cases hff (hw := hvf) with h1 | ⟨hfM, hAff, h1, h2⟩ <;>
          rcases choice_inl_cases hfg (hw := hvg) with g1 | ⟨hgM, gAff, g1, g2⟩
        · have hwf : w ∈ ef := (inl_mem_gadget (choiceSet_subset_gadget hff) hvf).2
          have hwg : w ∈ eg := (inl_mem_gadget (choiceSet_subset_gadget hfg) hvg).2
          exact Finset.disjoint_left.mp (hNstar.2 h1.1 g1.1 heq) hwf hwg
        · have hwf : w ∈ ef := (inl_mem_gadget (choiceSet_subset_gadget hff) hvf).2
          have hwg : w ∈ eg := (inl_mem_gadget (choiceSet_subset_gadget hfg) hvg).2
          have hge : eg ∈ Aff := by
            refine ⟨ef, h1, w, hwf, hwg, ?_⟩
            have hEq := (inl_mem_gadget (choiceSet_subset_gadget hfg) hvg).1
            rw [hEq] at hgM
            exact hgM
          exact gAff hge
        · have hwf : w ∈ ef := (inl_mem_gadget (choiceSet_subset_gadget hff) hvf).2
          have hwg : w ∈ eg := (inl_mem_gadget (choiceSet_subset_gadget hfg) hvg).2
          have hge : ef ∈ Aff := by
            refine ⟨eg, g1, w, hwg, hwf, ?_⟩
            have hEq := (inl_mem_gadget (choiceSet_subset_gadget hff) hvf).1
            rw [hEq] at hfM
            exact hfM
          exact hAff hge
        · exact Finset.disjoint_left.mp (hM.1.2 hfM hgM hne) hvf hvg
      | inr p =>
        have hvp : gadgetVertex p.1 p.2.1 p.2.2 ∈ f := hvf
        have hvg' : gadgetVertex p.1 p.2.1 p.2.2 ∈ g := hvg
        have h1 : p.1 = ef := gadget_of_vertex (choiceSet_subset_gadget hff) hvp
        have h2 : p.1 = eg := gadget_of_vertex (choiceSet_subset_gadget hfg) hvg'
        exact heq (h1.symm.trans h2)
  -- Counting: the new matching differs from `M` only on finitely many gadgets.
  set S : Set (Finset ℕ) := (Mstar \ Nstar) ∪ (Nstar \ Mstar) ∪ Aff with hSdef
  have hSfin : S.Finite := (hNfin2.union hNfin1).union hAff_fin
  set SF : Finset (Finset ℕ) := hSfin.toFinset with hSFdef
  have hmemSF : ∀ e, e ∈ SF ↔ e ∈ S := fun e ↦ by
    rw [hSFdef]
    exact hSfin.mem_toFinset
  have hsubS1 : Nstar \ Mstar ⊆ S :=
    fun e he ↦ Set.mem_union_left _ (Set.mem_union_right _ he)
  have hsubS2 : Mstar \ Nstar ⊆ S :=
    fun e he ↦ Set.mem_union_left _ (Set.mem_union_left _ he)
  have hS_cases : ∀ e ∈ S, e ∈ Mstar \ Nstar ∨ e ∈ Nstar \ Mstar ∨ e ∈ Aff := by
    intro e he
    rw [hSdef] at he
    simpa only [Set.mem_union, or_assoc] using he
  have hSF_star : ∀ e ∈ SF, e ∈ starEdges := by
    intro e heSF
    have heSOr := hS_cases e ((hmemSF e).mp heSF)
    rcases heSOr with h | h | h
    · exact hMstar_sub h.1
    · exact hNstar.1 h.1
    · exact haff_star e h
  have hown : ∀ f ∈ M, f ∉ N → ∃ e ∈ SF, f ∈ gadgetEdges e := by
    intro f hfM hfN
    obtain ⟨ef, hef, hff⟩ := exists_gadget_of_mem (hM.1.1 hfM)
    by_cases h1 : ef ∈ Nstar \ Mstar
    · exact ⟨ef, (hmemSF ef).mpr (hsubS1 h1), hff⟩
    · by_cases h2 : ef ∈ Mstar \ Nstar
      · exact ⟨ef, (hmemSF ef).mpr (hsubS2 h2), hff⟩
      · by_cases h3 : ef ∈ Aff
        · exact ⟨ef, (hmemSF ef).mpr (Set.mem_union_right _ h3), hff⟩
        · exfalso
          apply hfN
          have hch : f ∈ choiceSet M Mstar Nstar Aff ef := by
            rw [choiceSet_of_other h1 h2 h3]
            exact ⟨hfM, hff⟩
          exact Set.mem_biUnion hef hch
  have hchoice_ncard : ∀ e ∈ SF, (choiceSet M Mstar Nstar Aff e).ncard =
      (if e ∈ Nstar \ Mstar then e.card else e.card - 1) := by
    intro e heSF
    have heStar := hSF_star e heSF
    have heS : e ∈ S := (hmemSF e).mp heSF
    by_cases h1 : e ∈ Nstar \ Mstar
    · rw [choiceSet_of_gain h1, outerSet_ncard]
      simp only [h1, ite_true]
    · by_cases h2 : e ∈ Mstar \ Nstar
      · rw [choiceSet_of_loss h1 h2, innerSet_ncard (hMstar_sub h2.1)]
        simp only [h1, ite_false]
      · by_cases h3 : e ∈ Aff
        · rw [choiceSet_of_aff h1 h2 h3, innerSet_ncard (haff_star e h3)]
          simp only [h1, ite_false]
        · have heSOr := hS_cases e heS
          rcases heSOr with h | h | h
          · exact absurd h h2
          · exact absurd h h1
          · exact absurd h h3
  have hA_ncard : ∀ e ∈ SF, (M ∩ gadgetEdges e).ncard =
      (if e ∈ Mstar then e.card else e.card - 1) := by
    intro e heSF
    have heStar := hSF_star e heSF
    by_cases hMst : e ∈ Mstar
    · have hEq : (M ∩ gadgetEdges e).ncard = e.card := (hMstar_iff e heStar).mp hMst
      rw [hEq]
      simp only [hMst, ite_true]
    · have hEq : (M ∩ gadgetEdges e).ncard = e.card - 1 := by
        rcases hclass e heStar with h | h
        · exact absurd ((hMstar_iff e heStar).mpr h) hMst
        · exact h
      rw [hEq]
      simp only [hMst, ite_false]
  have hnet : ∀ e ∈ SF,
      ((choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e)).ncard : ℤ) -
        (((M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e).ncard : ℤ) =
      (if e ∈ Nstar \ Mstar then 1 else 0) - (if e ∈ Mstar \ Nstar then 1 else 0) := by
    intro e heSF
    have heStar := hSF_star e heSF
    have hpos : 1 ≤ e.card := hcard_pos e heStar
    have hAfin_e : (M ∩ gadgetEdges e).Finite :=
      (gadgetEdges_finite e).subset Set.inter_subset_right
    have hCfin_e : (choiceSet M Mstar Nstar Aff e).Finite :=
      (gadgetEdges_finite e).subset choiceSet_subset_gadget
    have hI : (choiceSet M Mstar Nstar Aff e ∩ (M ∩ gadgetEdges e)).ncard ≤
        (choiceSet M Mstar Nstar Aff e).ncard :=
      Set.ncard_le_ncard Set.inter_subset_left hCfin_e
    have hI2 : (choiceSet M Mstar Nstar Aff e ∩ (M ∩ gadgetEdges e)).ncard ≤
        (M ∩ gadgetEdges e).ncard :=
      Set.ncard_le_ncard Set.inter_subset_right hAfin_e
    have hd1 : (choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e)).ncard =
        (choiceSet M Mstar Nstar Aff e).ncard -
          (choiceSet M Mstar Nstar Aff e ∩ (M ∩ gadgetEdges e)).ncard := by
      have heq : choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e) =
          choiceSet M Mstar Nstar Aff e \
            (choiceSet M Mstar Nstar Aff e ∩ (M ∩ gadgetEdges e)) := by
        ext f
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h ↦ h2 h.2⟩
        · rintro ⟨h1, h⟩
          exact ⟨h1, fun hm ↦ h ⟨h1, hm⟩⟩
      rw [heq, Set.ncard_sdiff Set.inter_subset_left
        (hCfin_e.subset Set.inter_subset_left)]
    have hd2 : ((M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e).ncard =
        (M ∩ gadgetEdges e).ncard -
          (choiceSet M Mstar Nstar Aff e ∩ (M ∩ gadgetEdges e)).ncard := by
      have heq : (M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e =
          (M ∩ gadgetEdges e) \ (choiceSet M Mstar Nstar Aff e ∩ (M ∩ gadgetEdges e)) := by
        ext f
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h ↦ h2 h.1⟩
        · rintro ⟨h1, h⟩
          exact ⟨h1, fun hm ↦ h ⟨hm, h1⟩⟩
      rw [heq, Set.ncard_sdiff Set.inter_subset_right
        (hAfin_e.subset Set.inter_subset_right)]
    rw [hd1, hd2, hchoice_ncard e heSF, hA_ncard e heSF]
    rw [hchoice_ncard e heSF] at hI
    rw [hA_ncard e heSF] at hI2
    by_cases h1 : e ∈ Nstar \ Mstar
    · have hMst : e ∉ Mstar := h1.2
      have h2 : e ∉ Mstar \ Nstar := fun h ↦ hMst h.1
      simp only [h1, hMst, h2, ite_true, ite_false] at hI hI2 ⊢
      omega
    · by_cases h2 : e ∈ Mstar \ Nstar
      · have hMst : e ∈ Mstar := h2.1
        simp only [h1, hMst, h2, ite_true, ite_false] at hI hI2 ⊢
        omega
      · have h3 : e ∈ Aff := by
          have heSOr := hS_cases e ((hmemSF e).mp heSF)
          rcases heSOr with h | h | h
          · exact absurd h h2
          · exact absurd h h1
          · exact h
        have hMst : e ∉ Mstar := haff_not_Mstar e h3 h2
        simp only [h1, hMst, h2, ite_false] at hI hI2 ⊢
        omega
  have hNM_eq : N \ M =
      ⋃ e ∈ (SF : Set (Finset ℕ)),
        choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e) := by
    ext f
    constructor
    · intro hf
      obtain ⟨ef, hef, hff⟩ := Set.mem_iUnion₂.mp hf.1
      have hefS : ef ∈ SF := (hmemSF ef).mpr (by
        by_cases h1 : ef ∈ Nstar \ Mstar
        · exact hsubS1 h1
        · by_cases h2 : ef ∈ Mstar \ Nstar
          · exact hsubS2 h2
          · by_cases h3 : ef ∈ Aff
            · exact Set.mem_union_right _ h3
            · rw [choiceSet_of_other h1 h2 h3] at hff
              exact absurd hff.1 hf.2)
      exact Set.mem_biUnion (Finset.mem_coe.mpr hefS)
        ⟨hff, fun h ↦ hf.2 h.1⟩
    · intro hf
      obtain ⟨ef, hef, hff⟩ := Set.mem_iUnion₂.mp hf
      refine ⟨?_, ?_⟩
      · exact Set.mem_biUnion (hSF_star ef (Finset.mem_coe.mp hef)) hff.1
      · intro hfM
        exact hff.2 ⟨hfM, choiceSet_subset_gadget hff.1⟩
  have hMN_eq : M \ N =
      ⋃ e ∈ (SF : Set (Finset ℕ)),
        (M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e := by
    ext f
    constructor
    · intro hf
      obtain ⟨ef, hefS, hff⟩ := hown f hf.1 hf.2
      refine Set.mem_biUnion (Finset.mem_coe.mpr hefS) ⟨⟨hf.1, hff⟩, ?_⟩
      intro hch
      exact hf.2 (Set.mem_biUnion (hSF_star ef hefS) hch)
    · intro hf
      obtain ⟨ef, hef, hff⟩ := Set.mem_iUnion₂.mp hf
      refine ⟨hff.1.1, ?_⟩
      intro hfN
      obtain ⟨ef', hef', hff'⟩ := Set.mem_iUnion₂.mp hfN
      have heq : ef' = ef := by
        by_contra hne
        exact Set.disjoint_left.mp (gadgetEdges_disjoint hne)
          (choiceSet_subset_gadget hff') hff.1.2
      subst heq
      exact hff.2 hff'
  have hPfin : ∀ e ∈ SF,
      (choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e)).Finite :=
    fun e _ ↦ ((gadgetEdges_finite e).subset choiceSet_subset_gadget).subset Set.sdiff_subset
  have hQfin : ∀ e ∈ SF, ((M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e).Finite :=
    fun e _ ↦ ((gadgetEdges_finite e).subset Set.inter_subset_right).subset Set.sdiff_subset
  have hPdisj : ∀ e ∈ SF, ∀ e' ∈ SF, e ≠ e' →
      Disjoint (choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e))
        (choiceSet M Mstar Nstar Aff e' \ (M ∩ gadgetEdges e')) := by
    intro e _ e' _ hne
    exact Set.disjoint_left.mpr fun f hf1 hf2 ↦
      Set.disjoint_left.mp (gadgetEdges_disjoint hne)
        (choiceSet_subset_gadget hf1.1) (choiceSet_subset_gadget hf2.1)
  have hQdisj : ∀ e ∈ SF, ∀ e' ∈ SF, e ≠ e' →
      Disjoint ((M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e)
        ((M ∩ gadgetEdges e') \ choiceSet M Mstar Nstar Aff e') := by
    intro e _ e' _ hne
    exact Set.disjoint_left.mpr fun f hf1 hf2 ↦
      Set.disjoint_left.mp (gadgetEdges_disjoint hne) hf1.1.2 hf2.1.2
  have hcardP : (N \ M).ncard =
      ∑ e ∈ SF, (choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e)).ncard := by
    rw [hNM_eq]
    exact ncard_biUnion_eq_sum hPfin hPdisj
  have hcardQ : (M \ N).ncard =
      ∑ e ∈ SF, ((M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e).ncard := by
    rw [hMN_eq]
    exact ncard_biUnion_eq_sum hQfin hQdisj
  have hsum : (∑ e ∈ SF,
        ((choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e)).ncard : ℤ)) -
      (∑ e ∈ SF, (((M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e).ncard : ℤ)) =
      ((Nstar \ Mstar).ncard : ℤ) - ((Mstar \ Nstar).ncard : ℤ) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun e he ↦ hnet e he),
      Finset.sum_sub_distrib]
    congr 1
    · have hfilter : SF.filter (· ∈ Nstar \ Mstar) = hNfin1.toFinset := by
        ext e
        simp only [Finset.mem_filter, hmemSF, hNfin1.mem_toFinset]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · intro h
          exact ⟨hsubS1 h, h⟩
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hfilter,
        Set.ncard_eq_toFinset_card _ hNfin1]
    · have hfilter : SF.filter (· ∈ Mstar \ Nstar) = hNfin2.toFinset := by
        ext e
        simp only [Finset.mem_filter, hmemSF, hNfin2.mem_toFinset]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · intro h
          exact ⟨hsubS2 h, h⟩
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hfilter,
        Set.ncard_eq_toFinset_card _ hNfin2]
  have hNfin' : (N \ M).Finite := by
    apply Set.Finite.subset
      (s := ⋃ e ∈ (SF : Set (Finset ℕ)), gadgetEdges e)
    · exact Set.Finite.biUnion (Finset.finite_toSet SF) (fun e _ ↦ gadgetEdges_finite e)
    · intro f hf
      obtain ⟨ef, hef, hff⟩ := Set.mem_iUnion₂.mp hf.1
      have hefS : ef ∈ SF := (hmemSF ef).mpr (by
        by_cases h1 : ef ∈ Nstar \ Mstar
        · exact hsubS1 h1
        · by_cases h2 : ef ∈ Mstar \ Nstar
          · exact hsubS2 h2
          · by_cases h3 : ef ∈ Aff
            · exact Set.mem_union_right _ h3
            · rw [choiceSet_of_other h1 h2 h3] at hff
              exact absurd hff.1 hf.2)
      exact Set.mem_biUnion (Finset.mem_coe.mpr hefS) (choiceSet_subset_gadget hff)
  have hMfin' : (M \ N).Finite := by
    apply Set.Finite.subset
      (s := ⋃ e ∈ (SF : Set (Finset ℕ)), gadgetEdges e)
    · exact Set.Finite.biUnion (Finset.finite_toSet SF) (fun e _ ↦ gadgetEdges_finite e)
    · intro f hf
      obtain ⟨ef, hefS, hff⟩ := hown f hf.1 hf.2
      exact Set.mem_biUnion (Finset.mem_coe.mpr hefS) hff
  have hle := ncard_le_of_cardinal_le hNfin' hMfin' (hM.2 N ⟨hNsub, hNpair⟩)
  have hcast : ((N \ M).ncard : ℤ) ≤ ((M \ N).ncard : ℤ) := by exact_mod_cast hle
  rw [hcardP, hcardQ] at hcast
  have hcastN : ∑ e ∈ SF,
      (choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e)).ncard ≤
      ∑ e ∈ SF, ((M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e).ncard := by
    exact_mod_cast hcast
  have hcastZ : (∑ e ∈ SF,
        ((choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e)).ncard : ℤ)) ≤
      ∑ e ∈ SF, (((M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e).ncard : ℤ) := by
    have hcastsum : ∀ (T : Finset (Finset ℕ)) (g : Finset ℕ → ℕ),
        ((∑ e ∈ T, g e : ℕ) : ℤ) = ∑ e ∈ T, (g e : ℤ) := by
      intro T g
      induction T using Finset.induction with
      | empty => simp
      | @insert a T ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.cast_add, ih]
    have h2 : (((∑ e ∈ SF,
        (choiceSet M Mstar Nstar Aff e \ (M ∩ gadgetEdges e)).ncard : ℕ) : ℤ)) ≤
        ((∑ e ∈ SF,
          ((M ∩ gadgetEdges e) \ choiceSet M Mstar Nstar Aff e).ncard : ℕ) : ℤ) := by
      exact_mod_cast hcastN
    rw [hcastsum, hcastsum] at h2
    exact h2
  have hcountZ : ((Mstar \ Nstar).ncard : ℤ) < ((Nstar \ Mstar).ncard : ℤ) := by
    exact_mod_cast hcount
  omega

/--
**Bounded edge size does not guarantee a strongly maximal matching.** There are a vertex set
$V$, a set $E$ of finite subsets of $V$ and a natural number $k$ such that every edge in $E$ has
at most $k$ elements, but the hypergraph with edge set $E$ has no strongly maximal matching.

Hollom and Randall Shaw (Theorem 1.2) construct a $3$-uniform (infinite) hypergraph with no
strongly maximal matching, so bounded edge size does not suffice.

Source: EGRES Open
(Egerváry Research Group), list of open problems, Strongly maximal matchings,
https://oldlemon.cs.elte.hu/egres/open/Strongly_maximal_matchings; resolution: L. Hollom and B.
Randall Shaw, Counterexamples to conjectures on strong maximality and minimality, Electron. J.
Combin. 33(2) (2026), P2.11; arXiv:2511.13709, Theorem 1.2: there is a 3-uniform hypergraph H₁ with
no strongly maximal matching (refuting Conjecture 1.1 for matchings and Aharoni's question),
https://doi.org/10.37236/14948.
-/
theorem boundedEdgesStronglyMaximalMatching_refuted :
    ¬ boundedEdgesStronglyMaximalMatching := by
  intro h
  obtain ⟨M, hM⟩ := h GadgetV gadgetEdgeSet 3 (by
    intro e he
    obtain ⟨e', he', hmem⟩ := exists_gadget_of_mem he
    rcases hmem with ⟨x, -, rfl⟩ | ⟨x, y, -, rfl⟩
    · exact outerEdge_card_le e' x
    · exact innerEdge_card_le e' x y)
  exact gadget_no_strongly_maximal ⟨M, hM⟩

end MathlibExt.Combinatorics.StronglyMaximalMatchingAMR29Problem0084Wanted
