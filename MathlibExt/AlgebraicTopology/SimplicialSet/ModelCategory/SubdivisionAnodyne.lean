/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Nonsingular
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Order.Fin.InsertNth

/-!
# Subdivision preserves anodyne extensions

The subdivision of a horn inclusion is compared with the inclusion of a full
lower subposet of face chains.  A regular toggle pairing on the complementary
strict chains proves that inclusion anodyne.  The subdivision--Ex adjunction
then extends the result to arbitrary anodyne maps and all iterates.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  MorphismProperty Simplicial
open PartialOrder
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

namespace subdivisionHorn

attribute [local instance] Classical.propDecidable

private abbrev Vertex (n : ℕ) : Type u := ULift.{u} (Fin (n + 2))

private abbrev Face (n : ℕ) := NonemptyFiniteChains (Vertex.{u} n)

private def distinguished {n : ℕ} (i : Fin (n + 2)) : Vertex.{u} n := ULift.up i

private def missingFace {n : ℕ} (i : Fin (n + 2)) : Finset (Vertex.{u} n) :=
  Finset.univ.erase (distinguished.{u} i)

private def Allowed {n : ℕ} (i : Fin (n + 2)) (S : Face.{u} n) : Prop :=
  ¬missingFace.{u} i ⊆ S.finset

private abbrev H {n : ℕ} (i : Fin (n + 2)) :=
  {S : Face.{u} n // Allowed.{u} i S}

private def jH {n : ℕ} (i : Fin (n + 2)) : H.{u} i ↪o Face.{u} n :=
  OrderEmbedding.subtype _

private def jHOrd {n : ℕ} (i : Fin (n + 2)) :
    PartOrd.of (H.{u} i) ⟶ PartOrd.of (Face.{u} n) :=
  PartOrd.ofHom (jH.{u} i).toOrderHom

private def hMap {n : ℕ} (i : Fin (n + 2)) :
    nerve (H.{u} i) ⟶ nerve (Face.{u} n) :=
  PartOrd.nerveFunctor.map (jHOrd.{u} i)

private instance hMap_mono {n : ℕ} (i : Fin (n + 2)) : Mono (hMap.{u} i) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro x y hxy
  apply ComposableArrows.ext
    (h := fun j => by
      apply Subtype.ext
      have h := congrArg (fun z => z.obj j) hxy
      change (x.obj j).val = (y.obj j).val at h
      exact h)
    (w := by
      intro j hj
      subsingleton)

private def hornChains {n : ℕ} (i : Fin (n + 2)) :
    (nerve (Face.{u} n)).Subcomplex :=
  Subcomplex.range (hMap.{u} i)

private theorem mem_hornChains_iff {n d : ℕ} (i : Fin (n + 2))
    (s : (nerve (Face.{u} n)) _⦋d⦌) :
    s ∈ (hornChains.{u} i).obj _ ↔ ∀ j, Allowed.{u} i (s.obj j) := by
  change s ∈ Set.range ((hMap.{u} i).app _) ↔ _
  constructor
  · rintro ⟨t, rfl⟩ j
    exact (t.obj j).2
  · intro hs
    let t : (nerve (H.{u} i)) _⦋d⦌ :=
      (OrderHom.mk (fun j => ⟨s.obj j, hs j⟩)
        (fun a b hab => s.monotone hab)).monotone.functor
    refine ⟨t, ?_⟩
    apply ComposableArrows.ext
      (h := fun j => rfl)
      (w := by
        intro j hj
        subsingleton)

private theorem mem_hornChains_iff_last {n d : ℕ} (i : Fin (n + 2))
    (s : (nerve (Face.{u} n)) _⦋d⦌) :
    s ∈ (hornChains.{u} i).obj _ ↔
      Allowed.{u} i (s.obj (Fin.last d)) := by
  rw [mem_hornChains_iff]
  constructor
  · intro h
    exact h _
  · intro h j hbad
    apply h
    exact fun x hx => s.monotone (Fin.le_last j) (hbad hx)

private theorem outside_max_eq {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) :
    (x.simplex.obj (Fin.last x.dim)).finset = missingFace.{u} i ∨
      (x.simplex.obj (Fin.last x.dim)).finset = Finset.univ := by
  classical
  let M := (x.simplex.obj (Fin.last x.dim)).finset
  have hsub : missingFace.{u} i ⊆ M := by
    by_contra h
    apply x.notMem
    exact (mem_hornChains_iff_last i x.simplex).2 h
  by_cases hi : distinguished.{u} i ∈ M
  · right
    apply Finset.eq_univ_of_forall
    intro v
    by_cases hv : v = distinguished.{u} i
    · simpa [hv] using hi
    · have hv' : v ≠ ULift.up i := by simpa [distinguished] using hv
      exact hsub (by simp [missingFace, distinguished, hv'])
  · left
    apply Finset.Subset.antisymm
    · intro v hv
      have hvne : v ≠ distinguished.{u} i := by
        rintro rfl
        exact hi hv
      have hvne' : v ≠ ULift.up i := by simpa [distinguished] using hvne
      simp [missingFace, distinguished, hvne']
    · exact hsub

private theorem outside_strictMono {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) : StrictMono x.simplex.obj :=
  (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).1 x.nonDegenerate

private def contains {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) (j : Fin (x.dim + 1)) : Prop :=
  distinguished.{u} i ∈ (x.simplex.obj j).finset

private noncomputable def transition {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) : Fin (x.dim + 2) := by
  classical
  exact if h : ∃ j, contains.{u} i x j then
      (Fin.find (contains.{u} i x) h).castSucc
    else
      Fin.last (x.dim + 1)

private noncomputable def firstIndex {d : ℕ}
    (P : Fin (d + 1) → Prop) : Fin (d + 2) := by
  classical
  exact if h : ∃ j, P j then (Fin.find P h).castSucc
    else Fin.last (d + 1)

private theorem transition_eq_firstIndex {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) :
    transition.{u} i x = firstIndex (contains.{u} i x) := by
  rfl

private theorem firstIndex_eq {d : ℕ} (P : Fin (d + 1) → Prop)
    (r : Fin (d + 1)) (hr : P r)
    (hbefore : ∀ j, j < r → ¬P j) :
    firstIndex P = r.castSucc := by
  classical
  have h : ∃ j, P j := ⟨r, hr⟩
  simp only [firstIndex, h, dite_true]
  congr 1
  exact (Fin.find_eq_iff h).2
    ⟨hr, fun j hj htrue => hbefore j hj htrue⟩

private theorem firstIndex_remove_before {d : ℕ}
    (P : Fin (d + 2) → Prop) (p q : Fin (d + 2))
    (hqp : q < p) (hpP : P p)
    (hbefore : ∀ j, j < p → ¬P j) :
    firstIndex (fun j => P (q.succAbove j)) =
      (p.pred (Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le q) hqp))).castSucc := by
  let hp : p ≠ 0 := Fin.ne_of_gt
    (lt_of_le_of_lt (Fin.zero_le q) hqp)
  let r := p.pred hp
  have hr : r.castSucc < p := by
    change p.val - 1 < p.val
    have hpv : p.val ≠ 0 := by
      intro h
      apply hp
      apply Fin.ext
      simpa using h
    omega
  apply firstIndex_eq _ r
  · have hqr : q ≤ r.castSucc := by
      change q.val ≤ p.val - 1
      omega
    rw [Fin.succAbove_of_le_castSucc q r hqr, Fin.succ_pred]
    exact hpP
  · intro j hj
    apply hbefore
    by_cases hqj : q ≤ j.castSucc
    · rw [Fin.succAbove_of_le_castSucc q j hqj]
      change j.val + 1 < p.val
      change j.val < p.val - 1 at hj
      omega
    · rw [Fin.succAbove_of_castSucc_lt q j (lt_of_not_ge hqj)]
      exact lt_trans j.castSucc_lt_succ (by
        change j.val + 1 < p.val
        change j.val < p.val - 1 at hj
        omega)

private theorem firstIndex_remove_after {d : ℕ}
    (P : Fin (d + 2) → Prop) (p q : Fin (d + 2))
    (hpq : p < q) (hpP : P p)
    (hbefore : ∀ j, j < p → ¬P j) :
    firstIndex (fun j => P (q.succAbove j)) = p := by
  have hpLast : p ≠ Fin.last (d + 1) := Fin.ne_last_of_lt hpq
  let r := p.castPred hpLast
  have hr : r.castSucc = p := Fin.castSucc_castPred p hpLast
  refine (firstIndex_eq _ r ?_ ?_).trans hr
  · rw [Fin.succAbove_castPred_of_lt q p hpq]
    exact hpP
  · intro j hj
    have hjp : j.castSucc < p := by
      rw [← hr]
      exact Fin.castSucc_lt_castSucc_iff.2 hj
    have hjq : j.castSucc < q := lt_trans hjp hpq
    rw [Fin.succAbove_of_castSucc_lt q j hjq]
    exact hbefore j.castSucc hjp

private theorem not_contains_before {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) {j : Fin (x.dim + 1)}
    (hj : j.castSucc < transition.{u} i x) :
    ¬contains.{u} i x j := by
  classical
  unfold transition at hj
  split_ifs at hj with h
  · exact Fin.find_min h (by simpa using hj)
  · exact fun hj' => h ⟨j, hj'⟩

private theorem contains_from_transition {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) {j : Fin (x.dim + 1)}
    (hj : transition.{u} i x ≤ j.castSucc) :
    contains.{u} i x j := by
  classical
  unfold transition at hj
  split_ifs at hj with h
  · have hfind := Fin.find_spec h
    have hle : Fin.find (contains.{u} i x) h ≤ j := by
      simpa using hj
    exact (x.simplex.monotone hle) hfind
  · have : ¬(Fin.last (x.dim + 1) ≤ j.castSucc) := by simp
    exact (this hj).elim

private noncomputable def candidateFinset {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) : Finset (Vertex.{u} n) := by
  classical
  by_cases h : ∃ j, contains.{u} i x j
  · let q := Fin.find (contains.{u} i x) h
    by_cases hq : q = 0
    · exact {distinguished.{u} i}
    · exact (x.simplex.obj (q.pred hq).castSucc).finset ∪ {distinguished.{u} i}
  · exact Finset.univ

private noncomputable def candidate {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) : Face.{u} n where
  finset := candidateFinset.{u} i x
  nonempty := by
    classical
    dsimp [candidateFinset]
    split_ifs <;> simp
  comparable := fun a b => le_total a b

private theorem max_eq_missing_of_not_contains {n : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (h : ¬∃ j, contains.{u} i x j) :
    (x.simplex.obj (Fin.last x.dim)).finset = missingFace.{u} i := by
  rcases outside_max_eq i x with hC | hU
  · exact hC
  · exfalso
    apply h
    refine ⟨Fin.last x.dim, ?_⟩
    change distinguished.{u} i ∈
      (x.simplex.obj (Fin.last x.dim)).finset
    rw [hU]
    simp

private theorem candidate_finset_eq_transition {n : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N) :
    (candidate.{u} i x).finset =
      if hp : transition.{u} i x = 0 then
        {distinguished.{u} i}
      else
        (x.simplex.obj ((transition.{u} i x).pred hp)).finset ∪
          {distinguished.{u} i} := by
  classical
  change candidateFinset.{u} i x = _
  by_cases h : ∃ j, contains.{u} i x j
  · let q := Fin.find (contains.{u} i x) h
    have htrans : transition.{u} i x = q.castSucc := by
      simp only [transition, h, dite_true, q]
    have hcand : candidateFinset.{u} i x =
        if hq : q = 0 then {distinguished.{u} i}
        else (x.simplex.obj (q.pred hq).castSucc).finset ∪
          {distinguished.{u} i} := by
      simp only [candidateFinset]
      rw [dite_eq_left h]
    rw [hcand, htrans]
    by_cases hq : q = 0
    · have hq' : q.castSucc = 0 := by
        apply Fin.ext
        simp [hq]
      simp [hq]
    · have hq' : q.castSucc ≠ 0 := by
        intro h0
        apply hq
        apply Fin.ext
        simpa using congrArg Fin.val h0
      simp only [hq, hq', dite_false]
      congr 2
  · have htrans : transition.{u} i x = Fin.last (x.dim + 1) := by
      simp only [transition, h, dite_false]
    have hcand : candidateFinset.{u} i x = Finset.univ := by
      simp only [candidateFinset, h, dite_false]
    rw [hcand, htrans]
    have hlast0 : Fin.last (x.dim + 1) ≠ 0 :=
      Fin.ne_of_gt Fin.last_pos
    simp only [hlast0, dite_false]
    rw [Fin.pred_last, max_eq_missing_of_not_contains i x h]
    ext v
    by_cases hv : v = distinguished.{u} i
    · subst v
      simp [missingFace]
    · simp [missingFace]

private def CandidatePresent {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) : Prop :=
  ∃ j, x.simplex.obj j = candidate.{u} i x

private theorem candidate_contains {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) :
    distinguished.{u} i ∈ (candidate.{u} i x).finset := by
  classical
  dsimp [candidate, candidateFinset]
  split_ifs <;> simp

private theorem transition_eq_of_exists {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) (h : ∃ j, contains.{u} i x j) :
    transition.{u} i x = (Fin.find (contains.{u} i x) h).castSucc := by
  classical
  simp [transition, h]

private theorem transition_eq_of_not_exists {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) (h : ¬∃ j, contains.{u} i x j) :
    transition.{u} i x = Fin.last (x.dim + 1) := by
  classical
  simp [transition, h]

private theorem candidate_le_first_containing {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) (h : ∃ j, contains.{u} i x j) :
    candidate.{u} i x ≤
      x.simplex.obj (Fin.find (contains.{u} i x) h) := by
  classical
  let q := Fin.find (contains.{u} i x) h
  have hqmem : contains.{u} i x q := Fin.find_spec h
  by_cases hq0 : q = 0
  · change (candidate.{u} i x).finset ⊆
      (x.simplex.obj q).finset
    rw [show (candidate.{u} i x).finset = {distinguished.{u} i} by
      simp [candidate, candidateFinset, h, q, hq0]]
    simpa [contains] using hqmem
  · have hpq : (q.pred hq0).castSucc ≤ q := by
      grind [Fin.succ_pred q hq0]
    change (candidate.{u} i x).finset ⊆
      (x.simplex.obj q).finset
    rw [show (candidate.{u} i x).finset =
        (x.simplex.obj (q.pred hq0).castSucc).finset ∪
          {distinguished.{u} i} by
      simp [candidate, candidateFinset, h, q, hq0]]
    intro v hv
    rw [Finset.mem_union, Finset.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact x.simplex.monotone hpq hv
    · exact hqmem

private theorem candidate_occurs_at_transition {n : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) {j : Fin (x.dim + 1)}
    (hj : x.simplex.obj j = candidate.{u} i x) :
    j.castSucc = transition.{u} i x := by
  classical
  have hex : ∃ k, contains.{u} i x k := by
    refine ⟨j, ?_⟩
    change distinguished.{u} i ∈ (x.simplex.obj j).finset
    rw [hj]
    exact candidate_contains i x
  let q := Fin.find (contains.{u} i x) hex
  have hqj : q ≤ j := Fin.find_le_of_pos hex (by
    change distinguished.{u} i ∈ (x.simplex.obj j).finset
    rw [hj]
    exact candidate_contains i x)
  have hcand : candidate.{u} i x ≤ x.simplex.obj q :=
    candidate_le_first_containing i x hex
  have hjq : j = q := by
    by_contra hne
    have hqj' : q < j := lt_of_le_of_ne hqj (Ne.symm hne)
    have hlt : x.simplex.obj q < x.simplex.obj j :=
      outside_strictMono i x hqj'
    rw [hj] at hlt
    exact (not_lt_of_ge hcand hlt).elim
  subst j
  exact transition_eq_of_exists i x hex |>.symm

private theorem dim_pos_of_candidatePresent {n : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (h : CandidatePresent.{u} i x) : 0 < x.dim := by
  by_contra hdim
  have hdim0 : x.dim = 0 := Nat.eq_zero_of_not_pos hdim
  obtain ⟨j, hj⟩ := h
  have hjlast : j = Fin.last x.dim := by
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  have hmaxcand :
      (x.simplex.obj (Fin.last x.dim)).finset =
        (candidate.{u} i x).finset := by
    rw [← hjlast, hj]
  rcases outside_max_eq i x with hC | hU
  · have hpivot : distinguished.{u} i ∈ missingFace.{u} i := by
      rw [← hC, hmaxcand]
      exact candidate_contains i x
    simp [missingFace] at hpivot
  · have hcandU : (candidate.{u} i x).finset = Finset.univ :=
      hmaxcand.symm.trans hU
    have hp0 : transition.{u} i x = 0 := by
      rw [← candidate_occurs_at_transition i x hj, hjlast, hdim0]
      rfl
    have hcandOne :
        (candidate.{u} i x).finset = {distinguished.{u} i} := by
      rw [candidate_finset_eq_transition]
      simp [hp0]
    have hcard := congrArg Finset.card (hcandOne.symm.trans hcandU)
    simp at hcard

private abbrev TypeII {n : ℕ} (i : Fin (n + 2)) :=
  {x : (hornChains.{u} i).N // ¬CandidatePresent.{u} i x}

private theorem candidate_ne_obj {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) (j : Fin (s.1.dim + 1)) :
    candidate.{u} i s.1 ≠ s.1.simplex.obj j := by
  intro h
  exact s.2 ⟨j, h.symm⟩

private theorem face_le_candidate_of_before {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) (j : Fin (s.1.dim + 1))
    (hj : j.castSucc < transition.{u} i s.1) :
    s.1.simplex.obj j ≤ candidate.{u} i s.1 := by
  classical
  by_cases h : ∃ k, contains.{u} i s.1 k
  · let q := Fin.find (contains.{u} i s.1) h
    have hjq : j < q := by
      simpa [transition, h, q] using hj
    have hq0 : q ≠ 0 := by
      intro hq
      simp [hq] at hjq
    have hjp : j ≤ (q.pred hq0).castSucc := by
      grind [Fin.succ_pred q hq0]
    change (s.1.simplex.obj j).finset ⊆
      (candidate.{u} i s.1).finset
    rw [show (candidate.{u} i s.1).finset =
        (s.1.simplex.obj (q.pred hq0).castSucc).finset ∪
          {distinguished.{u} i} by
      simp [candidate, candidateFinset, h, q, hq0]]
    exact fun v hv => Finset.mem_union_left _
      (s.1.simplex.monotone hjp hv)
  · have hmax :
        (s.1.simplex.obj (Fin.last s.1.dim)).finset = missingFace.{u} i := by
      rcases outside_max_eq i s.1 with hC | hU
      · exact hC
      · exfalso
        apply h
        refine ⟨Fin.last s.1.dim, ?_⟩
        change distinguished.{u} i ∈
          (s.1.simplex.obj (Fin.last s.1.dim)).finset
        rw [hU]
        simp
    change (s.1.simplex.obj j).finset ⊆
      (candidate.{u} i s.1).finset
    rw [show (candidate.{u} i s.1).finset = Finset.univ by
      simp [candidate, candidateFinset, h]]
    exact Finset.subset_univ _

private theorem candidate_le_face_of_after {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) (j : Fin (s.1.dim + 1))
    (hj : transition.{u} i s.1 ≤ j.castSucc) :
    candidate.{u} i s.1 ≤ s.1.simplex.obj j := by
  classical
  have hjc : contains.{u} i s.1 j :=
    contains_from_transition i s.1 hj
  by_cases h : ∃ k, contains.{u} i s.1 k
  · let q := Fin.find (contains.{u} i s.1) h
    have hqj : q ≤ j := by
      simpa [transition, h, q] using hj
    by_cases hq0 : q = 0
    · change (candidate.{u} i s.1).finset ⊆
        (s.1.simplex.obj j).finset
      rw [show (candidate.{u} i s.1).finset = {distinguished.{u} i} by
        simp [candidate, candidateFinset, h, q, hq0]]
      simpa [contains] using hjc
    · have hpq : (q.pred hq0).castSucc ≤ q := by
        grind [Fin.succ_pred q hq0]
      change (candidate.{u} i s.1).finset ⊆
        (s.1.simplex.obj j).finset
      rw [show (candidate.{u} i s.1).finset =
          (s.1.simplex.obj (q.pred hq0).castSucc).finset ∪
            {distinguished.{u} i} by
        simp [candidate, candidateFinset, h, q, hq0]]
      intro v hv
      rw [Finset.mem_union, Finset.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact s.1.simplex.monotone (hpq.trans hqj) hv
      · exact hjc
  · exact (h ⟨j, hjc⟩).elim

private theorem face_lt_candidate_of_before {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) (j : Fin (s.1.dim + 1))
    (hj : j.castSucc < transition.{u} i s.1) :
    s.1.simplex.obj j < candidate.{u} i s.1 :=
  lt_of_le_of_ne (face_le_candidate_of_before i s j hj)
    (candidate_ne_obj i s j).symm

private theorem candidate_lt_face_of_after {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) (j : Fin (s.1.dim + 1))
    (hj : transition.{u} i s.1 ≤ j.castSucc) :
    candidate.{u} i s.1 < s.1.simplex.obj j :=
  lt_of_le_of_ne (candidate_le_face_of_after i s j hj)
    (candidate_ne_obj i s j)

private noncomputable def insertedObj {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) : Fin (s.1.dim + 2) → Face.{u} n :=
  Fin.insertNth (transition.{u} i s.1) (candidate.{u} i s.1)
    s.1.simplex.obj

private theorem insertedObj_strictMono {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) : StrictMono (insertedObj.{u} i s) := by
  unfold insertedObj
  rw [Fin.strictMono_insertNth_iff]
  exact ⟨outside_strictMono i s.1,
    fun j hj => face_lt_candidate_of_before i s j hj,
    fun j hj => candidate_lt_face_of_after i s j hj⟩

private noncomputable def insertedSimplex {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    (nerve (Face.{u} n)) _⦋s.1.dim + 1⦌ :=
  (OrderHom.mk (insertedObj.{u} i s)
    (insertedObj_strictMono i s).monotone).monotone.functor

private theorem insertedSimplex_nonDegenerate {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    insertedSimplex.{u} i s ∈
      (nerve (Face.{u} n)).nonDegenerate (s.1.dim + 1) :=
  (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).2
    (insertedObj_strictMono i s)

private theorem insertedSimplex_δ {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    (nerve (Face.{u} n)).δ (transition.{u} i s.1)
        (insertedSimplex.{u} i s) = s.1.simplex := by
  apply ComposableArrows.ext
    (h := fun j => by
      change insertedObj.{u} i s
          ((transition.{u} i s.1).succAbove j) = s.1.simplex.obj j
      exact Fin.insertNth_apply_succAbove _ _ _ _)
    (w := by
      intro j hj
      subsingleton)

private theorem insertedSimplex_notMem {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    insertedSimplex.{u} i s ∉ (hornChains.{u} i).obj _ := by
  intro hs
  apply s.1.notMem
  have hface := (hornChains.{u} i).map
    (SimplexCategory.δ (transition.{u} i s.1)).op hs
  change (nerve (Face.{u} n)).δ (transition.{u} i s.1)
    (insertedSimplex.{u} i s) ∈ (hornChains.{u} i).obj _ at hface
  rwa [insertedSimplex_δ] at hface

private theorem insertedObj_transition {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    insertedObj.{u} i s (transition.{u} i s.1) =
      candidate.{u} i s.1 := by
  apply Fin.insertNth_apply_same

private noncomputable def upper {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) : (hornChains.{u} i).N :=
  Subcomplex.N.mk (insertedSimplex.{u} i s)
    (insertedSimplex_nonDegenerate i s) (insertedSimplex_notMem i s)

private theorem upper_dim {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) : (upper.{u} i s).dim = s.1.dim + 1 :=
  rfl

private theorem upper_contains_transition {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    contains.{u} i (upper.{u} i s) (transition.{u} i s.1) := by
  change distinguished.{u} i ∈
    (insertedObj.{u} i s (transition.{u} i s.1)).finset
  rw [insertedObj_transition]
  exact candidate_contains i s.1

private theorem upper_not_contains_before {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) {j : Fin (s.1.dim + 2)}
    (hj : j < transition.{u} i s.1) :
    ¬contains.{u} i (upper.{u} i s) j := by
  obtain rfl | ⟨k, rfl⟩ :=
    (transition.{u} i s.1).eq_self_or_eq_succAbove j
  · simp at hj
  · change distinguished.{u} i ∉
      (insertedObj.{u} i s
        ((transition.{u} i s.1).succAbove k)).finset
    unfold insertedObj
    rw [Fin.insertNth_apply_succAbove]
    apply not_contains_before i s.1
    simpa [Fin.succAbove_lt_iff_castSucc_lt] using hj

private theorem find_upper_eq_transition {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    Fin.find (contains.{u} i (upper.{u} i s))
        ⟨transition.{u} i s.1, upper_contains_transition i s⟩ =
      transition.{u} i s.1 := by
  apply (Fin.find_eq_iff _).2
  exact ⟨upper_contains_transition i s,
    fun j hj => upper_not_contains_before i s hj⟩

private theorem transition_upper {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    transition.{u} i (upper.{u} i s) =
      (transition.{u} i s.1).castSucc := by
  rw [transition_eq_of_exists i (upper.{u} i s)
    ⟨transition.{u} i s.1, upper_contains_transition i s⟩]
  rw [find_upper_eq_transition]
  rfl

private theorem candidate_upper {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    candidate.{u} i (upper.{u} i s) = candidate.{u} i s.1 := by
  classical
  apply NonemptyFiniteChains.ext
  rw [candidate_finset_eq_transition,
    candidate_finset_eq_transition, transition_upper]
  let p := transition.{u} i s.1
  change (if hp' : p.castSucc = 0 then
      {distinguished.{u} i}
    else
      (insertedObj.{u} i s (p.castSucc.pred hp')).finset ∪
        {distinguished.{u} i}) =
    if hp : p = 0 then {distinguished.{u} i}
    else (s.1.simplex.obj (p.pred hp)).finset ∪
      {distinguished.{u} i}
  by_cases hp : p = 0
  · subst p
    simp [hp]
  · have hp' : p.castSucc ≠ 0 := by
      intro h
      apply hp
      apply Fin.ext
      simpa using congrArg Fin.val h
    rw [dite_eq_right hp', dite_eq_right hp]
    have hj : p.succAbove (p.pred hp) = p.castSucc.pred hp' := by
      rw [Fin.succAbove_pred_self]
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_pred]
    rw [← hj]
    unfold insertedObj
    rw [Fin.insertNth_apply_succAbove]

private theorem upper_injective' {n : ℕ} (i : Fin (n + 2))
    {s t : TypeII.{u} i}
    (h : SSet.S.mk (insertedSimplex.{u} i s) =
      SSet.S.mk (insertedSimplex.{u} i t)) :
    s = t := by
  have hut : upper.{u} i s = upper.{u} i t := by
    rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff]
  have hdim := congrArg (fun x => x.dim) hut
  change s.1.dim + 1 = t.1.dim + 1 at hdim
  have hdim' : s.1.dim = t.1.dim := by omega
  have httProp : ¬CandidatePresent.{u} i
      (t.1.cast hdim'.symm) := by
    simpa only [t.1.cast_eq_self] using t.2
  let tt : TypeII.{u} i := ⟨t.1.cast hdim'.symm, httProp⟩
  have htt : tt = t := by
    apply Subtype.ext
    exact t.1.cast_eq_self hdim'.symm
  rw [← htt] at h hut ⊢
  have hpval := congrArg (fun x => (transition.{u} i x).val) hut
  simp only [transition_upper, Fin.val_castSucc] at hpval
  have hp : transition.{u} i s.1 = transition.{u} i tt.1 :=
    Fin.ext hpval
  have hins : insertedSimplex.{u} i s = insertedSimplex.{u} i tt :=
    (SSet.S.ext_iff _ _).mp h
  have hlower : s.1.simplex = tt.1.simplex := by
    calc
      s.1.simplex =
          (nerve (Face.{u} n)).δ (transition.{u} i s.1)
            (insertedSimplex.{u} i s) := (insertedSimplex_δ i s).symm
      _ = (nerve (Face.{u} n)).δ (transition.{u} i tt.1)
            (insertedSimplex.{u} i tt) := by rw [hp, hins]
      _ = tt.1.simplex := insertedSimplex_δ i tt
  apply Subtype.ext
  rw [Subcomplex.N.eq_iff_sMk_eq, SSet.S.ext_iff]
  exact hlower

private theorem upper_ne_lower' {n : ℕ} (i : Fin (n + 2))
    (s t : TypeII.{u} i) :
    SSet.S.mk (insertedSimplex.{u} i s) ≠
      SSet.S.mk t.1.simplex := by
  intro h
  have hut : upper.{u} i s = t.1 := by
    rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff]
  apply t.2
  rw [← hut]
  refine ⟨transition.{u} i s.1, ?_⟩
  change insertedObj.{u} i s (transition.{u} i s.1) =
    candidate.{u} i (upper.{u} i s)
  rw [insertedObj_transition, candidate_upper]

private def deletedSimplex {n d : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) (hd : x.dim = d + 1)
    (j : Fin (d + 2)) :
    (nerve (Face.{u} n)) _⦋d⦌ :=
  (nerve (Face.{u} n)).δ j (x.cast hd).simplex

private theorem deletedSimplex_obj {n d : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) (hd : x.dim = d + 1)
    (j : Fin (d + 2)) (k : Fin (d + 1)) :
    (deletedSimplex.{u} i x hd j).obj k =
      (x.cast hd).simplex.obj (j.succAbove k) :=
  rfl

private theorem deletedSimplex_nonDegenerate {n d : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (hd : x.dim = d + 1) (j : Fin (d + 2)) :
    deletedSimplex.{u} i x hd j ∈
      (nerve (Face.{u} n)).nonDegenerate d := by
  rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  exact (outside_strictMono i (x.cast hd)).comp
    (Fin.strictMono_succAbove j)

private theorem eq_univ_erase_of_union_singleton_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (A : Finset V) (hp : pivot ∉ A)
    (hA : A ∪ {pivot} = Finset.univ) :
    A = Finset.univ.erase pivot := by
  ext v
  by_cases hv : v = pivot
  · subst v
    simp [hp]
  · have hvU : v ∈ A ∪ {pivot} := by
      rw [hA]
      simp
    simp only [Finset.mem_union, Finset.mem_singleton, hv, or_false] at hvU
    simp [hv, hvU]

private theorem deletedSimplex_max_eq {n d : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (hd : x.dim = d + 1) (j : Fin (d + 2))
    (hocc : (x.cast hd).simplex.obj j =
      candidate.{u} i (x.cast hd)) :
    ((deletedSimplex.{u} i x hd j).obj (Fin.last d)).finset =
        missingFace.{u} i ∨
      ((deletedSimplex.{u} i x hd j).obj (Fin.last d)).finset =
        Finset.univ := by
  classical
  let y : (hornChains.{u} i).N := x.cast hd
  by_cases hlast : j = Fin.last (d + 1)
  · subst j
    left
    have hocc' : y.simplex.obj (Fin.last (d + 1)) =
        candidate.{u} i y := hocc
    have hpivotMax : distinguished.{u} i ∈
        (y.simplex.obj (Fin.last (d + 1))).finset := by
      rw [hocc']
      exact candidate_contains i y
    have hmax :
        (y.simplex.obj (Fin.last (d + 1))).finset = Finset.univ := by
      rcases outside_max_eq i y with hC | hU
      · have : distinguished.{u} i ∈ missingFace.{u} i := hC ▸ hpivotMax
        simp [missingFace] at this
      · exact hU
    have hp : (Fin.last (d + 1)).castSucc =
        transition.{u} i y :=
      candidate_occurs_at_transition i y hocc'
    let k : Fin (d + 2) := (Fin.last d).castSucc
    have hkBefore : k.castSucc < transition.{u} i y := by
      rw [← hp]
      change d < d + 1
      omega
    have hpivotNot : distinguished.{u} i ∉
        (y.simplex.obj k).finset :=
      not_contains_before i y hkBefore
    have hcand := candidate_finset_eq_transition i y
    rw [← hp] at hcand
    have hp0 : (Fin.last (d + 1)).castSucc ≠ 0 := by
      exact Fin.ne_of_gt (by
        change 0 < d + 1
        omega)
    rw [dite_eq_right hp0] at hcand
    have hpred : (Fin.last (d + 1)).castSucc.pred hp0 = k := by
      apply Fin.ext
      simp [k, Fin.val_pred]
    rw [hpred] at hcand
    have hcandU : (candidate.{u} i y).finset = Finset.univ := by
      rw [← hocc']
      exact hmax
    have hk : (y.simplex.obj k).finset = missingFace.{u} i := by
      rw [missingFace]
      exact eq_univ_erase_of_union_singleton_eq_univ
        (distinguished.{u} i) _ hpivotNot (hcand.symm.trans hcandU)
    rw [deletedSimplex_obj, Fin.succAbove_last_apply]
    exact hk
  · rcases outside_max_eq i y with hC | hU
    · left
      rw [deletedSimplex_obj, Fin.succAbove_ne_last_last hlast]
      exact hC
    · right
      rw [deletedSimplex_obj, Fin.succAbove_ne_last_last hlast]
      exact hU

private theorem deletedSimplex_notMem {n d : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (hd : x.dim = d + 1) (j : Fin (d + 2))
    (hocc : (x.cast hd).simplex.obj j =
      candidate.{u} i (x.cast hd)) :
    deletedSimplex.{u} i x hd j ∉ (hornChains.{u} i).obj _ := by
  rw [mem_hornChains_iff_last]
  intro hAllowed
  apply hAllowed
  rcases deletedSimplex_max_eq i x hd j hocc with hC | hU
  · rw [hC]
  · rw [hU]
    exact Finset.subset_univ _

private noncomputable abbrev deleted {n d : ℕ} (i : Fin (n + 2))
    (x : (hornChains.{u} i).N) (hd : x.dim = d + 1)
    (j : Fin (d + 2))
    (hocc : (x.cast hd).simplex.obj j =
      candidate.{u} i (x.cast hd)) :
    (hornChains.{u} i).N :=
  Subcomplex.N.mk (deletedSimplex.{u} i x hd j)
    (deletedSimplex_nonDegenerate i x hd j)
    (deletedSimplex_notMem i x hd j hocc)

private theorem transition_deleted {n d : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (hd : x.dim = d + 1) (j : Fin (d + 2))
    (hocc : (x.cast hd).simplex.obj j =
      candidate.{u} i (x.cast hd)) :
    transition.{u} i (deleted.{u} i x hd j hocc) = j := by
  classical
  let y : (hornChains.{u} i).N := x.cast hd
  let z : (hornChains.{u} i).N := deleted.{u} i x hd j hocc
  have hp : j.castSucc = transition.{u} i y :=
    candidate_occurs_at_transition i y hocc
  by_cases hlast : j = Fin.last (d + 1)
  · subst j
    apply transition_eq_of_not_exists i z
    rintro ⟨r, hr⟩
    have hbefore :
        ¬contains.{u} i y r.castSucc := by
      apply not_contains_before i y
      rw [← hp]
      change r.val < d + 1
      exact r.isLt
    apply hbefore
    change distinguished.{u} i ∈
      ((deletedSimplex.{u} i x hd (Fin.last (d + 1))).obj r).finset at hr
    rw [deletedSimplex_obj, Fin.succAbove_last_apply] at hr
    exact hr
  · let r : Fin (d + 1) := j.castPred hlast
    have hrj : r.castSucc = j := Fin.castSucc_castPred j hlast
    have hrContains : contains.{u} i z r := by
      change distinguished.{u} i ∈
        ((deletedSimplex.{u} i x hd j).obj r).finset
      rw [deletedSimplex_obj, Fin.succAbove_castPred_self]
      apply contains_from_transition i y
      rw [← hp]
      change j.val ≤ r.succ.val
      simp [r]
    have hex : ∃ k, contains.{u} i z k := ⟨r, hrContains⟩
    rw [transition_eq_of_exists i z hex]
    have hfind : Fin.find (contains.{u} i z) hex = r := by
      apply (Fin.find_eq_iff hex).2
      refine ⟨hrContains, ?_⟩
      intro k hk hbad
      have hkj : k.castSucc < j := by
        rw [← hrj]
        exact Fin.castSucc_lt_castSucc_iff.2 hk
      have hbefore :
          ¬contains.{u} i y (j.succAbove k) := by
        apply not_contains_before i y
        rw [← hp]
        exact Fin.castSucc_lt_castSucc_iff.2
          (by
            rw [Fin.succAbove_of_castSucc_lt j k hkj]
            exact hkj)
      apply hbefore
      change distinguished.{u} i ∈
        ((deletedSimplex.{u} i x hd j).obj k).finset at hbad
      rw [deletedSimplex_obj] at hbad
      exact hbad
    rw [hfind]
    apply Fin.ext
    exact congrArg Fin.val hrj

private theorem candidate_deleted {n d : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (hd : x.dim = d + 1) (j : Fin (d + 2))
    (hocc : (x.cast hd).simplex.obj j =
      candidate.{u} i (x.cast hd)) :
    candidate.{u} i (deleted.{u} i x hd j hocc) =
      candidate.{u} i (x.cast hd) := by
  classical
  let y : (hornChains.{u} i).N := x.cast hd
  let z : (hornChains.{u} i).N := deleted.{u} i x hd j hocc
  have hp : j.castSucc = transition.{u} i y :=
    candidate_occurs_at_transition i y hocc
  apply NonemptyFiniteChains.ext
  rw [candidate_finset_eq_transition,
    candidate_finset_eq_transition, transition_deleted, ← hp]
  by_cases hj : j = 0
  · subst j
    simp
  · have hj' : j.castSucc ≠ 0 := by
      intro h0
      apply hj
      apply Fin.ext
      simpa using congrArg Fin.val h0
    rw [dite_eq_right hj, dite_eq_right hj']
    have hk : j.succAbove (j.pred hj) = j.castSucc.pred hj' := by
      rw [Fin.succAbove_pred_self]
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_pred]
    change ((deletedSimplex.{u} i x hd j).obj (j.pred hj)).finset ∪
        {distinguished.{u} i} =
      (y.simplex.obj (j.castSucc.pred hj')).finset ∪
        {distinguished.{u} i}
    rw [deletedSimplex_obj, hk]

private theorem deleted_not_candidatePresent {n d : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (hd : x.dim = d + 1) (j : Fin (d + 2))
    (hocc : (x.cast hd).simplex.obj j =
      candidate.{u} i (x.cast hd)) :
    ¬CandidatePresent.{u} i (deleted.{u} i x hd j hocc) := by
  rintro ⟨r, hr⟩
  have hinj : Function.Injective (x.cast hd).simplex.obj :=
    (outside_strictMono i (x.cast hd)).injective
  apply Fin.succAbove_ne j r
  apply hinj
  calc
    (x.cast hd).simplex.obj (j.succAbove r) =
        (deleted.{u} i x hd j hocc).simplex.obj r := rfl
    _ = candidate.{u} i (deleted.{u} i x hd j hocc) := hr
    _ = candidate.{u} i (x.cast hd) :=
      candidate_deleted i x hd j hocc
    _ = (x.cast hd).simplex.obj j := hocc.symm

private noncomputable abbrev deletedTypeII {n d : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (hd : x.dim = d + 1) (j : Fin (d + 2))
    (hocc : (x.cast hd).simplex.obj j =
      candidate.{u} i (x.cast hd)) :
    TypeII.{u} i :=
  ⟨deleted.{u} i x hd j hocc,
    deleted_not_candidatePresent i x hd j hocc⟩

private theorem upper_deletedTypeII {n d : ℕ}
    (i : Fin (n + 2)) (x : (hornChains.{u} i).N)
    (hd : x.dim = d + 1) (j : Fin (d + 2))
    (hocc : (x.cast hd).simplex.obj j =
      candidate.{u} i (x.cast hd)) :
    upper.{u} i (deletedTypeII.{u} i x hd j hocc) = x.cast hd := by
  rw [Subcomplex.N.ext_iff, SSet.N.ext_iff, SSet.S.ext_iff']
  refine ⟨rfl, ?_⟩
  change insertedSimplex.{u} i (deletedTypeII.{u} i x hd j hocc) =
    (x.cast hd).simplex
  apply CategoryTheory.nerve.ext_of_isThin
  funext k
  have htuple :
      insertedObj.{u} i (deletedTypeII.{u} i x hd j hocc) =
        (x.cast hd).simplex.obj := by
    unfold insertedObj
    rw [transition_deleted, candidate_deleted]
    · change Fin.insertNth (α := fun _ => Face.{u} n) j
          (candidate.{u} i (x.cast hd))
          (Fin.removeNth j (x.cast hd).simplex.obj) =
        (x.cast hd).simplex.obj
      rw [← hocc]
      exact Fin.insertNth_self_removeNth
        (α := fun _ => Face.{u} n) j (x.cast hd).simplex.obj
    all_goals exact hocc
  exact congrFun htuple k

private noncomputable abbrev pairingCore {n : ℕ} (i : Fin (n + 2)) :
    (hornChains.{u} i).PairingCore where
  ι := TypeII.{u} i
  dim s := s.1.dim
  simplex s := insertedSimplex.{u} i s
  index s := transition.{u} i s.1
  nonDegenerate₁ s := insertedSimplex_nonDegenerate i s
  nonDegenerate₂ s := by
    rw [insertedSimplex_δ]
    exact s.1.nonDegenerate
  notMem₁ s := insertedSimplex_notMem i s
  notMem₂ s := by
    rw [insertedSimplex_δ]
    exact s.1.notMem
  injective_type₁' h := upper_injective' i h
  injective_type₂' {s t} h := by
    rw [insertedSimplex_δ, insertedSimplex_δ] at h
    apply Subtype.ext
    rwa [Subcomplex.N.eq_iff_sMk_eq]
  type₁_ne_type₂' s t h := by
    apply upper_ne_lower' i s t
    rwa [insertedSimplex_δ] at h
  surjective' x := by
    by_cases hx : CandidatePresent.{u} i x
    · have hpos : 0 < x.dim := dim_pos_of_candidatePresent i x hx
      obtain ⟨d, hd⟩ : ∃ d, x.dim = d + 1 := by
        exact ⟨x.dim - 1, by omega⟩
      have hx' : CandidatePresent.{u} i (x.cast hd) := by
        simpa only [x.cast_eq_self] using hx
      obtain ⟨j, hj⟩ := hx'
      let s : TypeII.{u} i := deletedTypeII.{u} i x hd j hj
      refine ⟨s, Or.inl ?_⟩
      have hu : upper.{u} i s = x :=
        (upper_deletedTypeII i x hd j hj).trans (x.cast_eq_self hd)
      exact (congrArg
        (fun z : (hornChains.{u} i).N => z.toN.toS) hu).symm
    · let s : TypeII.{u} i := ⟨x, hx⟩
      refine ⟨s, Or.inr ?_⟩
      rw [insertedSimplex_δ]

private theorem pairingCore_type₁ {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    (pairingCore.{u} i).type₁ s = upper.{u} i s :=
  rfl

private theorem pairingCore_type₂ {n : ℕ} (i : Fin (n + 2))
    (s : TypeII.{u} i) :
    (pairingCore.{u} i).type₂ s = s.1 := by
  rw [Subcomplex.N.eq_iff_sMk_eq, SSet.S.ext_iff]
  exact insertedSimplex_δ i s

private theorem obj_eq_removeNth_of_lt_dim_succ
    {P : Type u} [PartialOrder P] {d : ℕ}
    {s : (nerve P) _⦋d⦌} {t : (nerve P) _⦋d + 1⦌}
    (hs : s ∈ (nerve P).nonDegenerate d)
    (ht : t ∈ (nerve P).nonDegenerate (d + 1))
    (hst : SSet.N.mk s hs < SSet.N.mk t ht) :
    ∃ q : Fin (d + 2),
      s.obj = Fin.removeNth (α := fun _ => P) q t.obj := by
  obtain ⟨f, hf, hmap⟩ := SSet.N.le_iff_exists_mono.mp hst.le
  obtain ⟨q, rfl⟩ := @SimplexCategory.eq_δ_of_mono d f hf
  refine ⟨q, ?_⟩
  funext j
  have hj := congrArg (fun z => z.obj j) hmap
  change t.obj (q.succAbove j) = s.obj j at hj
  simpa only [Fin.removeNth_apply] using hj.symm

private theorem transition_lt_of_ancestral {n : ℕ}
    (i : Fin (n + 2)) {s t : TypeII.{u} i}
    (hAnc : (pairingCore.{u} i).AncestralRel s t)
    (hdim : (pairingCore.{u} i).dim s =
      (pairingCore.{u} i).dim t) :
    (transition.{u} i s.1).val < (transition.{u} i t.1).val := by
  change s.1.dim = t.1.dim at hdim
  have httProp : ¬CandidatePresent.{u} i
      (t.1.cast hdim.symm) := by
    simpa only [t.1.cast_eq_self] using t.2
  let tt : TypeII.{u} i := ⟨t.1.cast hdim.symm, httProp⟩
  have htt : tt = t := by
    apply Subtype.ext
    exact t.1.cast_eq_self hdim.symm
  rw [← htt] at hAnc ⊢
  have hst : s.1 < upper.{u} i tt := by
    simpa only [pairingCore_type₁, pairingCore_type₂] using hAnc.2
  have hstN : s.1.toN < (upper.{u} i tt).toN := hst
  obtain ⟨q, hq⟩ := obj_eq_removeNth_of_lt_dim_succ
    s.1.nonDegenerate (insertedSimplex_nonDegenerate i tt) hstN
  let p := transition.{u} i tt.1
  have hcontains : contains.{u} i s.1 =
      fun k => contains.{u} i (upper.{u} i tt) (q.succAbove k) := by
    funext k
    apply propext
    change distinguished.{u} i ∈ (s.1.simplex.obj k).finset ↔
      distinguished.{u} i ∈
        (insertedObj.{u} i tt (q.succAbove k)).finset
    rw [congrFun hq k]
    rfl
  by_cases hqp : q = p
  · have hobj : s.1.simplex.obj = tt.1.simplex.obj := by
      calc
        s.1.simplex.obj =
            Fin.removeNth q (insertedObj.{u} i tt) := hq
        _ = tt.1.simplex.obj := by
          subst q
          exact Fin.removeNth_insertNth
            (α := fun _ => Face.{u} n) p
            (candidate.{u} i tt.1) tt.1.simplex.obj
    have hsimp : s.1.simplex = tt.1.simplex :=
      CategoryTheory.nerve.ext_of_isThin hobj
    have hstEq : s = tt := by
      apply Subtype.ext
      rw [Subcomplex.N.eq_iff_sMk_eq, SSet.S.ext_iff]
      exact hsimp
    exact (hAnc.1 hstEq).elim
  · rcases lt_or_gt_of_ne hqp with hqp | hpq
    · have hp0 : p ≠ 0 :=
        Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le q) hqp)
      have htrans : transition.{u} i s.1 = (p.pred hp0).castSucc := by
        rw [transition_eq_firstIndex, hcontains]
        exact firstIndex_remove_before
          (contains.{u} i (upper.{u} i tt)) p q hqp
          (upper_contains_transition i tt)
          (fun j hj => upper_not_contains_before i tt hj)
      rw [htrans]
      change p.val - 1 < p.val
      omega
    · have htrans : transition.{u} i s.1 = p := by
        rw [transition_eq_firstIndex, hcontains]
        exact firstIndex_remove_after
          (contains.{u} i (upper.{u} i tt)) p q hpq
          (upper_contains_transition i tt)
          (fun j hj => upper_not_contains_before i tt hj)
      have hcand : candidate.{u} i s.1 = candidate.{u} i tt.1 := by
        classical
        apply NonemptyFiniteChains.ext
        rw [candidate_finset_eq_transition,
          candidate_finset_eq_transition, htrans]
        change (if hp : p = 0 then {distinguished.{u} i}
          else (s.1.simplex.obj (p.pred hp)).finset ∪
            {distinguished.{u} i}) =
          if hp : p = 0 then {distinguished.{u} i}
          else (tt.1.simplex.obj (p.pred hp)).finset ∪
            {distinguished.{u} i}
        by_cases hp0 : p = 0
        · simp [hp0]
        · rw [dite_eq_right hp0, dite_eq_right hp0]
          have ha := congrFun hq (p.pred hp0)
          rw [Fin.removeNth_apply] at ha
          have hpred : (p.pred hp0).castSucc < q := by
            have hppred : (p.pred hp0).castSucc < p := by
              change p.val - 1 < p.val
              have hpv : p.val ≠ 0 := by
                intro hpv
                apply hp0
                apply Fin.ext
                simpa using hpv
              omega
            exact hppred.trans hpq
          rw [Fin.succAbove_of_castSucc_lt q (p.pred hp0) hpred,
            ← Fin.succAbove_pred_self p hp0] at ha
          change s.1.simplex.obj (p.pred hp0) =
            insertedObj.{u} i tt (p.succAbove (p.pred hp0)) at ha
          change (s.1.simplex.obj (p.pred hp0)).finset ∪
              {distinguished.{u} i} =
            (tt.1.simplex.obj (p.pred hp0)).finset ∪
              {distinguished.{u} i}
          rw [ha]
          unfold insertedObj
          rw [Fin.insertNth_apply_succAbove]
      exfalso
      apply s.2
      obtain heq | ⟨r, hr⟩ := Fin.eq_self_or_eq_succAbove q p
      · exact (hqp heq.symm).elim
      · refine ⟨r, ?_⟩
        have hrObj := congrFun hq r
        rw [Fin.removeNth_apply, ← hr] at hrObj
        change s.1.simplex.obj r = insertedObj.{u} i tt p at hrObj
        rw [insertedObj_transition] at hrObj
        exact hrObj.trans hcand.symm

private noncomputable def weakRank {n : ℕ} (i : Fin (n + 2)) :
    (pairingCore.{u} i).WeakRankFunction ℕ where
  rank s := (transition.{u} i s.1).val
  lt hAnc hdim := transition_lt_of_ancestral i hAnc hdim

private noncomputable instance pairingCore_isRegular {n : ℕ}
    (i : Fin (n + 2)) :
    (pairingCore.{u} i).IsRegular :=
  ((pairingCore.{u} i).isRegular_iff_nonempty_weakRankFunction).2
    ⟨weakRank.{u} i⟩

private theorem anodyne_hornChains_ι {n : ℕ} (i : Fin (n + 2)) :
    anodyneExtensions (hornChains.{u} i).ι :=
  (pairingCore.{u} i).pairing.anodyneExtensions

private noncomputable def faceOrderIso (n : ℕ) :
    (Δ[n + 1] : SSet.{u}).N ≃o Face.{u} n :=
  (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} (n + 1))).trans
    (PartOrd.nerveNOrderIso (PartOrd.of (Vertex.{u} n)))

private theorem mem_faceOrderIso_finset {n : ℕ}
    (x : (Δ[n + 1] : SSet.{u}).N) (v : Vertex.{u} n) :
    v ∈ (faceOrderIso.{u} n x).finset ↔
      ∃ j, ULift.up (x.simplex j) = v := by
  rw [faceOrderIso, OrderIso.trans_apply,
    PartOrd.mem_nerveNOrderIso_finset]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change ((SSet.stdSimplex.isoNerve.{u} (n + 1)).hom.app _
      x.simplex).obj j = v at hj
    exact (SSet.stdSimplex.isoNerve_hom_app_apply x.simplex j).symm.trans hj
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    change ((SSet.stdSimplex.isoNerve.{u} (n + 1)).hom.app _
      x.simplex).obj j = ULift.up (x.simplex j)
    exact SSet.stdSimplex.isoNerve_hom_app_apply _ _

private noncomputable def faceFinset {n : ℕ} (x : (Δ[n + 1] : SSet.{u}).N) :
    Finset (Fin (n + 2)) :=
  (faceOrderIso.{u} n x).finset.image ULift.down

private theorem mem_faceFinset_iff {n : ℕ}
    (x : (Δ[n + 1] : SSet.{u}).N) (v : Fin (n + 2)) :
    v ∈ faceFinset.{u} x ↔ ∃ j, x.simplex j = v := by
  classical
  rw [faceFinset, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨j, hj⟩ := (mem_faceOrderIso_finset x w).1 hw
    exact ⟨j, ULift.up_injective hj⟩
  · rintro ⟨j, rfl⟩
    exact ⟨ULift.up (x.simplex j),
      (mem_faceOrderIso_finset x _).2 ⟨j, rfl⟩, rfl⟩

private theorem faceFinset_eq_nonDegenerateEquiv {n : ℕ}
    (x : (Δ[n + 1] : SSet.{u}).N) :
    faceFinset.{u} x =
      (SSet.stdSimplex.nonDegenerateEquiv'
        ⟨x.simplex, x.nonDegenerate⟩).val := by
  classical
  ext v
  rw [mem_faceFinset_iff,
    SSet.stdSimplex.nonDegenerateEquiv'_iff]

private theorem mem_down_image_iff {n : ℕ} (S : Face.{u} n)
    (v : Fin (n + 2)) :
    v ∈ S.finset.image ULift.down ↔ ULift.up v ∈ S.finset := by
  classical
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hwv⟩
    have : w = ULift.up v := by
      apply ULift.down_injective
      simpa using hwv
    simpa [this] using hw
  · intro hv
    exact ⟨ULift.up v, hv, rfl⟩

private theorem missing_subset_iff {n : ℕ} (i : Fin (n + 2))
    (S : Face.{u} n) :
    missingFace.{u} i ⊆ S.finset ↔
      Finset.univ.erase i ⊆ S.finset.image ULift.down := by
  classical
  constructor
  · intro h v hv
    rw [mem_down_image_iff]
    apply h
    simpa [missingFace, distinguished] using hv
  · intro h v hv
    have hv0 : v ≠ ULift.up i := by
      rw [missingFace, distinguished, Finset.mem_erase] at hv
      exact hv.1
    have hv' : v.down ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hvi
      apply hv0
      apply ULift.down_injective
      simpa using hvi
    have := h hv'
    rw [mem_down_image_iff] at this
    simpa using this

private theorem erase_subset_iff_eq {n : ℕ} (i : Fin (n + 2))
    (D : Finset (Fin (n + 2))) :
    Finset.univ.erase i ⊆ D ↔
      D = Finset.univ.erase i ∨ D = Finset.univ := by
  classical
  constructor
  · intro h
    by_cases hi : i ∈ D
    · right
      apply Finset.eq_univ_of_forall
      intro v
      by_cases hvi : v = i
      · simpa [hvi] using hi
      · exact h (by simp [hvi])
    · left
      apply Finset.Subset.antisymm
      · intro v hv
        have hvi : v ≠ i := by
          rintro rfl
          exact hi hv
        simp [hvi]
      · exact h
  · rintro (rfl | rfl)
    · exact fun _ h => h
    · exact Finset.subset_univ _

private theorem allowed_iff {n : ℕ} (i : Fin (n + 2))
    (S : Face.{u} n) :
    Allowed.{u} i S ↔
      S.finset.image ULift.down ≠ Finset.univ ∧
        S.finset.image ULift.down ≠ {i}ᶜ := by
  classical
  have hcompl : ({i}ᶜ : Finset (Fin (n + 2))) =
      Finset.univ.erase i := by
    ext v
    simp
  rw [Allowed, missing_subset_iff, erase_subset_iff_eq, not_or]
  constructor
  · rintro ⟨hC, hU⟩
    exact ⟨hU, by simpa [hcompl] using hC⟩
  · rintro ⟨hU, hC⟩
    exact ⟨by simpa [hcompl] using hC, hU⟩

private theorem allowed_faceOrderIso_iff {n : ℕ} (i : Fin (n + 2))
    (x : (Δ[n + 1] : SSet.{u}).N) :
    Allowed.{u} i (faceOrderIso.{u} n x) ↔
      x.simplex ∈ (horn.{u} (n + 1) i).obj _ := by
  rw [allowed_iff]
  change faceFinset.{u} x ≠ Finset.univ ∧
      faceFinset.{u} x ≠ {i}ᶜ ↔ _
  rw [faceFinset_eq_nonDegenerateEquiv,
    ← SSet.face_le_horn_iff,
    SSet.stdSimplex.face_nonDegenerateEquiv',
    Subcomplex.ofSimplex_le_iff]

private theorem N_map_le_iff_of_mono {X Y : SSet.{u}}
    (f : X ⟶ Y) [Mono f] (x y : X.N) :
    SSet.N.map f x ≤ SSet.N.map f y ↔ x ≤ y := by
  rw [SSet.N.le_iff, SSet.N.le_iff,
    SSet.N.map_subcomplex, SSet.N.map_subcomplex,
    SSet.Subcomplex.image_le_image_iff]

private noncomputable def hornFaceOrderEmbedding {n : ℕ} (i : Fin (n + 2)) :
    (horn.{u} (n + 1) i : SSet.{u}).N ↪o H.{u} i where
  toFun x :=
    ⟨faceOrderIso.{u} n
      (SSet.N.map (horn.{u} (n + 1) i).ι x), by
      rw [allowed_faceOrderIso_iff]
      have hnon :
          (horn.{u} (n + 1) i).ι.app _ x.simplex ∈
            (Δ[n + 1] : SSet.{u}).nonDegenerate x.dim :=
        (SSet.nonDegenerate_iff_of_mono
          (horn.{u} (n + 1) i).ι x.simplex).2 x.nonDegenerate
      rw [SSet.N.map_eq_mk _ _ hnon]
      exact x.simplex.property⟩
  inj' x y hxy := by
    have hmap :
        SSet.N.map (horn.{u} (n + 1) i).ι x =
          SSet.N.map (horn.{u} (n + 1) i).ι y := by
      apply (faceOrderIso.{u} n).injective
      exact congrArg Subtype.val hxy
    apply le_antisymm
    · exact (N_map_le_iff_of_mono _ _ _).1 hmap.le
    · exact (N_map_le_iff_of_mono _ _ _).1 hmap.ge
  map_rel_iff' {x y} := by
    change faceOrderIso.{u} n
        (SSet.N.map (horn.{u} (n + 1) i).ι x) ≤
      faceOrderIso.{u} n
        (SSet.N.map (horn.{u} (n + 1) i).ι y) ↔ x ≤ y
    rw [(faceOrderIso.{u} n).le_iff_le,
      N_map_le_iff_of_mono]

private theorem hornFaceOrderEmbedding_surjective {n : ℕ}
    (i : Fin (n + 2)) :
    Function.Surjective (hornFaceOrderEmbedding.{u} i) := by
  intro S
  let y : (Δ[n + 1] : SSet.{u}).N :=
    (faceOrderIso.{u} n).symm S.1
  have hyMem : y.simplex ∈ (horn.{u} (n + 1) i).obj _ := by
    rw [← allowed_faceOrderIso_iff]
    simpa [y] using S.2
  let xs : (horn.{u} (n + 1) i).obj _ := ⟨y.simplex, hyMem⟩
  have hxnon : xs ∈
      (horn.{u} (n + 1) i : SSet.{u}).nonDegenerate y.dim :=
    (Subcomplex.mem_nonDegenerate_iff _ _).2 y.nonDegenerate
  let x : (horn.{u} (n + 1) i : SSet.{u}).N :=
    SSet.N.mk xs hxnon
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change faceOrderIso.{u} n
      (SSet.N.map (horn.{u} (n + 1) i).ι x) = S.1
  rw [show S.1 = faceOrderIso.{u} n y by simp [y]]
  congr 1
  have hnon :
      (horn.{u} (n + 1) i).ι.app _ x.simplex ∈
        (Δ[n + 1] : SSet.{u}).nonDegenerate x.dim :=
    (SSet.nonDegenerate_iff_of_mono
      (horn.{u} (n + 1) i).ι x.simplex).2 x.nonDegenerate
  rw [SSet.N.map_eq_mk _ _ hnon, SSet.N.ext_iff]
  rfl

private noncomputable def hornFaceOrderIso {n : ℕ} (i : Fin (n + 2)) :
    (horn.{u} (n + 1) i : SSet.{u}).N ≃o H.{u} i :=
  OrderIso.ofSurjective (hornFaceOrderEmbedding.{u} i)
    (hornFaceOrderEmbedding_surjective.{u} i)

private theorem hornFaceOrderIso_hom_comp_jHOrd {n : ℕ}
    (i : Fin (n + 2)) :
    (PartOrd.Iso.mk (hornFaceOrderIso.{u} i)).hom ≫ jHOrd.{u} i =
      SSet.N.functor.map (horn.{u} (n + 1) i).ι ≫
        (PartOrd.Iso.mk (faceOrderIso.{u} n)).hom := by
  apply PartOrd.ext
  intro x
  rfl

private noncomputable def hornFacePartOrdIso {n : ℕ}
    (i : Fin (n + 2)) :
    SSet.N.functor.obj (horn.{u} (n + 1) i) ≅ PartOrd.of (H.{u} i) :=
  PartOrd.Iso.mk (hornFaceOrderIso.{u} i)

private noncomputable def facePartOrdIso (n : ℕ) :
    SSet.N.functor.obj (Δ[n + 1] : SSet.{u}) ≅
      PartOrd.of (Face.{u} n) :=
  PartOrd.Iso.mk (faceOrderIso.{u} n)

private theorem hornFacePartOrdIso_hom_comp_jHOrd {n : ℕ}
    (i : Fin (n + 2)) :
    (hornFacePartOrdIso.{u} i).hom ≫ jHOrd.{u} i =
      SSet.N.functor.map (horn.{u} (n + 1) i).ι ≫
        (facePartOrdIso.{u} n).hom :=
  hornFaceOrderIso_hom_comp_jHOrd i

private noncomputable def hRangeIso {n : ℕ} (i : Fin (n + 2)) :
    nerve (H.{u} (n := n) i) ≅ hornChains.{u} (n := n) i := by
  haveI : Mono (hMap.{u} (n := n) i) := hMap_mono i
  let m : nerve (H.{u} (n := n) i) ⟶
      hornChains.{u} (n := n) i :=
    Subcomplex.toRange (hMap.{u} (n := n) i)
  haveI : Epi m := by
    dsimp [m]
    exact inferInstanceAs
      (Epi (Subfunctor.toRange (hMap.{u} (n := n) i)))
  haveI : Mono m := by
    dsimp [m]
    exact mono_of_mono_fac
      (Subcomplex.toRange_ι (hMap.{u} (n := n) i))
  haveI : IsIso m := by
    exact isIso_of_mono_of_epi m
  exact asIso m

private theorem hRangeIso_hom {n : ℕ} (i : Fin (n + 2)) :
    (hRangeIso.{u} i).hom =
      Subcomplex.toRange (hMap.{u} (n := n) i) := by
  rfl

private noncomputable def eSrc {n : ℕ} (i : Fin (n + 2)) :
    SSet.sd.obj (horn.{u} (n + 1) i) ≅
      hornChains.{u} (n := n) i :=
  SSet.sdIsoNondegenerateNerve (horn.{u} (n + 1) i) ≪≫
    PartOrd.nerveFunctor.mapIso (hornFacePartOrdIso.{u} i) ≪≫
    hRangeIso.{u} i

private noncomputable def eTgt (n : ℕ) :
    SSet.sd.obj (Δ[n + 1] : SSet.{u}) ≅ nerve (Face.{u} n) :=
  SSet.sdIsoNondegenerateNerve (Δ[n + 1] : SSet.{u}) ≪≫
    PartOrd.nerveFunctor.mapIso
      (facePartOrdIso.{u} n)

set_option backward.isDefEq.respectTransparency false in
private theorem eSrc_hom {n : ℕ} (i : Fin (n + 2)) :
    (eSrc.{u} i).hom =
      SSet.sdToNondegenerateNerve.app (horn.{u} (n + 1) i) ≫
        PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom ≫
          (hRangeIso.{u} i).hom := by
  rw [eSrc]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [SSet.sdIsoNondegenerateNerve_hom]

set_option backward.isDefEq.respectTransparency false in
private theorem eTgt_hom (n : ℕ) :
    (eTgt.{u} n).hom =
      SSet.sdToNondegenerateNerve.app (Δ[n + 1] : SSet.{u}) ≫
        PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom := by
  rw [eTgt]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [SSet.sdIsoNondegenerateNerve_hom]

set_option backward.isDefEq.respectTransparency false in
private theorem hornFacePartOrd_square {n : ℕ} (i : Fin (n + 2)) :
    PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom ≫
        hMap.{u} i =
      SSet.nondegenerateNerve.map (horn.{u} (n + 1) i).ι ≫
        PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom := by
  change PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom ≫
      PartOrd.nerveFunctor.map (jHOrd.{u} i) =
    PartOrd.nerveFunctor.map
        (SSet.N.functor.map (horn.{u} (n + 1) i).ι) ≫
      PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom
  rw [← Functor.map_comp, hornFacePartOrdIso_hom_comp_jHOrd,
    Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem eSrc_hom_comp_ι {n : ℕ} (i : Fin (n + 2)) :
    (eSrc.{u} i).hom ≫ (hornChains.{u} i).ι =
      SSet.sd.map (horn.{u} (n + 1) i).ι ≫ (eTgt.{u} n).hom := by
  rw [eSrc_hom, eTgt_hom]
  change (SSet.sdToNondegenerateNerve.app (horn.{u} (n + 1) i) ≫
      PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom ≫
      (hRangeIso.{u} i).hom) ≫
      (Subcomplex.range (hMap.{u} i)).ι = _
  calc
    (SSet.sdToNondegenerateNerve.app (horn.{u} (n + 1) i) ≫
          PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom ≫
          (hRangeIso.{u} i).hom) ≫
        (Subcomplex.range (hMap.{u} i)).ι =
        SSet.sdToNondegenerateNerve.app (horn.{u} (n + 1) i) ≫
          PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom ≫
          hMap.{u} i := by
      rw [hRangeIso_hom]
      simpa only [Category.assoc] using congrArg
        (fun k => SSet.sdToNondegenerateNerve.app
            (horn.{u} (n + 1) i) ≫
          PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom ≫ k)
        (Subcomplex.toRange_ι (hMap.{u} i))
    _ = SSet.sdToNondegenerateNerve.app (horn.{u} (n + 1) i) ≫
        SSet.nondegenerateNerve.map (horn.{u} (n + 1) i).ι ≫
        PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => SSet.sdToNondegenerateNerve.app
          (horn.{u} (n + 1) i) ≫ k)
        (hornFacePartOrd_square.{u} i)
    _ = (SSet.sd.map (horn.{u} (n + 1) i).ι ≫
          SSet.sdToNondegenerateNerve.app (Δ[n + 1] : SSet.{u})) ≫
        PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫
          PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom)
        (SSet.sdToNondegenerateNerve.naturality
          (horn.{u} (n + 1) i).ι).symm

end subdivisionHorn

/-- Subdivision sends every horn inclusion to an anodyne extension. -/
theorem anodyneExtensions_sd_map_horn_ι (n : ℕ) (i : Fin (n + 2)) :
    anodyneExtensions.{u} (sd.map (horn.{u} (n + 1) i).ι) := by
  exact (anodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (subdivisionHorn.eSrc.{u} i)
      (subdivisionHorn.eTgt.{u} n)
      (subdivisionHorn.eSrc_hom_comp_ι.{u} i))).2
    (subdivisionHorn.anodyne_hornChains_ι.{u} i)

/-- The Ex image of a simplicial fibration is again a fibration. -/
noncomputable instance instFibrationExMap {X Y : SSet.{u}}
    (p : X ⟶ Y) [Fibration p] : Fibration (ex.map p) := by
  rw [modelCategoryQuillen.fibration_iff]
  intro A B g hg
  simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hg
  obtain ⟨n, ⟨i⟩⟩ := hg
  exact (sdExAdjunction.hasLiftingProperty_iff
    (horn.{u} (n + 1) i).ι p).mp
      ((anodyneExtensions_sd_map_horn_ι n i) p
        (HomotopicalAlgebra.mem_fibrations p))

/-- Subdivision preserves arbitrary anodyne extensions. -/
theorem anodyneExtensions.sd_map {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : anodyneExtensions f) : anodyneExtensions (sd.map f) := by
  intro E B p hp
  let _ : Fibration p := ⟨hp⟩
  let _ : Fibration (ex.map p) := instFibrationExMap p
  exact (sdExAdjunction.hasLiftingProperty_iff f p).mpr
    (hf (ex.map p) (HomotopicalAlgebra.mem_fibrations (ex.map p)))

/-- Every finite iterate of subdivision preserves anodyne extensions. -/
theorem anodyneExtensions.sdIter_map {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : anodyneExtensions f) (k : ℕ) :
    anodyneExtensions ((sdIter k).map f) := by
  induction k with
  | zero =>
      rw [sdIter_map_zero]
      exact hf
  | succ k ih =>
      rw [sdIter_map_succ]
      exact anodyneExtensions.sd_map ih

end SSet
