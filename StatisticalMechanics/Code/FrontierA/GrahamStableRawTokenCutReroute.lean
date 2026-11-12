/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamMaskFiberMiddleReversal
import Code.FrontierA.GrahamTightFamilyCutParity












open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]





theorem canonicalStableOccupiedAlternate_opposingCuts_or_twoRow
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p c.1 c.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p d⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    let a := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p c.1 hc
    let owner := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p b.1 hb
    let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩
    CanonicalOpposingRootCutsAtRight
        ends m j k l zero p a owner q ∨
      CanonicalTightTwoRowCollision ends m j k l zero p a owner := by
  classical
  dsimp only
  obtain ⟨hcEdge, hdEdge, hqc⟩ := hcd
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p d,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p d⟩
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let hb := canonicalRawCommonClosure_leftGate
    ends m j k l zero p b.1 b.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let owner := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p b.1 hb
  let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p).symm ⟨d.1, hdEdge⟩
  have haowner : a ≠ owner := by
    intro h
    apply hne
    apply Subtype.ext
    exact congrArg (fun x => x.1.1) h
  have hqa : q ∈ canonicalMaskRightImages
      ends m j k l zero p a := by
    simpa only [q, a] using hqc
  have hbrel := canonicalStableRawPreferredRightBase_related
    ends m j k l zero hloop hjk hkl hk0 p d
  obtain ⟨hbEdge, hdOwner, hqowner⟩ := hbrel
  have hqo : q ∈ canonicalMaskRightImages
      ends m j k l zero p owner := by
    simpa only [q, owner, b] using hqowner
  exact canonicalCommonImage_opposingAtRight_or_twoCommon
    hloop hjk hkl a owner haowner q hqa hqo




theorem canonicalStableRawRightTarget_memClosure_or_positive
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    d.1 ∈ canonicalRawCommonClosure ends m j k l zero p ∨
      ReversalGatePositive ends m j k l zero p d.1 := by
  classical
  obtain ⟨source, hsource, hrelated⟩ :=
    (Finset.mem_filter.mp d.2).2
  obtain ⟨_, hdRight, _⟩ := hrelated
  by_cases hdLeft : RowsDisconnect ends m d.1.1 k zero
  · exact Or.inl
      ((canonicalRawCommonClosure_right_iff_neighborhood_left
        ends m j k l zero p d.1).mpr ⟨d.2, hdLeft⟩).1
  · exact Or.inr ⟨hdLeft, hdRight⟩




theorem canonicalStableOccupiedAlternate_positive_or_commonGeometry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    ReversalGatePositive ends m j k l zero p d.1 ∨
      ∃ dCommon : ↑(canonicalRawCommonClosure ends m j k l zero p),
        dCommon.1 = d.1 ∧
        let hc := canonicalRawCommonClosure_leftGate
          ends m j k l zero p c.1 c.2
        let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p d,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p d⟩
        let hb := canonicalRawCommonClosure_leftGate
          ends m j k l zero p b.1 b.2
        let a := sourceMaskGatePointToLeftMaskFiber
          ends m j k l zero p c.1 hc
        let owner := sourceMaskGatePointToLeftMaskFiber
          ends m j k l zero p b.1 hb
        let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
          ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩
        CanonicalOpposingRootCutsAtRight
            ends m j k l zero p a owner q ∨
          CanonicalTightTwoRowCollision ends m j k l zero p a owner := by
  rcases canonicalStableRawRightTarget_memClosure_or_positive
      ends m j k l zero p d with hdClosure | hdPositive
  · exact Or.inr ⟨⟨d.1, hdClosure⟩, rfl,
      canonicalStableOccupiedAlternate_opposingCuts_or_twoRow
        ends m j k l zero hloop hjk hkl hk0 p c d hcd hne⟩
  · exact Or.inl hdPositive





theorem canonicalStableOccupiedAlternate_opposingCuts_or_distinctReroute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p c.1 c.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p d⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    let a := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p c.1 hc
    let owner := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p b.1 hb
    let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩
    CanonicalOpposingRootCutsAtRight
        ends m j k l zero p a owner q ∨
      ∃ e : leftSourceMaskFiber ends m j k l zero p,
        CanonicalRawGateRelated ends m j k l zero p c.1 e ∧
          CanonicalRawGateRelated ends m j k l zero p b.1 e ∧
          e ≠ d.1 := by
  classical
  dsimp only
  obtain ⟨hcEdge, hdEdge, hqc⟩ := hcd
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p d,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p d⟩
  let hb := canonicalRawCommonClosure_leftGate
    ends m j k l zero p b.1 b.2
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let owner := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p b.1 hb
  let rawEquiv := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  let q := rawEquiv.symm ⟨d.1, hdEdge⟩
  have haowner : a ≠ owner := by
    intro h
    apply hne
    apply Subtype.ext
    exact congrArg (fun x => x.1.1) h
  have hqa : q ∈ canonicalMaskRightImages
      ends m j k l zero p a := by
    simpa only [q, a, rawEquiv] using hqc
  have hbrel := canonicalStableRawPreferredRightBase_related
    ends m j k l zero hloop hjk hkl hk0 p d
  obtain ⟨hbEdge, hdOwner, hqowner⟩ := hbrel
  have hqo : q ∈ canonicalMaskRightImages
      ends m j k l zero p owner := by
    simpa only [q, owner, b, rawEquiv] using hqowner
  rcases canonicalCommonImage_opposingAtRight_or_twoCommon
      hloop hjk hkl a owner haowner q hqa hqo with hcuts | htwo
  · exact Or.inl hcuts
  · obtain ⟨r, hrq, hra, hrowner⟩ :=
      (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
        ends m j k l zero p a owner q hqa hqo).mpr htwo
    let e := (rawEquiv r).1
    have heRight : RowsDisconnect ends m (middleSwap m e.1) k zero :=
      (rawEquiv r).2
    have hback : rawEquiv.symm ⟨e, heRight⟩ = r := by
      exact rawEquiv.symm_apply_apply r
    refine Or.inr ⟨e, ⟨hcEdge, heRight, ?_⟩,
      ⟨hbEdge, heRight, ?_⟩, ?_⟩
    · rw [hback]
      exact hra
    · rw [hback]
      exact hrowner
    · intro hed
      apply hrq
      apply rawEquiv.injective
      apply Subtype.ext
      change e = (rawEquiv q).1
      rw [rawEquiv.apply_symm_apply]
      exact hed




theorem canonicalStableOccupiedAlternate_cut_or_free_or_sameSourceNext
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p c.1 c.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p d⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    let a := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p c.1 hc
    let owner := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p b.1 hb
    let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩
    CanonicalOpposingRootCutsAtRight
        ends m j k l zero p a owner q ∨
      ∃ e : ↑(StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (canonicalRawCommonClosure ends m j k l zero p)),
        e.1 ≠ d.1 ∧
          CanonicalRawGateRelated ends m j k l zero p c.1 e.1 ∧
          (canonicalStableRawPreferredRightBase
                ends m j k l zero hloop hjk hkl hk0 p e = c.1 ∨
            c.1 ≠ canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p e) := by
  classical
  dsimp only
  rcases canonicalStableOccupiedAlternate_opposingCuts_or_distinctReroute
      ends m j k l zero hloop hjk hkl hk0 p c d hcd hne with
    hcuts | ⟨e, hce, _, hed⟩
  · exact Or.inl hcuts
  · have heMem : e ∈ StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, c.1, c.2, hce⟩
    let eTarget : ↑(StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)) := ⟨e, heMem⟩
    by_cases hfree : canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p eTarget = c.1
    · exact Or.inr ⟨eTarget, hed, hce, Or.inl hfree⟩
    · exact Or.inr ⟨eTarget, hed, hce, Or.inr (fun h => hfree h.symm)⟩



structure CanonicalStableRawExceptionalEdge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) where
  source : ↑(canonicalRawCommonClosure ends m j k l zero p)
  target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawCommonClosure ends m j k l zero p))
  related : CanonicalRawGateRelated ends m j k l zero p source.1 target.1
  exceptional : source.1 ≠ canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p target

theorem canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p}
    (hsource : s.source = t.source) (htarget : s.target = t.target) :
    s = t := by
  cases s
  cases t
  simp_all



theorem canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : s.target = t.target) :
    s.source ≠ t.source ∨ s = t := by
  by_cases hsource : s.source = t.source
  · exact Or.inr
      (canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource htarget)
  · exact Or.inl hsource




theorem exists_canonicalStableRawExceptionalEdge_of_distinct_commonTarget
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c d : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : c ≠ d)
    (hc : CanonicalRawGateRelated ends m j k l zero p c.1 target.1)
    (hd : CanonicalRawGateRelated ends m j k l zero p d.1 target.1) :
    ∃ s : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      s.target = target ∧ (s.source = c ∨ s.source = d) := by
  classical
  by_cases hcExceptional : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p target
  · exact ⟨⟨c, target, hc, hcExceptional⟩, rfl, Or.inl rfl⟩
  · have hcOwner : c.1 = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p target :=
      Classical.not_not.mp hcExceptional
    have hdExceptional : d.1 ≠ canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p target := by
      intro hdOwner
      apply hcd
      apply Subtype.ext
      exact hcOwner.trans hdOwner.symm
    exact ⟨⟨d, target, hd, hdExceptional⟩, rfl, Or.inr rfl⟩

noncomputable instance instFintypeCanonicalStableRawExceptionalEdge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) :
    Fintype (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) := by
  classical
  let T : Type _ := ↑(canonicalRawCommonClosure ends m j k l zero p)
  let U : Type _ := ↑(StatMech.FrontierA.finiteRelationNeighborhood
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawCommonClosure ends m j k l zero p))
  let E : Type _ := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let f : E → T × U := fun s => (s.source, s.target)
  letI : Finite E := Finite.of_injective f (by
    intro s t h
    cases s
    cases t
    simp only [f, Prod.mk.injEq] at h
    simp_all)
  exact Fintype.ofFinite E




noncomputable def canonicalStableRawExceptionalEdgeEquivRightCollisionToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p ≃
      StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase := by
  classical
  dsimp only
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let forward : E → StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase := fun s =>
    ⟨s.target, ⟨s.source.1, Finset.mem_erase.mpr
      ⟨s.exceptional, Finset.mem_filter.mpr ⟨s.source.2, s.related⟩⟩⟩⟩
  let inverse : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase → E := fun token =>
    ⟨⟨token.2.1, (Finset.mem_filter.mp
        (Finset.mem_of_mem_erase token.2.2)).1⟩,
      token.1,
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase token.2.2)).2,
      Finset.ne_of_mem_erase token.2.2⟩
  refine ⟨forward, inverse, ?_, ?_⟩
  · intro s
    cases s
    rfl
  · intro token
    rcases token with ⟨target, source, hsource⟩
    rfl



def CanonicalStableRawNoOpposingCuts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) : Prop :=
  ∀ s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p,
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p s.source.1 s.source.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    let a := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p s.source.1 hc
    let owner := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p b.1 hb
    let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm
        ⟨s.target.1, s.related.choose_spec.1⟩
    ¬ CanonicalOpposingRootCutsAtRight
      ends m j k l zero p a owner q



theorem exists_canonicalStableRawExceptionalEdge_next
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    ∃ t : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p s.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p s.target⟩
      t.target.1 ≠ s.target.1 ∧
        CanonicalRawGateRelated ends m j k l zero p
          s.source.1 t.target.1 ∧
        CanonicalRawGateRelated ends m j k l zero p b.1 t.target.1 ∧
        (t.source = s.source ∨ t.source = b) ∧
        (t.source = b ∨
          (t.source = s.source ∧
            canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p t.target = b.1)) := by
  classical
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p s.target,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p s.target⟩
  rcases canonicalStableOccupiedAlternate_opposingCuts_or_distinctReroute
      ends m j k l zero hloop hjk hkl hk0 p s.source s.target
        s.related s.exceptional with hcuts | ⟨e, hse, hbe, hes⟩
  · exact False.elim (hno s hcuts)
  · have heMem : e ∈ StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e,
        s.source.1, s.source.2, hse⟩
    let eTarget : ↑(StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)) := ⟨e, heMem⟩
    by_cases hbExceptional : b.1 ≠
        canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p eTarget
    · exact ⟨⟨b, eTarget, hbe, hbExceptional⟩,
        hes, hse, hbe, Or.inr rfl, Or.inl rfl⟩
    · have hsExceptional : s.source.1 ≠
          canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p eTarget := by
        intro hsBase
        apply s.exceptional
        exact hsBase.trans (Classical.not_not.mp hbExceptional).symm
      exact ⟨⟨s.source, eTarget, hse, hsExceptional⟩,
        hes, hse, hbe, Or.inl rfl, Or.inr ⟨rfl,
          (Classical.not_not.mp hbExceptional).symm⟩⟩


noncomputable def canonicalStableRawExceptionalEdgeNext
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p) :
    CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p →
      CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p := fun s =>
  Classical.choose (exists_canonicalStableRawExceptionalEdge_next
    ends m j k l zero hloop hjk hkl hk0 p hno s)






noncomputable def CanonicalStableRawWeakComponentTokenEmbeddingData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p) : Prop := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let leftBase := canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let L := StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  exact ∃ (leftComponent : L → Set E) (componentMap : Set E → E → L),
    (∀ component s,
      StatMech.FrontierA.functionWeakComponent next s = component ->
        leftComponent (componentMap component s) = component) ∧
    ∀ component, Function.Injective fun
      s : {s : E //
        StatMech.FrontierA.functionWeakComponent next s = component} =>
      componentMap component s.1





theorem canonicalStableRawCollisionTokenEmbedding_of_weakComponentData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (hcomponents : CanonicalStableRawWeakComponentTokenEmbeddingData
      ends m j k l zero hloop hjk hkl hk0 p hno) :
    CanonicalStableRawCollisionTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let leftBase := canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let L := StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  change Nonempty
    (StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase ↪ L)
  change ∃ (leftComponent : L → Set E) (componentMap : Set E → E → L),
      _ at hcomponents
  obtain ⟨leftComponent, componentMap, htag, hinj⟩ := hcomponents
  let stateEmbedding : E ↪ L :=
    StatMech.FrontierA.embeddingOf_functionWeakComponentwiseMaps
      next leftComponent componentMap htag hinj
  let stateEquiv :=
    canonicalStableRawExceptionalEdgeEquivRightCollisionToken
      ends m j k l zero hloop hjk hkl hk0 p
  exact ⟨stateEquiv.symm.toEmbedding.trans stateEmbedding⟩

theorem canonicalStableRawExceptionalEdgeNext_target_ne
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    (canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s).target.1 ≠
        s.target.1 :=
  Classical.choose_spec (exists_canonicalStableRawExceptionalEdge_next
    ends m j k l zero hloop hjk hkl hk0 p hno s) |>.1



theorem canonicalStableRawExceptionalEdgeNext_square
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let t := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
    CanonicalRawGateRelated ends m j k l zero p
        s.source.1 t.target.1 ∧
      CanonicalRawGateRelated ends m j k l zero p b.1 t.target.1 ∧
      (t.source = s.source ∨ t.source = b) := by
  dsimp only
  have hs := Classical.choose_spec
    (exists_canonicalStableRawExceptionalEdge_next
      ends m j k l zero hloop hjk hkl hk0 p hno s)
  exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1⟩




theorem canonicalStableRawExceptionalEdgeNext_source_or_owner_stable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let t := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
    t.source = b ∨
      (t.source = s.source ∧
        canonicalStableRawPreferredRightBase
          ends m j k l zero hloop hjk hkl hk0 p t.target = b.1) := by
  dsimp only
  exact (Classical.choose_spec
    (exists_canonicalStableRawExceptionalEdge_next
      ends m j k l zero hloop hjk hkl hk0 p hno s)).2.2.2.2



def CanonicalStableRawOwnerStableStep
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  let t := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s
  t.source = s.source ∧
    canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p t.target =
      canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p s.target



def CanonicalStableRawOwnerAdvancingStep
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  let t := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s
  t.source.1 = canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p s.target





theorem canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hpreferredSelf : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p s.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p s.target⟩)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    next.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p next.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p next.target⟩ := by
  dsimp only
  intro hnextSelf
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s
  let oldOwner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  let nextOwner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p next.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p next.target⟩
  have howner : nextOwner = oldOwner := by
    apply Subtype.ext
    exact hstable.2
  apply canonicalStableRawExceptionalEdgeNext_target_ne
    ends m j k l zero hloop hjk hkl hk0 p hno s
  calc
    next.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p nextOwner := hnextSelf
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          oldOwner := by rw [howner]
    _ = s.target.1 := hpreferredSelf.symm

theorem canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno s ∨
      CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  rcases canonicalStableRawExceptionalEdgeNext_source_or_owner_stable
      ends m j k l zero hloop hjk hkl hk0 p hno s with hadvance | hstable
  · exact Or.inl (congrArg Subtype.val hadvance)
  · exact Or.inr hstable




theorem canonicalStableRawOwnerAdvancingStep_rank_lt_of_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    canonicalStableRawSourceRank ends m j k l zero p
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno s).source <
      canonicalStableRawSourceRank ends m j k l zero p s.source := by
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hownerRank := canonicalStableRawPreferredRightBase_rank_lt_of_self
    ends m j k l zero hloop hjk hkl hk0 p s.target s.source hself.symm
      s.exceptional
  have hnextSource : (canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s).source = owner := by
    apply Subtype.ext
    exact hadvancing
  rw [hnextSource]
  exact hownerRank




theorem canonicalStableRawExceptionalEdgeNext_nonself_of_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (next s).target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p (next s).source := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have htargetNe := canonicalStableRawExceptionalEdgeNext_target_ne
    ends m j k l zero hloop hjk hkl hk0 p hno s
  rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
      ends m j k l zero hloop hjk hkl hk0 p hno s with
    hadvancing | hstable
  · let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p s.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p s.target⟩
    have hnextSource : (next s).source = owner := by
      apply Subtype.ext
      exact hadvancing
    have hownerSelf : canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p owner = s.target.1 :=
      canonicalStableRawPreferredRightBase_self_eq_of_exists
        ends m j k l zero hloop hjk hkl hk0 p s.target
          ⟨s.source, hself.symm⟩
    intro hnextSelf
    apply htargetNe
    calc
      (next s).target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p (next s).source := hnextSelf
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p owner := by rw [hnextSource]
      _ = s.target.1 := hownerSelf
  · intro hnextSelf
    apply htargetNe
    calc
      (next s).target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p (next s).source := hnextSelf
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p s.source := by rw [hstable.1]
      _ = s.target.1 := hself.symm



noncomputable abbrev CanonicalStableRawLeftSurplusToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) : Type _ := by
  classical
  exact StatMech.FrontierA.bipartiteLeftSurplusToken
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawCommonClosure ends m j k l zero p)
    (canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p)



noncomputable def canonicalStableRawDirectLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  exact ⟨s.source, ⟨s.target.1, Finset.mem_erase.mpr
    ⟨hdirect, Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.related⟩⟩⟩⟩



theorem canonicalStableRawDirectLeftToken_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) :
    Function.Injective fun s :
        {s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
          s.target.1 ≠ canonicalStableRawSelfBase
            ends m j k l zero hloop hjk hkl hk0 p s.source} =>
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s.1 s.2 := by
  classical
  intro s t hst
  unfold canonicalStableRawDirectLeftToken at hst
  apply Subtype.ext
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
  · exact congrArg Sigma.fst hst
  · apply Subtype.ext
    exact congrArg (fun token => token.2.1) hst



noncomputable def canonicalStableRawLeftTokenTarget
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) :
    ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)) := by
  classical
  refine ⟨token.2.1, ?_⟩
  simp only [StatMech.FrontierA.finiteRelationNeighborhood,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨token.1.1, token.1.2,
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase token.2.2)).2⟩



def CanonicalStableRawLeftTokenIsExceptional
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  token.1.1 ≠ canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
      (canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p token)

theorem canonicalStableRawDirectLeftToken_isExceptional
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hdirect) := by
  unfold CanonicalStableRawLeftTokenIsExceptional
    canonicalStableRawDirectLeftToken canonicalStableRawLeftTokenTarget
  exact s.exceptional



noncomputable def canonicalStableRawExceptionalEdgeOfLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token) :
    CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  exact {
    source := token.1
    target := canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p token
    related := (Finset.mem_filter.mp
      (Finset.mem_of_mem_erase token.2.2)).2
    exceptional := hexceptional }




noncomputable def canonicalStableRawLeftTokenComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) :
    Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · exact StatMech.FrontierA.functionWeakComponent
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)
      (canonicalStableRawExceptionalEdgeOfLeftToken
        ends m j k l zero hloop hjk hkl hk0 p token hexceptional)
  · exact ∅



theorem canonicalStableRawDirectLeftToken_component
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
      (canonicalStableRawDirectLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hdirect) =
      StatMech.FrontierA.functionWeakComponent
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno) s := by
  classical
  have hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hdirect) := by
    unfold CanonicalStableRawLeftTokenIsExceptional
    unfold canonicalStableRawDirectLeftToken
    simpa only [canonicalStableRawLeftTokenTarget] using s.exceptional
  have hstate : canonicalStableRawExceptionalEdgeOfLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawDirectLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hdirect)
          hexceptional = s := by
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    · change (canonicalStableRawDirectLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hdirect).1 = s.source
      unfold canonicalStableRawDirectLeftToken
      rfl
    · apply Subtype.ext
      change (canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawDirectLeftToken
              ends m j k l zero hloop hjk hkl hk0 p s hdirect)).1 =
        s.target.1
      unfold canonicalStableRawLeftTokenTarget
        canonicalStableRawDirectLeftToken
      rfl
  simp only [canonicalStableRawLeftTokenComponent, hexceptional,
    dite_true, hstate]




noncomputable def canonicalStableRawSelfRerouteLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have hrelated : CanonicalRawGateRelated ends m j k l zero p
      s.source.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).1
  have hne : (next s).target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    exact heq.trans hself.symm
  exact ⟨s.source, ⟨(next s).target.1, Finset.mem_erase.mpr
    ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrelated⟩⟩⟩⟩




noncomputable def canonicalStableRawSelfOwnerRerouteLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hownerSelf : canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p owner = s.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p s.target ⟨s.source, hself.symm⟩
  have hrelated : CanonicalRawGateRelated ends m j k l zero p
      owner.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).2.1
  have hne : (next s).target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p owner := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    exact heq.trans hownerSelf
  exact ⟨owner, ⟨(next s).target.1, Finset.mem_erase.mpr
    ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrelated⟩⟩⟩⟩



theorem canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    ¬ CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawSelfOwnerRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hself) := by
  classical
  intro hexceptional
  apply hexceptional
  have howner := hstable.2
  unfold canonicalStableRawSelfOwnerRerouteLeftToken
  simpa only [canonicalStableRawLeftTokenTarget] using howner.symm





theorem canonicalStableRawSelfReroute_eq_directToken_dichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (tdirect : t.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p t.source)
    (htoken : canonicalStableRawSelfRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hself =
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p t tdirect) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (t = next s ∧ CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) ∨
      (CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno s ∧
        t.source = s.source ∧ t.target = (next s).target ∧
        t ≠ next s) := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  unfold canonicalStableRawSelfRerouteLeftToken
    canonicalStableRawDirectLeftToken at htoken
  have hsource : t.source = s.source := by
    exact (congrArg Sigma.fst htoken).symm
  have htarget : t.target = (next s).target := by
    apply Subtype.ext
    exact (congrArg (fun token => token.2.1) htoken).symm
  rcases canonicalStableRawExceptionalEdgeNext_source_or_owner_stable
      ends m j k l zero hloop hjk hkl hk0 p hno s with
    hadvance | ⟨hnextSource, hnextOwner⟩
  · right
    refine ⟨congrArg Subtype.val hadvance, hsource, htarget, ?_⟩
    intro ht
    apply s.exceptional
    have hsources := congrArg
      (fun state : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p => state.source.1) ht
    exact (congrArg Subtype.val hsource).symm.trans
      (hsources.trans (congrArg Subtype.val hadvance))
  · left
    have ht : t = next s :=
      canonicalStableRawExceptionalEdge_eq_of_source_target_eq
        (hsource.trans hnextSource.symm) htarget
    refine ⟨ht, ?_⟩
    exact ⟨hnextSource, hnextOwner⟩





theorem canonicalStableRawSelfReroute_componentDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    let token := canonicalStableRawSelfRerouteLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s hself
    let component := StatMech.FrontierA.functionWeakComponent next
    ¬ CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token ∨
      canonicalStableRawLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token = component s ∨
      ∃ t : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno s ∧
          t.source = s.source ∧ t.target = (next s).target ∧
          t ≠ next s ∧
          canonicalStableRawLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token =
            component t := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let token := canonicalStableRawSelfRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  let component := StatMech.FrontierA.functionWeakComponent next
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · let t := canonicalStableRawExceptionalEdgeOfLeftToken
      ends m j k l zero hloop hjk hkl hk0 p token hexceptional
    have tdirect : t.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p t.source := by
      exact Finset.ne_of_mem_erase token.2.2
    have htokenDirect : token = canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p t tdirect := by
      apply Sigma.ext rfl
      rfl
    have htag : canonicalStableRawLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token =
        component t := by
      simp only [canonicalStableRawLeftTokenComponent, hexceptional,
        dite_true]
      apply congrArg component
      apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
      · rfl
      · rfl
    rcases canonicalStableRawSelfReroute_eq_directToken_dichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno s t hself tdirect
          htokenDirect with ⟨ht, hstable⟩ | ⟨hadvance, hsource, htarget,
            htne⟩
    · right
      left
      rw [htag, ht]
      exact StatMech.FrontierA.functionWeakComponent_next next s
    · right
      right
      exact ⟨t, hadvance, hsource, htarget, htne, htag⟩
  · exact Or.inl hexceptional




def CanonicalStableRawStateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  (token.1 = s.source ∨ token.1 = owner) ∧
    CanonicalRawGateRelated ends m j k l zero p
      s.source.1 token.2.1 ∧
    CanonicalRawGateRelated ends m j k l zero p
      owner.1 token.2.1



inductive CanonicalStableRawStateTokenIncidenceKind
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Type _ where
  | sourceExceptional
      (hsource : token.1 = s.source)
      (hexceptional : CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token)
  | sourceFree
      (hsource : token.1 = s.source)
      (hfree : ¬ CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token)
  | ownerExceptional
      (howner : token.1 =
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p s.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p s.target⟩)
      (hexceptional : CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token)
  | ownerFree
      (howner : token.1 =
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p s.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p s.target⟩)
      (hfree : ¬ CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token)



def CanonicalStableRawWitnessedStateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token s ∧
    Nonempty (CanonicalStableRawStateTokenIncidenceKind
      ends m j k l zero hloop hjk hkl hk0 p token s)

theorem canonicalStableRawWitnessedStateTokenIncidence_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p token s ↔
      CanonicalStableRawStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p token s := by
  classical
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rcases h.1 with hsource | howner
    · by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
          ends m j k l zero hloop hjk hkl hk0 p token
      · exact ⟨CanonicalStableRawStateTokenIncidenceKind.sourceExceptional
          hsource hexceptional⟩
      · exact ⟨CanonicalStableRawStateTokenIncidenceKind.sourceFree
          hsource hexceptional⟩
    · by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
          ends m j k l zero hloop hjk hkl hk0 p token
      · exact ⟨CanonicalStableRawStateTokenIncidenceKind.ownerExceptional
          howner hexceptional⟩
      · exact ⟨CanonicalStableRawStateTokenIncidenceKind.ownerFree
          howner hexceptional⟩



def CanonicalStableRawOwnerStableOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  t.source = s.source ∧
    canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p t.target =
      canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p s.target


def CanonicalStableRawOwnerAdvancingOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  t.source.1 = canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p s.target





def canonicalStableRawTokenComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :=
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  {t | Relation.EqvGen
    (fun a b => next a = b ∨ a.target = b.target ∨
      ∃ token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p,
        CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token a ∧
          CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token b) s t}

@[simp] theorem mem_canonicalStableRawTokenComponent_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    s ∈ canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s :=
  Relation.EqvGen.refl s

theorem canonicalStableRawTokenComponent_eq_of_mem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    {s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p}
    (hst : t ∈ canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t := by
  ext u
  constructor
  · intro hsu
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ hst) hsu
  · intro htu
    exact Relation.EqvGen.trans _ _ _ hst htu

@[simp] theorem canonicalStableRawTokenComponent_next
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno s) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  symm
  apply canonicalStableRawTokenComponent_eq_of_mem
  exact Relation.EqvGen.rel _ _ (Or.inl rfl)

@[simp] theorem canonicalStableRawTokenComponent_iterate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) (n : Nat) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (canonicalStableRawTokenComponent_next
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)).trans ih

theorem canonicalStableRawTokenComponent_eq_of_target_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : s.target = t.target) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t := by
  apply canonicalStableRawTokenComponent_eq_of_mem
  exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl htarget))



theorem canonicalStableRawStateTokenIncidence_component_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hs : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token s)
    (ht : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token t) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t := by
  apply canonicalStableRawTokenComponent_eq_of_mem
  exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr ⟨token, hs, ht⟩))



noncomputable def canonicalStableRawCollisionClosedLeftTokenComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) :
    Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · exact canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno
        (canonicalStableRawExceptionalEdgeOfLeftToken
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional)
  · exact ∅


theorem canonicalStableRawDirectLeftToken_collisionClosedComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawCollisionClosedLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawDirectLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hdirect) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawDirectLeftToken
    ends m j k l zero hloop hjk hkl hk0 p s hdirect
  have hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token := by
    unfold token CanonicalStableRawLeftTokenIsExceptional
    unfold canonicalStableRawDirectLeftToken
    simpa only [canonicalStableRawLeftTokenTarget] using s.exceptional
  let t := canonicalStableRawExceptionalEdgeOfLeftToken
    ends m j k l zero hloop hjk hkl hk0 p token hexceptional
  have ht : t = s := by
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    · rfl
    · apply Subtype.ext
      rfl
  rw [show canonicalStableRawCollisionClosedLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno token =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t by
      unfold canonicalStableRawCollisionClosedLeftTokenComponent
      rw [dif_pos hexceptional]]
  exact congrArg (canonicalStableRawTokenComponent
    ends m j k l zero hloop hjk hkl hk0 p hno) ht




theorem canonicalStableRawSelfReroute_collisionClosedComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawSelfRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hself)) :
    canonicalStableRawCollisionClosedLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawSelfRerouteLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawSelfRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  let t := canonicalStableRawExceptionalEdgeOfLeftToken
    ends m j k l zero hloop hjk hkl hk0 p token hexceptional
  have htarget : t.target =
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).target := by
    apply Subtype.ext
    rfl
  rw [show canonicalStableRawCollisionClosedLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno token =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t by
      unfold canonicalStableRawCollisionClosedLeftTokenComponent
      rw [dif_pos hexceptional]]
  rw [canonicalStableRawTokenComponent_eq_of_target_eq
      ends m j k l zero hloop hjk hkl hk0 p hno t
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno s) htarget]
  exact canonicalStableRawTokenComponent_next
    ends m j k l zero hloop hjk hkl hk0 p hno s


def CanonicalStableRawSelfReroutePredecessor
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  ∃ hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source,
    canonicalStableRawSelfRerouteLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s hself = token



theorem canonicalStableRawSelfReroutePredecessor_unique
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hs : CanonicalStableRawSelfReroutePredecessor
      ends m j k l zero hloop hjk hkl hk0 p hno token s)
    (ht : CanonicalStableRawSelfReroutePredecessor
      ends m j k l zero hloop hjk hkl hk0 p hno token t) :
    s = t := by
  classical
  obtain ⟨hselfS, hsToken⟩ := hs
  obtain ⟨hselfT, htToken⟩ := ht
  have htokens := hsToken.trans htToken.symm
  have hsource : s.source = t.source := by
    exact congrArg Sigma.fst htokens
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource
  apply Subtype.ext
  calc
    s.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.source := hselfS
    _ = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p t.source := by rw [hsource]
    _ = t.target.1 := hselfT.symm




def CanonicalStableRawSquareOutputPredecessor
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  (token.1 = s.source ∨
    token.1 = ⟨canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem
        ends m j k l zero hloop hjk hkl hk0 p s.target⟩) ∧
    canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p token =
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).target



theorem canonicalStableRawSquareOutputPredecessor_component_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hs : CanonicalStableRawSquareOutputPredecessor
      ends m j k l zero hloop hjk hkl hk0 p hno token s)
    (ht : CanonicalStableRawSquareOutputPredecessor
      ends m j k l zero hloop hjk hkl hk0 p hno token t) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t := by
  rw [← canonicalStableRawTokenComponent_next
      ends m j k l zero hloop hjk hkl hk0 p hno s,
    ← canonicalStableRawTokenComponent_next
      ends m j k l zero hloop hjk hkl hk0 p hno t]
  apply canonicalStableRawTokenComponent_eq_of_target_eq
  exact hs.2.symm.trans ht.2



theorem canonicalStableRawSelfReroute_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawSelfRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hself) s := by
  dsimp only [CanonicalStableRawStateTokenIncidence]
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · exact (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).1
  · exact (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).2.1



theorem canonicalStableRawSelfOwnerReroute_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawSelfOwnerRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hself) s := by
  dsimp only [CanonicalStableRawStateTokenIncidence]
  refine ⟨Or.inr rfl, ?_, ?_⟩
  · exact (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).1
  · exact (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).2.1




noncomputable def canonicalStableRawFullLeftTokenComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) :
    Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · exact canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno
        (canonicalStableRawExceptionalEdgeOfLeftToken
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional)
  · by_cases hpredecessor : ∃ s,
        CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token s
    · exact canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (Classical.choose hpredecessor)
    · exact ∅



theorem canonicalStableRawExceptionalLeftToken_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token
        (canonicalStableRawExceptionalEdgeOfLeftToken
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional) := by
  classical
  dsimp only [CanonicalStableRawStateTokenIncidence]
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · exact (Finset.mem_filter.mp
      (Finset.mem_of_mem_erase token.2.2)).2
  · exact canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token)





theorem canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hs : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token s) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno
            (canonicalStableRawExceptionalEdgeOfLeftToken
              ends m j k l zero hloop hjk hkl hk0 p token
                hexceptional) by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_pos hexceptional]]
    exact canonicalStableRawStateTokenIncidence_component_eq
      ends m j k l zero hloop hjk hkl hk0 p hno token
        (canonicalStableRawExceptionalEdgeOfLeftToken
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional) s
        (canonicalStableRawExceptionalLeftToken_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional) hs
  · have hpredecessor : ∃ t,
        CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token t := ⟨s, hs⟩
    rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno
            (Classical.choose hpredecessor) by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_neg hexceptional, dif_pos hpredecessor]]
    exact canonicalStableRawStateTokenIncidence_component_eq
      ends m j k l zero hloop hjk hkl hk0 p hno token
        (Classical.choose hpredecessor) s
        (Classical.choose_spec hpredecessor) hs





theorem exists_canonicalStableRawOverlapToken_in_component
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (c d : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : c ≠ d)
    (hself : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c ≠
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p d)
    (hc : CanonicalRawGateRelated ends m j k l zero p c.1 target.1)
    (hd : CanonicalRawGateRelated ends m j k l zero p d.1 target.1) :
    ∃ (s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p)
      (token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p),
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token = target ∧
      (token.1 = c ∨ token.1 = d) ∧
      CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token s ∧
      canonicalStableRawFullLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  have build (x y : ↑(canonicalRawCommonClosure ends m j k l zero p))
      (hxy : x ≠ y)
      (hx : CanonicalRawGateRelated ends m j k l zero p x.1 target.1)
      (hy : CanonicalRawGateRelated ends m j k l zero p y.1 target.1)
      (hxNonself : target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p x) :
      ∃ (s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p)
        (token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p),
        canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p token = target ∧
        token.1 = x ∧
        CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token s ∧
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s := by
    let token : CanonicalStableRawLeftSurplusToken
        ends m j k l zero hloop hjk hkl hk0 p :=
      ⟨x, ⟨target.1, Finset.mem_erase.mpr
        ⟨hxNonself, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩⟩⟩
    by_cases hxExceptional : x.1 ≠ canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p target
    · let s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p :=
        ⟨x, target, hx, hxExceptional⟩
      have hincidence : CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token s := by
        dsimp only [CanonicalStableRawStateTokenIncidence, token, s]
        exact ⟨Or.inl rfl, hx,
          canonicalStableRawPreferredRightBase_related
            ends m j k l zero hloop hjk hkl hk0 p target⟩
      exact ⟨s, token, by apply Subtype.ext; rfl, rfl, hincidence,
        canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p hno token s hincidence⟩
    · have hxOwner : x.1 = canonicalStableRawPreferredRightBase
          ends m j k l zero hloop hjk hkl hk0 p target :=
        Classical.not_not.mp hxExceptional
      have hyExceptional : y.1 ≠ canonicalStableRawPreferredRightBase
          ends m j k l zero hloop hjk hkl hk0 p target := by
        intro hyOwner
        apply hxy
        apply Subtype.ext
        exact hxOwner.trans hyOwner.symm
      let s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p :=
        ⟨y, target, hy, hyExceptional⟩
      have hincidence : CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token s := by
        dsimp only [CanonicalStableRawStateTokenIncidence, token, s]
        refine ⟨Or.inr ?_, hy, ?_⟩
        · apply Subtype.ext
          exact hxOwner
        · exact canonicalStableRawPreferredRightBase_related
            ends m j k l zero hloop hjk hkl hk0 p target
      exact ⟨s, token, by apply Subtype.ext; rfl, rfl, hincidence,
        canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p hno token s hincidence⟩
  by_cases hcNonself : target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p c
  · obtain ⟨s, token, htarget, hsource, hincidence, hcomponent⟩ :=
      build c d hcd hc hd hcNonself
    exact ⟨s, token, htarget, Or.inl hsource, hincidence, hcomponent⟩
  · have hcSelf : target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p c :=
      Classical.not_not.mp hcNonself
    have hdNonself : target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p d := by
      intro hdSelf
      apply hself
      exact hcSelf.symm.trans hdSelf
    obtain ⟨s, token, htarget, hsource, hincidence, hcomponent⟩ :=
      build d c hcd.symm hd hc hdNonself
    exact ⟨s, token, htarget, Or.inr hsource, hincidence, hcomponent⟩






theorem canonicalStableRawStateTokenIncidence_outputDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hincidence : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token s) :
    ∃ t : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      t.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p token ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p s t ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p s t) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno t =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let target := canonicalStableRawLeftTokenTarget
    ends m j k l zero hloop hjk hkl hk0 p token
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hsRelated : CanonicalRawGateRelated ends m j k l zero p
      s.source.1 target.1 := hincidence.2.1
  have hownerRelated : CanonicalRawGateRelated ends m j k l zero p
      owner.1 target.1 := hincidence.2.2
  have hsourceOwner : s.source ≠ owner := by
    intro h
    exact s.exceptional (congrArg Subtype.val h)
  by_cases hstable : canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p target = owner.1
  · have hexceptional : s.source.1 ≠
        canonicalStableRawPreferredRightBase
          ends m j k l zero hloop hjk hkl hk0 p target := by
      intro h
      apply hsourceOwner
      apply Subtype.ext
      exact h.trans hstable
    let t : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p :=
      ⟨s.source, target, hsRelated, hexceptional⟩
    have htIncidence : CanonicalStableRawStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p token t := by
      dsimp only [CanonicalStableRawStateTokenIncidence, t]
      refine ⟨?_, hsRelated, ?_⟩
      · simpa only [hstable, owner] using hincidence.1
      · simpa only [hstable] using hownerRelated
    refine ⟨t, rfl, Or.inl ⟨rfl, hstable⟩, ?_⟩
    exact canonicalStableRawStateTokenIncidence_component_eq
      ends m j k l zero hloop hjk hkl hk0 p hno token t s
        htIncidence hincidence
  · let t : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p :=
      ⟨owner, target, hownerRelated, Ne.symm hstable⟩
    have hcomponent : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno t =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s := by
      by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
          ends m j k l zero hloop hjk hkl hk0 p token
      · let u := canonicalStableRawExceptionalEdgeOfLeftToken
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional
        have huIncidence : CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token u :=
          canonicalStableRawExceptionalLeftToken_stateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token hexceptional
        rw [canonicalStableRawTokenComponent_eq_of_target_eq
            ends m j k l zero hloop hjk hkl hk0 p hno t u (by
              apply Subtype.ext
              rfl)]
        exact canonicalStableRawStateTokenIncidence_component_eq
          ends m j k l zero hloop hjk hkl hk0 p hno token u s
            huIncidence hincidence
      · have htokenPreferred : token.1.1 =
            canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p target :=
          Classical.not_not.mp hexceptional
        have htIncidence : CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token t := by
          dsimp only [CanonicalStableRawStateTokenIncidence, t]
          refine ⟨Or.inr ?_, hownerRelated, ?_⟩
          · apply Subtype.ext
            exact htokenPreferred
          · exact canonicalStableRawPreferredRightBase_related
              ends m j k l zero hloop hjk hkl hk0 p target
        exact canonicalStableRawStateTokenIncidence_component_eq
          ends m j k l zero hloop hjk hkl hk0 p hno token t s
            htIncidence hincidence
    exact ⟨t, rfl, Or.inr rfl, hcomponent⟩





theorem canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hs : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token s)
    (ht : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token t) :
    s = t ∨
      (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token ∧
        CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p s u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno t) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token ∧
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p s u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno t := by
  classical
  by_cases heq : s = t
  · exact Or.inl heq
  · right
    obtain ⟨u, huTarget, huKind, huComponent⟩ :=
      canonicalStableRawStateTokenIncidence_outputDichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno token s hs.1
    have hst : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno t :=
      canonicalStableRawStateTokenIncidence_component_eq
        ends m j k l zero hloop hjk hkl hk0 p hno token s t hs.1 ht.1
    rcases huKind with huStable | huAdvancing
    · exact Or.inl ⟨u, huTarget, huStable, huComponent, hst⟩
    · exact Or.inr ⟨u, huTarget, huAdvancing, huComponent, hst⟩


theorem canonicalStableRawDirectLeftToken_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawDirectLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hdirect) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawDirectLeftToken
    ends m j k l zero hloop hjk hkl hk0 p s hdirect
  have hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token := by
    unfold token CanonicalStableRawLeftTokenIsExceptional
    unfold canonicalStableRawDirectLeftToken
    simpa only [canonicalStableRawLeftTokenTarget] using s.exceptional
  let t := canonicalStableRawExceptionalEdgeOfLeftToken
    ends m j k l zero hloop hjk hkl hk0 p token hexceptional
  have ht : t = s := by
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    · rfl
    · apply Subtype.ext
      rfl
  rw [show canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno token =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t by
      unfold canonicalStableRawFullLeftTokenComponent
      rw [dif_pos hexceptional]]
  exact congrArg (canonicalStableRawTokenComponent
    ends m j k l zero hloop hjk hkl hk0 p hno) ht



theorem canonicalStableRawSelfReroute_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawSelfRerouteLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawSelfRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawCollisionClosedLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token by
        unfold canonicalStableRawFullLeftTokenComponent
          canonicalStableRawCollisionClosedLeftTokenComponent
        rw [dif_pos hexceptional, dif_pos hexceptional]]
    exact canonicalStableRawSelfReroute_collisionClosedComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s hself hexceptional
  · have hpredecessor : ∃ t,
        CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token t :=
      ⟨s, canonicalStableRawSelfReroute_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno s hself⟩
    let chosen := Classical.choose hpredecessor
    have hchosen : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno chosen =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s :=
      canonicalStableRawStateTokenIncidence_component_eq
        ends m j k l zero hloop hjk hkl hk0 p hno token chosen s
          (Classical.choose_spec hpredecessor)
          (canonicalStableRawSelfReroute_stateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p hno s hself)
    rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno chosen by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_neg hexceptional, dif_pos hpredecessor]]
    exact hchosen



theorem canonicalStableRawSelfOwnerReroute_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawSelfOwnerRerouteLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawSelfOwnerRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · let t := canonicalStableRawExceptionalEdgeOfLeftToken
      ends m j k l zero hloop hjk hkl hk0 p token hexceptional
    have htarget : t.target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno s).target := by
      apply Subtype.ext
      rfl
    rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno t by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_pos hexceptional]]
    rw [canonicalStableRawTokenComponent_eq_of_target_eq
        ends m j k l zero hloop hjk hkl hk0 p hno t
          (canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno s) htarget]
    exact canonicalStableRawTokenComponent_next
      ends m j k l zero hloop hjk hkl hk0 p hno s
  · have hpredecessor : ∃ t,
        CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token t :=
      ⟨s, canonicalStableRawSelfOwnerReroute_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno s hself⟩
    let chosen := Classical.choose hpredecessor
    have hchosen : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno chosen =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s :=
      canonicalStableRawStateTokenIncidence_component_eq
        ends m j k l zero hloop hjk hkl hk0 p hno token chosen s
          (Classical.choose_spec hpredecessor)
          (canonicalStableRawSelfOwnerReroute_stateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p hno s hself)
    rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno chosen by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_neg hexceptional, dif_pos hpredecessor]]
    exact hchosen




theorem canonicalStableRawOwnerStableSelfPair_componentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (_hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    Nonempty (Fin 2 ↪
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s}) := by
  classical
  let sourceToken := canonicalStableRawSelfRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  let ownerToken := canonicalStableRawSelfOwnerRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  have hsourceComponent : canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno sourceToken =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s :=
    canonicalStableRawSelfReroute_fullComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s hself
  have hownerComponent : canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno ownerToken =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s :=
    canonicalStableRawSelfOwnerReroute_fullComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s hself
  let sourceInComponent : {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    ⟨sourceToken, hsourceComponent⟩
  let ownerInComponent : {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    ⟨ownerToken, hownerComponent⟩
  have hne : sourceInComponent ≠ ownerInComponent := by
    intro heq
    apply s.exceptional
    exact congrArg (fun token => token.1.1.1) heq
  let f : Fin 2 → {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    fun i => if i = 0 then sourceInComponent else ownerInComponent
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [f]



noncomputable def canonicalStableRawStateLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  by_cases hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source
  · exact canonicalStableRawSelfRerouteLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s hself
  · exact canonicalStableRawDirectLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hself



theorem canonicalStableRawStateLeftToken_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s) s := by
  classical
  unfold canonicalStableRawStateLeftToken
  split
  next hself =>
    exact canonicalStableRawSelfReroute_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno s hself
  next _hdirect =>
    dsimp only [CanonicalStableRawStateTokenIncidence]
    refine ⟨Or.inl rfl, s.related, ?_⟩
    exact canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p s.target



theorem canonicalStableRawStateLeftToken_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  exact canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno
      (canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s) s
      (canonicalStableRawStateLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno s)




theorem canonicalStableRawSelfState_componentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Nonempty
      ({s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno s = component ∧
            s.target.1 = canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p s.source} ↪
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token = component}) := by
  classical
  let f : {s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno s = component ∧
            s.target.1 = canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p s.source} ->
      {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token = component} :=
    fun s => ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1,
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2.1⟩
  refine ⟨⟨f, ?_⟩⟩
  intro s t hst
  apply Subtype.ext
  have htokens := congrArg Subtype.val hst
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno t.1 at htokens
  unfold canonicalStableRawStateLeftToken at htokens
  rw [dif_pos s.2.2, dif_pos t.2.2] at htokens
  exact canonicalStableRawSelfReroutePredecessor_unique
    ends m j k l zero hloop hjk hkl hk0 p hno
      (canonicalStableRawSelfRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 s.2.2)
      s.1 t.1 ⟨s.2.2, rfl⟩ ⟨t.2.2, htokens.symm⟩




theorem canonicalStableRawDirectState_componentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Nonempty
      ({s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno s = component ∧
            s.target.1 ≠ canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p s.source} ↪
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token = component}) := by
  classical
  let f : {s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno s = component ∧
            s.target.1 ≠ canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p s.source} ->
      {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token = component} :=
    fun s => ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1,
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2.1⟩
  refine ⟨⟨f, ?_⟩⟩
  intro s t hst
  apply Subtype.ext
  have htokens := congrArg Subtype.val hst
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno t.1 at htokens
  unfold canonicalStableRawStateLeftToken at htokens
  rw [dif_neg s.2.2, dif_neg t.2.2] at htokens
  let sDirect : {u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p //
      u.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source} := ⟨s.1, s.2.2⟩
  let tDirect : {u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p //
      u.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source} := ⟨t.1, t.2.2⟩
  have htokens' : canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p sDirect.1 sDirect.2 =
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p tDirect.1 tDirect.2 := htokens
  have hsub := canonicalStableRawDirectLeftToken_injective
      ends m j k l zero hloop hjk hkl hk0 p htokens'
  simpa only [sDirect, tDirect] using congrArg Subtype.val hsub



def CanonicalStableRawSelfDirectTokenCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (self direct : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  self.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p self.source ∧
    direct.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p direct.source ∧
    ((direct = next self ∧ CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno self) ∨
      (CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno self ∧
        direct.source = self.source ∧
        direct.target = (next self).target ∧ direct ≠ next self))





theorem canonicalStableRawStateLeftToken_eq_imp
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno t ->
      s = t ∨
        CanonicalStableRawSelfDirectTokenCollision
          ends m j k l zero hloop hjk hkl hk0 p hno s t ∨
        CanonicalStableRawSelfDirectTokenCollision
          ends m j k l zero hloop hjk hkl hk0 p hno t s := by
  classical
  intro htoken
  by_cases hs : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source
  · by_cases ht : t.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p t.source
    · left
      apply canonicalStableRawSelfReroutePredecessor_unique
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s) s t
      · refine ⟨hs, ?_⟩
        simpa only [canonicalStableRawStateLeftToken, dif_pos hs]
      · refine ⟨ht, ?_⟩
        simpa only [canonicalStableRawStateLeftToken, dif_pos hs,
          dif_pos ht] using htoken.symm
    · right
      left
      refine ⟨hs, ht, ?_⟩
      apply canonicalStableRawSelfReroute_eq_directToken_dichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno s t hs ht
      simpa only [canonicalStableRawStateLeftToken, dif_pos hs,
        dif_neg ht] using htoken
  · by_cases ht : t.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p t.source
    · right
      right
      refine ⟨ht, hs, ?_⟩
      apply canonicalStableRawSelfReroute_eq_directToken_dichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno t s ht hs
      simpa only [canonicalStableRawStateLeftToken, dif_neg hs,
        dif_pos ht] using htoken.symm
    · left
      have hsub : (⟨s, hs⟩ : {u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
            u.target.1 ≠ canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p u.source}) = ⟨t, ht⟩ :=
        canonicalStableRawDirectLeftToken_injective
          ends m j k l zero hloop hjk hkl hk0 p (by
            simpa only [canonicalStableRawStateLeftToken, dif_neg hs,
              dif_neg ht] using htoken)
      exact congrArg Subtype.val hsub



theorem canonicalStableRawSelfDirectTokenCollision_of_token_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (self direct : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : self.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p self.source)
    (hdirect : direct.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p direct.source)
    (htoken : canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno self =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno direct) :
    CanonicalStableRawSelfDirectTokenCollision
      ends m j k l zero hloop hjk hkl hk0 p hno self direct := by
  rcases canonicalStableRawStateLeftToken_eq_imp
      ends m j k l zero hloop hjk hkl hk0 p hno self direct htoken with
    heq | hcollision | hreverse
  · exfalso
    apply hdirect
    simpa only [← heq] using hself
  · exact hcollision
  · exact False.elim (hdirect hreverse.1)






theorem canonicalClosedAdvancingExceptionalCycle_stateLeftToken_injective
    {C : Type*} [Fintype C]
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x)) :
    Function.Injective fun x => canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have collisionFalse (x y : C)
      (hcollision : CanonicalStableRawSelfDirectTokenCollision
        ends m j k l zero hloop hjk hkl hk0 p hno
          (state x) (state y)) : False := by
    rcases hcollision with ⟨hself, hdirect,
      ⟨hnext, hstable⟩ | ⟨hadvanceCollision, hsource, htargetEq, hne⟩⟩
    · have ha := hadvance x
      simp only [CanonicalStableRawOwnerAdvancingStep] at ha
      apply (state x).exceptional
      calc
        (state x).source.1 = (next (state x)).source.1 :=
          congrArg Subtype.val hstable.1.symm
        _ = canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p (state x).target := ha
    · have hy : y = σ x := by
        apply htarget
        calc
          (state y).target = (next (state x)).target := htargetEq
          _ = (state (σ x)).target :=
            congrArg (fun edge => edge.target) (hstep x).symm
      have ha := hadvance x
      simp only [CanonicalStableRawOwnerAdvancingStep] at ha
      apply (state x).exceptional
      calc
        (state x).source.1 = (state y).source.1 :=
          (congrArg Subtype.val hsource).symm
        _ = (state (σ x)).source.1 := by rw [hy]
        _ = (next (state x)).source.1 :=
          congrArg (fun edge => edge.source.1) (hstep x)
        _ = canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p (state x).target := ha
  intro x y hxy
  rcases canonicalStableRawStateLeftToken_eq_imp
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) (state y) hxy with
    hstate | hcollision | hcollision
  · apply htarget
    exact congrArg (fun edge => edge.target) hstate
  · exact False.elim (collisionFalse x y hcollision)
  · exact False.elim (collisionFalse y x hcollision)




theorem canonicalClosedAdvancingExceptionalCycle_componentEmbedding
    {C : Type*} [Fintype C] (root : C)
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (hcomponent : ∀ x, canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state root)) :
    Nonempty (C ↪
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno (state root)}) := by
  let f : C -> {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno (state root)} :=
    fun x => ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno (state x),
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state x)).trans
          (hcomponent x)⟩
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  apply canonicalClosedAdvancingExceptionalCycle_stateLeftToken_injective
    ends m j k l zero hloop hjk hkl hk0 p hno σ state hstep htarget
      hadvance
  exact congrArg Subtype.val hxy



theorem canonicalStableRawExceptionalEdgeNext_twoRowCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p s.source.1 s.source.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    CanonicalTightTwoRowCollision ends m j k l zero p
      (sourceMaskGatePointToLeftMaskFiber
        ends m j k l zero p s.source.1 hc)
      (sourceMaskGatePointToLeftMaskFiber
        ends m j k l zero p b.1 hb) := by
  classical
  dsimp only
  let t := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p s.target,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p s.target⟩
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p s.source.1 s.source.2
  let hb := canonicalRawCommonClosure_leftGate
    ends m j k l zero p b.1 b.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p s.source.1 hc
  let owner := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p b.1 hb
  obtain ⟨hcOld, hdOld, hqA⟩ := s.related
  obtain ⟨hbOld, _, hqOwner⟩ :=
    canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p s.target
  obtain ⟨hANew, hOwnerNew, _⟩ :=
    canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s
  obtain ⟨_, htNew, hrA⟩ := hANew
  obtain ⟨_, _, hrOwner⟩ := hOwnerNew
  let rawEquiv := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  let q := rawEquiv.symm ⟨s.target.1, hdOld⟩
  let r := rawEquiv.symm ⟨t.target.1, htNew⟩
  have hqr : q ≠ r := by
    intro h
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    have hraw := congrArg rawEquiv h
    simpa only [q, r, rawEquiv, Equiv.apply_symm_apply] using
      (congrArg (fun x => x.1) hraw).symm
  refine ⟨q, r, hqr, ?_, ?_, ?_, ?_⟩
  · simpa only [q, a, rawEquiv] using hqA
  · simpa only [q, owner, b, rawEquiv] using hqOwner
  · simpa only [r, a, t, rawEquiv] using hrA
  · simpa only [r, owner, b, t, rawEquiv] using hrOwner





theorem exists_ownerStableSquare_collisionTokens_and_surplusTokens
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    ∃ r0 r1 : StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase,
      r0 ≠ r1 ∧
        ∃ l0 l1 : StatMech.FrontierA.bipartiteLeftSurplusToken
            R T leftBase,
          l0 ≠ l1 := by
  classical
  dsimp only
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let leftBase := canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  let t := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s
  let b : ↑T := ⟨rightBase s.target,
    canonicalStableRawPreferredRightBase_mem
      ends m j k l zero hloop hjk hkl hk0 p s.target⟩
  have hstable' : t.source = s.source ∧ rightBase t.target = b.1 := by
    simpa only [CanonicalStableRawOwnerStableStep, t, b, rightBase] using hstable
  obtain ⟨hsourceNew, hownerNew, _⟩ :=
    canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s
  have hcOldMem : s.source.1 ∈ T.filter fun c => R c s.target.1 :=
    Finset.mem_filter.mpr ⟨s.source.2, s.related⟩
  have hcNewRelated : R s.source.1 t.target.1 := hsourceNew
  have hcNewMem : s.source.1 ∈ T.filter fun c => R c t.target.1 :=
    Finset.mem_filter.mpr ⟨s.source.2, hcNewRelated⟩
  have hcNewExceptional : s.source.1 ≠ rightBase t.target := by
    intro h
    apply t.exceptional
    rw [hstable'.1]
    exact h
  let r0 : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase :=
    ⟨s.target, ⟨s.source.1, Finset.mem_erase.mpr
      ⟨s.exceptional, hcOldMem⟩⟩⟩
  let r1 : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase :=
    ⟨t.target, ⟨s.source.1, Finset.mem_erase.mpr
      ⟨hcNewExceptional, hcNewMem⟩⟩⟩
  have hr01 : r0 ≠ r1 := by
    intro h
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    exact (congrArg (fun x => x.1.1) h).symm
  have hbOldRelated : R b.1 s.target.1 := by
    exact canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p s.target
  have hbNewRelated : R b.1 t.target.1 := hownerNew
  let cAlt := if s.target.1 = leftBase s.source then
      t.target.1 else s.target.1
  have hcAltRelated : R s.source.1 cAlt := by
    dsimp only [cAlt]
    split
    · exact hcNewRelated
    · exact s.related
  have hcAltNe : cAlt ≠ leftBase s.source := by
    dsimp only [cAlt]
    split
    next heq =>
      intro h
      apply canonicalStableRawExceptionalEdgeNext_target_ne
        ends m j k l zero hloop hjk hkl hk0 p hno s
      exact h.trans heq.symm
    next hne => exact hne
  let bAlt := if s.target.1 = leftBase b then
      t.target.1 else s.target.1
  have hbAltRelated : R b.1 bAlt := by
    dsimp only [bAlt]
    split
    · exact hbNewRelated
    · exact hbOldRelated
  have hbAltNe : bAlt ≠ leftBase b := by
    dsimp only [bAlt]
    split
    next heq =>
      intro h
      apply canonicalStableRawExceptionalEdgeNext_target_ne
        ends m j k l zero hloop hjk hkl hk0 p hno s
      exact h.trans heq.symm
    next hne => exact hne
  let l0 : StatMech.FrontierA.bipartiteLeftSurplusToken
      R T leftBase :=
    ⟨s.source, ⟨cAlt, Finset.mem_erase.mpr ⟨hcAltNe,
      Finset.mem_filter.mpr ⟨Finset.mem_univ cAlt, hcAltRelated⟩⟩⟩⟩
  let l1 : StatMech.FrontierA.bipartiteLeftSurplusToken
      R T leftBase :=
    ⟨b, ⟨bAlt, Finset.mem_erase.mpr ⟨hbAltNe,
      Finset.mem_filter.mpr ⟨Finset.mem_univ bAlt, hbAltRelated⟩⟩⟩⟩
  have hcb : s.source ≠ b := by
    intro h
    apply s.exceptional
    exact congrArg Subtype.val h
  have hl01 : l0 ≠ l1 := by
    intro h
    exact hcb (congrArg Sigma.fst h)
  exact ⟨r0, r1, hr01, l0, l1, hl01⟩



theorem exists_two_collisionTokens_of_sameTarget_distinctSources
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : s.target = t.target) (hsource : s.source ≠ t.source) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    ∃ r0 r1 : StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase,
      r0 ≠ r1 := by
  classical
  dsimp only
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  have htRelated : R t.source.1 s.target.1 := by
    simpa only [htarget] using t.related
  have htExceptional : t.source.1 ≠ rightBase s.target := by
    simpa only [htarget] using t.exceptional
  have hsMem : s.source.1 ∈
      (T.filter fun c => R c s.target.1).erase (rightBase s.target) :=
    Finset.mem_erase.mpr ⟨s.exceptional,
      Finset.mem_filter.mpr ⟨s.source.2, s.related⟩⟩
  have htMem : t.source.1 ∈
      (T.filter fun c => R c s.target.1).erase (rightBase s.target) :=
    Finset.mem_erase.mpr ⟨htExceptional,
      Finset.mem_filter.mpr ⟨t.source.2, htRelated⟩⟩
  let r0 : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase := ⟨s.target, ⟨s.source.1, hsMem⟩⟩
  let r1 : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase := ⟨s.target, ⟨t.source.1, htMem⟩⟩
  have hr01 : r0 ≠ r1 := by
    intro h
    apply hsource
    apply Subtype.ext
    exact congrArg (fun x => x.2.1) h
  exact ⟨r0, r1, hr01⟩



theorem ownerStableSquare_twoTokenEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    Nonempty (Fin 2 ↪ StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase) ∧
      Nonempty (Fin 2 ↪ StatMech.FrontierA.bipartiteLeftSurplusToken
        R T leftBase) := by
  classical
  dsimp only
  obtain ⟨r0, r1, hr01, l0, l1, hl01⟩ :=
    exists_ownerStableSquare_collisionTokens_and_surplusTokens
      ends m j k l zero hloop hjk hkl hk0 p hno s hstable
  let fr : Fin 2 -> StatMech.FrontierA.bipartiteRightCollisionToken
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p))
      (canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p) :=
    fun i => if i = 0 then r0 else r1
  let fl : Fin 2 -> StatMech.FrontierA.bipartiteLeftSurplusToken
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)
      (canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p) :=
    fun i => if i = 0 then l0 else l1
  have hfr : Function.Injective fr := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [fr]
  have hfl : Function.Injective fl := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [fl]
  exact ⟨⟨⟨fr, hfr⟩⟩, ⟨⟨fl, hfl⟩⟩⟩




theorem canonicalClosedAdvancingExceptionalCycle_tokenEmbeddings
    {C : Type*} [Fintype C]
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hσ : ∀ x, σ x ≠ x)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x)) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    Nonempty (C ↪ StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase) ∧
      Nonempty (C ↪ StatMech.FrontierA.bipartiteLeftSurplusToken
        R T leftBase) := by
  classical
  dsimp only
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let leftBase := canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  have hsourceNext (x : C) : (state x).source ≠ (state (σ x)).source := by
    intro hs
    apply (state x).exceptional
    have hsVal := congrArg Subtype.val hs
    have ha := hadvance x
    simp only [CanonicalStableRawOwnerAdvancingStep] at ha
    rw [hstep x] at hsVal
    exact hsVal.trans ha
  have hnext (x : C) : R (state x).source.1 (state (σ x)).target.1 := by
    have hsquare := canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno (state x)
    rw [hstep x]
    exact hsquare.1
  exact StatMech.FrontierA.cycleCollisionAndSurplusTokenEmbeddings
    R T U leftBase rightBase σ
      (fun x => (state x).source) (fun x => (state x).target)
      hσ htarget hsourceNext (fun x => (state x).related) hnext
      (fun x => (state x).exceptional)





theorem canonicalClosedPreferredSelfExceptionalCycle_tokenEmbeddings
    {C : Type*} [Fintype C]
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hσ : ∀ x, σ x ≠ x)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hpreferredSelf : ∀ x, (state x).target.1 =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p (state x).target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p (state x).target⟩) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    Nonempty (C ↪ StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase) ∧
      Nonempty (C ↪ StatMech.FrontierA.bipartiteLeftSurplusToken
        R T leftBase) := by
  classical
  have hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
    intro x
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) with
      hadvance | hstable
    · exact hadvance
    · exfalso
      apply canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
        ends m j k l zero hloop hjk hkl hk0 p hno (state x)
          (hpreferredSelf x) hstable
      simpa only [← hstep x] using hpreferredSelf (σ x)
  exact canonicalClosedAdvancingExceptionalCycle_tokenEmbeddings
    ends m j k l zero hloop hjk hkl hk0 p hno σ state hσ hstep
      htarget hadvance


theorem canonicalClosedPreferredSelfExceptionalCycle_componentEmbedding
    {C : Type*} [Fintype C] (root : C)
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hpreferredSelf : ∀ x, (state x).target.1 =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p (state x).target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p (state x).target⟩)
    (hcomponent : ∀ x, canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state root)) :
    Nonempty (C ↪
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno (state root)}) := by
  have hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
    intro x
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) with
      hadvance | hstable
    · exact hadvance
    · exfalso
      apply canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
        ends m j k l zero hloop hjk hkl hk0 p hno (state x)
          (hpreferredSelf x) hstable
      simpa only [← hstep x] using hpreferredSelf (σ x)
  exact canonicalClosedAdvancingExceptionalCycle_componentEmbedding
    root ends m j k l zero hloop hjk hkl hk0 p hno σ state hstep
      htarget hadvance hcomponent




theorem symmDiffFold_exceptionalCycle_endpointRows_eq_empty
    {A : Type*} [Fintype A]
    (m : Finset I) (σ : Equiv.Perm A)
    (source owner : A -> ↑m -> Fin 4)
    (hadvance : ∀ x, source (σ x) = owner x) :
    symmDiffFold Finset.univ (fun x =>
      rowClass m (source x) 0 ∆ rowClass m (owner x) 0) = ∅ := by
  let R := fun x : A => rowClass m (source x) 0
  calc
    symmDiffFold Finset.univ (fun x =>
        rowClass m (source x) 0 ∆ rowClass m (owner x) 0) =
        symmDiffFold Finset.univ (fun x =>
          (∅ : Finset I) ∆ R x ∆ R (σ x)) := by
      unfold symmDiffFold
      apply Finset.fold_congr
      intro x _
      rw [show rowClass m (owner x) 0 = R (σ x) by
        simp only [R, hadvance x]]
      change R x ∆ R (σ x) = (∅ : Finset I) ∆ R x ∆ R (σ x)
      have hempty : (∅ : Finset I) ∆ R x = R x := by
        ext i
        simp [Finset.mem_symmDiff]
      rw [hempty]
    _ = symmDiffFold Finset.univ (fun _ : A => (∅ : Finset I)) :=
      symmDiffFold_endpointCancellation
        (fun _ : A => (∅ : Finset I)) R σ
    _ = ∅ := by
      rw [symmDiffFold_const]
      split <;> rfl




theorem exists_referenceTransferFold_eq_of_indexedTranslatedRows
    {A : Type*} [Fintype A]
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (source : A -> leftMaskFiber ends m j k l zero p)
    (σ : Equiv.Perm A)
    (hrows : ∀ x : A, ∃ a b : leftMaskFiber ends m j k l zero p,
      RowSupportDisconnects ends m
          (canonicalTranslatedRow ends m k zero a.1.1 (source x).1.1) k zero ∧
        canonicalTranslatedRow ends m k zero a.1.1 (source x).1.1 =
          canonicalTranslatedRow ends m k zero
            b.1.1 (source (σ x)).1.1) :
    ∃ a b : A -> leftMaskFiber ends m j k l zero p,
      (∀ x, RowSupportDisconnects ends m
        (canonicalTranslatedRow ends m k zero
          (a x).1.1 (source x).1.1) k zero) ∧
      (∀ x, canonicalTranslatedRow ends m k zero
          (a x).1.1 (source x).1.1 =
        canonicalTranslatedRow ends m k zero
          (b x).1.1 (source (σ x)).1.1) ∧
      symmDiffFold Finset.univ (fun x =>
          canonicalTransferUnion ends m k zero (a x).1.1) =
        symmDiffFold Finset.univ (fun x =>
          canonicalTransferUnion ends m k zero (b x).1.1) := by
  classical
  choose a b hdisc heq using hrows
  refine ⟨a, b, hdisc, heq, ?_⟩
  let R := fun x : A => rowClass m (source x).1.1 0
  let TA := fun x : A =>
    canonicalTransferUnion ends m k zero (a x).1.1
  let TB := fun x : A =>
    canonicalTransferUnion ends m k zero (b x).1.1
  have hpoint : ∀ x, R x ∆ TA x = R (σ x) ∆ TB x := by
    intro x
    simpa only [R, TA, TB, canonicalTranslatedRow] using heq x
  have hfold : symmDiffFold Finset.univ (fun x => R x ∆ TA x) =
      symmDiffFold Finset.univ (fun x => R (σ x) ∆ TB x) := by
    unfold symmDiffFold
    apply Finset.fold_congr
    intro x _
    exact hpoint x
  rw [symmDiffFold_pair, symmDiffFold_pair,
    symmDiffFold_equiv σ R] at hfold
  have hcancel {X Y Z : Finset I} (h : X ∆ Y = X ∆ Z) : Y = Z := by
    have h' := congrArg (fun K : Finset I => X ∆ K) h
    simpa [symmDiff_assoc] using h'
  exact hcancel hfold




theorem exists_canonicalStableRawExceptionalEdge_iterate_repeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let E := CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    ∃ i j : Fin (Fintype.card E + 1), i ≠ j ∧
      next^[i.1] s = next^[j.1] s := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let orbit : Fin (Fintype.card E + 1) → E := fun n => next^[n.1] s
  have hnotinj : ¬ Function.Injective orbit := by
    intro hinj
    have hcard := Fintype.card_le_of_injective orbit hinj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnotinj
  exact ⟨i, j, hne, hij⟩




theorem exists_canonicalStableRawExceptionalEdge_target_iterate_repeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    ∃ i j : Fin (Fintype.card U + 1), i ≠ j ∧
      (next^[i.1] s).target = (next^[j.1] s).target := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawCommonClosure ends m j k l zero p))
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let targets : Fin (Fintype.card U + 1) → U := fun n =>
    (next^[n.1] s).target
  have hnotinj : ¬ Function.Injective targets := by
    intro hinj
    have hcard := Fintype.card_le_of_injective targets hinj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnotinj
  exact ⟨i, j, hne, hij⟩



theorem exists_canonicalStableRawExceptionalEdge_minimalTargetRepeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    ∃ i j : Nat, i < j ∧ j ≤ Fintype.card U ∧
      (next^[i] s).target = (next^[j] s).target ∧
      ∀ a b : Nat, a < b -> b < j ->
        (next^[a] s).target ≠ (next^[b] s).target := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawCommonClosure ends m j k l zero p))
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let target : Nat -> U := fun n => (next^[n] s).target
  obtain ⟨u, v, huv, heq⟩ :=
    exists_canonicalStableRawExceptionalEdge_target_iterate_repeat
      ends m j k l zero hloop hjk hkl hk0 p hno s
  obtain ⟨i0, j0, hij0, heq0, hj0Bound⟩ :
      ∃ i0 j0 : Nat, i0 < j0 ∧ target i0 = target j0 ∧
        j0 ≤ Fintype.card U := by
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · refine ⟨u.1, v.1, huv', ?_, ?_⟩
      · simpa only [target] using heq
      · exact Nat.le_of_lt_succ v.2
    · refine ⟨v.1, u.1, hvu', ?_, ?_⟩
      · simpa only [target] using heq.symm
      · exact Nat.le_of_lt_succ u.2
  let P := fun n : Nat => ∃ i < n, target i = target n
  have hP : ∃ n, P n := ⟨j0, i0, hij0, heq0⟩
  let n := Nat.find hP
  obtain ⟨i, hin, hitarget⟩ := Nat.find_spec hP
  have hnBound : n ≤ Fintype.card U := by
    exact (Nat.find_min' hP ⟨i0, hij0, heq0⟩).trans hj0Bound
  refine ⟨i, n, hin, hnBound, hitarget, ?_⟩
  intro a b hab hbn habTarget
  have hPb : P b := ⟨a, hab, habTarget⟩
  have hnb := Nat.find_min' hP hPb
  exact (Nat.not_le_of_lt hbn) hnb




theorem exists_canonicalStableRawExceptionalEdge_minimalCycleDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    ∃ start stop : Nat, start < stop ∧ stop ≤ Fintype.card U ∧
      (next^[start] s).target = (next^[stop] s).target ∧
      (∀ a b : Nat, a < b -> b < stop ->
        (next^[a] s).target ≠ (next^[b] s).target) ∧
      ((∃ n : Nat, start ≤ n ∧ n < stop ∧
          CanonicalStableRawOwnerStableStep
            ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s)) ∨
        ∀ n : Nat, start ≤ n -> n < stop ->
          CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s)) := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  obtain ⟨start, stop, hlt, hstopBound, hrepeat, hdistinct⟩ :=
    exists_canonicalStableRawExceptionalEdge_minimalTargetRepeat
      ends m j k l zero hloop hjk hkl hk0 p hno s
  refine ⟨start, stop, hlt, hstopBound, hrepeat, hdistinct, ?_⟩
  by_cases hstable : ∃ n : Nat, start ≤ n ∧ n < stop ∧
      CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s)
  · exact Or.inl hstable
  · right
    intro n hin hnj
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s) with
      hadvance | hownerStable
    · exact hadvance
    · exact False.elim (hstable ⟨n, hin, hnj, hownerStable⟩)



theorem canonicalMinimalClosedAdvancingCycle_tokenEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hstate :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s) =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s))
    (hdistinct : ∀ a b : Nat, start ≤ a -> a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    Nonempty (Fin (stop - start) ↪
        StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase) ∧
      Nonempty (Fin (stop - start) ↪
        StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase) := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have hdpos : 0 < stop - start := by omega
  obtain ⟨cycleN, hcycle⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hdpos)
  let state : Fin (cycleN + 1) → E := fun x => next^[start + x.1] s
  let σ : Equiv.Perm (Fin (cycleN + 1)) := finRotate (cycleN + 1)
  have hstep : ∀ x, state (σ x) = next (state x) := by
    intro x
    by_cases hx : x = Fin.last cycleN
    · subst x
      simp only [state, σ, finRotate_last, Fin.val_zero, Fin.val_last]
      calc
        next^[start] s = next^[stop] s := hstate
        _ = next^[Nat.succ (start + cycleN)] s := by congr 2 <;> omega
        _ = next (next^[start + cycleN] s) :=
          Function.iterate_succ_apply' next (start + cycleN) s
    · have hrotate : (σ x).1 = x.1 + 1 := by
        exact coe_finRotate_of_ne_last hx
      simp only [state]
      rw [hrotate]
      convert Function.iterate_succ_apply' next (start + x.1) s using 1 <;>
        omega
  have htarget : Function.Injective fun x => (state x).target := by
    intro x y hxy
    apply Fin.ext
    by_contra hval
    rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
    · exact (hdistinct (start + x.1) (start + y.1) (by omega)
        (by omega) (by omega)) hxy
    · exact (hdistinct (start + y.1) (start + x.1) (by omega)
        (by omega) (by omega)) hxy.symm
  have hσ : ∀ x, σ x ≠ x := by
    intro x hx
    have htargetEq : (state (σ x)).target = (state x).target := by rw [hx]
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno (state x)
    calc
      (next (state x)).target.1 = (state (σ x)).target.1 := by
        rw [hstep x]
      _ = (state x).target.1 := congrArg Subtype.val htargetEq
  have hadvanceState : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
    intro x
    exact hadvance (start + x.1) (by omega) (by omega)
  have htokens := canonicalClosedAdvancingExceptionalCycle_tokenEmbeddings
    ends m j k l zero hloop hjk hkl hk0 p hno σ state hσ hstep
      htarget hadvanceState
  simpa only [hcycle] using htokens




theorem canonicalMinimalClosedAdvancingCycle_componentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hstate :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s) =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s))
    (hdistinct : ∀ a b : Nat, start ≤ a -> a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    Nonempty (Fin (stop - start) ↪
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawExceptionalEdgeNext
                ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s)}) := by
  classical
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have hdpos : 0 < stop - start := by omega
  obtain ⟨cycleN, hcycle⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hdpos)
  let state : Fin (cycleN + 1) → E := fun x => next^[start + x.1] s
  let σ : Equiv.Perm (Fin (cycleN + 1)) := finRotate (cycleN + 1)
  have hstep : ∀ x, state (σ x) = next (state x) := by
    intro x
    by_cases hx : x = Fin.last cycleN
    · subst x
      simp only [state, σ, finRotate_last, Fin.val_zero, Fin.val_last]
      calc
        next^[start] s = next^[stop] s := hstate
        _ = next^[Nat.succ (start + cycleN)] s := by congr 2 <;> omega
        _ = next (next^[start + cycleN] s) :=
          Function.iterate_succ_apply' next (start + cycleN) s
    · have hrotate : (σ x).1 = x.1 + 1 :=
        coe_finRotate_of_ne_last hx
      simp only [state]
      rw [hrotate]
      convert Function.iterate_succ_apply' next (start + x.1) s using 1 <;>
        omega
  have htarget : Function.Injective fun x => (state x).target := by
    intro x y hxy
    apply Fin.ext
    by_contra hval
    rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
    · exact (hdistinct (start + x.1) (start + y.1) (by omega)
        (by omega) (by omega)) hxy
    · exact (hdistinct (start + y.1) (start + x.1) (by omega)
        (by omega) (by omega)) hxy.symm
  have hadvanceState : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
    intro x
    exact hadvance (start + x.1) (by omega) (by omega)
  have hcomponent : ∀ x, canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state 0) := by
    intro x
    have hstateIter : state x = next^[x.1] (next^[start] s) := by
      simp only [state]
      rw [Nat.add_comm start x.1]
      exact Function.iterate_add_apply next x.1 start s
    rw [hstateIter]
    exact canonicalStableRawTokenComponent_iterate
      ends m j k l zero hloop hjk hkl hk0 p hno (next^[start] s) x.1
  have hemb := canonicalClosedAdvancingExceptionalCycle_componentEmbedding
    (0 : Fin (cycleN + 1)) ends m j k l zero hloop hjk hkl hk0 p hno
      σ state hstep htarget hadvanceState hcomponent
  simpa only [hcycle, state, Fin.val_zero, Nat.add_zero] using hemb





theorem canonicalMinimalAdvancingRepeat_componentDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (((next^[start] s).source ≠ (next^[stop] s).source) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno (next^[start] s) =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno (next^[stop] s)) ∨
      Nonempty (Fin (stop - start) ↪
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token =
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno
                (next^[start] s)}) := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
      (next^[start] s) (next^[stop] s) hrepeat with hsource | hstate
  · left
    exact ⟨hsource, canonicalStableRawTokenComponent_eq_of_target_eq
      ends m j k l zero hloop hjk hkl hk0 p hno
        (next^[start] s) (next^[stop] s) hrepeat⟩
  · right
    exact canonicalMinimalClosedAdvancingCycle_componentEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno s start stop
        hstartStop hstate (fun a b _ hab hb => hdistinct a b hab hb)
        hadvance



theorem canonicalSameTargetDistinctExceptionalPair_componentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : s.target = t.target) (hsource : s.source ≠ t.source) :
    Nonempty (Fin 2 ↪
      {u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s}) := by
  let sInComponent :
      {u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} := ⟨s, rfl⟩
  let tInComponent :
      {u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    ⟨t, (canonicalStableRawTokenComponent_eq_of_target_eq
      ends m j k l zero hloop hjk hkl hk0 p hno s t htarget).symm⟩
  have hst : sInComponent ≠ tInComponent := by
    intro h
    apply hsource
    exact congrArg (fun u => u.1.source) h
  let f : Fin 2 ->
      {u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    fun i => if i = 0 then sInComponent else tInComponent
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [f]




theorem canonicalMinimalAdvancingRepeat_componentEmbeddingDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    Nonempty (Fin 2 ↪
        {u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u =
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno
                (next^[start] s)}) ∨
      Nonempty (Fin (stop - start) ↪
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token =
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno
                (next^[start] s)}) := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases canonicalMinimalAdvancingRepeat_componentDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno s start stop
        hstartStop hrepeat hdistinct hadvance with
    ⟨hsource, _hcomponent⟩ | hleft
  · left
    exact canonicalSameTargetDistinctExceptionalPair_componentEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno
        (next^[start] s) (next^[stop] s) hrepeat hsource
  · exact Or.inr hleft




theorem canonicalMinimalAdvancingRepeat_tokenDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    (∃ r0 r1 : StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase, r0 ≠ r1) ∨
      (Nonempty (Fin (stop - start) ↪
          StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase) ∧
        Nonempty (Fin (stop - start) ↪
          StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase)) := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
      (next^[start] s) (next^[stop] s) hrepeat with hsource | hstate
  · exact Or.inl
      (exists_two_collisionTokens_of_sameTarget_distinctSources
        ends m j k l zero hloop hjk hkl hk0 p
          (next^[start] s) (next^[stop] s) hrepeat hsource)
  · exact Or.inr
      (canonicalMinimalClosedAdvancingCycle_tokenEmbeddings
        ends m j k l zero hloop hjk hkl hk0 p hno s start stop
          hstartStop hstate (fun a b _ hab hb => hdistinct a b hab hb)
          hadvance)




theorem ownerStableSquare_targets_isolated_in_minimalCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop n : Nat) (hstartStop : start < stop)
    (hnStart : start ≤ n) (hnStop : n < stop)
    (hrepeat :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno
        ((canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    let succIndex := if n + 1 < stop then n + 1 else start
    ∀ q : Nat, start ≤ q -> q < stop -> q ≠ n -> q ≠ succIndex ->
      (next^[q] s).target ≠ (next^[n] s).target ∧
        (next^[q] s).target ≠ (next^[n + 1] s).target := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let target := fun a : Nat => (next^[a] s).target
  have target_ne {a b : Nat} (ha : a < stop) (hb : b < stop)
      (hab : a ≠ b) : target a ≠ target b := by
    rcases lt_or_gt_of_ne hab with hab' | hba'
    · exact hdistinct a b hab' hb
    · exact (hdistinct b a hba' ha).symm
  have hnSucc : n + 1 ≤ stop := by omega
  by_cases hnNext : n + 1 < stop
  · intro q hqStart hqStop hqn hqSucc
    have hqOld := target_ne hqStop hnStop hqn
    have hqNew := target_ne hqStop hnNext (by
      simpa only [hnNext, if_pos] using hqSucc)
    exact ⟨hqOld, hqNew⟩
  · have hnEq : n + 1 = stop := by omega
    intro q hqStart hqStop hqn hqSucc
    have hqOld := target_ne hqStop hnStop hqn
    have hqStartNe : q ≠ start := by
      simpa only [hnNext, if_neg] using hqSucc
    have hqWrap := target_ne hqStop hstartStop hqStartNe
    have hnextRepeat : target (n + 1) = target start := by
      rw [hnEq]
      exact hrepeat.symm
    exact ⟨hqOld, fun h => hqWrap (h.trans hnextRepeat)⟩





theorem canonicalSelfImageFiber_referenceTransfer_common_ne_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (q r : leftMaskFiber ends m j k l zero p)
    (hqr : q ≠ r)
    (himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p q q
          (canonicalTransferWorks_self hloop hjk hkl hk0 q)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p r r
            (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1) :
    let hworks := (canonicalSelfTransfer_collision_oppositeWorks
      ends m j k l zero hloop hjk hkl hk0 p q r himage).1
    let alt := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r q hworks
    let self := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p q q
        (canonicalTransferWorks_self hloop hjk hkl hk0 q)
    alt ∈ canonicalMaskRightImages ends m j k l zero p q ∧
      alt ∈ canonicalMaskRightImages ends m j k l zero p r ∧
      alt ≠ self := by
  classical
  dsimp only
  let hworksRQ := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p q r himage).1
  let hworksQR := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p q r himage).2
  let alt := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p r q hworksRQ
  let selfQ := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p q q
      (canonicalTransferWorks_self hloop hjk hkl hk0 q)
  let selfR := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p r r
      (canonicalTransferWorks_self hloop hjk hkl hk0 r)
  have haltQ : alt ∈ canonicalMaskRightImages
      ends m j k l zero p q := by
    exact (mem_canonicalMaskRightImages_iff
      ends m j k l zero p q alt).mpr ⟨r, hworksRQ, rfl⟩
  have htranslated : canonicalTranslatedRow ends m k zero q.1.1 q.1.1 =
      canonicalTranslatedRow ends m k zero r.1.1 r.1.1 := by
    have hrow := congrArg (fun c => rowClass m c 0) himage
    have hqrow := rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p q q
        (canonicalTransferWorks_self hloop hjk hkl hk0 q)
    have hrrow := rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r r
        (canonicalTransferWorks_self hloop hjk hkl hk0 r)
    exact hqrow.symm.trans (hrow.trans hrrow)
  have hopposite := canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero q.1.1 r.1.1 q.1.1 r.1.1 htranslated
  have hraw : alt.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m q.1.1 k zero)
      (canonicalOuterTransfer ends m q.1.1 k zero) r.1.1 := by
    exact (canonicalBalancedSwaps_eq_iff_rowSymmDiff
      hloop hjk hkl r q q r).mpr hopposite
  have haltR : alt ∈ canonicalMaskRightImages
      ends m j k l zero p r := by
    exact (mem_canonicalMaskRightImages_iff
      ends m j k l zero p r alt).mpr ⟨q, hworksQR, hraw⟩
  have hselfQR : selfQ = selfR := by
    apply Subtype.ext
    apply Subtype.ext
    exact himage
  have haltNe : alt ≠ selfQ := by
    intro halt
    have hrawEq := congrArg
      (fun z : rightMaskFiber ends m j k l zero p => z.1.1)
      (halt.trans hselfQR)
    change balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) q.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) r.1.1 at hrawEq
    have hinv := congrArg (balancedSwap m
      (canonicalMiddleTransfer ends m r.1.1 k zero)
      (canonicalOuterTransfer ends m r.1.1 k zero)) hrawEq
    simp only [balancedSwap_involutive] at hinv
    apply hqr
    apply Subtype.ext
    apply Subtype.ext
    exact hinv
  exact ⟨haltQ, haltR, haltNe⟩



structure CanonicalStableRawReferenceAlternateData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c r : ↑(canonicalRawCommonClosure ends m j k l zero p)) where
  target : leftSourceMaskFiber ends m j k l zero p
  sourceRelated : CanonicalRawGateRelated ends m j k l zero p c.1 target
  referenceRelated : CanonicalRawGateRelated ends m j k l zero p r.1 target
  target_ne_referenceSelf : target ≠ canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p r



noncomputable def canonicalStableRawReferenceAlternateData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c r : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hcr : c ≠ r)
    (hbase : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r) :
    CanonicalStableRawReferenceAlternateData
      ends m j k l zero hloop hjk hkl hk0 p c r := by
  classical
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let hr := canonicalRawCommonClosure_leftGate
    ends m j k l zero p r.1 r.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let ref := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p r.1 hr
  have haref : a ≠ ref := by
    intro har
    apply hcr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : leftMaskFiber ends m j k l zero p => x.1.1) har
  let qa := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p c.1 hc
  let qref := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p r.1 hr
  let e := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  have hselfEq : qa = qref := by
    apply e.injective
    apply Subtype.ext
    exact hbase
  have himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p a a
          (canonicalTransferWorks_self hloop hjk hkl hk0 a)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p ref ref
            (canonicalTransferWorks_self hloop hjk hkl hk0 ref)).1.1 := by
    exact congrArg (fun q : rightMaskFiber ends m j k l zero p => q.1.1)
      hselfEq
  let hworks := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p a ref himage).1
  let alt := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p ref a hworks
  have hcommon := canonicalSelfImageFiber_referenceTransfer_common_ne_self
    ends m j k l zero hloop hjk hkl hk0 p a ref haref himage
  let raw := (e alt).1
  have hsourceRelated : CanonicalRawGateRelated
      ends m j k l zero p c.1 raw := by
    refine ⟨hc, (e alt).2, ?_⟩
    have hback : e.symm ⟨raw, (e alt).2⟩ = alt := by
      exact e.symm_apply_apply alt
    rw [hback]
    exact hcommon.1
  have hrefRelated : CanonicalRawGateRelated
      ends m j k l zero p r.1 raw := by
    refine ⟨hr, (e alt).2, ?_⟩
    have hback : e.symm ⟨raw, (e alt).2⟩ = alt := by
      exact e.symm_apply_apply alt
    rw [hback]
    exact hcommon.2.1
  have hrawNe : raw ≠ canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p r := by
    intro hraw
    apply hcommon.2.2
    let self := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a a
        (canonicalTransferWorks_self hloop hjk hkl hk0 a)
    apply e.injective
    apply Subtype.ext
    change raw = (e self).1
    exact hraw.trans hbase.symm
  exact ⟨raw, hsourceRelated, hrefRelated, hrawNe⟩



theorem canonicalStableRawReferenceAlternateData_target_comm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c r : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hcr : c ≠ r)
    (hbase : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r) :
    (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p c r hcr hbase).target =
      (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p r c hcr.symm hbase.symm).target := by
  classical
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let hr := canonicalRawCommonClosure_leftGate
    ends m j k l zero p r.1 r.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let ref := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p r.1 hr
  have haref : a ≠ ref := by
    intro h
    apply hcr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : leftMaskFiber ends m j k l zero p => q.1.1) h
  let qa := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p c.1 hc
  let qref := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p r.1 hr
  let e := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  have hselfEq : qa = qref := by
    apply e.injective
    apply Subtype.ext
    exact hbase
  have himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p a a
          (canonicalTransferWorks_self hloop hjk hkl hk0 a)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p ref ref
            (canonicalTransferWorks_self hloop hjk hkl hk0 ref)).1.1 := by
    exact congrArg (fun q : rightMaskFiber ends m j k l zero p => q.1.1)
      hselfEq
  let hworksRA := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p a ref himage).1
  let hworksAR := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p a ref himage).2
  let altRA := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p ref a hworksRA
  let altAR := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p a ref hworksAR
  have htranslated : canonicalTranslatedRow ends m k zero a.1.1 a.1.1 =
      canonicalTranslatedRow ends m k zero ref.1.1 ref.1.1 := by
    have hrow := congrArg (fun q => rowClass m q 0) himage
    have harow := rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a a
        (canonicalTransferWorks_self hloop hjk hkl hk0 a)
    have hrefrow := rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p ref ref
        (canonicalTransferWorks_self hloop hjk hkl hk0 ref)
    exact harow.symm.trans (hrow.trans hrefrow)
  have hopposite := canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero a.1.1 ref.1.1 a.1.1 ref.1.1 htranslated
  have hraw : altRA.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m a.1.1 k zero)
      (canonicalOuterTransfer ends m a.1.1 k zero) ref.1.1 := by
    exact (canonicalBalancedSwaps_eq_iff_rowSymmDiff
      hloop hjk hkl ref a a ref).mpr hopposite
  have halt : altRA = altAR := by
    apply Subtype.ext
    apply Subtype.ext
    exact hraw
  unfold canonicalStableRawReferenceAlternateData
  dsimp only
  exact congrArg (fun q : rightMaskFiber ends m j k l zero p => (e q).1) halt




theorem canonicalStableRawReferenceAlternateData_target_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c d r : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hcr : c ≠ r) (hdr : d ≠ r)
    (hbasec : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r)
    (hbased : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p d =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r)
    (htarget : (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p c r hcr hbasec).target =
      (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p d r hdr hbased).target) :
    c = d := by
  classical
  unfold canonicalStableRawReferenceAlternateData at htarget
  dsimp only at htarget
  have hright := (rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p).injective (Subtype.ext htarget)
  have hraw := congrArg
    (fun q : rightMaskFiber ends m j k l zero p => q.1.1) hright
  change balancedSwap m
      (canonicalMiddleTransfer ends m
        (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
          (canonicalRawCommonClosure_leftGate
            ends m j k l zero p r.1 r.2)).1.1 k zero)
      (canonicalOuterTransfer ends m
        (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
          (canonicalRawCommonClosure_leftGate
            ends m j k l zero p r.1 r.2)).1.1 k zero)
      (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p c.1 c.2)).1.1 =
    balancedSwap m
      (canonicalMiddleTransfer ends m
        (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
          (canonicalRawCommonClosure_leftGate
            ends m j k l zero p r.1 r.2)).1.1 k zero)
      (canonicalOuterTransfer ends m
        (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
          (canonicalRawCommonClosure_leftGate
            ends m j k l zero p r.1 r.2)).1.1 k zero)
      (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p d.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p d.1 d.2)).1.1 at hraw
  have hinv := congrArg (balancedSwap m
    (canonicalMiddleTransfer ends m
      (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p r.1 r.2)).1.1 k zero)
    (canonicalOuterTransfer ends m
      (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p r.1 r.2)).1.1 k zero)) hraw
  simp only [balancedSwap_involutive] at hinv
  apply Subtype.ext
  apply Subtype.ext
  exact hinv



theorem canonicalStableRawReferenceAlternateData_target_injective_of_reference_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c d r q : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hcr : c ≠ r) (hdq : d ≠ q)
    (hbasec : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r)
    (hbased : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p d =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p q)
    (hrq : r = q)
    (htarget : (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p c r hcr hbasec).target =
      (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p d q hdq hbased).target) :
    c = d := by
  subst q
  exact canonicalStableRawReferenceAlternateData_target_injective
    ends m j k l zero hloop hjk hkl hk0 p c d r
      hcr hdq hbasec hbased htarget



noncomputable def canonicalStableRawReferenceOwner
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    ↑(canonicalRawCommonClosure ends m j k l zero p) :=
  ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p s.target⟩

theorem canonicalStableRawReferenceOwner_source_ne
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    s.source ≠ canonicalStableRawReferenceOwner
      ends m j k l zero hloop hjk hkl hk0 p s := by
  intro h
  apply s.exceptional
  exact congrArg Subtype.val h

theorem canonicalStableRawReferenceOwner_selfBase
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p s) =
      s.target.1 :=
  canonicalStableRawPreferredRightBase_self_eq_of_exists
    ends m j k l zero hloop hjk hkl hk0 p s.target
      ⟨s.source, hself.symm⟩

theorem canonicalStableRawReferenceOwner_sourceBase
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p s) :=
  hself.symm.trans
    (canonicalStableRawReferenceOwner_selfBase
      ends m j k l zero hloop hjk hkl hk0 p s hself).symm

noncomputable def canonicalStableRawReferenceOwnerAlternateData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawReferenceAlternateData
      ends m j k l zero hloop hjk hkl hk0 p s.source
        (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p s) :=
  canonicalStableRawReferenceAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s.source
      (canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s)
      (canonicalStableRawReferenceOwner_source_ne
        ends m j k l zero hloop hjk hkl hk0 p s)
      (canonicalStableRawReferenceOwner_sourceBase
        ends m j k l zero hloop hjk hkl hk0 p s hself)




noncomputable def canonicalStableRawReferenceOwnerLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let owner := canonicalStableRawReferenceOwner
    ends m j k l zero hloop hjk hkl hk0 p s
  let data := canonicalStableRawReferenceOwnerAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s hself
  exact ⟨owner, ⟨data.target, Finset.mem_erase.mpr
    ⟨data.target_ne_referenceSelf,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, data.referenceRelated⟩⟩⟩⟩

@[simp] theorem canonicalStableRawReferenceOwnerLeftToken_source
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawReferenceOwnerLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hself).1 =
      canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s := rfl

@[simp] theorem canonicalStableRawReferenceOwnerLeftToken_target
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawReferenceOwnerLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hself).2.1 =
      (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p s hself).target := rfl



theorem canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hself) s := by
  classical
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hsourceOwner : s.source ≠ owner := by
    intro h
    apply s.exceptional
    exact congrArg Subtype.val h
  have hownerSelf : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p owner = s.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p s.target
        ⟨s.source, hself.symm⟩
  have hbase : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p s.source =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p owner := hself.symm.trans hownerSelf.symm
  let data := canonicalStableRawReferenceAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s.source owner
      hsourceOwner hbase
  change (owner = s.source ∨ owner = owner) ∧
    CanonicalRawGateRelated ends m j k l zero p s.source.1 data.target ∧
    CanonicalRawGateRelated ends m j k l zero p owner.1 data.target
  exact ⟨Or.inr rfl, data.sourceRelated, data.referenceRelated⟩

theorem canonicalStableRawReferenceOwnerLeftToken_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawReferenceOwnerLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  exact canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno _ s
      (canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p s hself)

set_option maxHeartbeats 800000 in

lemma canonicalStableRawReferenceOwnerLeftToken_eq_imp
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hselfS : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hselfT : t.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p t.source)
    (htoken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hselfS =
      canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p t hselfT) :
    s = t := by
  classical
  let ownerS : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    canonicalStableRawReferenceOwner
      ends m j k l zero hloop hjk hkl hk0 p s
  let ownerT : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    canonicalStableRawReferenceOwner
      ends m j k l zero hloop hjk hkl hk0 p t
  have howner : ownerS = ownerT := by
    have hsource := congrArg Sigma.fst htoken
    simpa only [canonicalStableRawReferenceOwnerLeftToken_source] using hsource
  have hownerSelfS : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p ownerS = s.target.1 :=
    canonicalStableRawReferenceOwner_selfBase
      ends m j k l zero hloop hjk hkl hk0 p s hselfS
  have hownerSelfT : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p ownerT = t.target.1 :=
    canonicalStableRawReferenceOwner_selfBase
      ends m j k l zero hloop hjk hkl hk0 p t hselfT
  have htarget : s.target = t.target := by
    apply Subtype.ext
    calc
      s.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p ownerS := hownerSelfS.symm
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p ownerT := by rw [howner]
      _ = t.target.1 := hownerSelfT
  have hsne : s.source ≠ ownerS := by
    exact canonicalStableRawReferenceOwner_source_ne
      ends m j k l zero hloop hjk hkl hk0 p s
  have htne : t.source ≠ ownerS := by
    intro h
    exact (canonicalStableRawReferenceOwner_source_ne
      ends m j k l zero hloop hjk hkl hk0 p t) (h.trans howner)
  have hbaseS : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p s.source =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p ownerS :=
    canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p s hselfS
  have hbaseT : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p t.source =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p ownerS :=
    (canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p t hselfT).trans
        (congrArg (canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p) howner.symm)
  have htokenTarget := congrArg (fun token :
      CanonicalStableRawLeftSurplusToken
        ends m j k l zero hloop hjk hkl hk0 p => token.2.1) htoken
  change (canonicalStableRawReferenceOwnerAlternateData
      ends m j k l zero hloop hjk hkl hk0 p s hselfS).target =
    (canonicalStableRawReferenceOwnerAlternateData
      ends m j k l zero hloop hjk hkl hk0 p t hselfT).target at htokenTarget
  unfold canonicalStableRawReferenceOwnerAlternateData at htokenTarget
  have hsources : s.source = t.source :=
    canonicalStableRawReferenceAlternateData_target_injective_of_reference_eq
      ends m j k l zero hloop hjk hkl hk0 p s.source t.source ownerS ownerT
        hsne
        (canonicalStableRawReferenceOwner_source_ne
          ends m j k l zero hloop hjk hkl hk0 p t)
        hbaseS
        (canonicalStableRawReferenceOwner_sourceBase
          ends m j k l zero hloop hjk hkl hk0 p t hselfT)
        howner htokenTarget
  exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    hsources htarget



noncomputable def canonicalStableRawReferenceSourceLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let data := canonicalStableRawReferenceOwnerAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s hself
  have htargetNe : data.target ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source := by
    intro h
    apply data.target_ne_referenceSelf
    exact h.trans (canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p s hself)
  exact ⟨s.source, ⟨data.target, Finset.mem_erase.mpr
    ⟨htargetNe, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, data.sourceRelated⟩⟩⟩⟩

@[simp] theorem canonicalStableRawReferenceSourceLeftToken_source
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawReferenceSourceLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hself).1 = s.source := rfl

@[simp] theorem canonicalStableRawReferenceSourceLeftToken_target
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawReferenceSourceLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hself).2.1 =
      (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p s hself).target := rfl

theorem canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceSourceLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hself) s := by
  classical
  let data := canonicalStableRawReferenceOwnerAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s hself
  change (s.source = s.source ∨
      s.source = canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s) ∧
    CanonicalRawGateRelated ends m j k l zero p s.source.1 data.target ∧
    CanonicalRawGateRelated ends m j k l zero p
      (canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s).1 data.target
  exact ⟨Or.inl rfl, data.sourceRelated, data.referenceRelated⟩

theorem canonicalStableRawReferenceSourceLeftToken_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawReferenceSourceLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s :=
  canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno _ s
      (canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p s hself)




theorem canonicalStableRawReferenceSourceLeftToken_eq_imp
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hselfS : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hselfT : t.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p t.source)
    (htoken : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hselfS =
      canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p t hselfT) :
    s = t := by
  have hsource : s.source = t.source := by
    simpa only [canonicalStableRawReferenceSourceLeftToken_source] using
      congrArg Sigma.fst htoken
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource
  apply Subtype.ext
  calc
    s.target.1 = canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p s.source := hselfS
    _ = canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p t.source := by rw [hsource]
    _ = t.target.1 := hselfT.symm




theorem canonicalStableRawReferenceOwnerLeftToken_eq_selfOwnerReroute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hsource : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hself =
      canonicalStableRawSelfRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hself) :
    canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hself =
      canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hself := by
  have htarget : (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p s hself).target =
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).target.1 := by
    have h := congrArg (fun token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.2.1) hsource
    exact h
  have hfirst : (canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hself).1 =
      (canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hself).1 := by
    apply Subtype.ext
    rfl
  apply Sigma.ext hfirst
  cases hfirst
  apply heq_of_eq
  apply Subtype.ext
  exact htarget





noncomputable def canonicalStableRawDirectAlternateLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hsourceNew : CanonicalRawGateRelated ends m j k l zero p
      s.source.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).1
  have hownerNew : CanonicalRawGateRelated ends m j k l zero p
      owner.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).2.1
  have hownerOld : CanonicalRawGateRelated ends m j k l zero p
      owner.1 s.target.1 :=
    canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p s.target
  by_cases hsourceSelf : (next s).target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source
  · by_cases hownerSelf : s.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p owner
    · have hownerNewNe : (next s).target.1 ≠ canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p owner := by
        intro h
        apply canonicalStableRawExceptionalEdgeNext_target_ne
          ends m j k l zero hloop hjk hkl hk0 p hno s
        exact h.trans hownerSelf.symm
      exact ⟨owner, ⟨(next s).target.1, Finset.mem_erase.mpr
        ⟨hownerNewNe, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hownerNew⟩⟩⟩⟩
    · exact ⟨owner, ⟨s.target.1, Finset.mem_erase.mpr
        ⟨hownerSelf, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hownerOld⟩⟩⟩⟩
  · exact ⟨s.source, ⟨(next s).target.1, Finset.mem_erase.mpr
      ⟨hsourceSelf, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hsourceNew⟩⟩⟩⟩





theorem canonicalStableRawDirectAlternateLeftToken_source_split
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p s.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p s.target⟩
    (next.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p s.source ∧
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect).1 = owner) ∨
      (next.target.1 ≠ canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p s.source ∧
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect).1 = s.source) := by
  classical
  dsimp only
  rw [canonicalStableRawDirectAlternateLeftToken]
  dsimp only
  split
  next hsourceSelf =>
    left
    refine ⟨hsourceSelf, ?_⟩
    split <;> rfl
  next hsourceSelf =>
    exact Or.inr ⟨hsourceSelf, rfl⟩

theorem canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect) s := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hsourceNew : CanonicalRawGateRelated ends m j k l zero p
      s.source.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).1
  have hownerNew : CanonicalRawGateRelated ends m j k l zero p
      owner.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).2.1
  have hownerOld : CanonicalRawGateRelated ends m j k l zero p
      owner.1 s.target.1 :=
    canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p s.target
  rw [canonicalStableRawDirectAlternateLeftToken]
  dsimp only
  split
  next hsourceSelf =>
    split
    next hownerSelf => exact ⟨Or.inr rfl, hsourceNew, hownerNew⟩
    next hownerSelf => exact ⟨Or.inr rfl, s.related, hownerOld⟩
  next hsourceSelf => exact ⟨Or.inl rfl, hsourceNew, hownerNew⟩

theorem canonicalStableRawDirectAlternateLeftToken_ne_natural
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hdirect ≠
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  intro htoken
  unfold canonicalStableRawStateLeftToken at htoken
  rw [dif_neg hdirect] at htoken
  rw [canonicalStableRawDirectAlternateLeftToken] at htoken
  dsimp only at htoken
  split at htoken
  next hsourceSelf =>
    split at htoken
    next hownerSelf =>
      exact s.exceptional (congrArg (fun token => token.1.1) htoken).symm
    next hownerSelf =>
      exact s.exceptional (congrArg (fun token => token.1.1) htoken).symm
  next hsourceSelf =>
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    exact congrArg (fun token => token.2.1) htoken

theorem canonicalStableRawDirectAlternateLeftToken_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawDirectAlternateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hdirect) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  exact canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno _ s
      (canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)





theorem card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (S : Finset ↑(canonicalRawCommonClosure ends m j k l zero p))
    (r : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hfiber : ∀ c ∈ S,
      canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c =
        canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p r) :
    S.card ≤
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (S.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let toLeft : ↑(canonicalRawCommonClosure ends m j k l zero p) ->
      leftMaskFiber ends m j k l zero p := fun c =>
    sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1
      (canonicalRawCommonClosure_leftGate
        ends m j k l zero p c.1 c.2)
  let leftS : Finset (leftMaskFiber ends m j k l zero p) := S.image toLeft
  have htoLeft : Function.Injective toLeft := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : leftMaskFiber ends m j k l zero p => x.1.1) hcd
  have hleftCard : leftS.card = S.card := by
    exact Finset.card_image_of_injective S htoLeft
  have himage : ∀ c ∈ leftS,
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p (toLeft r) (toLeft r)
          (canonicalTransferWorks_self hloop hjk hkl hk0 (toLeft r))).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p c c
            (canonicalTransferWorks_self hloop hjk hkl hk0 c)).1.1 := by
    intro c hc
    obtain ⟨cRaw, hcRaw, rfl⟩ := Finset.mem_image.mp hc
    let e := rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p
    let qr := canonicalSelfRightPointOfSourceGate ends m j k l zero
      hloop hjk hkl hk0 p r.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p r.1 r.2)
    let qc := canonicalSelfRightPointOfSourceGate ends m j k l zero
      hloop hjk hkl hk0 p cRaw.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p cRaw.1 cRaw.2)
    have heqRaw := hfiber cRaw hcRaw
    have heq : e qr = e qc := by
      apply Subtype.ext
      change canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p r =
        canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p cRaw
      exact heqRaw.symm
    exact congrArg (fun q : rightMaskFiber ends m j k l zero p => q.1.1)
      (e.injective heq)
  have hcanonical :=
    card_le_canonicalMaskRightNeighborhood_of_selfImageFiber
      ends m j k l zero hloop hjk hkl hk0 p leftS (toLeft r) himage
  let e := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  let rawS : Finset (leftSourceMaskFiber ends m j k l zero p) :=
    S.map ⟨Subtype.val, Subtype.val_injective⟩
  let rawNeighborhood := StatMech.FrontierA.finiteRelationNeighborhood
    (CanonicalRawGateRelated ends m j k l zero p) rawS
  let rawTargetValue :
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p leftS) ->
        leftSourceMaskFiber ends m j k l zero p := fun q => (e q.1).1
  have rawTargetValue_mem (q :
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p leftS)) :
      rawTargetValue q ∈ rawNeighborhood := by
    let d := rawTargetValue q
    have hq := (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p leftS q.1).1 q.2
    obtain ⟨c, hcLeft, hqc⟩ := hq
    obtain ⟨cRaw, hcRaw, hc⟩ := Finset.mem_image.mp hcLeft
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ d, cRaw.1, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨cRaw, hcRaw, rfl⟩
    refine ⟨canonicalRawCommonClosure_leftGate
        ends m j k l zero p cRaw.1 cRaw.2, (e q.1).2, ?_⟩
    have hcEq : c = toLeft cRaw := hc.symm
    have heqGate :
        (⟨d, (e q.1).2⟩ : reversedRightSourceMaskGateFiber
          ends m j k l zero p) = e q.1 := by
      apply Subtype.ext
      rfl
    rw [heqGate, e.symm_apply_apply]
    simpa only [hcEq] using hqc
  let rawTarget :
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p leftS) ->
        ↑rawNeighborhood := fun q => ⟨rawTargetValue q, rawTargetValue_mem q⟩
  have hrawTarget : Function.Injective rawTarget := by
    intro q₁ q₂ hq
    have hval := congrArg Subtype.val hq
    change (e q₁.1).1 = (e q₂.1).1 at hval
    have he : e q₁.1 = e q₂.1 := Subtype.ext hval
    exact Subtype.ext (e.injective he)
  have hrightCard :
      (canonicalMaskRightNeighborhood ends m j k l zero p leftS).card ≤
        rawNeighborhood.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective rawTarget hrawTarget
  rw [← hleftCard]
  exact hcanonical.trans hrightCard


abbrev CanonicalStableRawComponentState
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :=
  {s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p //
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s = component}


abbrev CanonicalStableRawComponentToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :=
  {token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p //
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token = component}

abbrev CanonicalStableRawComponentSelfState
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :=
  {s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p //
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s = component ∧
      s.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.source}

abbrev CanonicalStableRawComponentDirectState
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :=
  {s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p //
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s = component ∧
      s.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.source}

noncomputable def canonicalStableRawComponentSelfEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let f : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1,
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2.1⟩
  refine ⟨f, ?_⟩
  intro s t hst
  have htokens := congrArg Subtype.val hst
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno t.1 at htokens
  unfold canonicalStableRawStateLeftToken at htokens
  rw [dif_pos s.2.2, dif_pos t.2.2] at htokens
  apply Subtype.ext
  exact canonicalStableRawSelfReroutePredecessor_unique
    ends m j k l zero hloop hjk hkl hk0 p hno
      (canonicalStableRawSelfRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 s.2.2)
      s.1 t.1 ⟨s.2.2, rfl⟩ ⟨t.2.2, htokens.symm⟩

noncomputable def canonicalStableRawComponentDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let f : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1,
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2.1⟩
  refine ⟨f, ?_⟩
  intro s t hst
  have htokens := congrArg Subtype.val hst
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno t.1 at htokens
  unfold canonicalStableRawStateLeftToken at htokens
  rw [dif_neg s.2.2, dif_neg t.2.2] at htokens
  let sDirect : {u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p //
      u.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source} := ⟨s.1, s.2.2⟩
  let tDirect : {u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p //
      u.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source} := ⟨t.1, t.2.2⟩
  have htokens' : canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p sDirect.1 sDirect.2 =
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p tDirect.1 tDirect.2 := htokens
  have hsub := canonicalStableRawDirectLeftToken_injective
      ends m j k l zero hloop hjk hkl hk0 p htokens'
  apply Subtype.ext
  simpa only [sDirect, tDirect] using congrArg Subtype.val hsub

@[simp] theorem canonicalStableRawComponentSelfEmbedding_apply
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    (canonicalStableRawComponentSelfEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component s).1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 := by
  rfl

@[simp] theorem canonicalStableRawComponentDirectEmbedding_apply
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component s).1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 := by
  rfl






noncomputable def canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let f : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ->
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun x =>
    ⟨canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p x.1.1.1 x.1.1.2.2,
      (canonicalStableRawReferenceOwnerLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          x.1.1.1 x.1.1.2.2).trans x.1.1.2.1⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  apply StatMech.FrontierA.crossCollision_fst_injective
  apply Subtype.ext
  apply canonicalStableRawReferenceOwnerLeftToken_eq_imp
    ends m j k l zero hloop hjk hkl hk0 p
      x.1.1.1 y.1.1.1 x.1.1.2.2 y.1.1.2.2
  exact congrArg Subtype.val hxy

@[simp] theorem canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component x).1 =
      canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p x.1.1.1 x.1.1.2.2 := by
  rfl

theorem canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x ≠
      canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self := by
  classical
  intro heq
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target⟩
  have hownerSelf : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p owner = x.1.1.1.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p x.1.1.1.target
        ⟨x.1.1.1.source, x.1.1.2.2.symm⟩
  have htoken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p x.1.1.1 x.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno self.1 := by
    simpa only [canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
      canonicalStableRawComponentSelfEmbedding_apply] using congrArg Subtype.val heq
  have hsourceRaw := congrArg (fun token :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.1.1) htoken
  unfold canonicalStableRawReferenceOwnerLeftToken
    canonicalStableRawStateLeftToken at hsourceRaw
  rw [dif_pos self.2.2] at hsourceRaw
  change owner.1 = self.1.source.1 at hsourceRaw
  have hownerSource : owner = self.1.source := Subtype.ext hsourceRaw
  have htarget : self.1.target = x.1.1.1.target := by
    apply Subtype.ext
    calc
      self.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p self.1.source := self.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p owner := by rw [hownerSource]
      _ = x.1.1.1.target.1 := hownerSelf
  apply self.1.exceptional
  calc
    self.1.source.1 = owner.1 := congrArg Subtype.val hownerSource.symm
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target := rfl
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p self.1.target := by rw [htarget]



theorem canonicalStableRawComponentReferenceOwner_directOccupant_source
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.2.1.source.1 =
      canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p collision.1.1.1.1.1.target := by
  have htoken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1.1.1 collision.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.2.1 := by
    simpa only [canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
      canonicalStableRawComponentDirectEmbedding_apply] using
        congrArg Subtype.val collision.2
  have hsource := congrArg (fun token :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.1.1) htoken
  unfold canonicalStableRawReferenceOwnerLeftToken
    canonicalStableRawStateLeftToken at hsource
  rw [dif_neg collision.1.2.2.2] at hsource
  exact hsource.symm




noncomputable def canonicalStableRawComponentReferenceSourceCollisionEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  let f : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ->
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun x =>
    ⟨canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          x.1.1.1.1.1 x.1.1.1.1.2.2,
      (canonicalStableRawReferenceSourceLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          x.1.1.1.1.1 x.1.1.1.1.2.2).trans x.1.1.1.1.2.1⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  apply StatMech.FrontierA.crossCollision_fst_injective
  apply StatMech.FrontierA.crossCollision_fst_injective
  apply Subtype.ext
  apply canonicalStableRawReferenceSourceLeftToken_eq_imp
    ends m j k l zero hloop hjk hkl hk0 p
      x.1.1.1.1.1 y.1.1.1.1.1 x.1.1.1.1.2.2 y.1.1.1.1.2.2
  exact congrArg Subtype.val hxy

@[simp] theorem canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    (canonicalStableRawComponentReferenceSourceCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component x).1 =
      canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          x.1.1.1.1.1 x.1.1.1.1.2.2 := rfl

theorem canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_first
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x ≠
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1.1 := by
  intro h
  apply canonicalStableRawReferenceOwner_source_ne
    ends m j k l zero hloop hjk hkl hk0 p x.1.1.1.1.1
  have hsource := congrArg
    (fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.1) h
  simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
    canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
    canonicalStableRawReferenceSourceLeftToken_source,
    canonicalStableRawReferenceOwnerLeftToken_source] using hsource





theorem canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_firstRange
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (old : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x ≠
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component old := by
  intro heq
  let sx := x.1.1.1.1.1
  let sy := old.1.1.1
  let c := sx.source
  let r := canonicalStableRawReferenceOwner
    ends m j k l zero hloop hjk hkl hk0 p sx
  let d := sy.source
  let q := canonicalStableRawReferenceOwner
    ends m j k l zero hloop hjk hkl hk0 p sy
  have hcr : c ≠ r := canonicalStableRawReferenceOwner_source_ne
    ends m j k l zero hloop hjk hkl hk0 p sx
  have hdq : d ≠ q := canonicalStableRawReferenceOwner_source_ne
    ends m j k l zero hloop hjk hkl hk0 p sy
  have hbaseCR : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r :=
    canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p sx x.1.1.1.1.2.2
  have hbaseDQ : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p d =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p q :=
    canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p sy old.1.1.2.2
  have hcq : c = q := by
    have h := congrArg
      (fun token : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.1) heq
    simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
      canonicalStableRawReferenceSourceLeftToken_source,
      canonicalStableRawReferenceOwnerLeftToken_source] using h
  have htarget : (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p c r hcr hbaseCR).target =
      (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p d q hdq hbaseDQ).target := by
    have h := congrArg
      (fun token : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.2.1) heq
    exact h
  have hcomm := canonicalStableRawReferenceAlternateData_target_comm
    ends m j k l zero hloop hjk hkl hk0 p c r hcr hbaseCR
  have hrd : r = d :=
    canonicalStableRawReferenceAlternateData_target_injective_of_reference_eq
      ends m j k l zero hloop hjk hkl hk0 p r d c q hcr.symm hdq
        hbaseCR.symm hbaseDQ hcq (hcomm.symm.trans htarget)
  have htargetState : sy.target = sx.target := by
    apply Subtype.ext
    calc
      sy.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p d := old.1.1.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p r := by rw [← hrd]
      _ = sx.target.1 := canonicalStableRawReferenceOwner_selfBase
        ends m j k l zero hloop hjk hkl hk0 p sx x.1.1.1.1.2.2
  apply sy.exceptional
  calc
    sy.source.1 = d.1 := rfl
    _ = r.1 := congrArg Subtype.val hrd.symm
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p sx.target := rfl
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p sy.target := by rw [htargetState]

theorem canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_occupant
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x ≠
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1.2 := by
  intro h
  apply x.1.1.1.1.1.exceptional
  have htoken : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          x.1.1.1.1.1 x.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1 := by
    simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
      canonicalStableRawComponentDirectEmbedding_apply] using
        congrArg Subtype.val h
  have hsource : x.1.1.1.1.1.source =
      (canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1).1 := by
    simpa only [canonicalStableRawReferenceSourceLeftToken_source] using
      congrArg Sigma.fst htoken
  unfold canonicalStableRawStateLeftToken at hsource
  rw [dif_neg x.1.2.2.2] at hsource
  calc
    x.1.1.1.1.1.source.1 = x.1.2.1.source.1 := congrArg Subtype.val hsource
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.1.1.target :=
      canonicalStableRawComponentReferenceOwner_directOccupant_source
        ends m j k l zero hloop hjk hkl hk0 p hno component x





theorem canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hcollision : canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x =
      canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self) :
    self.1 = x.1.1.1.1.1 ∧
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1.1.1 ∧
      x.1.2.1 = canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1.1.1 := by
  let s := x.1.1.1.1.1
  let d := x.1.2.1
  have htoken : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s x.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno self.1 := by
    simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
      canonicalStableRawComponentSelfEmbedding_apply] using
        congrArg Subtype.val hcollision
  have hsource : s.source = self.1.source := by
    have h := congrArg Sigma.fst htoken
    unfold canonicalStableRawStateLeftToken at h
    rw [dif_pos self.2.2] at h
    exact h
  have hstate : self.1 = s := by
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource.symm
    apply Subtype.ext
    calc
      self.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p self.1.source := self.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p s.source := by rw [hsource]
      _ = s.target.1 := x.1.1.1.1.2.2.symm
  have hsourceReroute : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s x.1.1.1.1.2.2 =
      canonicalStableRawSelfRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s x.1.1.1.1.2.2 := by
    calc
      canonicalStableRawReferenceSourceLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s x.1.1.1.1.2.2 =
        canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno self.1 := htoken
      _ = canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s :=
        congrArg (canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno) hstate
      _ = canonicalStableRawSelfRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s x.1.1.1.1.2.2 := by
        unfold canonicalStableRawStateLeftToken
        rw [dif_pos x.1.1.1.1.2.2]
  have hownerReroute :=
    canonicalStableRawReferenceOwnerLeftToken_eq_selfOwnerReroute
      ends m j k l zero hloop hjk hkl hk0 p hno s
        x.1.1.1.1.2.2 hsourceReroute
  have hownerDirect : canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s x.1.1.1.1.2.2 =
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p d x.1.2.2.2 := by
    have hfirst : canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s x.1.1.1.1.2.2 =
        canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno d := by
      simpa only [canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
        canonicalStableRawComponentDirectEmbedding_apply] using
          congrArg Subtype.val x.2
    unfold canonicalStableRawStateLeftToken at hfirst
    rw [dif_neg x.1.2.2.2] at hfirst
    exact hownerReroute.symm.trans hfirst
  have hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno s := by
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno s with
      hadvancing | hstable
    · exact hadvancing
    · exfalso
      apply canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno s
          x.1.1.1.1.2.2 hstable
      rw [hownerDirect]
      exact canonicalStableRawDirectLeftToken_isExceptional
        ends m j k l zero hloop hjk hkl hk0 p d x.1.2.2.2
  have hnextSource : (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).source =
      canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s := by
    apply Subtype.ext
    exact hadvancing
  have hdSource : d.source = canonicalStableRawReferenceOwner
      ends m j k l zero hloop hjk hkl hk0 p s := by
    have h := congrArg Sigma.fst hownerDirect
    exact h.symm
  have hdTarget : d.target = (canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s).target := by
    apply Subtype.ext
    exact (congrArg (fun token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.2.1) hownerDirect).symm
  refine ⟨hstate, hadvancing, ?_⟩
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
  · exact hdSource.trans hnextSource.symm
  · exact hdTarget




theorem canonicalStableRawComponentReferenceSource_selfCollision_next_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Function.Injective fun collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) =>
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1.1.1.1.1 := by
  intro x y hnext
  have hx :=
    canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component
        x.1.1 x.1.2 x.2
  have hy :=
    canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component
        y.1.1 y.1.2 y.2
  apply StatMech.FrontierA.crossCollision_fst_injective
  apply StatMech.FrontierA.crossCollision_snd_injective
  apply Subtype.ext
  exact hx.2.2.trans (hnext.trans hy.2.2.symm)




noncomputable def canonicalStableRawReferenceSourceSelfCollisionToDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : StatMech.FrontierA.crossCollision sourceMap selfMap ->
      StatMech.FrontierA.crossCollision sourceMap directMap := fun collision => by
    have hforce :=
      canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.1 collision.1.2 collision.2
    have hselfState : collision.1.2 = collision.1.1.1.1.1.1 := by
      apply Subtype.ext
      exact hforce.1
    exact ⟨(collision.1.1, collision.1.1.1.1.1.2),
      collision.2.trans ((congrArg selfMap hselfState).trans
        collision.1.1.1.1.2)⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  apply StatMech.FrontierA.crossCollision_fst_injective
  change f x = f y at hxy
  exact congrArg (fun collision : StatMech.FrontierA.crossCollision
    sourceMap directMap => collision.1.1) hxy




theorem canonicalStableRawComponentReferenceSource_directCollision_source
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.2.1.source = collision.1.1.1.1.1.1.1.source := by
  have htoken := congrArg Subtype.val collision.2
  have hsource := congrArg Sigma.fst htoken
  simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
    canonicalStableRawComponentDirectEmbedding_apply,
    canonicalStableRawReferenceSourceLeftToken_source,
    canonicalStableRawStateLeftToken, dif_neg collision.1.2.2.2] using
      hsource.symm



theorem canonicalStableRawComponentReferenceSource_directCollision_target
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.2.1.target = collision.1.1.1.2.1.target := by
  apply Subtype.ext
  have hsourceToken : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1.1.1.1.1 collision.1.1.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.2.1 := by
    simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
      canonicalStableRawComponentDirectEmbedding_apply] using
        congrArg Subtype.val collision.2
  have hsourceTarget := congrArg
    (fun token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.2.1) hsourceToken
  have hownerToken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1.1.1.1.1 collision.1.1.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1.2.1 := by
    simpa only [canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
      canonicalStableRawComponentDirectEmbedding_apply] using
        congrArg Subtype.val collision.1.1.2
  have hownerTarget := congrArg
    (fun token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.2.1) hownerToken
  simp only [canonicalStableRawReferenceSourceLeftToken_target,
    canonicalStableRawReferenceOwnerLeftToken_target] at hsourceTarget hownerTarget
  unfold canonicalStableRawStateLeftToken at hsourceTarget hownerTarget
  rw [dif_neg collision.1.2.2.2] at hsourceTarget
  rw [dif_neg collision.1.1.1.2.2.2] at hownerTarget
  exact hsourceTarget.symm.trans hownerTarget



theorem canonicalStableRawComponentReferenceSource_directCollision_selfBase_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        collision.1.2.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1.2.1.source := by
  let s := collision.1.1.1.1.1.1.1
  have hz : collision.1.2.1.source = s.source :=
    canonicalStableRawComponentReferenceSource_directCollision_source
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hd : collision.1.1.1.2.1.source =
      canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s := by
    apply Subtype.ext
    exact canonicalStableRawComponentReferenceOwner_directOccupant_source
      ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1
  calc
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        collision.1.2.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        s.source := congrArg _ hz
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p s) :=
      canonicalStableRawReferenceOwner_sourceBase
        ends m j k l zero hloop hjk hkl hk0 p s
          collision.1.1.1.1.1.1.2.2
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1.2.1.source := congrArg _ hd.symm




theorem canonicalStableRawComponentReferenceSource_directCollision_threeSources
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ owner : ↑(canonicalRawCommonClosure ends m j k l zero p),
      collision.1.2.1.source ≠ collision.1.1.1.2.1.source ∧
        collision.1.2.1.source ≠ owner ∧
        collision.1.1.1.2.1.source ≠ owner ∧
        CanonicalRawGateRelated ends m j k l zero p
          collision.1.2.1.source.1 collision.1.2.1.target.1 ∧
        CanonicalRawGateRelated ends m j k l zero p
          collision.1.1.1.2.1.source.1 collision.1.2.1.target.1 ∧
        CanonicalRawGateRelated ends m j k l zero p
          owner.1 collision.1.2.1.target.1 := by
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p collision.1.2.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p collision.1.2.1.target⟩
  have htarget :=
    canonicalStableRawComponentReferenceSource_directCollision_target
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hsource :=
    canonicalStableRawComponentReferenceSource_directCollision_source
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hfirstSecond : collision.1.2.1.source ≠
      collision.1.1.1.2.1.source := by
    intro heq
    apply collision.1.1.1.1.1.1.1.exceptional
    calc
      collision.1.1.1.1.1.1.1.source.1 =
          collision.1.2.1.source.1 := congrArg Subtype.val hsource.symm
      _ = collision.1.1.1.2.1.source.1 := congrArg Subtype.val heq
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p collision.1.1.1.1.1.1.1.target :=
        canonicalStableRawComponentReferenceOwner_directOccupant_source
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision.1.1
  have hfirstOwner : collision.1.2.1.source ≠ owner := by
    intro heq
    apply collision.1.2.1.exceptional
    exact congrArg Subtype.val heq
  have hsecondOwner : collision.1.1.1.2.1.source ≠ owner := by
    intro heq
    apply collision.1.1.1.2.1.exceptional
    rw [← htarget]
    exact congrArg Subtype.val heq
  refine ⟨owner, hfirstSecond, hfirstOwner, hsecondOwner,
    collision.1.2.1.related, ?_, ?_⟩
  · rw [htarget]
    exact collision.1.1.1.2.1.related
  · exact canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1.target



theorem canonicalStableRawComponentReferenceSource_directCollision_three_le_degree
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let degree : Nat := by
      classical
      exact ((canonicalRawCommonClosure ends m j k l zero p).filter
        (fun c => CanonicalRawGateRelated ends m j k l zero p c
          collision.1.2.1.target.1)).card
    3 ≤ degree := by
  classical
  dsimp only
  obtain ⟨owner, h12, h1o, h2o, hrel1, hrel2, hrelo⟩ :=
    canonicalStableRawComponentReferenceSource_directCollision_threeSources
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have h12v : collision.1.2.1.source.1 ≠
      collision.1.1.1.2.1.source.1 := fun h => h12 (Subtype.ext h)
  have h1ov : collision.1.2.1.source.1 ≠ owner.1 :=
    fun h => h1o (Subtype.ext h)
  have h2ov : collision.1.1.1.2.1.source.1 ≠ owner.1 :=
    fun h => h2o (Subtype.ext h)
  let witnesses : Finset (leftSourceMaskFiber ends m j k l zero p) :=
    {collision.1.2.1.source.1, collision.1.1.1.2.1.source.1, owner.1}
  have hwitnesses : witnesses.card = 3 := by
    simp only [witnesses]
    simp [h12v, h1ov, h2ov]
  rw [← hwitnesses]
  apply Finset.card_le_card
  intro c hc
  simp only [witnesses, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · exact Finset.mem_filter.mpr ⟨collision.1.2.1.source.2, hrel1⟩
  · exact Finset.mem_filter.mpr ⟨collision.1.1.1.2.1.source.2, hrel2⟩
  · exact Finset.mem_filter.mpr ⟨owner.2, hrelo⟩





noncomputable def
    canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      {direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component //
        ∀ old : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          direct ≠ old.1.2} := by
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : StatMech.FrontierA.crossCollision sourceMap directMap ->
      {direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component //
        ∀ old : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          directMap, direct ≠ old.1.2} := fun collision =>
    ⟨collision.1.2, by
      intro old heq
      apply canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_firstRange
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.1 old.1.1
      calc
        sourceMap collision.1.1 = directMap collision.1.2 := collision.2
        _ = directMap old.1.2 := congrArg directMap heq
        _ = canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              old.1.1 := old.2.symm⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  apply StatMech.FrontierA.crossCollision_snd_injective
  exact congrArg Subtype.val hxy




noncomputable def canonicalStableRawResidualTargetBlockSourceEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htarget : ∀ x ∈ A, x.1.2.1.target = x₀.1.2.1.target) :
    ((↑A ⊕ ↑A) ⊕ Unit) ↪
      {source : ↑(canonicalRawCommonClosure ends m j k l zero p) //
        CanonicalRawGateRelated ends m j k l zero p source.1
          x₀.1.2.1.target.1} := by
  let unused :=
    canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x₀.1.2.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p x₀.1.2.1.target⟩
  let f : ((↑A ⊕ ↑A) ⊕ Unit) →
      {source : ↑(canonicalRawCommonClosure ends m j k l zero p) //
        CanonicalRawGateRelated ends m j k l zero p source.1
          x₀.1.2.1.target.1}
    | Sum.inl (Sum.inl x) =>
        ⟨x.1.1.2.1.source, by
          rw [← htarget x.1 x.2]
          exact x.1.1.2.1.related⟩
    | Sum.inl (Sum.inr x) =>
        ⟨x.1.1.1.1.2.1.source, by
          rw [← htarget x.1 x.2]
          rw [canonicalStableRawComponentReferenceSource_directCollision_target
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1]
          exact x.1.1.1.1.2.1.related⟩
    | Sum.inr _ =>
        ⟨owner, canonicalStableRawPreferredRightBase_related
          ends m j k l zero hloop hjk hkl hk0 p x₀.1.2.1.target⟩
  have hexposedTarget (x : ↑A) : x.1.1.2.1.target = x₀.1.2.1.target :=
    htarget x.1 x.2
  have hrootTarget (x : ↑A) :
      x.1.1.1.1.2.1.target = x₀.1.2.1.target :=
    (canonicalStableRawComponentReferenceSource_directCollision_target
      ends m j k l zero hloop hjk hkl hk0 p hno component x.1).symm.trans
        (htarget x.1 x.2)
  have hexposedInjective : Function.Injective fun x : ↑A =>
      x.1.1.2.1.source := by
    intro x y hs
    apply Subtype.ext
    apply StatMech.FrontierA.crossCollision_snd_injective
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
    apply Subtype.ext
    exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq hs
      ((hexposedTarget x).trans (hexposedTarget y).symm)
  have hrootInjective : Function.Injective fun x : ↑A =>
      x.1.1.1.1.2.1.source := by
    intro x y hs
    apply Subtype.ext
    apply StatMech.FrontierA.crossCollision_fst_injective
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
    apply StatMech.FrontierA.crossCollision_snd_injective
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
    apply Subtype.ext
    exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq hs
      ((hrootTarget x).trans (hrootTarget y).symm)
  have hexposedRootNe (x y : ↑A) :
      x.1.1.2.1.source ≠ y.1.1.1.1.2.1.source := by
    intro hs
    apply (unused x.1).2 y.1.1.1
    apply Subtype.ext
    exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq hs
      ((hexposedTarget x).trans (hrootTarget y).symm)
  have hexposedOwnerNe (x : ↑A) : x.1.1.2.1.source ≠ owner := by
    intro hs
    apply x.1.1.2.1.exceptional
    calc
      x.1.1.2.1.source.1 = owner.1 := congrArg Subtype.val hs
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p x₀.1.2.1.target := rfl
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p x.1.1.2.1.target := by rw [hexposedTarget x]
  have hrootOwnerNe (x : ↑A) : x.1.1.1.1.2.1.source ≠ owner := by
    intro hs
    apply x.1.1.1.1.2.1.exceptional
    calc
      x.1.1.1.1.2.1.source.1 = owner.1 := congrArg Subtype.val hs
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p x₀.1.2.1.target := rfl
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p x.1.1.1.1.2.1.target := by rw [hrootTarget x]
  refine ⟨f, ?_⟩
  intro x y hxy
  cases x with
  | inl x =>
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              cases y with
              | inl y =>
                  congr 2
                  exact hexposedInjective (congrArg Subtype.val hxy)
              | inr y =>
                  exfalso
                  exact hexposedRootNe x y (congrArg Subtype.val hxy)
          | inr y =>
              exfalso
              exact hexposedOwnerNe x (congrArg Subtype.val hxy)
      | inr x =>
          cases y with
          | inl y =>
              cases y with
              | inl y =>
                  exfalso
                  exact hexposedRootNe y x (congrArg Subtype.val hxy).symm
              | inr y =>
                  congr 2
                  exact hrootInjective (congrArg Subtype.val hxy)
          | inr y =>
              exfalso
              exact hrootOwnerNe x (congrArg Subtype.val hxy)
  | inr x =>
      cases y with
      | inl y =>
          cases y with
          | inl y =>
              exfalso
              exact hexposedOwnerNe y (congrArg Subtype.val hxy).symm
          | inr y =>
              exfalso
              exact hrootOwnerNe y (congrArg Subtype.val hxy).symm
      | inr y => rfl


theorem canonicalStableRawResidualTargetBlock_two_mul_card_add_one_le_degree
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htarget : ∀ x ∈ A, x.1.2.1.target = x₀.1.2.1.target) :
    let degree : Nat := by
      classical
      exact ((canonicalRawCommonClosure ends m j k l zero p).filter
        (fun c => CanonicalRawGateRelated ends m j k l zero p c
          x₀.1.2.1.target.1)).card
    2 * A.card + 1 ≤ degree := by
  classical
  dsimp only
  let Neighbor :=
    {source : ↑(canonicalRawCommonClosure ends m j k l zero p) //
      CanonicalRawGateRelated ends m j k l zero p source.1
        x₀.1.2.1.target.1}
  let emb := canonicalStableRawResidualTargetBlockSourceEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ htarget
  letI : Fintype Neighbor := Fintype.ofInjective
    (fun source : Neighbor => source.1.1) (by
      intro x y hxy
      exact Subtype.ext (Subtype.ext hxy))
  have hcard := Fintype.card_le_of_injective emb emb.injective
  have hneighbor : Fintype.card Neighbor =
      ((canonicalRawCommonClosure ends m j k l zero p).filter
        (fun c => CanonicalRawGateRelated ends m j k l zero p c
          x₀.1.2.1.target.1)).card := by
    classical
    let filtered := (canonicalRawCommonClosure ends m j k l zero p).filter
      (fun c => CanonicalRawGateRelated ends m j k l zero p c
        x₀.1.2.1.target.1)
    let e : Neighbor ≃ ↑filtered := by
      refine
        { toFun := fun source =>
            ⟨source.1.1, Finset.mem_filter.mpr ⟨source.1.2, source.2⟩⟩
          invFun := fun source =>
            ⟨⟨source.1, (Finset.mem_filter.mp source.2).1⟩,
              (Finset.mem_filter.mp source.2).2⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro source
        apply Subtype.ext
        apply Subtype.ext
        rfl
      · intro source
        apply Subtype.ext
        rfl
    calc
      Fintype.card Neighbor = Fintype.card ↑filtered := Fintype.card_congr e
      _ = filtered.card := Fintype.card_coe filtered
      _ = _ := rfl
  rw [Fintype.card_sum, Fintype.card_sum] at hcard
  rw [Fintype.card_coe A] at hcard
  change A.card + A.card + Fintype.card Unit ≤ Fintype.card Neighbor at hcard
  rw [Fintype.card_unique, hneighbor] at hcard
  omega




theorem card_le_canonicalRawRelationNeighborhood_of_residualTargetFiberBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htarget : ∀ x ∈ A, x.1.2.1.target = x₀.1.2.1.target)
    (r : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hbase : ∀ x ∈ A,
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        x.1.2.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      sources.card = 2 * A.card ∧
        sources.card ≤
          (StatMech.FrontierA.finiteRelationNeighborhood
            (CanonicalRawGateRelated ends m j k l zero p)
            (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let block := canonicalStableRawResidualTargetBlockSourceEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ htarget
  let sourceEmbedding : (↑A ⊕ ↑A) ↪
      ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨fun x => (block (Sum.inl x)).1, fun x y hxy => by
      apply Sum.inl_injective
      apply block.injective
      apply Subtype.ext
      exact hxy⟩
  let sources := Finset.univ.image sourceEmbedding
  have hsourcesCard : sources.card = 2 * A.card := by
    change (Finset.univ.image sourceEmbedding).card = 2 * A.card
    rw [Finset.card_image_of_injective _ sourceEmbedding.injective,
      Finset.card_univ, Fintype.card_sum]
    rw [Fintype.card_coe A]
    omega
  have hfiber : ∀ c ∈ sources,
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r := by
    intro c hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
    cases x with
    | inl x => exact hbase x.1 x.2
    | inr x =>
        exact (canonicalStableRawComponentReferenceSource_directCollision_selfBase_eq
          ends m j k l zero hloop hjk hkl hk0 p hno component x.1).symm.trans
            (hbase x.1 x.2)
  refine ⟨sources, hsourcesCard, ?_⟩
  exact card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber
    ends m j k l zero hloop hjk hkl hk0 p sources r hfiber



theorem canonicalStableRaw_referenceSourceDirectCollision_card_add_le_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Nat.card (StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)) +
      Nat.card (StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)) ≤
      Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let unused :=
    canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let combined : StatMech.FrontierA.crossCollision first directMap ⊕
        StatMech.FrontierA.crossCollision sourceMap directMap →
      CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl old => old.1.2
    | Sum.inr collision => (unused collision).1
  have hinjective : Function.Injective combined := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            congr 1
            exact StatMech.FrontierA.crossCollision_snd_injective
              first directMap hxy
        | inr y =>
            exfalso
            exact (unused y).2 x hxy.symm
    | inr x =>
        cases y with
        | inl y =>
            exfalso
            exact (unused x).2 y hxy
        | inr y =>
            congr 1
            apply unused.injective
            apply Subtype.ext
            exact hxy
  letI : Fintype (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Fintype.ofFinite _
  letI : Fintype (CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Fintype.ofFinite _
  letI : DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Classical.decEq _
  letI : Fintype (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      directMap) := Fintype.ofInjective
    (fun collision => collision.1.1)
    (StatMech.FrontierA.crossCollision_fst_injective
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component) directMap)
  letI : Fintype (StatMech.FrontierA.crossCollision first directMap) :=
    Fintype.ofInjective (fun collision => collision.1.1)
      (StatMech.FrontierA.crossCollision_fst_injective first directMap)
  letI : Fintype (StatMech.FrontierA.crossCollision sourceMap directMap) :=
    Fintype.ofInjective (fun collision => collision.1.1)
      (StatMech.FrontierA.crossCollision_fst_injective sourceMap directMap)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sum] using
    Fintype.card_le_of_injective combined hinjective



noncomputable def
    canonicalStableRawReferenceSourceSelfCollisionToUnusedDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      {direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component //
        ∀ old : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          direct ≠ old.1.2} :=
  (canonicalStableRawReferenceSourceSelfCollisionToDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).trans
    (canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)



noncomputable def canonicalStableRawComponentSecondCollisionAlternateToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  ⟨canonicalStableRawDirectAlternateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.2.1 collision.1.2.2.2,
    (canonicalStableRawDirectAlternateLeftToken_fullComponent
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.2.1 collision.1.2.2.2).trans collision.1.2.2.1⟩



theorem canonicalStableRawComponentSecondCollisionAlternateToken_ne_occupant
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 := by
  intro h
  apply canonicalStableRawDirectAlternateLeftToken_ne_natural
    ends m j k l zero hloop hjk hkl hk0 p hno
      collision.1.2.1 collision.1.2.2.2
  have h' := congrArg Subtype.val h
  simpa only [canonicalStableRawComponentSecondCollisionAlternateToken,
    canonicalStableRawComponentDirectEmbedding_apply] using h'

theorem canonicalStableRawComponentSecondCollisionAlternateToken_ne_first
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 := by
  intro h
  apply canonicalStableRawComponentSecondCollisionAlternateToken_ne_occupant
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  exact h.trans collision.2



theorem canonicalStableRawComponentSecondCollisionAlternateToken_merge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x y : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hxy : canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component x =
      canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component y) :
    x.1.2.1 = y.1.2.1 ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p x.1.2.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p x.1.2.1 u := by
  let token := canonicalStableRawDirectAlternateLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1 x.1.2.2.2
  have hxInc : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token x.1.2.1 :=
    (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token x.1.2.1).2
        (canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1 x.1.2.2.2)
  have hyInc : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token y.1.2.1 := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token y.1.2.1).2
    have hy := canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno y.1.2.1 y.1.2.2.2
    have htoken := congrArg Subtype.val hxy
    change canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1 x.1.2.2.2 =
      canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno y.1.2.1 y.1.2.2.2 at htoken
    change CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno
            x.1.2.1 x.1.2.2.2) y.1.2.1
    rw [htoken]
    exact hy
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno token
        x.1.2.1 y.1.2.1 hxInc hyInc with heq | hstable | hadvancing
  · exact Or.inl heq
  · exact Or.inr ⟨hstable.choose, Or.inl hstable.choose_spec.2.1⟩
  · exact Or.inr ⟨hadvancing.choose, Or.inr hadvancing.choose_spec.2.1⟩





theorem canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentSecondCollisionAlternateToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
              collision).1 ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let token := canonicalStableRawDirectAlternateLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno
      collision.1.2.1 collision.1.2.2.2
  have hincidence : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token collision.1.2.1 :=
    canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.2.1 collision.1.2.2.2
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawStateTokenIncidence_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno token
        collision.1.2.1 hincidence
  refine ⟨u, huTarget, huKind, ?_⟩
  exact huComponent.trans collision.1.2.2.1



noncomputable def canonicalStableRawComponentSecondCollisionAlternateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  classical
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Second := StatMech.FrontierA.crossCollision
    (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  letI : Fintype Direct := Fintype.ofFinite Direct
  letI : Fintype Second := Fintype.ofInjective
    (fun collision : Second => collision.1.2)
    (StatMech.FrontierA.crossCollision_snd_injective
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
  exact Finset.univ.filter fun collision =>
    canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component collision =
      canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor





theorem canonicalStableRawComponentSecondCollisionAlternateFiber_outputBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hcollision : collision ∈
      canonicalStableRawComponentSecondCollisionAlternateFiber
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor) :
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentSecondCollisionAlternateToken
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  have htoken : canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component collision =
      canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor :=
    by
      simpa only [canonicalStableRawComponentSecondCollisionAlternateFiber,
        Finset.mem_filter, Finset.mem_univ, true_and] using hcollision
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  refine ⟨u, ?_, huKind, huComponent⟩
  exact huTarget.trans (congrArg
    (canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p)
    (congrArg Subtype.val htoken))






theorem canonicalStableRawComponentSecondCollisionAlternateFiber_source_or_owner
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hcollision : collision ∈
      canonicalStableRawComponentSecondCollisionAlternateFiber
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor) :
    let direct := collision.1.2
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p direct.1.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p direct.1.target⟩
    (next.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p direct.1.source ∧
        owner =
          (canonicalStableRawComponentSecondCollisionAlternateToken
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1.1) ∨
      (next.target.1 ≠ canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p direct.1.source ∧
        direct.1.source =
          (canonicalStableRawComponentSecondCollisionAlternateToken
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1.1) := by
  classical
  dsimp only
  have htoken : canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component collision =
      canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor := by
    simpa only [canonicalStableRawComponentSecondCollisionAlternateFiber,
      Finset.mem_filter, Finset.mem_univ, true_and] using hcollision
  have hsource := congrArg
    (fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.1)
    htoken
  rcases canonicalStableRawDirectAlternateLeftToken_source_split
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.2.1 collision.1.2.2.2 with howner | hdirect
  · exact Or.inl ⟨howner.1, howner.2.symm.trans hsource⟩
  · exact Or.inr ⟨hdirect.1, hdirect.2.symm.trans hsource⟩



noncomputable def canonicalStableRawPreferredFreeLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hfree : target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p target⟩) :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  exact
    ⟨⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p target⟩,
      ⟨target.1, Finset.mem_erase.mpr
        ⟨hfree, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, canonicalStableRawPreferredRightBase_related
            ends m j k l zero hloop hjk hkl hk0 p target⟩⟩⟩⟩

@[simp] theorem canonicalStableRawPreferredFreeLeftToken_target
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hfree : target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p target⟩) :
    canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawPreferredFreeLeftToken
            ends m j k l zero hloop hjk hkl hk0 p target hfree) = target := by
  apply Subtype.ext
  rfl

theorem canonicalStableRawPreferredFreeLeftToken_not_exceptional
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hfree : target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p target⟩) :
    ¬ CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawPreferredFreeLeftToken
          ends m j k l zero hloop hjk hkl hk0 p target hfree) := by
  intro hexceptional
  apply hexceptional
  rfl



theorem canonicalStableRawPreferredFreeLeftToken_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hfree : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p u.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p u.target⟩) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawPreferredFreeLeftToken
          ends m j k l zero hloop hjk hkl hk0 p u.target hfree) u := by
  refine ⟨Or.inr ?_, ?_, ?_⟩
  · apply Subtype.ext
    rfl
  · exact u.related
  · exact canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p u.target


theorem canonicalStableRawPreferredFreeLeftToken_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hfree : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p u.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p u.target⟩) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawPreferredFreeLeftToken
            ends m j k l zero hloop hjk hkl hk0 p u.target hfree) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno u :=
  canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno _ u
      (canonicalStableRawPreferredFreeLeftToken_incident
        ends m j k l zero hloop hjk hkl hk0 p u hfree)



noncomputable def CanonicalStableRawComponentCollisionCharge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) : Prop := by
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  exact ∃ charge : StatMech.FrontierA.crossCollision selfMap directMap ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
    (∀ collision self, charge collision ≠ selfMap self) ∧
      ∀ collision direct, charge collision ≠ directMap direct




noncomputable def CanonicalStableRawComponentSecondCollisionCharge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) : Prop := by
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  exact ∃ second : StatMech.FrontierA.crossCollision first directMap ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
    (∀ collision self, second collision ≠ selfMap self) ∧
    (∀ collision direct, second collision ≠ directMap direct) ∧
      ∀ collision old, second collision ≠ first old





theorem canonicalStableRawComponentSecondCollisionCharge_of_sourceDirectDisjoint
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdisjoint : ∀ collision direct,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct) :
    CanonicalStableRawComponentSecondCollisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  refine ⟨sourceMap, ?_, hdisjoint, ?_⟩
  · intro collision self heq
    let selfCollision : StatMech.FrontierA.crossCollision sourceMap selfMap :=
      ⟨(collision, self), heq⟩
    let directCollision :=
      canonicalStableRawReferenceSourceSelfCollisionToDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component selfCollision
    exact hdisjoint collision directCollision.1.2 directCollision.2
  · intro collision old
    exact canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_firstRange
      ends m j k l zero hloop hjk hkl hk0 p hno component collision old




theorem canonicalStableRawComponentSecondCollisionCharge_of_cardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
        Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    CanonicalStableRawComponentSecondCollisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let State := CanonicalStableRawComponentState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let join : Self ⊕ Direct ↪ State := by
    let toState : Self ⊕ Direct → State
      | Sum.inl s => ⟨s.1, s.2.1⟩
      | Sum.inr s => ⟨s.1, s.2.1⟩
    refine ⟨toState, ?_⟩
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            have hv : x.1 = y.1 :=
              congrArg (fun z : State => z.1) hxy
            exact congrArg Sum.inl (Subtype.ext hv)
        | inr y =>
            exfalso
            apply y.2.2
            rw [← congrArg Subtype.val hxy]
            exact x.2.2
    | inr x =>
        cases y with
        | inl y =>
            exfalso
            apply x.2.2
            rw [congrArg Subtype.val hxy]
            exact y.2.2
        | inr y =>
            have hv : x.1 = y.1 :=
              congrArg (fun z : State => z.1) hxy
            exact congrArg Sum.inr (Subtype.ext hv)
  have hsumCard : Fintype.card Self + Fintype.card Direct ≤
      Fintype.card Token := by
    have hjoin := Fintype.card_le_of_injective join join.injective
    simpa only [Self, Direct, State, Token, Fintype.card_sum] using
      hjoin.trans hcard
  exact StatMech.FrontierA.exists_secondCollisionCharge_of_card_le
    selfMap directMap first
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      hsumCard



theorem canonicalStableRawComponentCrossCollision_classification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    CanonicalStableRawSelfDirectTokenCollision
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.1.1 collision.1.2.1 := by
  apply canonicalStableRawSelfDirectTokenCollision_of_token_eq
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.1.1 collision.1.2.1 collision.1.1.2.2 collision.1.2.2.2
  have htoken := congrArg Subtype.val collision.2
  simpa only [canonicalStableRawComponentSelfEmbedding_apply,
    canonicalStableRawComponentDirectEmbedding_apply] using htoken

theorem canonicalStableRawComponentCrossCollision_stable_or_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 ∨
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 := by
  have hclassify := canonicalStableRawComponentCrossCollision_classification
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  rcases hclassify.2.2 with ⟨_, hstable⟩ | ⟨hadvancing, _⟩
  · exact Or.inl hstable
  · exact Or.inr hadvancing




theorem canonicalStableRawComponentCrossCollision_source_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Function.Injective fun x : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) =>
      x.1.1.1.source := by
  intro x y hsource
  change x.1.1.1.source = y.1.1.1.source at hsource
  apply StatMech.FrontierA.crossCollision_fst_injective
  apply Subtype.ext
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource
  apply Subtype.ext
  calc
    x.1.1.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.source := x.1.1.2.2
    _ = canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p y.1.1.1.source := by rw [hsource]
    _ = y.1.1.1.target.1 := y.1.1.2.2.symm




theorem canonicalStableRawAdvancingCrossCollision_selfBase_eq_of_next_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x y : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hx : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
    (hy : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1)
    (hnext : canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        x.1.1.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        y.1.1.1.source := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let ownerX : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target⟩
  let ownerY : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p y.1.1.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p y.1.1.1.target⟩
  have hsourceX : (next x.1.1.1).source = ownerX := by
    apply Subtype.ext
    exact hx
  have hsourceY : (next y.1.1.1).source = ownerY := by
    apply Subtype.ext
    exact hy
  have hownerXY : ownerX = ownerY := by
    calc
      ownerX = (next x.1.1.1).source := hsourceX.symm
      _ = (next y.1.1.1).source := congrArg
        (fun s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p => s.source) hnext
      _ = ownerY := hsourceY
  have hownerSelfX : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p ownerX = x.1.1.1.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p x.1.1.1.target
        ⟨x.1.1.1.source, x.1.1.2.2.symm⟩
  have hownerSelfY : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p ownerY = y.1.1.1.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p y.1.1.1.target
        ⟨y.1.1.1.source, y.1.1.2.2.symm⟩
  calc
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        x.1.1.1.source = x.1.1.1.target.1 := x.1.1.2.2.symm
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ownerX := hownerSelfX.symm
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ownerY := by rw [hownerXY]
    _ = y.1.1.1.target.1 := hownerSelfY
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        y.1.1.1.source := y.1.1.2.2





theorem card_le_canonicalRawRelationNeighborhood_of_advancingCollisionBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hx₀ : x₀ ∈ A)
    (hadvancing : ∀ x ∈ A, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
    (hnext : ∀ x ∈ A,
      canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧
      sources.card = A.card ∧
      A.card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let collisionSource := fun x : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) =>
      x.1.1.1.source
  let sources := A.image collisionSource
  have hsourceInjective : Function.Injective collisionSource := by
    intro x y hsource
    change x.1.1.1.source = y.1.1.1.source at hsource
    apply StatMech.FrontierA.crossCollision_fst_injective
    apply Subtype.ext
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource
    apply Subtype.ext
    calc
      x.1.1.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p x.1.1.1.source := x.1.1.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p y.1.1.1.source := by rw [hsource]
      _ = y.1.1.1.target.1 := y.1.1.2.2.symm
  have hsourcesCard : sources.card = A.card := by
    exact Finset.card_image_of_injective A hsourceInjective
  have hfiber : ∀ c ∈ sources,
      canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c =
        canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p (collisionSource x₀) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact canonicalStableRawAdvancingCrossCollision_selfBase_eq_of_next_eq
      ends m j k l zero hloop hjk hkl hk0 p hno component x x₀
        (hadvancing x hx) (hadvancing x₀ hx₀) (hnext x hx)
  refine ⟨sources, ?_, hsourcesCard, ?_⟩
  · intro c
    simp only [sources, collisionSource, Finset.mem_image]
  · rw [← hsourcesCard]
    exact card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber
      ends m j k l zero hloop hjk hkl hk0 p sources
        (collisionSource x₀) hfiber





theorem exists_canonicalRawRelationNeighborhoodEmbedding_of_advancingCollisionBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hx₀ : x₀ ∈ A)
    (hadvancing : ∀ x ∈ A, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
    (hnext : ∀ x ∈ A,
      canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧
      Nonempty (↑A ↪
        ↑(StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩))) := by
  classical
  obtain ⟨sources, hsources, _, hcard⟩ :=
    card_le_canonicalRawRelationNeighborhood_of_advancingCollisionBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀
        hadvancing hnext
  refine ⟨sources, hsources, ?_⟩
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using hcard



theorem canonicalStableRawTokenComponent_embedding_of_sumEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (merged : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let split : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    if hs : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source then
      Sum.inl ⟨s.1, s.2, hs⟩ else Sum.inr ⟨s.1, s.2, hs⟩
  let recover :
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl s => ⟨s.1, s.2.1⟩
    | Sum.inr s => ⟨s.1, s.2.1⟩
  have hrecover : Function.LeftInverse recover split := by
    intro s
    by_cases hs : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source
    · simp [split, recover, hs]
    · simp [split, recover, hs]
  let splitEmbedding : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨split, hrecover.injective⟩
  exact ⟨splitEmbedding.trans merged⟩



theorem canonicalStableRawTokenComponent_embedding_of_secondCollisionCharge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcharge : CanonicalStableRawComponentSecondCollisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨second, hfreshSelf, hfreshDirect, hfreshFirst⟩ := hcharge
  let merged := StatMech.FrontierA.embeddingSumOfCrossCollisionSecondCharge
    selfMap directMap first
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      second hfreshSelf hfreshDirect hfreshFirst
  exact canonicalStableRawTokenComponent_embedding_of_sumEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component merged



theorem canonicalStableRawTokenComponent_embedding_of_sourceDirectDisjoint
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdisjoint : ∀ collision direct,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  canonicalStableRawTokenComponent_embedding_of_secondCollisionCharge
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (canonicalStableRawComponentSecondCollisionCharge_of_sourceDirectDisjoint
        ends m j k l zero hloop hjk hkl hk0 p hno component hdisjoint)




theorem canonicalStableRawComponentSecondCollisionCharge_iff_cardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentSecondCollisionCharge
        ends m j k l zero hloop hjk hkl hk0 p hno component ↔
      Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
        Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  constructor
  · intro hcharge
    obtain ⟨embedding⟩ :=
      canonicalStableRawTokenComponent_embedding_of_secondCollisionCharge
        ends m j k l zero hloop hjk hkl hk0 p hno component hcharge
    exact Fintype.card_le_of_injective embedding embedding.injective
  · exact canonicalStableRawComponentSecondCollisionCharge_of_cardLE
      ends m j k l zero hloop hjk hkl hk0 p hno component



theorem canonicalStableRawTokenComponent_embedding_of_collisionCharge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcharge : CanonicalStableRawComponentCollisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨charge, hfreshSelf, hfreshDirect⟩ := hcharge
  let merged := StatMech.FrontierA.embeddingSumOfCrossCollisionCharge
    selfMap directMap charge hfreshSelf hfreshDirect
  let split : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    if hs : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source then
      Sum.inl ⟨s.1, s.2, hs⟩ else Sum.inr ⟨s.1, s.2, hs⟩
  let recover :
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl s => ⟨s.1, s.2.1⟩
    | Sum.inr s => ⟨s.1, s.2.1⟩
  have hrecover : Function.LeftInverse recover split := by
    intro s
    by_cases hs : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source
    · simp [split, recover, hs]
    · simp [split, recover, hs]
  let splitEmbedding : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨split, hrecover.injective⟩
  exact ⟨splitEmbedding.trans merged⟩


def CanonicalStableRawComponentIncident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  CanonicalStableRawWitnessedStateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p token.1 s.1


noncomputable def canonicalStableRawComponentNaturalToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  ⟨canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s.1,
    (canonicalStableRawStateLeftToken_fullComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2⟩

theorem canonicalStableRawComponentNaturalToken_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component s
        (canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s) := by
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ _).2
  exact canonicalStableRawStateLeftToken_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno s.1





theorem exists_canonicalStableRawComponentPartialMatching_saturating
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    let State :=
      {s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s = component}
    let Token :=
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token = component}
    let incident : State -> Token -> Prop := fun s token =>
      CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p token.1 s.1
    ∃ matching : StatMech.FrontierA.RelationPartialMatching incident,
      matching.IsMaximum ∧
        ∀ s, s ∉ matching.support ->
          ∃ t, matching.toFun t = some
            (⟨canonicalStableRawStateLeftToken
                  ends m j k l zero hloop hjk hkl hk0 p hno s.1,
              (canonicalStableRawStateLeftToken_fullComponent
                ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2⟩ :
              Token) := by
  classical
  dsimp only
  let State :=
    {s : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p //
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s = component}
  let Token :=
    {token : CanonicalStableRawLeftSurplusToken
        ends m j k l zero hloop hjk hkl hk0 p //
      canonicalStableRawFullLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token = component}
  let incident : State -> Token -> Prop := fun s token =>
    CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1 s.1
  obtain ⟨matching, hmaximum, hsaturates⟩ :=
    StatMech.FrontierA.exists_relationPartialMatching_saturating_unmatched
      incident
  refine ⟨matching, hmaximum, ?_⟩
  intro s hs
  let naturalToken : Token :=
    ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1,
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2⟩
  exact hsaturates s hs naturalToken
    ((canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p naturalToken.1 s.1).2
      (canonicalStableRawStateLeftToken_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p hno s.1))





theorem canonicalStableRawComponentHoleMove_classification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState
      (CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let hnatural := canonicalStableRawComponentNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let moved := state.move natural hnatural
    state.hole ≠ moved.hole ∧
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p (natural state.hole).1 ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let hnatural := canonicalStableRawComponentNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let moved := state.move natural hnatural
  have hoccupied : state.matching.toFun moved.hole =
      some (natural state.hole) := by
    exact state.matching_apply_move_hole natural hnatural
  have hne : state.hole ≠ moved.hole := by
    intro h
    apply state.hole_unmatched
    apply (StatMech.FrontierA.RelationPartialMatching.mem_support_iff
      state.matching state.hole).2
    exact ⟨natural state.hole, h ▸ hoccupied⟩
  have hs : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (natural state.hole).1 state.hole.1 := hnatural state.hole
  have ht : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (natural state.hole).1 moved.hole.1 :=
    state.matching.related hoccupied
  have hclassify :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (natural state.hole).1 state.hole.1 moved.hole.1 hs ht
  refine ⟨hne, ?_⟩
  rcases hclassify with heq | hstable | hadvancing
  · exact False.elim (hne (Subtype.ext heq))
  · obtain ⟨u, huTarget, huStable, huComponent, _⟩ := hstable
    exact ⟨u, huTarget, Or.inl huStable, huComponent.trans state.hole.2⟩
  · obtain ⟨u, huTarget, huAdvancing, huComponent, _⟩ := hadvancing
    exact ⟨u, huTarget, Or.inr huAdvancing, huComponent.trans state.hole.2⟩






theorem exists_canonicalStableRawComponentCrossCollision_of_card_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let selfMap := canonicalStableRawComponentSelfEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let directMap := canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let incident := CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let hnatural := canonicalStableRawComponentNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision selfMap directMap,
        state.hole.1 = collision.1.1.1 ∧
          (state.move natural hnatural).hole.1 = collision.1.2.1 := by
  classical
  dsimp only
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let incident := CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let hnatural := canonicalStableRawComponentNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨state, hholes, htoken⟩ :=
    StatMech.FrontierA.RelationPartialMatching.exists_maximalNatural_holeState_collision
      incident natural hnatural hcard
  have hrawToken : canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          (state.move natural hnatural).hole.1 := by
    exact congrArg Subtype.val htoken
  rcases canonicalStableRawStateLeftToken_eq_imp
      ends m j k l zero hloop hjk hkl hk0 p hno
        state.hole.1 (state.move natural hnatural).hole.1 hrawToken with
    heq | hforward | hreverse
  · exact False.elim (hholes (Subtype.ext heq))
  · let self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨state.hole.1, state.hole.2, hforward.1⟩
    let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨(state.move natural hnatural).hole.1,
          (state.move natural hnatural).hole.2, hforward.2.1⟩
    let collision : StatMech.FrontierA.crossCollision selfMap directMap :=
      ⟨(self, direct), by
        apply Subtype.ext
        exact hrawToken⟩
    exact ⟨state, collision, rfl, rfl⟩
  · let self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨(state.move natural hnatural).hole.1,
          (state.move natural hnatural).hole.2, hreverse.1⟩
    let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨state.hole.1, state.hole.2, hreverse.2.1⟩
    let collision : StatMech.FrontierA.crossCollision selfMap directMap :=
      ⟨(self, direct), by
        apply Subtype.ext
        exact hrawToken.symm⟩
    have hback := state.move_move_hole_eq_of_natural_eq
      natural hnatural htoken
    refine ⟨state.move natural hnatural, collision, rfl, ?_⟩
    exact congrArg Subtype.val hback




noncomputable def
    canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  let f : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ->
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun x =>
    ⟨canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          x.1.1.1 x.1.1.2.2,
      (canonicalStableRawReferenceSourceLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          x.1.1.1 x.1.1.2.2).trans x.1.1.2.1⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  apply StatMech.FrontierA.crossCollision_fst_injective
  apply Subtype.ext
  apply canonicalStableRawReferenceSourceLeftToken_eq_imp
    ends m j k l zero hloop hjk hkl hk0 p
      x.1.1.1 y.1.1.1 x.1.1.2.2 y.1.1.2.2
  exact congrArg Subtype.val hxy





theorem exists_canonicalStableRawComponentFirstChargeOccupant_of_card_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let selfMap := canonicalStableRawComponentSelfEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let directMap := canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let incident := CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let hnatural := canonicalStableRawComponentNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision selfMap directMap,
      ∃ third : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        state.hole.1 = collision.1.1.1 ∧
        (state.move natural hnatural).hole.1 = collision.1.2.1 ∧
        state.matching.toFun third = some (first collision) ∧
        third ≠ state.hole ∧
        third ≠ (state.move natural hnatural).hole ∧
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p (first collision).1 ∧
          (CanonicalStableRawOwnerStableOutput
                ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨
              CanonicalStableRawOwnerAdvancingOutput
                ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let incident := CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let hnatural := canonicalStableRawComponentNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨state, collision, hself, hdirect⟩ :=
    exists_canonicalStableRawComponentCrossCollision_of_card_lt
      ends m j k l zero hloop hjk hkl hk0 p hno component hcard
  have hfirstIncident : incident state.hole (first collision) := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p
        (first collision).1 state.hole.1).2
    rw [hself]
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  obtain ⟨third, hthird⟩ :=
    state.maximum.saturates_target_of_unmatched
      state.hole state.hole_unmatched (first collision) hfirstIncident
  have hthirdNeHole : third ≠ state.hole := by
    intro heq
    subst third
    exact state.hole_unmatched
      ((StatMech.FrontierA.RelationPartialMatching.mem_support_iff
        state.matching state.hole).2 ⟨first collision, hthird⟩)
  have hthirdNeDirect : third ≠ (state.move natural hnatural).hole := by
    intro heq
    have hfirstNatural : first collision = natural state.hole := by
      apply Option.some.inj
      exact hthird.symm.trans
        (heq ▸ state.matching_apply_move_hole natural hnatural)
    apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
      ends m j k l zero hloop hjk hkl hk0 p hno component
        collision collision.1.1
    calc
      first collision = natural state.hole := hfirstNatural
      _ = selfMap collision.1.1 := by
        apply Subtype.ext
        change canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
        rw [hself]
  have hthirdIncident : incident third (first collision) :=
    state.matching.related hthird
  have hclassify :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (first collision).1 state.hole.1 third.1
        hfirstIncident hthirdIncident
  have houtput : ∃ u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p (first collision).1 ∧
      (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
    rcases hclassify with heq | hstable | hadvancing
    · exact False.elim (hthirdNeHole (Subtype.ext heq).symm)
    · exact ⟨hstable.choose, hstable.choose_spec.1,
        Or.inl hstable.choose_spec.2.1,
        hstable.choose_spec.2.2.1.trans state.hole.2⟩
    · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
        Or.inr hadvancing.choose_spec.2.1,
        hadvancing.choose_spec.2.2.1.trans state.hole.2⟩
  exact ⟨state, collision, third, hself, hdirect, hthird,
    hthirdNeHole, hthirdNeDirect, houtput⟩





theorem exists_canonicalStableRawComponentResidualCollision_of_card_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nonempty (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  classical
  by_contra hnone
  have hdisjoint : ∀ collision direct,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
    intro collision direct heq
    exact hnone ⟨⟨(collision, direct), heq⟩⟩
  obtain ⟨embedding⟩ :=
    canonicalStableRawTokenComponent_embedding_of_sourceDirectDisjoint
      ends m j k l zero hloop hjk hkl hk0 p hno component hdisjoint
  have hle := Fintype.card_le_of_embedding embedding
  omega



theorem canonicalStableRawTokenComponent_embedding_of_cardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card
        {s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno s = component} ≤
      Fintype.card
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :
    Nonempty
      ({s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno s = component} ↪
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :=
  Function.Embedding.nonempty_of_card_le hcard



theorem canonicalStableRawExceptionalEdgeEmbedding_of_componentCardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (hcard : ∀ component : Set (CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p),
      Fintype.card
          {s : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p //
            canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno s = component} ≤
        Fintype.card
          {token : CanonicalStableRawLeftSurplusToken
              ends m j k l zero hloop hjk hkl hk0 p //
            canonicalStableRawFullLeftTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :
    Nonempty
      (CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p ↪
        CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p) := by
  classical
  exact ⟨StatMech.FrontierA.embeddingOf_taggedFiberwiseCardLE
    (canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno)
    (canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno) hcard⟩



theorem canonicalStableRawCollisionTokenEmbedding_of_componentCardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (hcard : ∀ component : Set (CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p),
      Fintype.card
          {s : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p //
            canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno s = component} ≤
        Fintype.card
          {token : CanonicalStableRawLeftSurplusToken
              ends m j k l zero hloop hjk hkl hk0 p //
            canonicalStableRawFullLeftTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :
    CanonicalStableRawCollisionTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  obtain ⟨stateEmbedding⟩ :=
    canonicalStableRawExceptionalEdgeEmbedding_of_componentCardLE
      ends m j k l zero hloop hjk hkl hk0 p hno hcard
  let stateEquiv :=
    canonicalStableRawExceptionalEdgeEquivRightCollisionToken
      ends m j k l zero hloop hjk hkl hk0 p
  exact ⟨stateEquiv.symm.toEmbedding.trans stateEmbedding⟩

end StatMech.GrahamGHS.FourColor
