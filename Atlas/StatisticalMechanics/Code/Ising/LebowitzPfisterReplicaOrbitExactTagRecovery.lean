/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery

open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj := Classical.decRel _

theorem lpReplicaRowTag_eq_of_false_class_iff
    (a b : LPReplicaRowTag)
    (hrow : (a.1 = false ↔ b.1 = false))
    (hfalse : (a = (false, false) ↔ b = (false, false)))
    (htrue : (a = (true, false) ↔ b = (true, false))) :
    a = b := by
  rcases a with ⟨ar, ac⟩
  rcases b with ⟨br, bc⟩
  cases ar <;> cases ac <;> cases br <;> cases bc <;> simp_all

theorem lpReplica_mem_cast_finset
    {J : Type*} (F : J -> Type*) [∀ j, DecidableEq (F j)]
    {a b : J} (h : a = b) (x : F a) (S : Finset (F a)) :
    cast (congrArg F h) x ∈
        cast (congrArg (fun j => Finset (F j)) h) S ↔ x ∈ S := by
  subst b
  rfl

set_option maxHeartbeats 1200000 in

theorem lpReplicaOrbitCollisionSplitTag_of_tag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    let a := lpReplicaTaggedOriginProfile G sites m tag false
    let P := lpReplicaRowCopies G sites m tag false
    let Sa := lpReplicaTaggedRowCurrentSubset G sites m tag false false
    let Sb0 := lpReplicaReflectCopies G sites
      (lpReplicaTaggedRowProfile G sites m tag true)
      (lpReplicaTaggedRowCurrentSubset G sites m tag true false)
    let hb := lpReplicaTaggedOrigin_right_eq_reflectedResidual G sites m tag
    let Sb : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites)
        (lpReplicaReflectedResidual G sites m a)) :=
      cast (congrArg
        (fun p => Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) p)) hb) Sb0
    let hP : StatMech.Sharpness.FluxEdgeCopy.profileFlux
        (lpReplicaCurrentGraph G sites) m P = a := rfl
    lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb = tag := by
  classical
  dsimp only
  let a := lpReplicaTaggedOriginProfile G sites m tag false
  let P := lpReplicaRowCopies G sites m tag false
  let Sa := lpReplicaTaggedRowCurrentSubset G sites m tag false false
  let b := lpReplicaTaggedOriginProfile G sites m tag true
  let Sb0 := lpReplicaReflectCopies G sites
    (lpReplicaTaggedRowProfile G sites m tag true)
    (lpReplicaTaggedRowCurrentSubset G sites m tag true false)
  have hb : b = lpReplicaReflectedResidual G sites m a := by
    exact lpReplicaTaggedOrigin_right_eq_reflectedResidual G sites m tag
  let Sb : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a)) :=
    cast (congrArg
      (fun p => Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) p)) hb) Sb0
  have hP : StatMech.Sharpness.FluxEdgeCopy.profileFlux
      (lpReplicaCurrentGraph G sites) m P = a := rfl
  let split := lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb
  have hrows : lpReplicaRowCopies G sites m split false =
      lpReplicaRowCopies G sites m tag false := by
    change lpReplicaRowCopies G sites m
      (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) false = P
    apply lpReplicaOrbitCollisionSplitTag_rowCopies_false
  have hcurrent0 : lpReplicaCurrentCopies G sites m split false false =
      lpReplicaCurrentCopies G sites m tag false false := by
    let E := lpReplicaOrbitCollisionSplitEquiv G sites m a P hP
    let left := lpReplicaCollisionLeftCopyEmbedding G sites a
      (lpReplicaReflectedResidual G sites m a)
    have hformula := lpReplicaOrbitCollisionSplitTag_currentCopies_left_false
      G sites m a P hP Sa Sb
    ext c
    by_cases hc : c ∈ P
    · let d0 := lpReplicaCopySubsetEquivProfile G sites m P ⟨c, hc⟩
      let d : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) a :=
        cast (congrArg
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites)) hP) d0
      have hpre : E.symm (left d) = c := by
        calc
          _ = ((lpReplicaCopySubsetEquivProfile G sites m P).symm
              (cast (congrArg
                (StatMech.Sharpness.FluxEdgeCopy.Copy
                  (lpReplicaCurrentGraph G sites)) hP.symm) d)).1 :=
            lpReplicaOrbitCollisionSplitEquiv_symm_left
              G sites m a P hP d
          _ = c := by
            simpa only [d, d0, Equiv.cast_symm, Equiv.cast_apply] using
              congrArg Subtype.val
                ((lpReplicaCopySubsetEquivProfile G sites m P).symm_apply_apply
                  ⟨c, hc⟩)
      have hback : lpReplicaTaggedRowBackEmbedding G sites m tag false d = c := by
        change ((lpReplicaCopySubsetEquivProfile G sites m P).symm
          (cast (congrArg
            (StatMech.Sharpness.FluxEdgeCopy.Copy
              (lpReplicaCurrentGraph G sites)) hP) d0)).1 = c
        exact congrArg Subtype.val
          ((lpReplicaCopySubsetEquivProfile G sites m P).symm_apply_apply
            ⟨c, hc⟩)
      rw [hformula]
      constructor
      · intro htarget
        obtain ⟨y, hy, hyc⟩ := Finset.mem_map.mp htarget
        obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
        subst y
        have hxd : x = d := by
          apply left.injective
          apply E.symm.injective
          exact hyc.trans hpre.symm
        subst x
        have hrow : (tag c).1 = false := by
          simpa only [P, lpReplicaRowCopies, Finset.mem_filter,
            Finset.mem_univ, true_and] using hc
        have hcur : (tag c).2 = false := by
          dsimp only [Sa] at hx
          have hx' := (Finset.mem_filter.mp hx).2
          rwa [hback] at hx'
        simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using Prod.ext hrow hcur
      · intro hsource
        have hcur : (tag c).2 = false := by
          exact congrArg Prod.snd (by simpa only [lpReplicaCurrentCopies,
            Finset.mem_filter, Finset.mem_univ, true_and] using hsource)
        have hdSa : d ∈ Sa := by
          dsimp only [Sa]
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rwa [hback]
        exact Finset.mem_map.mpr ⟨left d,
          Finset.mem_map.mpr ⟨d, hdSa, rfl⟩, hpre⟩
    · constructor
      · intro htarget
        have hrow : c ∈ lpReplicaRowCopies G sites m split false := by
          simpa only [lpReplicaCurrentCopies, lpReplicaRowCopies,
            Finset.mem_filter, Finset.mem_univ, true_and] using
              congrArg Prod.fst (by simpa only [lpReplicaCurrentCopies,
                Finset.mem_filter, Finset.mem_univ, true_and] using htarget)
        rw [hrows] at hrow
        exact (hc hrow).elim
      · intro hsource
        have hrow : c ∈ P := by
          simpa only [P, lpReplicaRowCopies, Finset.mem_filter,
            Finset.mem_univ, true_and] using
              congrArg Prod.fst (by simpa only [lpReplicaCurrentCopies,
                Finset.mem_filter, Finset.mem_univ, true_and] using hsource)
        exact (hc hrow).elim
  have hcurrent1 : lpReplicaCurrentCopies G sites m split true false =
      lpReplicaCurrentCopies G sites m tag true false := by
    let E := lpReplicaOrbitCollisionSplitEquiv G sites m a P hP
    let right := lpReplicaCollisionRightCopyEmbedding G sites a
      (lpReplicaReflectedResidual G sites m a)
    let R := lpReplicaRowCopies G sites m tag true
    let S1 := lpReplicaTaggedRowCurrentSubset G sites m tag true false
    have hR : R = Finset.univ \ P := by
      exact lpReplicaRowCopies_true_eq_compl_false G sites m tag
    have hformula := lpReplicaOrbitCollisionSplitTag_currentCopies_right_false
      G sites m a P hP Sa Sb
    ext c
    by_cases hc : c ∈ P
    · constructor
      · intro htarget
        have hrowTrue : c ∈ lpReplicaRowCopies G sites m split true := by
          simpa only [lpReplicaCurrentCopies, lpReplicaRowCopies,
            Finset.mem_filter, Finset.mem_univ, true_and] using
              congrArg Prod.fst (by simpa only [lpReplicaCurrentCopies,
                Finset.mem_filter, Finset.mem_univ, true_and] using htarget)
        have hrowFalse : c ∉ lpReplicaRowCopies G sites m split false := by
          simpa only [lpReplicaRowCopies_true_eq_compl_false,
            Finset.mem_sdiff, Finset.mem_univ, true_and] using hrowTrue
        exact (hrowFalse (by rw [hrows]; exact hc)).elim
      · intro hsource
        have hrowTrue : c ∈ R := by
          simpa only [R, lpReplicaCurrentCopies, lpReplicaRowCopies,
            Finset.mem_filter, Finset.mem_univ, true_and] using
              congrArg Prod.fst (by simpa only [lpReplicaCurrentCopies,
                Finset.mem_filter, Finset.mem_univ, true_and] using hsource)
        have hrowFalse : c ∉ P := by
          simpa only [R, lpReplicaRowCopies_true_eq_compl_false,
            Finset.mem_sdiff, Finset.mem_univ, true_and] using hrowTrue
        exact (hrowFalse hc).elim
    · have hcR : c ∈ R := by
        simpa only [R, lpReplicaRowCopies_true_eq_compl_false,
          Finset.mem_sdiff, Finset.mem_univ, true_and]
      let d0 := lpReplicaCopySubsetEquivProfile G sites m R ⟨c, hcR⟩
      let dr0 := lpReplicaReflectCopyEquiv G sites
        (lpReplicaTaggedRowProfile G sites m tag true) d0
      let dr : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites)
          (lpReplicaReflectedResidual G sites m a) :=
        cast (congrArg
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites)) hb) dr0
      have hback : lpReplicaTaggedRowBackEmbedding
          G sites m tag true d0 = c := by
        change ((lpReplicaCopySubsetEquivProfile G sites m R).symm d0).1 = c
        exact congrArg Subtype.val
          ((lpReplicaCopySubsetEquivProfile G sites m R).symm_apply_apply
            ⟨c, hcR⟩)
      have hpre : E.symm (right dr) = c := by
        calc
          _ = lpReplicaTaggedRowBackEmbedding
              G sites m tag true d0 :=
            lpReplicaOrbitCollisionSplitEquiv_symm_taggedRowOne
              G sites m tag d0
          _ = c := hback
      have hdrSb : dr ∈ Sb ↔ d0 ∈ S1 := by
        have hcast : dr ∈ Sb ↔ dr0 ∈ Sb0 := by
          exact lpReplica_mem_cast_finset
            (fun p => StatMech.Sharpness.FluxEdgeCopy.Copy
              (lpReplicaCurrentGraph G sites) p) hb dr0 Sb0
        have hreflect : dr0 ∈ Sb0 ↔
            d0 ∈ lpReplicaTaggedRowCurrentSubset
              G sites m tag true false := by
          dsimp only [dr0, Sb0]
          rw [mem_lpReplicaReflectCopies]
          simp only [Equiv.symm_apply_apply]
          exact Iff.rfl
        change dr ∈ Sb ↔
          d0 ∈ lpReplicaTaggedRowCurrentSubset G sites m tag true false
        exact hcast.trans hreflect
      rw [hformula]
      constructor
      · intro htarget
        obtain ⟨y, hy, hyc⟩ := Finset.mem_map.mp htarget
        obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
        subst y
        have hxd : x = dr := by
          apply right.injective
          apply E.symm.injective
          exact hyc.trans hpre.symm
        subst x
        have hdS1 : d0 ∈ S1 := hdrSb.mp hx
        have hrow : (tag c).1 = true := by
          simpa only [R, lpReplicaRowCopies, Finset.mem_filter,
            Finset.mem_univ, true_and] using hcR
        have hcur : (tag c).2 = false := by
          dsimp only [S1] at hdS1
          have hdS1' := (Finset.mem_filter.mp hdS1).2
          rwa [hback] at hdS1'
        simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using Prod.ext hrow hcur
      · intro hsource
        have hcur : (tag c).2 = false := by
          exact congrArg Prod.snd (by simpa only [lpReplicaCurrentCopies,
            Finset.mem_filter, Finset.mem_univ, true_and] using hsource)
        have hdS1 : d0 ∈ S1 := by
          dsimp only [S1]
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rwa [hback]
        have hdr : dr ∈ Sb := hdrSb.mpr hdS1
        exact Finset.mem_map.mpr ⟨right dr,
          Finset.mem_map.mpr ⟨dr, hdr, rfl⟩, hpre⟩
  funext c
  apply lpReplicaRowTag_eq_of_false_class_iff
  · simpa only [lpReplicaRowCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using Finset.ext_iff.mp hrows c
  · simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using Finset.ext_iff.mp hcurrent0 c
  · simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using Finset.ext_iff.mp hcurrent1 c

end
end StatMech.Ising
