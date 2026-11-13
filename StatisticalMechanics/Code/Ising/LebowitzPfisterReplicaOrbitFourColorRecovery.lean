/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber









open Finset

namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaFourColorRecoveryDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

set_option maxHeartbeats 800000 in



theorem lpReplicaOrbitCollisionSplitTag_rowCopies_false
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a))) :
    lpReplicaRowCopies G sites m
        (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) false = P := by
  rw [lpReplicaOrbitCollisionSplitTag, lpReplicaRowCopies_transportTag,
    lpReplicaCollision_rowCopies_false]
  ext c
  let E := lpReplicaOrbitCollisionSplitEquiv G sites m a P hP
  let left := lpReplicaCollisionLeftCopyEmbedding G sites a
    (lpReplicaReflectedResidual G sites m a)
  by_cases hc : c ∈ P
  · refine ⟨fun _ => hc, fun _ => ?_⟩
    let d0 := lpReplicaCopySubsetEquivProfile G sites m P ⟨c, hc⟩
    let d : Copy (lpReplicaCurrentGraph G sites) a :=
      cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hP) d0
    apply Finset.mem_map.mpr
    refine ⟨left d, Finset.mem_map.mpr ⟨d, Finset.mem_univ _, rfl⟩, ?_⟩
    change E.symm (left d) = c
    apply E.injective
    rw [E.apply_symm_apply]
    simp [E, left, d, d0, lpReplicaOrbitCollisionSplitEquiv, hc,
      lpReplicaCopySubsetEquivProfile, lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCollisionLeftCopyEmbedding, lpReplicaCollisionCopyEquiv]
    exact ⟨rfl, HEq.rfl⟩
  · refine ⟨?_, fun h => False.elim (hc h)⟩
    intro hmap
    obtain ⟨x, hx, hxc⟩ := Finset.mem_map.mp hmap
    obtain ⟨d, _, _⟩ := Finset.mem_map.mp hx
    subst x
    have hEc : E (E.symm (left d)) = E c := congrArg E hxc
    rw [E.apply_symm_apply] at hEc
    have hEc' := (lpReplicaCollisionCopyEquiv G sites a
      (lpReplicaReflectedResidual G sites m a)).injective hEc
    simp [hc,
      lpReplicaCopySubsetEquivProfile, lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCopyNotMemEquivCompl] at hEc'
    have hk := congrArg (fun z : LPReplicaCollisionCopy G sites a
        (lpReplicaReflectedResidual G sites m a) =>
      match z.2 with | Sum.inl _ => false | Sum.inr _ => true) hEc'
    simp [Sigma.map] at hk



theorem lpReplicaOrbitCollisionSplitTag_originProfile_false
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a))) :
    lpReplicaTaggedOriginProfile G sites m
        (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) false = a := by
  simp [lpReplicaTaggedOriginProfile, lpReplicaTaggedRowProfile,
    lpReplicaOrbitCollisionSplitTag_rowCopies_false
      G sites m a P hP Sa Sb, hP]



theorem lpReplicaOrbitCollisionSplitTag_originProfile_true
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a))) :
    lpReplicaTaggedOriginProfile G sites m
        (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) true =
      lpReplicaReflectedResidual G sites m a := by
  rw [lpReplicaTaggedOrigin_right_eq_reflectedResidual,
    lpReplicaOrbitCollisionSplitTag_originProfile_false
      G sites m a P hP Sa Sb]

theorem lpReplicaReflectCopyEquiv_cast_twice
    (G : SimpleGraph V) (sites : I -> V)
    (p q r : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hpq : (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) = q)
    (hqr : (fun e => q (lpReplicaCurrentEdgeReflect G sites e)) = r)
    (hpr : p = r)
    (d : Copy (lpReplicaCurrentGraph G sites) p) :
    cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hqr)
        (lpReplicaReflectCopyEquiv G sites q
          (cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hpq)
            (lpReplicaReflectCopyEquiv G sites p d))) =
      cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hpr) d := by
  let H := lpReplicaCurrentGraph G sites
  let d0 := lpReplicaReflectCopyEquiv G sites p d
  let d1 : Copy H q := cast (congrArg (Copy H) hpq) d0
  let d2 := lpReplicaReflectCopyEquiv G sites q d1
  let lhs : Copy H r := cast (congrArg (Copy H) hqr) d2
  let rhs : Copy H r := cast (congrArg (Copy H) hpr) d
  change lhs = rhs
  have hd1 : d1.1 = d0.1 := lpReplicaCopy_cast_edge H _ _ hpq d0
  have hlhs : lhs.1 = d2.1 := lpReplicaCopy_cast_edge H _ _ hqr d2
  have hrhs : rhs.1 = d.1 := lpReplicaCopy_cast_edge H _ _ hpr d
  have hd1val : d1.2.val = d0.2.val :=
    lpReplicaCopy_cast_index H _ _ hpq d0
  have hlhsval : lhs.2.val = d2.2.val :=
    lpReplicaCopy_cast_index H _ _ hqr d2
  have hrhsval : rhs.2.val = d.2.val :=
    lpReplicaCopy_cast_index H _ _ hpr d
  have he : lhs.1 = rhs.1 := by
    calc
      lhs.1 = d2.1 := hlhs
      _ = lpReplicaCurrentEdgeReflect G sites d1.1 := rfl
      _ = lpReplicaCurrentEdgeReflect G sites d0.1 :=
        congrArg (lpReplicaCurrentEdgeReflect G sites) hd1
      _ = lpReplicaCurrentEdgeReflect G sites
          (lpReplicaCurrentEdgeReflect G sites d.1) := rfl
      _ = d.1 := lpReplicaCurrentEdgeReflect_involutive G sites d.1
      _ = rhs.1 := hrhs.symm
  have hval : lhs.2.val = rhs.2.val := by
    calc
      lhs.2.val = d2.2.val := hlhsval
      _ = d1.2.val := rfl
      _ = d0.2.val := hd1val
      _ = d.2.val := rfl
      _ = rhs.2.val := hrhsval.symm
  apply Sigma.ext he
  exact (Fin.heq_ext_iff (congrArg r he)).2 hval

set_option maxHeartbeats 800000 in




theorem lpReplicaOrbitCollisionSplitEquiv_symm_taggedRowOne
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (d : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaTaggedRowProfile G sites m tag true)) :
    let a := lpReplicaTaggedOriginProfile G sites m tag false
    let P := lpReplicaRowCopies G sites m tag false
    let hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a := rfl
    let hb := lpReplicaTaggedOrigin_right_eq_reflectedResidual
      G sites m tag
    let dr0 := lpReplicaReflectCopyEquiv G sites
      (lpReplicaTaggedRowProfile G sites m tag true) d
    let dr : Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaReflectedResidual G sites m a) :=
      cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hb) dr0
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm
        (lpReplicaCollisionRightCopyEmbedding G sites a
          (lpReplicaReflectedResidual G sites m a) dr) =
      lpReplicaTaggedRowBackEmbedding G sites m tag true d := by
  classical
  dsimp only
  rw [lpReplicaOrbitCollisionSplitEquiv_symm_right]
  have hR := lpReplicaRowCopies_true_eq_compl_false G sites m tag
  have hprofile : lpReplicaTaggedRowProfile G sites m tag true =
      profileFlux (lpReplicaCurrentGraph G sites) m
        (Finset.univ \ lpReplicaRowCopies G sites m tag false) := by
    exact congrArg (profileFlux (lpReplicaCurrentGraph G sites) m) hR
  have hd :
      cast (congrArg (Copy (lpReplicaCurrentGraph G sites))
          (lpReplicaCollisionSplit_complProfile G sites m
            (lpReplicaTaggedOriginProfile G sites m tag false)
            (lpReplicaRowCopies G sites m tag false) rfl).symm)
        (lpReplicaReflectCopyEquiv G sites
          (lpReplicaReflectedResidual G sites m
            (lpReplicaTaggedOriginProfile G sites m tag false))
          (cast (congrArg (Copy (lpReplicaCurrentGraph G sites))
              (lpReplicaTaggedOrigin_right_eq_reflectedResidual
                G sites m tag))
            (lpReplicaReflectCopyEquiv G sites
              (lpReplicaTaggedRowProfile G sites m tag true) d))) =
        cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hprofile) d := by
    exact lpReplicaReflectCopyEquiv_cast_twice G sites
      (lpReplicaTaggedRowProfile G sites m tag true)
      (lpReplicaReflectedResidual G sites m
        (lpReplicaTaggedOriginProfile G sites m tag false))
      (profileFlux (lpReplicaCurrentGraph G sites) m
        (Finset.univ \ lpReplicaRowCopies G sites m tag false))
      (lpReplicaTaggedOrigin_right_eq_reflectedResidual G sites m tag)
      (lpReplicaCollisionSplit_complProfile G sites m
        (lpReplicaTaggedOriginProfile G sites m tag false)
        (lpReplicaRowCopies G sites m tag false) rfl).symm
      hprofile d
  rw [hd]
  unfold lpReplicaTaggedRowBackEmbedding
  change ((lpReplicaCopySubsetEquivProfile G sites m
      (Finset.univ \ lpReplicaRowCopies G sites m tag false)).symm
        (cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hprofile) d)).1 =
    ((lpReplicaCopySubsetEquivProfile G sites m
      (lpReplicaRowCopies G sites m tag true)).symm d).1
  exact lpReplicaCopySubsetEquivProfile_symm_cast G sites m
    (lpReplicaRowCopies G sites m tag true)
    (Finset.univ \ lpReplicaRowCopies G sites m tag false) hR d



theorem lpReplicaOrbitCollisionSplitTag_currentCopies_left_false
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a))) :
    lpReplicaCurrentCopies G sites m
        (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb)
        false false =
      (Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a
          (lpReplicaReflectedResidual G sites m a))).map
        (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm.toEmbedding := by
  rw [lpReplicaOrbitCollisionSplitTag, lpReplicaCurrentCopies_transportTag,
    lpReplicaCollision_currentCopies_left_false]



theorem lpReplicaOrbitCollisionSplitTag_currentCopies_right_false
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a))) :
    lpReplicaCurrentCopies G sites m
        (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb)
        true false =
      (Sb.map (lpReplicaCollisionRightCopyEmbedding G sites a
          (lpReplicaReflectedResidual G sites m a))).map
        (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm.toEmbedding := by
  rw [lpReplicaOrbitCollisionSplitTag, lpReplicaCurrentCopies_transportTag,
    lpReplicaCollision_currentCopies_right_false]



theorem lpReplicaOrbitCollisionSplitTag_currentSubsets_injective
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
    Function.Injective (fun x :
        Finset (Copy (lpReplicaCurrentGraph G sites) a) ×
          Finset (Copy (lpReplicaCurrentGraph G sites)
            (lpReplicaReflectedResidual G sites m a)) =>
      lpReplicaOrbitCollisionSplitTag G sites m a P hP x.1 x.2) := by
  rintro ⟨Sa, Sb⟩ ⟨Ta, Tb⟩ htag
  change lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb =
    lpReplicaOrbitCollisionSplitTag G sites m a P hP Ta Tb at htag
  have hleft := congrArg (fun tag =>
    lpReplicaCurrentCopies G sites m tag false false) htag
  change lpReplicaCurrentCopies G sites m
      (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb)
        false false =
    lpReplicaCurrentCopies G sites m
      (lpReplicaOrbitCollisionSplitTag G sites m a P hP Ta Tb)
        false false at hleft
  rw [lpReplicaOrbitCollisionSplitTag_currentCopies_left_false,
    lpReplicaOrbitCollisionSplitTag_currentCopies_left_false] at hleft
  have hleft' := Finset.map_injective
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm.toEmbedding hleft
  have hSa := Finset.map_injective
    (lpReplicaCollisionLeftCopyEmbedding G sites a
      (lpReplicaReflectedResidual G sites m a)) hleft'
  have hright := congrArg (fun tag =>
    lpReplicaCurrentCopies G sites m tag true false) htag
  change lpReplicaCurrentCopies G sites m
      (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb)
        true false =
    lpReplicaCurrentCopies G sites m
      (lpReplicaOrbitCollisionSplitTag G sites m a P hP Ta Tb)
        true false at hright
  rw [lpReplicaOrbitCollisionSplitTag_currentCopies_right_false,
    lpReplicaOrbitCollisionSplitTag_currentCopies_right_false] at hright
  have hright' := Finset.map_injective
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm.toEmbedding hright
  have hSb := Finset.map_injective
    (lpReplicaCollisionRightCopyEmbedding G sites a
      (lpReplicaReflectedResidual G sites m a)) hright'
  exact Prod.ext hSa hSb

end

end StatMech.Ising
