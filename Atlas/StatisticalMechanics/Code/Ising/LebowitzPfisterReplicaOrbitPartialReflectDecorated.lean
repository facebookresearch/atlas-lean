/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitSplitTag
import Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport
import Code.Ising.LebowitzPfisterReplicaOrbitTagReconstruction











open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

theorem lpReplica_cast_subtype_val
    {J : Type*} (F : J -> Type*) (P : ∀ j, F j -> Prop)
    {a b : J} (h : a = b) (x : {y : F a // P a y}) :
    (cast (congrArg (fun j => {y : F j // P j y}) h) x).1 =
      cast (congrArg F h) x.1 := by
  subst b
  rfl




noncomputable def lpReplicaDecoratedOrbitAtomOfRowGate
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaDecoratedOrbitAtom G sites A
      (B.map lpReplicaCurrentReflect.toEmbedding) q := by
  classical
  let a := lpReplicaTaggedOriginProfile G sites m tag false
  let Sa := lpReplicaTaggedRowCurrentSubset G sites m tag false false
  let b := lpReplicaTaggedOriginProfile G sites m tag true
  let Sb0 := lpReplicaReflectCopies G sites
    (lpReplicaTaggedRowProfile G sites m tag true)
    (lpReplicaTaggedRowCurrentSubset G sites m tag true false)
  let P0 := lpReplicaRowCopies G sites m tag false
  have ha : a <= m := lpReplicaTaggedOrigin_left_le G sites m tag
  have hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites A a :=
    lpReplicaTaggedRowCurrentSubset_mem_disconnFamily
      G sites m tag A B hgate false
  have hSb0 : Sb0 ∈ lpReplicaDisconnProfileFamily G sites
      (B.map lpReplicaCurrentReflect.toEmbedding) b :=
    lpReplicaTaggedRowOne_reflectedCurrentSubset_mem_disconnFamily
      G sites m tag A B hgate
  have hb : b = lpReplicaReflectedResidual G sites m a :=
    lpReplicaTaggedOrigin_right_eq_reflectedResidual G sites m tag
  let Sb : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a)) :=
    cast (congrArg
      (fun p => Finset (Copy (lpReplicaCurrentGraph G sites) p)) hb) Sb0
  have hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaReflectedResidual G sites m a) := by
    let xb : ↑(lpReplicaDisconnProfileFamily G sites
        (B.map lpReplicaCurrentReflect.toEmbedding) b) := ⟨Sb0, hSb0⟩
    let xb' : ↑(lpReplicaDisconnProfileFamily G sites
        (B.map lpReplicaCurrentReflect.toEmbedding)
        (lpReplicaReflectedResidual G sites m a)) :=
      cast (congrArg (fun p =>
        {S // S ∈ lpReplicaDisconnProfileFamily G sites
          (B.map lpReplicaCurrentReflect.toEmbedding) p}) hb) xb
    have hx : xb'.1 = Sb := by
      simpa only [xb', xb, Sb] using lpReplica_cast_subtype_val
        (fun p => Finset (Copy (lpReplicaCurrentGraph G sites) p))
        (fun p S => S ∈ lpReplicaDisconnProfileFamily G sites
          (B.map lpReplicaCurrentReflect.toEmbedding) p) hb xb
    rw [← hx]
    exact xb'.2
  have hP0 : P0 ∈ LPReplicaCollisionSplitLabel G sites m a := by
    change P0 ∈ (Finset.univ : Finset (Finset
      (Copy (lpReplicaCurrentGraph G sites) m))).filter fun P =>
        profileFlux (lpReplicaCurrentGraph G sites) m P = a
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rfl
  exact ⟨⟨⟨m, hm⟩, ⟨⟨a, ha⟩,
    (⟨Sa, hSa⟩, ⟨Sb, hSb⟩)⟩⟩, (⟨P0, hP0⟩, L)⟩



def LPReplicaPartialReflectDecoratedBranch
    (G : SimpleGraph V) (sites : I -> V)
    (A : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ y : LPReplicaDecoratedOrbitAtom G sites A ∅ q,
    {tag : Copy (lpReplicaCurrentGraph G sites) y.1.1.1 -> LPReplicaRowTag //
      LPReplicaRowGate G sites y.1.1.1 A ∅ tag}



def LPReplicaPartialReflectDecoratedTrace
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  LPReplicaDecoratedOrbitAtom G sites ∅ (Si ∆ Sj ∆ T) q ×
    (LPReplicaPartialReflectDecoratedBranch G sites Si q ⊕
      LPReplicaPartialReflectDecoratedBranch G sites Sj q)

set_option maxHeartbeats 800000 in



noncomputable def lpReplicaDecoratedOrbitAtomPartialReflect
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaDecoratedOrbitAtom G sites ∅
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q) :
    LPReplicaPartialReflectDecoratedBranch G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) q ⊕
      LPReplicaPartialReflectDecoratedBranch G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let m := z.1.1.1
  let a := z.1.2.1.1
  let Sa := z.1.2.2.1.1
  let Sb := z.1.2.2.2.1
  let P0 := z.2.1.1
  let L := z.2.2
  have hm : lpReplicaSymmetrizedProfile G sites m = q := z.1.1.2
  have ha : a <= m := z.1.2.1.2
  have hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites ∅ a :=
    z.1.2.2.1.2
  have hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites
      (Si ∆ Sj ∆ T) (lpReplicaReflectedResidual G sites m a) := by
    exact z.1.2.2.2.2
  have hP0 : profileFlux (lpReplicaCurrentGraph G sites) m P0 = a := by
    exact (Finset.mem_filter.mp z.2.1.2).2
  let tag := lpReplicaOrbitCollisionSplitTag G sites m a P0 hP0 Sa Sb
  have hgate0 := lpReplicaRowGate_orbitCollisionSplitTag
    G sites m a ha P0 hP0 Sa Sb ∅ (Si ∆ Sj ∆ T) hSa hSb
  have hfixed := lpReplicaCurrentReflect_offdiagSource G sites i j
  have hgate : LPReplicaRowGate G sites m ∅ (Si ∆ Sj ∆ T) tag := by
    simpa only [Si, Sj, T, hfixed, tag] using hgate0
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m tag true
  let P := StatMech.GrahamGHS.FourColor.edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
    (profileFlux (lpReplicaCurrentGraph G sites) m P)
  let movedTag := lpReplicaSwapRowsTag
    (lpReplicaPartialReflectTagRaw G sites m P tag)
  have htarget : lpReplicaSymmetrizedProfile G sites target = q := by
    unfold target
    rw [lpReplicaCollisionProfile_compl_eq_partialReflectProfile,
      lpReplicaSymmetrizedProfile_partialReflectCopies, hm]
  let Lpartial := lpReplicaProfileOrbitLabelPartialReflectCopies
    G sites q m hm P L
  have hprofile : target = lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P) :=
    lpReplicaCollisionProfile_compl_eq_partialReflectProfile G sites m P
  let Ltarget : LPReplicaProfileOrbitLabel G sites q target :=
    cast (congrArg (LPReplicaProfileOrbitLabel G sites q) hprofile.symm)
      Lpartial
  have hmove := lpReplicaRowGate_partialReflect_offdiag_swapRows
    G sites hsite hij m tag hgate
  by_cases hgi : LPReplicaRowGate G sites target Si ∅ movedTag
  · left
    let y := lpReplicaDecoratedOrbitAtomOfRowGate
      G sites target q movedTag Si ∅ htarget hgi Ltarget
    exact ⟨y, ⟨movedTag, hgi⟩⟩
  · right
    have hgj : LPReplicaRowGate G sites target Sj ∅ movedTag := by
      rcases hmove with hi | hj
      · exact False.elim (hgi (by
          simpa only [e, K, P, target, movedTag, Si, Sj, T] using hi.1))
      · simpa only [e, K, P, target, movedTag, Si, Sj, T] using hj.1
    let y := lpReplicaDecoratedOrbitAtomOfRowGate
      G sites target q movedTag Sj ∅ htarget hgj Ltarget
    exact ⟨y, ⟨movedTag, hgj⟩⟩


noncomputable def lpReplicaPartialReflectDecoratedTraceMap
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaDecoratedOrbitAtom G sites ∅
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q ->
      LPReplicaPartialReflectDecoratedTrace G sites i j q :=
  fun z => ⟨z,
    lpReplicaDecoratedOrbitAtomPartialReflect G sites hsite hij q z⟩


theorem lpReplicaPartialReflectDecoratedTraceMap_injective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (lpReplicaPartialReflectDecoratedTraceMap
        G sites hsite hij q) := by
  intro x y hxy
  exact congrArg Prod.fst hxy

end

end StatMech.Ising
