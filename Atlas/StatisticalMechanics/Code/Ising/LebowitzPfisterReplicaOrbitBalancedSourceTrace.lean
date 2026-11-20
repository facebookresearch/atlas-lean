/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph











open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaBalancedSourceTraceDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect_ghost1
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
    (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let C := StatMech.Sharpness.RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
    let X :=
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) ∩ C
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    ((Si ∆ Sj ∆ T) ∆ Si =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨
      ((Si ∆ Sj ∆ T) ∆ Sj =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
  classical
  dsimp only
  let mr := fun e => m (lpReplicaCurrentEdgeReflect G sites e)
  let Kr := lpReplicaReflectCopies G sites m K
  have hsrcR : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) mr) Kr =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
    rw [lpReplicaReflectCopies_sources, hsrc,
      lpReplicaCurrentReflect_offdiagSource G sites i j]
  have hdiscR : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) mr) Kr
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hc
    have hc' : StatMech.Sharpness.RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) mr) Kr
        (lpReplicaCurrentReflect
          (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V))
        (lpReplicaCurrentReflect
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)) := by
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hc
    have horiginal := (lpReplicaReflectCopies_connK G sites m K
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost0).mp hc'
    exact hdisc (StatMech.Sharpness.RandomCurrent.connK_symm _ _ horiginal)
  have hcomp :
      StatMech.Sharpness.RandomCurrent.compOf
          (endsM (lpReplicaCurrentGraph G sites) mr) Kr
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) =
        (StatMech.Sharpness.RandomCurrent.compOf
          (endsM (lpReplicaCurrentGraph G sites) m) K
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)).map
            lpReplicaCurrentReflect.toEmbedding := by
    ext x
    simp only [StatMech.Sharpness.RandomCurrent.mem_compOf,
      Finset.mem_map]
    constructor
    · intro hx
      refine ⟨lpReplicaCurrentReflect x, ?_,
        lpReplicaCurrentReflect_involutive x⟩
      have hreflect := (lpReplicaReflectCopies_connK G sites m K
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
        (lpReplicaCurrentReflect x)).mp
      apply hreflect
      change StatMech.Sharpness.RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) mr) Kr
        lpReplicaCurrentGhost0
        (lpReplicaCurrentReflect (lpReplicaCurrentReflect x))
      rw [lpReplicaCurrentReflect_involutive]
      exact hx
    · rintro ⟨y, hy, hyx⟩
      change lpReplicaCurrentReflect y = x at hyx
      subst x
      have hreflect := (lpReplicaReflectCopies_connK G sites m K
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) y).mpr hy
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hreflect
  have h := lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect
    G sites hsite hij mr Kr hsrcR hdiscR
  dsimp only at h
  rw [hcomp] at h
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  let C := StatMech.Sharpness.RandomCurrent.compOf
    (endsM (lpReplicaCurrentGraph G sites) m) K
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
  let X := B ∩ C
  have hB : B.map lpReplicaCurrentReflect.toEmbedding = B :=
    lpReplicaCurrentReflect_offdiagSource G sites i j
  have hX : B ∩ C.map lpReplicaCurrentReflect.toEmbedding =
      X.map lpReplicaCurrentReflect.toEmbedding := by
    rw [Finset.map_inter]
    rw [hB]
  rw [hX] at h
  have hdouble :
      (X.map lpReplicaCurrentReflect.toEmbedding).map
          lpReplicaCurrentReflect.toEmbedding = X := by
    ext x
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
      change lpReplicaCurrentReflect z = y at hzy
      change lpReplicaCurrentReflect y = x at hyx
      subst y
      rw [lpReplicaCurrentReflect_involutive] at hyx
      simpa [← hyx] using hz
    · intro hx
      refine ⟨lpReplicaCurrentReflect x, ?_,
        lpReplicaCurrentReflect_involutive x⟩
      exact ⟨x, hx, rfl⟩
  have hbalanced :
      X.map lpReplicaCurrentReflect.toEmbedding ∆
          (X.map lpReplicaCurrentReflect.toEmbedding).map
            lpReplicaCurrentReflect.toEmbedding =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding := by
    rw [hdouble, symmDiff_comm]
  simpa only [B, C, X, hbalanced] using h



noncomputable def lpReplicaDecoratedSourceRowGateData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    {tag : Copy (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag //
      LPReplicaRowGate G sites z.1.1.1 ∅
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) tag} := by
  let m := z.1.1.1
  let a := z.1.2.1.1
  let Sa := z.1.2.2.1.1
  let Sb := z.1.2.2.2.1
  let P0 := z.2.1.1
  have ha : a <= m := z.1.2.1.2
  have hSa := z.1.2.2.1.2
  have hSb := z.1.2.2.2.2
  have hP0 : profileFlux (lpReplicaCurrentGraph G sites) m P0 = a :=
    (Finset.mem_filter.mp z.2.1.2).2
  let tag := lpReplicaOrbitCollisionSplitTag G sites m a P0 hP0 Sa Sb
  have hgate0 := lpReplicaRowGate_orbitCollisionSplitTag
    G sites m a ha P0 hP0 Sa Sb ∅
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      hSa hSb
  have hfixed := lpReplicaCurrentReflect_offdiagSource G sites i j
  refine ⟨tag, ?_⟩
  simpa only [m, a, Sa, Sb, P0, tag, hfixed] using hgate0



noncomputable def lpReplicaDecoratedSourceSwappedRowGateData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    {tag : Copy (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag //
      LPReplicaRowGate G sites z.1.1.1
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) ∅ tag} := by
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  exact ⟨lpReplicaSwapRowsTag d.1,
    lpReplicaRowGate_swapRows G sites z.1.1.1 _ _ d.1 d.2⟩


noncomputable def lpReplicaDecoratedSourceCanonicalHalf
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaCurrentVertex V) :=
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  B ∩ StatMech.Sharpness.RandomCurrent.compOf
    (endsM (lpReplicaCurrentGraph G sites) z.1.1.1)
    (lpReplicaRowCopies G sites z.1.1.1 d.1 false)
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)



noncomputable def lpReplicaDecoratedSourceCanonicalHalfSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaBalancedSelector G sites
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      (lpReplicaDecoratedSourceCanonicalHalf G sites i j q z) q := by
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  simpa only [lpReplicaDecoratedSourceCanonicalHalf, B, d] using
    lpReplicaBalancedSelectorOfComponentExchange G sites B q z.1.1.1
      d.1 z.1.1.2 d.2 z.2.2




theorem lpReplicaDecoratedSourceCanonicalHalf_missingSource
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    let X := lpReplicaDecoratedSourceCanonicalHalf G sites i j q z
    ((Si ∆ Sj ∆ T) ∆ Si =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨
      ((Si ∆ Sj ∆ T) ∆ Sj =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
  dsimp only
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  let K := lpReplicaRowCopies G sites z.1.1.1 d.1 false
  have hrows := lpReplicaRowGate_rowSources G sites z.1.1.1 B ∅ d.1 d.2
  have h := lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect_ghost1
    G sites hsite hij z.1.1.1 K hrows.1 d.2.2.2.1
  simpa only [B, d, K, lpReplicaDecoratedSourceCanonicalHalf] using h



def LPReplicaDecoratedSourceCanonicalHalfBranch
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  (Σ X : Finset (LPReplicaCurrentVertex V),
      {_s : LPReplicaBalancedSelector G sites B X q //
        Sj ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding}) ⊕
    (Σ X : Finset (LPReplicaCurrentVertex V),
      {_s : LPReplicaBalancedSelector G sites B X q //
        Si ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding})

set_option maxHeartbeats 800000 in



noncomputable def lpReplicaDecoratedSourceCanonicalHalfBranch
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaDecoratedSourceCanonicalHalfBranch G sites i j q := by
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let X := lpReplicaDecoratedSourceCanonicalHalf G sites i j q z
  let s := lpReplicaDecoratedSourceCanonicalHalfSelector G sites i j q z
  have hmissing := lpReplicaDecoratedSourceCanonicalHalf_missingSource
    G sites hsite hij q z
  dsimp only [Si, Sj, T, X] at hmissing
  have hi : B ∆ Si = Sj ∆ T := by
    ext x
    simp only [B, Finset.mem_symmDiff]
    tauto
  have hj : B ∆ Sj = Si ∆ T := by
    ext x
    simp only [B, Finset.mem_symmDiff]
    tauto
  by_cases hleft : B ∆ Si = X ∆ X.map lpReplicaCurrentReflect.toEmbedding
  · exact Sum.inl ⟨X, s, hi.symm.trans hleft⟩
  · have hright := hmissing.resolve_left (by simpa only [B] using hleft)
    exact Sum.inr ⟨X, s, hj.symm.trans hright⟩


def LPReplicaDecoratedSourceCanonicalHalfTrace
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  LPReplicaOffdiagDecoratedSource G sites i j q ×
    LPReplicaDecoratedSourceCanonicalHalfBranch G sites i j q

noncomputable def lpReplicaDecoratedSourceCanonicalHalfTraceMap
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaDecoratedSourceCanonicalHalfTrace G sites i j q :=
  fun z => ⟨z,
    lpReplicaDecoratedSourceCanonicalHalfBranch G sites hsite hij q z⟩

theorem lpReplicaDecoratedSourceCanonicalHalfTraceMap_injective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (lpReplicaDecoratedSourceCanonicalHalfTraceMap
        G sites hsite hij q) := by
  intro z w hzw
  exact congrArg Prod.fst hzw




noncomputable def lpReplicaDecoratedOrbitAtomOfBalancedSelectorGeneral
    (G : SimpleGraph V) (sites : I -> V)
    (B D : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites B D q) :
    LPReplicaDecoratedOrbitAtom G sites (B ∆ D)
      (D.map lpReplicaCurrentReflect.toEmbedding) q := by
  let movedTag := lpReplicaToggleRows G sites s.profile s.selector s.tag
  have hgate0 := lpReplicaRowGate_toggle G sites s.profile B ∅
    s.tag s.selector s.gate s.trueSource s.row0Disconn s.row1Disconn
  dsimp only at hgate0
  rw [s.falseSource] at hgate0
  have hempty : (∅ : Finset (LPReplicaCurrentVertex V)) ∆ D = D := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hempty] at hgate0
  exact lpReplicaDecoratedOrbitAtomOfRowGate G sites s.profile q movedTag
    (B ∆ D) D s.orbit hgate0 s.orbitLabel


noncomputable def lpReplicaDecoratedSourceCanonicalHalfAtom
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let B :=
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    let X := lpReplicaDecoratedSourceCanonicalHalf G sites i j q z
    LPReplicaDecoratedOrbitAtom G sites (B ∆ X)
      (X.map lpReplicaCurrentReflect.toEmbedding) q := by
  dsimp only
  exact lpReplicaDecoratedOrbitAtomOfBalancedSelectorGeneral G sites _ _ q
    (lpReplicaDecoratedSourceCanonicalHalfSelector G sites i j q z)

end

end StatMech.Ising
