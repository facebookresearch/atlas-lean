/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms








open Finset

namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


theorem lpReplicaRowCopies_true_eq_compl_false
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaRowCopies G sites m tag true =
      Finset.univ \ lpReplicaRowCopies G sites m tag false := by
  ext c
  simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff]
  cases (tag c).1 <;> simp


def lpReplicaTaggedRowProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    (lpReplicaCurrentGraph G sites).edgeFinset -> Nat :=
  profileFlux (lpReplicaCurrentGraph G sites) m
    (lpReplicaRowCopies G sites m tag row)



def lpReplicaTaggedOriginProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    (lpReplicaCurrentGraph G sites).edgeFinset -> Nat :=
  if row then
    fun e => lpReplicaTaggedRowProfile G sites m tag true
      (lpReplicaCurrentEdgeReflect G sites e)
  else lpReplicaTaggedRowProfile G sites m tag false



theorem lpReplicaTaggedOrigin_collisionProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaCollisionProfile G sites
        (lpReplicaTaggedOriginProfile G sites m tag false)
        (lpReplicaTaggedOriginProfile G sites m tag true) = m := by
  funext e
  unfold lpReplicaCollisionProfile lpReplicaTaggedOriginProfile
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [lpReplicaCurrentEdgeReflect_involutive]
  unfold lpReplicaTaggedRowProfile
  rw [lpReplicaRowCopies_true_eq_compl_false,
    profileFlux_compl]
  exact Nat.add_sub_cancel'
    (profileFlux_le (lpReplicaCurrentGraph G sites) m
      (lpReplicaRowCopies G sites m tag false) e)



theorem lpReplicaTaggedOrigin_left_le
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaTaggedOriginProfile G sites m tag false <= m := by
  intro e
  exact profileFlux_le (lpReplicaCurrentGraph G sites) m
    (lpReplicaRowCopies G sites m tag false) e



def lpReplicaTaggedRowBackEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaTaggedRowProfile G sites m tag row) ↪
      Copy (lpReplicaCurrentGraph G sites) m :=
  (lpReplicaCopySubsetEquivProfile G sites m
      (lpReplicaRowCopies G sites m tag row)).symm.toEmbedding |>.trans
    (Function.Embedding.subtype _)

theorem lpReplicaTaggedRowBackEmbedding_ends
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool)
    (c : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaTaggedRowProfile G sites m tag row)) :
    endsM (lpReplicaCurrentGraph G sites) m
        (lpReplicaTaggedRowBackEmbedding G sites m tag row c) =
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaTaggedRowProfile G sites m tag row) c := by
  let E := lpReplicaCopySubsetEquivProfile G sites m
    (lpReplicaRowCopies G sites m tag row)
  have h := lpReplicaCopySubsetEquivProfile_ends G sites m
    (lpReplicaRowCopies G sites m tag row) (E.symm c)
  simpa only [E, lpReplicaTaggedRowBackEmbedding,
    Equiv.apply_symm_apply] using h.symm


def lpReplicaTaggedRowCurrentSubset
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaTaggedRowProfile G sites m tag row)) :=
  Finset.univ.filter fun c =>
    (tag (lpReplicaTaggedRowBackEmbedding G sites m tag row c)).2 = current



theorem lpReplicaTaggedRowCurrentSubset_map_back
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    (lpReplicaTaggedRowCurrentSubset G sites m tag row current).map
        (lpReplicaTaggedRowBackEmbedding G sites m tag row) =
      lpReplicaCurrentCopies G sites m tag row current := by
  classical
  ext c
  simp only [lpReplicaTaggedRowCurrentSubset, Finset.mem_map,
    Finset.mem_filter, Finset.mem_univ, true_and,
    lpReplicaCurrentCopies]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hrow :
        (lpReplicaTaggedRowBackEmbedding G sites m tag row d) ∈
          lpReplicaRowCopies G sites m tag row :=
      (lpReplicaCopySubsetEquivProfile G sites m
        (lpReplicaRowCopies G sites m tag row)).symm d |>.2
    rw [lpReplicaRowCopies, Finset.mem_filter] at hrow
    exact Prod.ext hrow.2 hd
  · intro hc
    have hrow : c ∈ lpReplicaRowCopies G sites m tag row := by
      rw [lpReplicaRowCopies, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, congrArg Prod.fst hc⟩
    let E := lpReplicaCopySubsetEquivProfile G sites m
      (lpReplicaRowCopies G sites m tag row)
    let d := E ⟨c, hrow⟩
    have hback : lpReplicaTaggedRowBackEmbedding G sites m tag row d = c := by
      change (E.symm d).1 = c
      dsimp only [d]
      rw [E.symm_apply_apply]
    refine ⟨d, ?_, ?_⟩
    · rw [hback]
      exact congrArg Prod.snd hc
    · exact hback


theorem lpReplicaTaggedRowCurrentSubset_true_eq_compl_false
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaTaggedRowCurrentSubset G sites m tag row true =
      Finset.univ \
        lpReplicaTaggedRowCurrentSubset G sites m tag row false := by
  ext c
  simp only [lpReplicaTaggedRowCurrentSubset, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_sdiff]
  cases (tag (lpReplicaTaggedRowBackEmbedding G sites m tag row c)).2 <;>
    simp



theorem lpReplicaTaggedRowCurrentSubset_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    StatMech.Sharpness.RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaTaggedRowProfile G sites m tag row))
        (lpReplicaTaggedRowCurrentSubset G sites m tag row current) =
      StatMech.Sharpness.RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaCurrentCopies G sites m tag row current) := by
  have h := randomCurrent_sources_map_embedding
    (endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaTaggedRowProfile G sites m tag row))
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaTaggedRowBackEmbedding G sites m tag row)
    (lpReplicaTaggedRowBackEmbedding_ends G sites m tag row)
    (lpReplicaTaggedRowCurrentSubset G sites m tag row current)
  rw [lpReplicaTaggedRowCurrentSubset_map_back] at h
  exact h.symm



theorem lpReplicaTaggedRow_univ_map_back
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaTaggedRowProfile G sites m tag row))).map
        (lpReplicaTaggedRowBackEmbedding G sites m tag row) =
      lpReplicaRowCopies G sites m tag row := by
  classical
  let E := lpReplicaCopySubsetEquivProfile G sites m
    (lpReplicaRowCopies G sites m tag row)
  ext c
  constructor
  · intro hc
    obtain ⟨d, _, rfl⟩ := Finset.mem_map.mp hc
    exact (E.symm d).2
  · intro hc
    apply Finset.mem_map.mpr
    let d := E ⟨c, hc⟩
    refine ⟨d, Finset.mem_univ _, ?_⟩
    change (E.symm d).1 = c
    dsimp only [d]
    rw [E.symm_apply_apply]



theorem lpReplicaTaggedRow_ghost_disconn
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool)
    (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m tag row)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaTaggedRowProfile G sites m tag row))
      Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  intro hconn
  have h := (randomCurrent_connK_map_embedding
    (endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaTaggedRowProfile G sites m tag row))
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaTaggedRowBackEmbedding G sites m tag row)
    (lpReplicaTaggedRowBackEmbedding_ends G sites m tag row)
    Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).2 hconn
  rw [lpReplicaTaggedRow_univ_map_back] at h
  exact hdisc h



theorem lpReplicaTaggedRowCurrentSubset_mem_disconnFamily
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hgate : LPReplicaRowGate G sites m A B tag)
    (row : Bool) :
    lpReplicaTaggedRowCurrentSubset G sites m tag row false ∈
      lpReplicaDisconnProfileFamily G sites
        (if row then B else A)
        (lpReplicaTaggedRowProfile G sites m tag row) := by
  rw [mem_lpReplicaDisconnProfileFamily]
  have hsrc0 := lpReplicaTaggedRowCurrentSubset_sources
    G sites m tag row false
  have hsrc1 := lpReplicaTaggedRowCurrentSubset_sources
    G sites m tag row true
  have hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m tag row)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    cases row
    · exact hgate.2.2.1
    · exact hgate.2.2.2.2.2
  refine ⟨?_, ?_, lpReplicaTaggedRow_ghost_disconn
    G sites m tag row hdisc⟩
  · cases row
    · simpa only [Bool.false_eq_true, ↓reduceIte, hgate.1] using hsrc0
    · simpa only [if_true, hgate.2.2.2.1] using hsrc0
  · rw [<- lpReplicaTaggedRowCurrentSubset_true_eq_compl_false]
    cases row
    · simpa only [hgate.2.1] using hsrc1
    · simpa only [hgate.2.2.2.2.1] using hsrc1



theorem lpReplicaDisconnProfileFamily_reflect_mem
    (G : SimpleGraph V) (sites : I -> V)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hS : S ∈ lpReplicaDisconnProfileFamily G sites A m) :
    lpReplicaReflectCopies G sites m S ∈
      lpReplicaDisconnProfileFamily G sites
        (A.map lpReplicaCurrentReflect.toEmbedding)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) := by
  rw [mem_lpReplicaDisconnProfileFamily] at hS ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [lpReplicaReflectCopies_sources, hS.1]
  · rw [<- lpReplicaReflectCopies_compl,
      lpReplicaReflectCopies_sources, hS.2.1]
    simp
  · have hd := (lpReplicaReflectCopies_ghost_disconn_iff
      G sites m (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) m))).2 hS.2.2
    have huniv : lpReplicaReflectCopies G sites m
        (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) =
        Finset.univ := by
      ext c
      simp
    rwa [huniv] at hd



theorem lpReplicaTaggedOrigin_right_eq_reflectedResidual
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaTaggedOriginProfile G sites m tag true =
      lpReplicaReflectedResidual G sites m
        (lpReplicaTaggedOriginProfile G sites m tag false) := by
  have hcollision := lpReplicaTaggedOrigin_collisionProfile G sites m tag
  funext e
  have he := congrFun hcollision
    (lpReplicaCurrentEdgeReflect G sites e)
  unfold lpReplicaCollisionProfile at he
  unfold lpReplicaReflectedResidual
  rw [lpReplicaCurrentEdgeReflect_involutive] at he
  omega



theorem lpReplicaTaggedRowOne_reflectedCurrentSubset_mem_disconnFamily
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hgate : LPReplicaRowGate G sites m A B tag) :
    lpReplicaReflectCopies G sites
        (lpReplicaTaggedRowProfile G sites m tag true)
        (lpReplicaTaggedRowCurrentSubset G sites m tag true false) ∈
      lpReplicaDisconnProfileFamily G sites
        (B.map lpReplicaCurrentReflect.toEmbedding)
        (lpReplicaTaggedOriginProfile G sites m tag true) := by
  exact lpReplicaDisconnProfileFamily_reflect_mem G sites B
    (lpReplicaTaggedRowProfile G sites m tag true)
    (lpReplicaTaggedRowCurrentSubset G sites m tag true false)
    (lpReplicaTaggedRowCurrentSubset_mem_disconnFamily
      G sites m tag A B hgate true)

set_option maxHeartbeats 800000 in




theorem exists_lpReplicaOrbitConfiguration_of_rowGate
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    ∃ x : LPReplicaOrbitConfiguration G sites A
        (B.map lpReplicaCurrentReflect.toEmbedding) q,
      x.1.1 = m := by
  classical
  let a := lpReplicaTaggedOriginProfile G sites m tag false
  let Sa := lpReplicaTaggedRowCurrentSubset G sites m tag false false
  let b := lpReplicaTaggedOriginProfile G sites m tag true
  let Sb0 := lpReplicaReflectCopies G sites
    (lpReplicaTaggedRowProfile G sites m tag true)
    (lpReplicaTaggedRowCurrentSubset G sites m tag true false)
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
  let xb : ↑(lpReplicaDisconnProfileFamily G sites
      (B.map lpReplicaCurrentReflect.toEmbedding) b) := ⟨Sb0, hSb0⟩
  have xb' : ↑(lpReplicaDisconnProfileFamily G sites
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaReflectedResidual G sites m a)) := by
    rw [← hb]
    exact xb
  exact ⟨⟨⟨m, hm⟩, ⟨⟨a, ha⟩,
    (⟨Sa, hSa⟩, xb')⟩⟩, rfl⟩

end

end StatMech.Ising
