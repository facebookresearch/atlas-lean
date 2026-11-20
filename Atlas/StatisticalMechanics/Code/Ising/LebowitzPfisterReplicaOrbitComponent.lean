/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaFiberInequality
import Code.FrontierA.GrahamFourColorBalancedCore









open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent
open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


theorem lpReplicaProfile_le_symmetrizedProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    m <= lpReplicaSymmetrizedProfile G sites m := by
  intro e
  exact Nat.le_add_right (m e) _



theorem lpReplicaProfile_le_of_symmetrizedProfile_eq
    (G : SimpleGraph V) (sites : I -> V)
    {m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (hm : lpReplicaSymmetrizedProfile G sites m = q) :
    m <= q := by
  rw [<- hm]
  exact lpReplicaProfile_le_symmetrizedProfile G sites m


theorem lpReplicaSymmetrizedProfile_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaSymmetrizedProfile G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) =
      lpReplicaSymmetrizedProfile G sites m := by
  funext e
  unfold lpReplicaSymmetrizedProfile
  dsimp only
  rw [lpReplicaCurrentEdgeReflect_involutive]
  exact Nat.add_comm _ _




noncomputable instance lpReplicaProfileOrbitFintype
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype {m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites m = q} := by
  classical
  let f : {m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites m = q} ->
      {m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // m <= q} :=
    fun m => ⟨m.1,
      lpReplicaProfile_le_of_symmetrizedProfile_eq G sites m.2⟩
  exact Fintype.ofInjective f (fun a b h => by
    apply Subtype.ext
    exact congrArg (fun z => z.1) h)


def lpReplicaProfileOrbitReflectEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    {m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
        lpReplicaSymmetrizedProfile G sites m = q} ≃
      {m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
        lpReplicaSymmetrizedProfile G sites m = q} where
  toFun m := ⟨fun e => m.1 (lpReplicaCurrentEdgeReflect G sites e), by
    rw [lpReplicaSymmetrizedProfile_reflect, m.2]⟩
  invFun m := ⟨fun e => m.1 (lpReplicaCurrentEdgeReflect G sites e), by
    rw [lpReplicaSymmetrizedProfile_reflect, m.2]⟩
  left_inv := by
    intro m
    apply Subtype.ext
    funext e
    exact congrArg m.1 (lpReplicaCurrentEdgeReflect_involutive G sites e)
  right_inv := by
    intro m
    apply Subtype.ext
    funext e
    exact congrArg m.1 (lpReplicaCurrentEdgeReflect_involutive G sites e)




theorem lpReplicaProfileOrbitMass_eq_sum
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q =
      ∑ m : {p :
          (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
          lpReplicaSymmetrizedProfile G sites p = q},
        lpReplicaRowFiberMass G sites beta J hf r A B m.1 := by
  unfold lpReplicaProfileOrbitMass
  rw [tsum_fintype]



theorem lpReplicaReflectCopies_compl
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    lpReplicaReflectCopies G sites m (Finset.univ \ S) =
      Finset.univ \ lpReplicaReflectCopies G sites m S := by
  ext c
  simp



theorem lpReplicaReflectCopies_ghost_disconn_iff
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    (Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
      (lpReplicaReflectCopies G sites m S)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) <->
      Not (RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m) S
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
  apply not_congr
  constructor
  · intro h
    have hr : RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S)
        (lpReplicaCurrentReflect lpReplicaCurrentGhost0)
        (lpReplicaCurrentReflect lpReplicaCurrentGhost1) := by
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using
        (RandomCurrent.connK_symm _ _ h)
    exact (lpReplicaReflectCopies_connK G sites m S
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).1 hr
  · intro h
    have hr := (lpReplicaReflectCopies_connK G sites m S
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).2 h
    have hs := RandomCurrent.connK_symm
      (endsM (lpReplicaCurrentGraph G sites)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
      (lpReplicaReflectCopies G sites m S) hr
    simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hs

set_option maxHeartbeats 800000 in



theorem lpReplicaDisconnProfileTerm_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaDisconnProfileTerm G sites beta J hf r
        (A.map lpReplicaCurrentReflect.toEmbedding)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) =
      lpReplicaDisconnProfileTerm G sites beta J hf r A m := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let mr : H.edgeFinset -> Nat :=
    fun e => m (lpReplicaCurrentEdgeReflect G sites e)
  let Q : Finset (Copy H m) ≃ Finset (Copy H mr) :=
    Equiv.finsetCongr (lpReplicaReflectCopyEquiv G sites m)
  have hQ (S : Finset (Copy H m)) :
      Q S = lpReplicaReflectCopies G sites m S := rfl
  have hterm (S : Finset (Copy H m)) :
      ((if RandomCurrent.sources (endsM H m) S = A then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM H m) (Finset.univ \ S) = (∅ : Finset _)
            then 1 else 0) *
          (if Not (RandomCurrent.connK (endsM H m) Finset.univ
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) then 1 else 0)) =
        ((if RandomCurrent.sources (endsM H mr) (Q S) =
              A.map lpReplicaCurrentReflect.toEmbedding
            then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM H mr) (Finset.univ \ Q S) = (∅ : Finset _)
            then 1 else 0) *
          (if Not (RandomCurrent.connK (endsM H mr) Finset.univ
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) then 1 else 0)) := by
    have hs := lpReplicaReflectCopies_sources G sites m S
    have hc := lpReplicaReflectCopies_compl G sites m S
    have hscompl := lpReplicaReflectCopies_sources G sites m (Finset.univ \ S)
    have hd := lpReplicaReflectCopies_ghost_disconn_iff G sites m
      (Finset.univ : Finset (Copy H m))
    have hruniv : lpReplicaReflectCopies G sites m
        (Finset.univ : Finset (Copy H m)) = Finset.univ := by
      ext c
      simp
    rw [hQ, <- hc, hs, hscompl]
    rw [hruniv] at hd
    have hsource :
        RandomCurrent.sources (endsM H mr)
            (lpReplicaReflectCopies G sites m S) =
              A.map lpReplicaCurrentReflect.toEmbedding <->
          RandomCurrent.sources (endsM H m) S = A := by
      rw [hs]
      exact Finset.map_inj
    have hsourceCompl :
        RandomCurrent.sources (endsM H mr)
            (lpReplicaReflectCopies G sites m (Finset.univ \ S)) = (∅ : Finset _) <->
      RandomCurrent.sources (endsM H m) (Finset.univ \ S) = (∅ : Finset _) := by
      rw [hscompl]
      simp [H]
    have hd' : Not (RandomCurrent.connK (endsM H mr) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) <->
        Not (RandomCurrent.connK (endsM H m) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
      simpa [H, mr] using hd
    simp only [Finset.map_inj, Finset.map_eq_empty, hd']
    rfl
  unfold lpReplicaDisconnProfileTerm
  change (∑ S : Finset (Copy H mr),
      (if RandomCurrent.sources (endsM H mr) S =
          A.map lpReplicaCurrentReflect.toEmbedding then (1 : Real) else 0) *
        (if RandomCurrent.sources (endsM H mr) (Finset.univ \ S) = (∅ : Finset _)
          then 1 else 0) *
        (if Not (RandomCurrent.connK (endsM H mr) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) then 1 else 0)) *
        weight H beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun H mr) = _
  rw [lpReplicaWeight_reflect]
  congr 1
  symm
  exact Fintype.sum_equiv Q _ _ hterm



def lpReplicaSubprofileReflectEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m} ≃
      {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
        a <= fun e => m (lpReplicaCurrentEdgeReflect G sites e)} where
  toFun a := ⟨fun e => a.1 (lpReplicaCurrentEdgeReflect G sites e), by
    intro e
    exact a.2 (lpReplicaCurrentEdgeReflect G sites e)⟩
  invFun a := ⟨fun e => a.1 (lpReplicaCurrentEdgeReflect G sites e), by
    intro e
    have h := a.2 (lpReplicaCurrentEdgeReflect G sites e)
    change a.1 (lpReplicaCurrentEdgeReflect G sites e) <=
      m (lpReplicaCurrentEdgeReflect G sites
        (lpReplicaCurrentEdgeReflect G sites e)) at h
    rw [lpReplicaCurrentEdgeReflect_involutive] at h
    exact h⟩
  left_inv := by
    intro a
    apply Subtype.ext
    funext e
    exact congrArg a.1 (lpReplicaCurrentEdgeReflect_involutive G sites e)
  right_inv := by
    intro a
    apply Subtype.ext
    funext e
    exact congrArg a.1 (lpReplicaCurrentEdgeReflect_involutive G sites e)


theorem lpReplicaReflectedResidual_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaReflectedResidual G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
        (fun e => a (lpReplicaCurrentEdgeReflect G sites e)) =
      fun e => lpReplicaReflectedResidual G sites m a
        (lpReplicaCurrentEdgeReflect G sites e) := by
  funext e
  unfold lpReplicaReflectedResidual
  dsimp only

set_option maxHeartbeats 800000 in



theorem lpReplicaRowFiberMass_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaRowFiberMass G sites beta J hf r
        (A.map lpReplicaCurrentReflect.toEmbedding)
        (B.map lpReplicaCurrentReflect.toEmbedding)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) =
      lpReplicaRowFiberMass G sites beta J hf r A B m := by
  classical
  let Q := lpReplicaSubprofileReflectEquiv G sites m
  unfold lpReplicaRowFiberMass
  symm
  apply Fintype.sum_equiv Q
  intro a
  change lpReplicaDisconnProfileTerm G sites beta J hf r A a.1 *
      lpReplicaDisconnProfileTerm G sites beta J hf r B
        (lpReplicaReflectedResidual G sites m a.1) =
    lpReplicaDisconnProfileTerm G sites beta J hf r
        (A.map lpReplicaCurrentReflect.toEmbedding)
        (fun e => a.1 (lpReplicaCurrentEdgeReflect G sites e)) *
      lpReplicaDisconnProfileTerm G sites beta J hf r
        (B.map lpReplicaCurrentReflect.toEmbedding)
        (lpReplicaReflectedResidual G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (fun e => a.1 (lpReplicaCurrentEdgeReflect G sites e)))
  rw [lpReplicaDisconnProfileTerm_reflect,
    lpReplicaReflectedResidual_reflect,
    lpReplicaDisconnProfileTerm_reflect]



theorem lpReplicaProfileOrbitMass_reflectSources
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaProfileOrbitMass G sites beta J hf r
        (A.map lpReplicaCurrentReflect.toEmbedding)
        (B.map lpReplicaCurrentReflect.toEmbedding) q =
      lpReplicaProfileOrbitMass G sites beta J hf r A B q := by
  classical
  rw [lpReplicaProfileOrbitMass_eq_sum,
    lpReplicaProfileOrbitMass_eq_sum]
  symm
  apply Fintype.sum_equiv (lpReplicaProfileOrbitReflectEquiv G sites q)
  intro m
  exact (lpReplicaRowFiberMass_reflect G sites beta J hf r A B m.1).symm


theorem lpReplicaCurrentReflect_seamSource
    (G : SimpleGraph V) (sites : I -> V) (i : I) :
    (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i).map
      lpReplicaCurrentReflect.toEmbedding =
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
  let R := lpReplicaCurrent_reflectedMatchingCut G
    (fun _ => 0) (fun _ => 0) sites 0
  simpa [lpReflectSource, R] using lpReflectSource_seam R i


theorem lpReplicaCurrentReflect_ghostSource
    (G : SimpleGraph V) (sites : I -> V) :
    (lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1).map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1 := by
  let R := lpReplicaCurrent_reflectedMatchingCut G
    (fun _ => 0) (fun _ => 0) sites 0
  simpa [lpReflectSource, R] using lpReflectSource_ghost R


theorem lpReplicaCurrentReflect_offdiagSource
    (G : SimpleGraph V) (sites : I -> V) (i j : I) :
    (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1).map
        lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
  let R := lpReplicaCurrent_reflectedMatchingCut G
    (fun _ => 0) (fun _ => 0) sites 0
  simpa [lpReflectSource, R] using
    lpReflectSource_matchingCommonSource R i j




def lpReplicaPartialReflectProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaCurrentGraph G sites).edgeFinset -> Nat :=
  fun e => m e - p e + p (lpReplicaCurrentEdgeReflect G sites e)



theorem lpReplicaReflectSubprofile_le_partialReflectProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) <=
      lpReplicaPartialReflectProfile G sites m p := by
  intro e
  unfold lpReplicaPartialReflectProfile
  exact Nat.le_add_left _ _



theorem lpReplicaSymmetrizedProfile_partialReflect
    (G : SimpleGraph V) (sites : I -> V)
    (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hp : p <= m) :
    lpReplicaSymmetrizedProfile G sites
        (lpReplicaPartialReflectProfile G sites m p) =
      lpReplicaSymmetrizedProfile G sites m := by
  funext e
  have he : p e <= m e := hp e
  have hr : p (lpReplicaCurrentEdgeReflect G sites e) <=
      m (lpReplicaCurrentEdgeReflect G sites e) :=
    hp (lpReplicaCurrentEdgeReflect G sites e)
  unfold lpReplicaSymmetrizedProfile lpReplicaPartialReflectProfile
  rw [lpReplicaCurrentEdgeReflect_involutive]
  omega



theorem lpReplicaPartialReflectProfile_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hp : p <= m) :
    lpReplicaPartialReflectProfile G sites
        (lpReplicaPartialReflectProfile G sites m p)
        (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) = m := by
  funext e
  have he : p e <= m e := hp e
  unfold lpReplicaPartialReflectProfile
  dsimp only
  rw [lpReplicaCurrentEdgeReflect_involutive]
  omega



theorem lpReplicaSymmetrizedProfile_partialReflectCopies
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    lpReplicaSymmetrizedProfile G sites
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) =
      lpReplicaSymmetrizedProfile G sites m :=
  lpReplicaSymmetrizedProfile_partialReflect G sites m _
    (profileFlux_le (lpReplicaCurrentGraph G sites) m P)


def lpReplicaCopySubsetSigmaEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P} ≃
      Σ e : (lpReplicaCurrentGraph G sites).edgeFinset,
        {c : Copy (lpReplicaCurrentGraph G sites) m //
          c ∈ P.filter (fun d => d.1 = e)} where
  toFun c := ⟨c.1.1, ⟨c.1, by simp [c.2]⟩⟩
  invFun c := ⟨c.2.1, (Finset.mem_filter.mp c.2.2).1⟩
  left_inv := by
    intro c
    rfl
  right_inv := by
    rintro ⟨e, ⟨c, hc⟩⟩
    have he : c.1 = e := (Finset.mem_filter.mp hc).2
    subst e
    rfl


noncomputable def lpReplicaCopyIndicesAtEdge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) : Finset (Fin (m e)) := by
  classical
  exact Finset.univ.filter fun i =>
    (Sigma.mk e i : Copy (lpReplicaCurrentGraph G sites) m) ∈ P

omit [Fintype I] [DecidableEq I] in

theorem card_lpReplicaCopyIndicesAtEdge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    (lpReplicaCopyIndicesAtEdge G sites m P e).card =
      profileFlux (lpReplicaCurrentGraph G sites) m P e := by
  classical
  let incl : Fin (m e) ↪ Copy (lpReplicaCurrentGraph G sites) m :=
    ⟨fun i => Sigma.mk e i, fun _ _ h => by simpa using h⟩
  have hmap : (lpReplicaCopyIndicesAtEdge G sites m P e).map incl =
      P.filter fun c => c.1 = e := by
    ext c
    constructor
    · intro hc
      obtain ⟨i, hi, hic⟩ := Finset.mem_map.mp hc
      simp only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
        Finset.mem_univ, true_and] at hi
      subst c
      exact Finset.mem_filter.mpr ⟨hi, rfl⟩
    · intro hc
      rw [Finset.mem_filter] at hc
      rcases c with ⟨f, i⟩
      simp only at hc
      obtain rfl := hc.2
      apply Finset.mem_map.mpr
      exact ⟨i, by
        simp only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hc.1, rfl⟩
  unfold profileFlux
  rw [← hmap, Finset.card_map]



noncomputable def lpReplicaCopiesAtEdgeEquivIndices
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    {c : Copy (lpReplicaCurrentGraph G sites) m //
      c ∈ P.filter (fun d => d.1 = e)} ≃
      {i : Fin (m e) // i ∈ lpReplicaCopyIndicesAtEdge G sites m P e} := by
  classical
  let toFun : {c : Copy (lpReplicaCurrentGraph G sites) m //
      c ∈ P.filter (fun d => d.1 = e)} ->
      {i : Fin (m e) //
        i ∈ lpReplicaCopyIndicesAtEdge G sites m P e} := fun c => by
    rcases c with ⟨⟨f, i⟩, hc⟩
    have hfe : f = e := (Finset.mem_filter.mp hc).2
    subst f
    exact ⟨i, by
      simp only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp hc).1⟩
  let invFun : {i : Fin (m e) //
      i ∈ lpReplicaCopyIndicesAtEdge G sites m P e} ->
      {c : Copy (lpReplicaCurrentGraph G sites) m //
        c ∈ P.filter (fun d => d.1 = e)} := fun i =>
    ⟨Sigma.mk e i.1, Finset.mem_filter.mpr ⟨by
      simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
        Finset.mem_univ, true_and] using i.2, rfl⟩⟩
  exact {
    toFun := toFun
    invFun := invFun
    left_inv := by
      rintro ⟨⟨f, i⟩, hc⟩
      have hfe : f = e := (Finset.mem_filter.mp hc).2
      subst f
      rfl
    right_inv := by
      rintro ⟨i, hi⟩
      rfl
  }




def lpReplicaCopySubsetEquivProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P} ≃
      Copy (lpReplicaCurrentGraph G sites)
        (profileFlux (lpReplicaCurrentGraph G sites) m P) :=
  (lpReplicaCopySubsetSigmaEquiv G sites m P).trans
    (Equiv.sigmaCongrRight fun e =>
      (lpReplicaCopiesAtEdgeEquivIndices G sites m P e).trans
        ((lpReplicaCopyIndicesAtEdge G sites m P e).orderIsoOfFin
          (card_lpReplicaCopyIndicesAtEdge G sites m P e)).symm.toEquiv)

@[simp] theorem lpReplicaCopySubsetEquivProfile_edge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P}) :
    (lpReplicaCopySubsetEquivProfile G sites m P c).1 = c.1.1 := rfl



@[simp] theorem lpReplicaCopySubsetEquivProfile_apply
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P}) :
    lpReplicaCopySubsetEquivProfile G sites m P c =
      Sigma.mk c.1.1
        (((lpReplicaCopyIndicesAtEdge G sites m P c.1.1).orderIsoOfFin
          (card_lpReplicaCopyIndicesAtEdge G sites m P c.1.1)).symm
            ⟨c.1.2, by
              simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
                Finset.mem_univ, true_and] using c.2⟩) := by
  rcases c with ⟨⟨e, k⟩, hc⟩
  rfl



theorem lpReplicaCopySubsetEquivProfile_symm_cast
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P Q : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hPQ : P = Q)
    (d : Copy (lpReplicaCurrentGraph G sites)
      (profileFlux (lpReplicaCurrentGraph G sites) m P)) :
    ((lpReplicaCopySubsetEquivProfile G sites m Q).symm
        (cast (congrArg (Copy (lpReplicaCurrentGraph G sites))
          (congrArg (profileFlux (lpReplicaCurrentGraph G sites) m) hPQ)) d)).1 =
      ((lpReplicaCopySubsetEquivProfile G sites m P).symm d).1 := by
  subst Q
  rfl

theorem lpReplicaCopySubsetEquivProfile_ends
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P}) :
    endsM (lpReplicaCurrentGraph G sites)
        (profileFlux (lpReplicaCurrentGraph G sites) m P)
        (lpReplicaCopySubsetEquivProfile G sites m P c) =
      endsM (lpReplicaCurrentGraph G sites) m c.1 := by
  rfl



def lpReplicaCopyNotMemEquivCompl
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    {c : Copy (lpReplicaCurrentGraph G sites) m // c ∉ P} ≃
      {c : Copy (lpReplicaCurrentGraph G sites) m //
        c ∈ Finset.univ \ P} where
  toFun c := ⟨c.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, c.2⟩⟩
  invFun c := ⟨c.1, (Finset.mem_sdiff.mp c.2).2⟩
  left_inv := by intro c; rfl
  right_inv := by intro c; rfl



theorem lpReplicaCollisionProfile_compl_eq_partialReflectProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P) =
      lpReplicaPartialReflectProfile G sites m
        (profileFlux (lpReplicaCurrentGraph G sites) m P) := by
  rw [profileFlux_compl]
  rfl



def lpReplicaPartialReflectCopyEquivRaw
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let p := profileFlux H m P
  let a := profileFlux H m (Finset.univ \ P)
  let split : Copy H m ≃ Copy H p ⊕ Copy H a :=
    (Equiv.sumCompl (fun c : Copy H m => c ∈ P)).symm |>.trans
      (Equiv.sumCongr
        (lpReplicaCopySubsetEquivProfile G sites m P)
        ((lpReplicaCopyNotMemEquivCompl G sites m P).trans
          (lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P))))
  let collide : Copy H a ⊕ Copy H p ≃
      Copy H (lpReplicaCollisionProfile G sites a p) :=
    (Equiv.sumCongr (Equiv.refl _)
        (lpReplicaReflectCopyEquiv G sites p)).trans
      ((Equiv.sigmaSumDistrib
        (fun e : H.edgeFinset => Fin (a e))
        (fun e : H.edgeFinset =>
          Fin (p (lpReplicaCurrentEdgeReflect G sites e)))).symm.trans
        (lpReplicaCollisionCopyEquiv G sites a p))
  exact split |>.trans (Equiv.sumComm _ _) |>.trans collide





def lpReplicaPartialReflectCopyEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) :=
  (lpReplicaPartialReflectCopyEquivRaw G sites m P).trans
    (Equiv.cast (congrArg (Copy (lpReplicaCurrentGraph G sites))
      (lpReplicaCollisionProfile_compl_eq_partialReflectProfile
        G sites m P)))

set_option maxHeartbeats 800000 in



theorem lpReplicaPartialReflectCopyEquivRaw_edge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaPartialReflectCopyEquivRaw G sites m P c).1 =
      if c ∈ P then lpReplicaCurrentEdgeReflect G sites c.1 else c.1 := by
  classical
  by_cases hc : c ∈ P
  · simp [lpReplicaPartialReflectCopyEquivRaw, hc,
      lpReplicaCopySubsetEquivProfile,
      lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCopyNotMemEquivCompl,
      lpReplicaCollisionCopyEquiv,
      lpReplicaReflectCopyEquiv]
    rfl
  · simp [lpReplicaPartialReflectCopyEquivRaw, hc,
      lpReplicaCopySubsetEquivProfile,
      lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCopyNotMemEquivCompl,
      lpReplicaCollisionCopyEquiv,
      lpReplicaReflectCopyEquiv]
    rfl

set_option maxHeartbeats 800000 in



theorem lpReplicaPartialReflectCopyEquivRaw_index_of_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) (hc : c ∈ P) :
    (lpReplicaPartialReflectCopyEquivRaw G sites m P c).2.val =
      profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)
          (lpReplicaCurrentEdgeReflect G sites c.1) +
        (((lpReplicaCopyIndicesAtEdge G sites m P c.1).orderIsoOfFin
          (card_lpReplicaCopyIndicesAtEdge G sites m P c.1)).symm
            ⟨c.2, by
              simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
                Finset.mem_univ, true_and] using hc⟩).val := by
  classical
  unfold lpReplicaPartialReflectCopyEquivRaw
  dsimp only [Equiv.trans_apply]
  have hsplit : (Equiv.sumCompl (fun d : Copy
      (lpReplicaCurrentGraph G sites) m => d ∈ P)).symm c =
      Sum.inl (⟨c, hc⟩ : {d : Copy
        (lpReplicaCurrentGraph G sites) m // d ∈ P}) := by
    simp [Equiv.sumCompl, hc]
  rw [hsplit]
  rfl

set_option maxHeartbeats 800000 in



theorem lpReplicaPartialReflectCopyEquivRaw_index_of_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) (hc : c ∉ P) :
    (lpReplicaPartialReflectCopyEquivRaw G sites m P c).2.val =
        (((lpReplicaCopyIndicesAtEdge G sites m (Finset.univ \ P) c.1).orderIsoOfFin
          (card_lpReplicaCopyIndicesAtEdge G sites m
            (Finset.univ \ P) c.1)).symm
            ⟨c.2, by
              simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
                Finset.mem_univ, Finset.mem_sdiff, true_and] using hc⟩).val := by
  classical
  unfold lpReplicaPartialReflectCopyEquivRaw
  dsimp only [Equiv.trans_apply]
  have hsplit : (Equiv.sumCompl (fun d : Copy
      (lpReplicaCurrentGraph G sites) m => d ∈ P)).symm c =
      Sum.inr (⟨c, hc⟩ : {d : Copy
        (lpReplicaCurrentGraph G sites) m // d ∉ P}) := by
    simp [Equiv.sumCompl, hc]
  rw [hsplit]
  rfl



def lpReplicaPartialReflectCopiesRaw
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P K : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))) :=
  K.map (lpReplicaPartialReflectCopyEquivRaw G sites m P).toEmbedding



theorem lpReplicaPartialReflectCopiesRaw_selected_profileFlux
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    profileFlux (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopiesRaw G sites m P P) =
      fun e => profileFlux (lpReplicaCurrentGraph G sites) m P
        (lpReplicaCurrentEdgeReflect G sites e) := by
  funext e
  unfold profileFlux lpReplicaPartialReflectCopiesRaw
  let E := (lpReplicaPartialReflectCopyEquivRaw G sites m P).toEmbedding
  change #((P.map E).filter (fun i => i.1 = e)) =
    #(P.filter (fun i => i.1 = lpReplicaCurrentEdgeReflect G sites e))
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c hc
  change (lpReplicaPartialReflectCopyEquivRaw G sites m P c).1 = e <->
    c.1 = lpReplicaCurrentEdgeReflect G sites e
  rw [lpReplicaPartialReflectCopyEquivRaw_edge, if_pos hc]
  constructor
  · intro h
    have hr := congrArg (lpReplicaCurrentEdgeReflect G sites) h
    rw [lpReplicaCurrentEdgeReflect_involutive G sites c.1] at hr
    exact hr
  · intro h
    have hr := congrArg (lpReplicaCurrentEdgeReflect G sites) h
    rw [lpReplicaCurrentEdgeReflect_involutive G sites e] at hr
    exact hr



theorem lpReplicaPartialReflectCopiesRaw_selected_profile_inverse
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let P' := lpReplicaPartialReflectCopiesRaw G sites m P P
    lpReplicaPartialReflectProfile G sites target
      (profileFlux (lpReplicaCurrentGraph G sites) target P') = m := by
  dsimp only
  rw [lpReplicaPartialReflectCopiesRaw_selected_profileFlux,
    lpReplicaCollisionProfile_compl_eq_partialReflectProfile]
  exact lpReplicaPartialReflectProfile_involutive G sites m _
    (profileFlux_le (lpReplicaCurrentGraph G sites) m P)

theorem lpReplicaPartialReflectCopyEquivRaw_ends_of_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) (hc : c ∈ P) :
    endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) =
      Sym2.map lpReplicaCurrentReflect
        (endsM (lpReplicaCurrentGraph G sites) m c) := by
  change (lpReplicaPartialReflectCopyEquivRaw G sites m P c).1.1 =
    Sym2.map lpReplicaCurrentReflect c.1.1
  rw [lpReplicaPartialReflectCopyEquivRaw_edge, if_pos hc,
    lpReplicaCurrentEdgeReflect_val]

theorem lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) (hc : c ∉ P) :
    endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) =
      endsM (lpReplicaCurrentGraph G sites) m c := by
  change (lpReplicaPartialReflectCopyEquivRaw G sites m P c).1.1 = c.1.1
  rw [lpReplicaPartialReflectCopyEquivRaw_edge, if_neg hc]


theorem lpReplicaPartialReflectCopiesRaw_selected_degK
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (x : LPReplicaCurrentVertex V) :
    RandomCurrent.degK
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P P)
        (lpReplicaCurrentReflect x) =
      RandomCurrent.degK
        (endsM (lpReplicaCurrentGraph G sites) m) P x := by
  unfold RandomCurrent.degK lpReplicaPartialReflectCopiesRaw
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c hc
  change lpReplicaCurrentReflect x ∈
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) <->
    x ∈ endsM (lpReplicaCurrentGraph G sites) m c
  rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_mem G sites m P c hc,
    Sym2.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := lpReplicaCurrentReflect.injective hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩


theorem lpReplicaPartialReflectCopiesRaw_selected_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P P) =
      (RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) m) P).map
          lpReplicaCurrentReflect.toEmbedding := by
  ext y
  have hy := lpReplicaCurrentReflect_involutive (V := V) y
  rw [<- hy]
  simp only [RandomCurrent.mem_sources,
    lpReplicaPartialReflectCopiesRaw_selected_degK]
  simp


theorem lpReplicaPartialReflectCopiesRaw_compl_degK
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (x : LPReplicaCurrentVertex V) :
    RandomCurrent.degK
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P)) x =
      RandomCurrent.degK (endsM (lpReplicaCurrentGraph G sites) m)
        (Finset.univ \ P) x := by
  unfold RandomCurrent.degK lpReplicaPartialReflectCopiesRaw
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c hc
  have hcP : c ∉ P := (Finset.mem_sdiff.mp hc).2
  change x ∈ endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      (lpReplicaPartialReflectCopyEquivRaw G sites m P c) <->
    x ∈ endsM (lpReplicaCurrentGraph G sites) m c
  rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem G sites m P c hcP]


theorem lpReplicaPartialReflectCopiesRaw_compl_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P)) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (Finset.univ \ P) := by
  ext x
  simp only [RandomCurrent.mem_sources,
    lpReplicaPartialReflectCopiesRaw_compl_degK]



theorem lpReplicaPartialReflectCopiesRaw_compl_union_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P) ∪
        lpReplicaPartialReflectCopiesRaw G sites m P P = Finset.univ := by
  unfold lpReplicaPartialReflectCopiesRaw
  rw [<- Finset.map_union,
    Finset.sdiff_union_of_subset (Finset.subset_univ P)]
  ext c
  simp

theorem lpReplicaPartialReflectCopiesRaw_compl_disjoint_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Disjoint
      (lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P))
      (lpReplicaPartialReflectCopiesRaw G sites m P P) := by
  unfold lpReplicaPartialReflectCopiesRaw
  rw [Finset.disjoint_map]
  exact Finset.sdiff_disjoint



theorem lpReplicaPartialReflectCopiesRaw_univ_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P))) Finset.univ =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (Finset.univ \ P) ∆
        (RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) P).map
            lpReplicaCurrentReflect.toEmbedding := by
  rw [<- lpReplicaPartialReflectCopiesRaw_compl_union_selected G sites m P,
    sources_union_of_disjoint
      (lpReplicaPartialReflectCopiesRaw_compl_disjoint_selected G sites m P),
    lpReplicaPartialReflectCopiesRaw_compl_sources,
    lpReplicaPartialReflectCopiesRaw_selected_sources]



theorem lpReplicaPartialReflect_rootComponent_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A : Finset (LPReplicaCurrentVertex V))
    (root : LPReplicaCurrentVertex V)
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) = A) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ root
    let C := RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ root
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P))) Finset.univ =
      lpReplicaPartialReflectSource A C := by
  dsimp only
  classical
  classical
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let P := edgeComponent e Finset.univ root
  let C := RandomCurrent.compOf e Finset.univ root
  have hPsub : P ⊆ (Finset.univ :
      Finset (Copy (lpReplicaCurrentGraph G sites) m)) := Finset.subset_univ _
  have hPsrc : RandomCurrent.sources e P = A ∩ C := by
    rw [sources_edgeComponent, hsrc]
  have hcompl : RandomCurrent.sources e (Finset.univ \ P) = A \ C := by
    rw [sources_sdiff_of_subset hPsub, hsrc, hPsrc]
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [lpReplicaPartialReflectCopiesRaw_univ_sources, hcompl, hPsrc]
  rfl



theorem lpReplicaPartialReflectCopiesRaw_sdiff_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P K : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (K \ P)) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (K \ P) := by
  ext x
  simp only [RandomCurrent.mem_sources]
  unfold RandomCurrent.degK lpReplicaPartialReflectCopiesRaw
  rw [Finset.filter_map, Finset.card_map]
  change Odd #((K \ P).filter (fun c => x ∈
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c))) <->
    Odd #((K \ P).filter (fun c =>
      x ∈ endsM (lpReplicaCurrentGraph G sites) m c))
  have hfilter :
      (K \ P).filter (fun c => x ∈
        endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P))
          (lpReplicaPartialReflectCopyEquivRaw G sites m P c)) =
        (K \ P).filter (fun c =>
          x ∈ endsM (lpReplicaCurrentGraph G sites) m c) := by
    apply Finset.filter_congr
    intro c hc
    have hcP : c ∉ P := (Finset.mem_sdiff.mp hc).2
    rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem
      G sites m P c hcP]
  rw [hfilter]



theorem lpReplicaPartialReflectCopiesRaw_sdiff_union_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hPK : P ⊆ K) :
    lpReplicaPartialReflectCopiesRaw G sites m P (K \ P) ∪
        lpReplicaPartialReflectCopiesRaw G sites m P P =
      lpReplicaPartialReflectCopiesRaw G sites m P K := by
  unfold lpReplicaPartialReflectCopiesRaw
  rw [<- Finset.map_union, Finset.sdiff_union_of_subset hPK]

theorem lpReplicaPartialReflectCopiesRaw_sdiff_disjoint_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P K : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Disjoint
      (lpReplicaPartialReflectCopiesRaw G sites m P (K \ P))
      (lpReplicaPartialReflectCopiesRaw G sites m P P) := by
  unfold lpReplicaPartialReflectCopiesRaw
  rw [Finset.disjoint_map]
  exact Finset.sdiff_disjoint



theorem lpReplicaPartialReflect_rowComponent_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (A : Finset (LPReplicaCurrentVertex V))
    (root : LPReplicaCurrentVertex V)
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K = A) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) K root
    let C := RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K root
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P K) =
      lpReplicaPartialReflectSource A C := by
  dsimp only
  classical
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let P := edgeComponent e K root
  let C := RandomCurrent.compOf e K root
  have hPsub : P ⊆ K := by
    intro c hc
    change c ∈ edgeComponent e K root at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hPsrc : RandomCurrent.sources e P = A ∩ C := by
    rw [sources_edgeComponent, hsrc]
  have houtside : RandomCurrent.sources e (K \ P) = A \ C := by
    rw [sources_sdiff_of_subset hPsub, hsrc, hPsrc]
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [<- lpReplicaPartialReflectCopiesRaw_sdiff_union_selected
      G sites m P K hPsub,
    sources_union_of_disjoint
      (lpReplicaPartialReflectCopiesRaw_sdiff_disjoint_selected
        G sites m P K),
    lpReplicaPartialReflectCopiesRaw_sdiff_sources,
    lpReplicaPartialReflectCopiesRaw_selected_sources,
    houtside, hPsrc]
  rfl



theorem lpReplicaPartialReflect_rowComponent_ghost_disconn
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hdisc : Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)))
      (lpReplicaPartialReflectCopiesRaw G sites m P K)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
  dsimp only
  classical
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  change Not (RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P)))
    (lpReplicaPartialReflectCopiesRaw G sites m P K)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
  apply not_connK_of_no_incident
    (show (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ≠
      lpReplicaCurrentGhost1 by simp
        [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])
  intro d hd hdg0
  rw [lpReplicaPartialReflectCopiesRaw] at hd
  obtain ⟨c, hcK, rfl⟩ := Finset.mem_map.mp hd
  by_cases hcP : c ∈ P
  · change lpReplicaCurrentGhost0 ∈
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) at hdg0
    rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_mem
      G sites m P c hcP, Sym2.mem_map] at hdg0
    obtain ⟨x, hxc, hxg0⟩ := hdg0
    have hx : x = (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) := by
      apply lpReplicaCurrentReflect.injective
      simpa [lpReplicaCurrentGhost1] using hxg0
    subst x
    change c ∈ edgeComponent e K lpReplicaCurrentGhost0 at hcP
    rw [edgeComponent, Finset.mem_filter] at hcP
    exact hdisc (hcP.2 lpReplicaCurrentGhost1 hxc)
  · change lpReplicaCurrentGhost0 ∈
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) at hdg0
    rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem
      G sites m P c hcP] at hdg0
    exact hcP (mem_edgeComponent_of_endpoint hcK hdg0)




theorem lpReplicaOffdiagRowComponent_partialReflectAllocation
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) :
    let C := RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    let P := lpReplicaPartialReflectSource (Si ∆ Sj ∆ T) C
    (P = Si ∧ (Si ∆ Sj ∆ T) ∆ P = Sj ∆ T) ∨
      (P = Sj ∧ (Si ∆ Sj ∆ T) ∆ P = Si ∆ T) := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let p := profileFlux H m K
  have hsrcp : RandomCurrent.sources (endsM H p)
      (Finset.univ : Finset (Copy H p)) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
    rw [StatMech.Sharpness.FluxEdgeCopy.sources_eq,
      profileFlux_univ]
    rw [<- StatMech.Sharpness.FluxEdgeCopy.sources_eq H m K]
    exact hsrc
  have hdiscp : Not (RandomCurrent.connK (endsM H p)
      (Finset.univ : Finset (Copy H p))
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
    intro hpconn
    apply hdisc
    rw [StatMech.Sharpness.FluxEdgeCopy.connK_iff,
      profileFlux_univ] at hpconn
    rw [StatMech.Sharpness.FluxEdgeCopy.connK_iff]
    exact hpconn
  have halloc := lpReplicaOffdiagComponent_partialReflectAllocation
    G sites hsite hij p hsrcp hdiscp
  have hcomp : RandomCurrent.compOf (endsM H p) Finset.univ
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) =
    RandomCurrent.compOf (endsM H m) K lpReplicaCurrentGhost0 := by
    ext x
    simp only [RandomCurrent.mem_compOf]
    rw [StatMech.Sharpness.FluxEdgeCopy.connK_iff,
      profileFlux_univ,
      StatMech.Sharpness.FluxEdgeCopy.connK_iff]
  dsimp only at halloc
  rw [hcomp] at halloc
  exact halloc



theorem lpReplicaOffdiagRowComponent_partialReflectTargetAllocation
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let Q := RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)))
      (lpReplicaPartialReflectCopiesRaw G sites m P K)
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    (Q = Si ∧ (Si ∆ Sj ∆ T) ∆ Q = Sj ∆ T) ∨
      (Q = Sj ∧ (Si ∆ Sj ∆ T) ∆ Q = Si ∆ T) := by
  dsimp only
  have hQ := lpReplicaPartialReflect_rowComponent_sources
    G sites m K
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) hsrc
  have halloc := lpReplicaOffdiagRowComponent_partialReflectAllocation
    G sites hsite hij m K hsrc hdisc
  dsimp only at hQ halloc
  rw [hQ]
  exact halloc



theorem lpReplicaPartialReflectCopiesRaw_inter_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P T : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (T ∩ P)) =
      (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (T ∩ P)).map lpReplicaCurrentReflect.toEmbedding := by
  ext y
  have hdeg : RandomCurrent.degK
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (T ∩ P)) y =
      RandomCurrent.degK (endsM (lpReplicaCurrentGraph G sites) m)
        (T ∩ P) (lpReplicaCurrentReflect y) := by
    unfold RandomCurrent.degK lpReplicaPartialReflectCopiesRaw
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    apply Finset.filter_congr
    intro c hc
    have hcP : c ∈ P := (Finset.mem_inter.mp hc).2
    change y ∈ endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P))
          (lpReplicaPartialReflectCopyEquivRaw G sites m P c) <->
        lpReplicaCurrentReflect y ∈
          endsM (lpReplicaCurrentGraph G sites) m c
    rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_mem G sites m P c hcP,
      Sym2.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hx' : x = lpReplicaCurrentReflect y :=
        lpReplicaCurrentReflect.injective
          (hxy.trans (lpReplicaCurrentReflect_involutive y).symm)
      simpa [hx'] using hx
    · intro hy
      exact ⟨lpReplicaCurrentReflect y, hy,
        lpReplicaCurrentReflect_involutive y⟩
  simp only [RandomCurrent.mem_sources, hdeg, Finset.mem_map]
  constructor
  · intro hy
    exact ⟨lpReplicaCurrentReflect y, hy,
      lpReplicaCurrentReflect_involutive y⟩
  · rintro ⟨x, hx, hxy⟩
    have hx' : x = lpReplicaCurrentReflect y :=
      lpReplicaCurrentReflect.injective
        (hxy.trans (lpReplicaCurrentReflect_involutive y).symm)
    simpa [hx'] using hx



theorem lpReplicaPartialReflectCopiesRaw_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P T : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P T) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (T \ P) ∆
        (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (T ∩ P)).map lpReplicaCurrentReflect.toEmbedding := by
  have hunion : T \ P ∪ T ∩ P = T := by
    ext c
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisj : Disjoint (T \ P) (T ∩ P) := by
    rw [Finset.disjoint_left]
    intro c hc hcp
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_inter.mp hcp).2
  have hraw : lpReplicaPartialReflectCopiesRaw G sites m P T =
      lpReplicaPartialReflectCopiesRaw G sites m P (T \ P) ∪
        lpReplicaPartialReflectCopiesRaw G sites m P (T ∩ P) := by
    unfold lpReplicaPartialReflectCopiesRaw
    rw [<- Finset.map_union, hunion]
  have hrawdisj : Disjoint
      (lpReplicaPartialReflectCopiesRaw G sites m P (T \ P))
      (lpReplicaPartialReflectCopiesRaw G sites m P (T ∩ P)) := by
    unfold lpReplicaPartialReflectCopiesRaw
    exact (Finset.disjoint_map _).2 hdisj
  rw [hraw,
    sources_union_of_disjoint hrawdisj,
    lpReplicaPartialReflectCopiesRaw_sdiff_sources,
    lpReplicaPartialReflectCopiesRaw_inter_sources]



theorem lpReplicaPartialReflect_rowComponent_subconfig_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K T : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hTK : T ⊆ K)
    (root : LPReplicaCurrentVertex V) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) K root
    let C := RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K root
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P T) =
      lpReplicaPartialReflectSource
        (RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) T) C := by
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let P := edgeComponent e K root
  let C := RandomCurrent.compOf e K root
  have hinter : RandomCurrent.sources e (T ∩ P) =
      RandomCurrent.sources e T ∩ C := by
    exact sources_inter_edgeComponent hTK root
  have houtside : RandomCurrent.sources e (T \ P) =
      RandomCurrent.sources e T \ C := by
    have hsdiff : T \ P = T \ (T ∩ P) := by
      ext c
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [hsdiff, sources_sdiff_of_subset Finset.inter_subset_left, hinter]
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [lpReplicaPartialReflectCopiesRaw_sources, houtside, hinter]
  rfl



theorem lpReplicaReflectCopies_edgeComponent
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (root : LPReplicaCurrentVertex V) :
    lpReplicaReflectCopies G sites m
        (edgeComponent
          (endsM (lpReplicaCurrentGraph G sites) m) K root) =
      edgeComponent
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m K)
        (lpReplicaCurrentReflect root) := by
  ext c
  let R := lpReplicaReflectCopyEquiv G sites m
  let d := R.symm c
  have hdc : R d = c := R.apply_symm_apply c
  rw [mem_lpReplicaReflectCopies]
  unfold edgeComponent
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hdK, hdconn⟩
    refine ⟨(mem_lpReplicaReflectCopies G sites m K c).2 hdK, ?_⟩
    intro y hy
    rw [← hdc] at hy
    rw [lpReplicaReflectCopyEquiv_ends, Sym2.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (lpReplicaReflectCopies_connK G sites m K root x).2
      (hdconn x hx)
  · rintro ⟨hcK, hcconn⟩
    refine ⟨(mem_lpReplicaReflectCopies G sites m K c).1 hcK, ?_⟩
    intro x hx
    have hy : lpReplicaCurrentReflect x ∈
        endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) c := by
      rw [← hdc]
      exact (lpReplicaReflectCopyEquiv_incident G sites m d x).2 hx
    exact (lpReplicaReflectCopies_connK G sites m K root x).1
      (hcconn (lpReplicaCurrentReflect x) hy)



theorem lpReplicaReflectCopies_edgeComponent_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (root : LPReplicaCurrentVertex V) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (edgeComponent
          (endsM (lpReplicaCurrentGraph G sites)
            (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
          (lpReplicaReflectCopies G sites m K)
          (lpReplicaCurrentReflect root)) =
      (RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) m)
        (edgeComponent
          (endsM (lpReplicaCurrentGraph G sites) m) K root)).map
        lpReplicaCurrentReflect.toEmbedding := by
  rw [← lpReplicaReflectCopies_edgeComponent]
  exact lpReplicaReflectCopies_sources G sites m _

end

end StatMech.Ising
