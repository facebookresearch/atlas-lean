/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching










open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveOrderedPairSwapDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaOffdiagSeamSelector_swap
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    lpReplicaOffdiagSeamSelector G sites hsite i j hij
        (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
      lpReplicaOffdiagSeamSelector G sites hsite j i hij.symm
        (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
  unfold lpReplicaOffdiagSeamSelector
  simp only [lpReplicaCurrentEdgeFlux_ofEdgeFun]
  rw [dif_pos hsrc]
  have hsrc' : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
    simpa only [symmDiff_assoc, symmDiff_left_comm, symmDiff_comm] using hsrc
  rw [dif_pos hsrc']

omit [Fintype V] [Fintype I] [DecidableEq I] in


theorem lpReplicaOffdiagSourceBoundary_swap
    (sites : I -> V) (i j : I) :
    lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
  exact congrArg
    (fun X => X ∆ lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1)
    (symmDiff_comm _ _)


noncomputable def lpReplicaOffdiagDecoratedSourceSwap
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedSource G sites i j q ≃
      LPReplicaOffdiagDecoratedSource G sites j i q :=
  Equiv.cast (congrArg
    (fun B => LPReplicaDecoratedOrbitAtom G sites ∅ B q)
    (lpReplicaOffdiagSourceBoundary_swap sites i j))


noncomputable def lpReplicaAggregateDecoratedSourceSwap
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
  LPReplicaAggregateDecoratedSource G sites q := by
  have hij := lpReplicaAggregateDecoratedSource_indices_ne G sites q z
  exact ⟨z.2.1, z.1,
    ⟨z.2.2.1.1, by simpa [hij, hij.symm] using z.2.2.1.2⟩,
    lpReplicaOffdiagDecoratedSourceSwap
      G sites z.1 z.2.1 q z.2.2.2⟩

set_option maxHeartbeats 1000000 in


theorem lpReplicaAggregateDecoratedSourceSwap_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Involutive
      (lpReplicaAggregateDecoratedSourceSwap G sites q) := by
  intro z
  rcases z with ⟨i, j, w, atom⟩
  simp only [lpReplicaAggregateDecoratedSourceSwap]
  congr
  have hswap : lpReplicaOffdiagDecoratedSourceSwap G sites j i q =
      (lpReplicaOffdiagDecoratedSourceSwap G sites i j q).symm := by
    unfold lpReplicaOffdiagDecoratedSourceSwap
    rw [← Equiv.cast_symm]
  rw [hswap]
  exact (lpReplicaOffdiagDecoratedSourceSwap
    G sites i j q).symm_apply_apply atom


theorem lpReplicaAggregateDecoratedSourceSwap_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (lpReplicaAggregateDecoratedSourceSwap G sites q) :=
  (lpReplicaAggregateDecoratedSourceSwap_involutive G sites q).injective


theorem lpReplicaAggregateDecoratedSourceSwap_ne
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    lpReplicaAggregateDecoratedSourceSwap G sites q z ≠ z := by
  intro hswap
  have hindices := congrArg Sigma.fst hswap
  exact lpReplicaAggregateDecoratedSource_indices_ne G sites q z hindices.symm



def LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) : Prop :=
  ((Fintype.equivFin I) z.1).val <
    ((Fintype.equivFin I) z.2.1).val


def LPReplicaAggregateDecoratedSourcePairRepresentative
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  {z : LPReplicaAggregateDecoratedSource G sites q //
    LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair G sites q z}

noncomputable instance
    instFintypeLPReplicaAggregateDecoratedSourcePairRepresentative
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaAggregateDecoratedSourcePairRepresentative
      G sites q) := by
  classical
  unfold LPReplicaAggregateDecoratedSourcePairRepresentative
  exact Fintype.ofFinite _

theorem lpReplicaAggregateDecoratedSourceSwap_canonical_of_not
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (h : ¬ LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
      G sites q z) :
    LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair G sites q
      (lpReplicaAggregateDecoratedSourceSwap G sites q z) := by
  have hne : ((Fintype.equivFin I) z.1).val ≠
      ((Fintype.equivFin I) z.2.1).val := by
    intro heq
    apply lpReplicaAggregateDecoratedSource_indices_ne G sites q z
    apply (Fintype.equivFin I).injective
    exact Fin.ext heq
  unfold LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair at h ⊢
  simp only [lpReplicaAggregateDecoratedSourceSwap]
  omega

theorem lpReplicaAggregateDecoratedSourceSwap_not_canonical_of_canonical
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (h : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
      G sites q z) :
    ¬ LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair G sites q
      (lpReplicaAggregateDecoratedSourceSwap G sites q z) := by
  unfold LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair at h ⊢
  simp only [lpReplicaAggregateDecoratedSourceSwap]
  omega


noncomputable def lpReplicaAggregateDecoratedSourcePairCode
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    Fin 2 × LPReplicaAggregateDecoratedSourcePairRepresentative
      G sites q := by
  classical
  exact if h : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
      G sites q z then
      ⟨0, ⟨z, h⟩⟩
    else
      ⟨1, ⟨lpReplicaAggregateDecoratedSourceSwap G sites q z,
        lpReplicaAggregateDecoratedSourceSwap_canonical_of_not
          G sites q z h⟩⟩



noncomputable def lpReplicaAggregateDecoratedSourcePairDecode
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fin 2 × LPReplicaAggregateDecoratedSourcePairRepresentative G sites q ->
      LPReplicaAggregateDecoratedSource G sites q
  | ⟨b, z⟩ => if b.1 = 0 then z.1 else
      lpReplicaAggregateDecoratedSourceSwap G sites q z.1

theorem lpReplicaAggregateDecoratedSourcePairDecode_code
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    lpReplicaAggregateDecoratedSourcePairDecode G sites q
        (lpReplicaAggregateDecoratedSourcePairCode G sites q z) = z := by
  by_cases h : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair
      G sites q z
  · simp [lpReplicaAggregateDecoratedSourcePairCode,
      lpReplicaAggregateDecoratedSourcePairDecode, h]
  · simp [lpReplicaAggregateDecoratedSourcePairCode,
      lpReplicaAggregateDecoratedSourcePairDecode, h,
      lpReplicaAggregateDecoratedSourceSwap_involutive G sites q z]

theorem lpReplicaAggregateDecoratedSourcePairCode_decode
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (x : Fin 2 × LPReplicaAggregateDecoratedSourcePairRepresentative
      G sites q) :
    lpReplicaAggregateDecoratedSourcePairCode G sites q
        (lpReplicaAggregateDecoratedSourcePairDecode G sites q x) = x := by
  rcases x with ⟨b, z⟩
  fin_cases b
  · simp [lpReplicaAggregateDecoratedSourcePairDecode,
      lpReplicaAggregateDecoratedSourcePairCode, z.2]
  · have hn :=
      lpReplicaAggregateDecoratedSourceSwap_not_canonical_of_canonical
        G sites q z.1 z.2
    simp [lpReplicaAggregateDecoratedSourcePairDecode,
      lpReplicaAggregateDecoratedSourcePairCode, hn,
      lpReplicaAggregateDecoratedSourceSwap_involutive G sites q z.1]



noncomputable def lpReplicaAggregateDecoratedSourcePairEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaAggregateDecoratedSource G sites q ≃
      Fin 2 × LPReplicaAggregateDecoratedSourcePairRepresentative
        G sites q where
  toFun := lpReplicaAggregateDecoratedSourcePairCode G sites q
  invFun := lpReplicaAggregateDecoratedSourcePairDecode G sites q
  left_inv := lpReplicaAggregateDecoratedSourcePairDecode_code G sites q
  right_inv := lpReplicaAggregateDecoratedSourcePairCode_decode G sites q

end

end StatMech.Ising
