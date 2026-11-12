/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaTagEquiv
import Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms










open Finset

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaOrbitSplitTagDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaCollisionSplit_complProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
    profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P) =
      fun e => lpReplicaReflectedResidual G sites m a
        (lpReplicaCurrentEdgeReflect G sites e) := by
  funext e
  rw [profileFlux_compl, hP]
  unfold lpReplicaReflectedResidual
  rw [lpReplicaCurrentEdgeReflect_involutive]

@[simp] theorem lpReplicaCopy_cast_edge
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (p q : H.edgeFinset -> Nat) (h : p = q)
    (c : Copy H p) :
    (cast (congrArg (Copy H) h) c).1 = c.1 := by
  subst q
  rfl

@[simp] theorem lpReplicaCopy_cast_index
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (p q : H.edgeFinset -> Nat) (h : p = q)
    (c : Copy H p) :
    (cast (congrArg (Copy H) h) c).2.val = c.2.val := by
  subst q
  rfl



def lpReplicaOrbitCollisionSplitEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a) :
    Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a
          (lpReplicaReflectedResidual G sites m a)) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let b := lpReplicaReflectedResidual G sites m a
  let split : Copy H m ≃ Copy H a ⊕ Copy H (fun e => b
      (lpReplicaCurrentEdgeReflect G sites e)) :=
    (Equiv.sumCompl (fun c : Copy H m => c ∈ P)).symm |>.trans
      (Equiv.sumCongr
        ((lpReplicaCopySubsetEquivProfile G sites m P).trans
          (Equiv.cast (congrArg (Copy H) hP)))
        ((lpReplicaCopyNotMemEquivCompl G sites m P).trans
          ((lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P)).trans
            (Equiv.cast (congrArg (Copy H)
              (lpReplicaCollisionSplit_complProfile G sites m a P hP))))))
  let collide : Copy H a ⊕ Copy H (fun e => b
      (lpReplicaCurrentEdgeReflect G sites e)) ≃
      Copy H (lpReplicaCollisionProfile G sites a b) :=
    (Equiv.sigmaSumDistrib
        (fun e : H.edgeFinset => Fin (a e))
        (fun e : H.edgeFinset =>
          Fin (b (lpReplicaCurrentEdgeReflect G sites e)))).symm |>.trans
      (lpReplicaCollisionCopyEquiv G sites a b)
  exact split.trans collide





theorem lpReplicaOrbitCollisionSplitEquiv_symm_left
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (d : Copy (lpReplicaCurrentGraph G sites) a) :
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm
        (lpReplicaCollisionLeftCopyEmbedding G sites a
          (lpReplicaReflectedResidual G sites m a) d) =
      ((lpReplicaCopySubsetEquivProfile G sites m P).symm
        (cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hP.symm) d)).1 := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let b := lpReplicaReflectedResidual G sites m a
  let leftEquiv :=
    (lpReplicaCopySubsetEquivProfile G sites m P).trans
      (Equiv.cast (congrArg (Copy H) hP))
  let rightEquiv :=
    (lpReplicaCopyNotMemEquivCompl G sites m P).trans
      ((lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P)).trans
        (Equiv.cast (congrArg (Copy H)
          (lpReplicaCollisionSplit_complProfile G sites m a P hP))))
  let split : Copy H m ≃ Copy H a ⊕ Copy H (fun e =>
      b (lpReplicaCurrentEdgeReflect G sites e)) :=
    (Equiv.sumCompl (fun c : Copy H m => c ∈ P)).symm |>.trans
      (Equiv.sumCongr leftEquiv rightEquiv)
  let collide : Copy H a ⊕ Copy H (fun e =>
      b (lpReplicaCurrentEdgeReflect G sites e)) ≃
      Copy H (lpReplicaCollisionProfile G sites a b) :=
    (Equiv.sigmaSumDistrib
        (fun e : H.edgeFinset => Fin (a e))
        (fun e : H.edgeFinset =>
          Fin (b (lpReplicaCurrentEdgeReflect G sites e)))).symm |>.trans
      (lpReplicaCollisionCopyEquiv G sites a b)
  change (split.trans collide).symm
      (lpReplicaCollisionLeftCopyEmbedding G sites a b d) = _
  rw [Equiv.symm_trans_apply]
  have hcollide : collide.symm
      (lpReplicaCollisionLeftCopyEmbedding G sites a b d) = Sum.inl d := by
    apply collide.injective
    rw [collide.apply_symm_apply]
    rfl
  rw [hcollide]
  simp [split, leftEquiv]
  cases hP
  rfl




theorem lpReplicaOrbitCollisionSplitEquiv_symm_right
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (d : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a)) :
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm
        (lpReplicaCollisionRightCopyEmbedding G sites a
          (lpReplicaReflectedResidual G sites m a) d) =
      ((lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P)).symm
        (cast (congrArg (Copy (lpReplicaCurrentGraph G sites))
          (lpReplicaCollisionSplit_complProfile G sites m a P hP).symm)
          (lpReplicaReflectCopyEquiv G sites
            (lpReplicaReflectedResidual G sites m a) d))).1 := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let b := lpReplicaReflectedResidual G sites m a
  let hcompl := lpReplicaCollisionSplit_complProfile G sites m a P hP
  let leftEquiv :=
    (lpReplicaCopySubsetEquivProfile G sites m P).trans
      (Equiv.cast (congrArg (Copy H) hP))
  let rightEquiv :=
    (lpReplicaCopyNotMemEquivCompl G sites m P).trans
      ((lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P)).trans
        (Equiv.cast (congrArg (Copy H) hcompl)))
  let split : Copy H m ≃ Copy H a ⊕ Copy H (fun e =>
      b (lpReplicaCurrentEdgeReflect G sites e)) :=
    (Equiv.sumCompl (fun c : Copy H m => c ∈ P)).symm |>.trans
      (Equiv.sumCongr leftEquiv rightEquiv)
  let collide : Copy H a ⊕ Copy H (fun e =>
      b (lpReplicaCurrentEdgeReflect G sites e)) ≃
      Copy H (lpReplicaCollisionProfile G sites a b) :=
    (Equiv.sigmaSumDistrib
        (fun e : H.edgeFinset => Fin (a e))
        (fun e : H.edgeFinset =>
          Fin (b (lpReplicaCurrentEdgeReflect G sites e)))).symm |>.trans
      (lpReplicaCollisionCopyEquiv G sites a b)
  change (split.trans collide).symm
      (lpReplicaCollisionRightCopyEmbedding G sites a b d) = _
  rw [Equiv.symm_trans_apply]
  have hcollide : collide.symm
      (lpReplicaCollisionRightCopyEmbedding G sites a b d) =
        Sum.inr (lpReplicaReflectCopyEquiv G sites b d) := by
    apply collide.injective
    rw [collide.apply_symm_apply]
    rfl
  rw [hcollide]
  simp [split, rightEquiv, lpReplicaCopyNotMemEquivCompl]
  rw [← Equiv.cast_symm, Equiv.cast_apply]

set_option maxHeartbeats 800000 in


theorem lpReplicaOrbitCollisionSplitEquiv_edge
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP c).1 = c.1 := by
  classical
  subst a
  by_cases hc : c ∈ P
  · simp [lpReplicaOrbitCollisionSplitEquiv, hc,
      lpReplicaCopySubsetEquivProfile, lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCollisionCopyEquiv, Sigma.map]
  · simp [lpReplicaOrbitCollisionSplitEquiv, hc,
      lpReplicaCopySubsetEquivProfile, lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCopyNotMemEquivCompl, lpReplicaCollisionCopyEquiv, Sigma.map]
    apply lpReplicaCopy_cast_edge
    exact lpReplicaCollisionSplit_complProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P) P rfl


theorem lpReplicaOrbitCollisionSplitEquiv_ends
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a
          (lpReplicaReflectedResidual G sites m a))
        (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP c) =
      endsM (lpReplicaCurrentGraph G sites) m c := by
  unfold endsM
  rw [lpReplicaOrbitCollisionSplitEquiv_edge]


def lpReplicaOrbitCollisionSplitTag
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a))) :
    Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag :=
  lpReplicaTransportTag G sites
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm
    (lpReplicaCollisionRowTag G sites a
      (lpReplicaReflectedResidual G sites m a) Sa Sb)



theorem lpReplicaRowGate_orbitCollisionSplitTag
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (ha : a <= m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a)))
    (A B : Finset (LPReplicaCurrentVertex V))
    (hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites A a)
    (hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites B
      (lpReplicaReflectedResidual G sites m a)) :
    LPReplicaRowGate G sites m A
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) := by
  let b := lpReplicaReflectedResidual G sites m a
  let E := lpReplicaOrbitCollisionSplitEquiv G sites m a P hP
  have hcanonical := lpReplicaCollisionRowGate_of_mem_disconnFamilies
    G sites a b Sa Sb A B hSa hSb
  have htransport := lpReplicaRowGate_transportTag G sites E.symm (by
    intro c
    have h := lpReplicaOrbitCollisionSplitEquiv_ends
      G sites m a P hP (E.symm c)
    simpa [E] using h.symm) A (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaCollisionRowTag G sites a b Sa Sb) hcanonical
  have hprofile : lpReplicaCollisionProfile G sites a b = m :=
    lpReplicaCollision_projection G sites m a ha
  simpa only [b, E, lpReplicaOrbitCollisionSplitTag, hprofile] using htransport

end

end StatMech.Ising
