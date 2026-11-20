/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaRowTagged
import Code.Sharpness.GhostCurrentRep











open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



def lpReplicaDisconnProfileTerm
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Real := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  exact (∑ S : Finset (Copy H m),
    (if RandomCurrent.sources (endsM H m) S = A then (1 : Real) else 0) *
      (if RandomCurrent.sources (endsM H m) (Finset.univ \ S) = ∅
        then 1 else 0) *
      (if ¬ RandomCurrent.connK (endsM H m) Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 then 1 else 0)) *
      weight H beta Jr (ofEdgeFun H m)



noncomputable def lpReplicaDisconnProfileFamily
    (G : SimpleGraph V) (sites : I -> V)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (Finset (Copy (lpReplicaCurrentGraph G sites) m)) := by
  classical
  exact Finset.univ.filter fun S =>
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) S = A ∧
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (Finset.univ \ S) = ∅ ∧
      ¬ RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1

@[simp] theorem mem_lpReplicaDisconnProfileFamily
    (G : SimpleGraph V) (sites : I -> V)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    S ∈ lpReplicaDisconnProfileFamily G sites A m ↔
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) S = A ∧
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (Finset.univ \ S) = ∅ ∧
      ¬ RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  simp [lpReplicaDisconnProfileFamily]




set_option maxHeartbeats 800000 in
theorem lpReplicaDisconnProfileTerm_eq_card_mul_weight
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaDisconnProfileTerm G sites beta J hf r A m =
      (#(lpReplicaDisconnProfileFamily G sites A m) : Real) *
        weight (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r)
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let P : Finset (Copy H m) -> Prop := fun S =>
    RandomCurrent.sources (endsM H m) S = A ∧
      RandomCurrent.sources (endsM H m) (Finset.univ \ S) = ∅ ∧
      ¬ RandomCurrent.connK (endsM H m) Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  change ((∑ S : Finset (Copy H m),
      (if RandomCurrent.sources (endsM H m) S = A then (1 : Real) else 0) *
        (if RandomCurrent.sources (endsM H m) (Finset.univ \ S) = ∅
          then 1 else 0) *
        (if ¬ RandomCurrent.connK (endsM H m) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 then 1 else 0)) *
      weight H beta Jr (ofEdgeFun H m)) =
    (#((Finset.univ : Finset (Finset (Copy H m))).filter P) : Real) *
      weight H beta Jr (ofEdgeFun H m)
  congr 1
  calc
    (∑ S : Finset (Copy H m),
        (if RandomCurrent.sources (endsM H m) S = A then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM H m) (Finset.univ \ S) = ∅
            then 1 else 0) *
          (if ¬ RandomCurrent.connK (endsM H m) Finset.univ
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 then 1 else 0)) =
      ∑ S : Finset (Copy H m), if P S then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      dsimp only [P]
      by_cases hA : RandomCurrent.sources (endsM H m) S = A <;>
        by_cases hzero : RandomCurrent.sources (endsM H m)
          (Finset.univ \ S) = ∅ <;>
        by_cases hdisc : ¬ RandomCurrent.connK (endsM H m) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <;>
        simp [hA, hzero, hdisc]
    _ = (#((Finset.univ : Finset (Finset (Copy H m))).filter P) : Real) := by
      exact Finset.sum_boole P Finset.univ



theorem lpReplicaCollisionRowGate_of_mem_disconnFamilies
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b))
    (A B : Finset (LPReplicaCurrentVertex V))
    (hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites A a)
    (hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites B b) :
    LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites a b) A
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaCollisionRowTag G sites a b Sa Sb) := by
  rw [mem_lpReplicaDisconnProfileFamily] at hSa hSb
  exact lpReplicaCollisionRowGate G sites a b Sa Sb A B
    hSa.1 hSa.2.1 hSa.2.2 hSb.1 hSb.2.1 hSb.2.2



theorem lpReplicaDisconnProfileTerm_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    0 <= lpReplicaDisconnProfileTerm G sites beta J hf r A m := by
  classical
  unfold lpReplicaDisconnProfileTerm
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro S _
    positivity
  · exact StatMech.Ising.acw_weight_nonneg
      (lpReplicaCurrentGraph G sites) beta
      (lpReplicaCurrentCoupling J hf r) hbeta
      (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr) _




def lpReplicaRowFiberMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Real :=
  ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m},
    lpReplicaDisconnProfileTerm G sites beta J hf r A K.1 *
      lpReplicaDisconnProfileTerm G sites beta J hf r B
        (lpReplicaReflectedResidual G sites m K.1)



theorem lpReplicaRowFiberMass_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    0 <= lpReplicaRowFiberMass G sites beta J hf r A B m := by
  unfold lpReplicaRowFiberMass
  apply Finset.sum_nonneg
  intro K _
  exact mul_nonneg
    (lpReplicaDisconnProfileTerm_nonneg
      G sites beta J hf r hbeta hJ hhf hr A K.1)
    (lpReplicaDisconnProfileTerm_nonneg
      G sites beta J hf r hbeta hJ hhf hr B
        (lpReplicaReflectedResidual G sites m K.1))

theorem lpReplicaDisconnProfileTerm_summable
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A : Finset (LPReplicaCurrentVertex V)) :
    Summable (lpReplicaDisconnProfileTerm G sites beta J hf r A) := by
  exact StatMech.Sharpness.GhostCurrentRep.gcr_summable_edgecopy_disconn
    (lpReplicaCurrentGraph G sites) beta
    (lpReplicaCurrentCoupling J hf r)
    (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr) hbeta A
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1

set_option maxHeartbeats 800000 in
theorem lpReplicaRowFiberMass_summable
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V)) :
    Summable (lpReplicaRowFiberMass G sites beta J hf r A B) := by
  let E := (lpReplicaCurrentGraph G sites).edgeFinset
  let f := lpReplicaDisconnProfileTerm G sites beta J hf r A
  let g := lpReplicaDisconnProfileTerm G sites beta J hf r B
  let Q := lpReplicaPairEquivCollisionSigma G sites
  have hf' := lpReplicaDisconnProfileTerm_summable
    G sites beta J hf r hbeta hJ hhf hr A
  have hg' := lpReplicaDisconnProfileTerm_summable
    G sites beta J hf r hbeta hJ hhf hr B
  have hpair : Summable (fun z : (E -> Nat) × (E -> Nat) =>
      f z.1 * g z.2) :=
    summable_mul_of_summable_norm hf'.norm hg'.norm
  let F : (Σ m : E -> Nat, {a : E -> Nat // a <= m}) -> Real :=
    fun s => f s.2.1 *
      g (lpReplicaReflectedResidual G sites s.1 s.2.1)
  have hcomp : ∀ z : (E -> Nat) × (E -> Nat),
      f z.1 * g z.2 = F (Q z) := by
    rintro ⟨a, b⟩
    change f a * g b = f a * g (fun e =>
      (a (lpReplicaCurrentEdgeReflect G sites e) +
          b (lpReplicaCurrentEdgeReflect G sites
            (lpReplicaCurrentEdgeReflect G sites e))) -
        a (lpReplicaCurrentEdgeReflect G sites e))
    congr 2
    funext e
    rw [lpReplicaCurrentEdgeReflect_involutive]
    exact (Nat.add_sub_cancel_left
      (a (lpReplicaCurrentEdgeReflect G sites e)) (b e)).symm
  have hF : Summable F := by
    rw [← Q.summable_iff]
    exact hpair.congr hcomp
  have hout := hF.sigma
  apply hout.congr
  intro m
  rw [tsum_fintype]
  rfl

set_option maxHeartbeats 800000 in


theorem lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V)) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr A ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
      sourcePairDisconnSum H beta Jr B ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑' m, lpReplicaRowFiberMass G sites beta J hf r A B m := by
  dsimp only
  rw [sourcePairDisconnSum_eq_edgecopy,
    sourcePairDisconnSum_eq_edgecopy]
  change (∑' a, lpReplicaDisconnProfileTerm G sites beta J hf r A a) *
      (∑' b, lpReplicaDisconnProfileTerm G sites beta J hf r B b) = _
  exact lpReplicaCollision_tsum_mul G sites _ _
    (lpReplicaDisconnProfileTerm_summable
      G sites beta J hf r hbeta hJ hhf hr A).norm
    (lpReplicaDisconnProfileTerm_summable
      G sites beta J hf r hbeta hJ hhf hr B).norm



def lpReplicaSymmetrizedProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaCurrentGraph G sites).edgeFinset -> Nat :=
  fun e => m e + m (lpReplicaCurrentEdgeReflect G sites e)




def lpReplicaProfileOrbitMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Real :=
  ∑' m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q},
    lpReplicaRowFiberMass G sites beta J hf r A B m.1


theorem lpReplicaProfileOrbitMass_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    0 <= lpReplicaProfileOrbitMass G sites beta J hf r A B q := by
  unfold lpReplicaProfileOrbitMass
  exact tsum_nonneg fun m => lpReplicaRowFiberMass_nonneg
    G sites beta J hf r hbeta hJ hhf hr A B m.1

theorem lpReplicaProfileOrbitMass_summable
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V)) :
    Summable (lpReplicaProfileOrbitMass G sites beta J hf r A B) := by
  have h := (lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr A B).hasSum.tsum_fiberwise
      (lpReplicaSymmetrizedProfile G sites)
  exact h.summable




theorem lpReplica_sourcePairDisconn_mul_eq_tsum_profileOrbitMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V)) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr A ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
      sourcePairDisconnSum H beta Jr B ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑' q, lpReplicaProfileOrbitMass G sites beta J hf r A B q := by
  dsimp only
  rw [lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
    G sites beta J hf r hbeta hJ hhf hr A B]
  have h := (lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr A B).hasSum.tsum_fiberwise
      (lpReplicaSymmetrizedProfile G sites)
  exact h.tsum_eq.symm





def LPReplicaAggregateProfileOrbitInequality
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real) : Prop :=
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  ∀ q,
    (∑ i : I, ∑ j : I, if i = j then 0 else
      lpReplicaProfileOrbitMass G sites beta J hf r ∅
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ T) q) <=
      ∑ i : I, ∑ j : I, 2 *
        lpReplicaProfileOrbitMass G sites beta J hf r
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ T) q




theorem lpReplicaAggregateProfileOrbitInequality_of_offdiag
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hpoint : ∀ q i j, i ≠ j ->
      let Si := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
      let Sj := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
      let T := lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
      lpReplicaProfileOrbitMass G sites beta J hf r ∅ (Si ∆ Sj ∆ T) q <=
        lpReplicaProfileOrbitMass G sites beta J hf r Si (Sj ∆ T) q +
          lpReplicaProfileOrbitMass G sites beta J hf r Sj (Si ∆ T) q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  classical
  let Si : I -> Finset (LPReplicaCurrentVertex V) := fun i =>
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let o := lpReplicaProfileOrbitMass G sites beta J hf r
  intro q
  have hterm (i j : I) :
      (if i = j then 0 else o ∅ (Si i ∆ Si j ∆ T) q) <=
        o (Si i) (Si j ∆ T) q + o (Si j) (Si i ∆ T) q := by
    by_cases hij : i = j
    · rw [if_pos hij]
      exact add_nonneg
        (lpReplicaProfileOrbitMass_nonneg
          G sites beta J hf r hbeta hJ hhf hr (Si i) (Si j ∆ T) q)
        (lpReplicaProfileOrbitMass_nonneg
          G sites beta J hf r hbeta hJ hhf hr (Si j) (Si i ∆ T) q)
    · rw [if_neg hij]
      simpa only [o, Si, T] using hpoint q i j hij
  calc
    (∑ i : I, ∑ j : I, if i = j then 0 else
        o ∅ (Si i ∆ Si j ∆ T) q) <=
        ∑ i : I, ∑ j : I,
          (o (Si i) (Si j ∆ T) q + o (Si j) (Si i ∆ T) q) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm i j
    _ = ∑ i : I, ∑ j : I, 2 * o (Si i) (Si j ∆ T) q := by
      simp only [Finset.sum_add_distrib, <- Finset.mul_sum]
      rw [Finset.sum_comm]
      ring

private theorem summable_finset_sum_apply
    {X Y : Type*} [DecidableEq X]
    (s : Finset X) (f : X -> Y -> Real)
    (hf : ∀ x ∈ s, Summable (f x)) :
    Summable (fun y => ∑ x ∈ s, f x y) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      exact (hf x (Finset.mem_insert_self x s)).add
        (ih fun y hy => hf y (Finset.mem_insert_of_mem hy))




theorem lpReplicaMatchingDisconn_le_of_profileOrbit
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (horbit : LPReplicaAggregateProfileOrbitInequality
      G sites beta J hf r) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnTwo H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      2 * lpMatchingDisconnZero H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnOne H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let Si : I -> Finset (LPReplicaCurrentVertex V) := fun i =>
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let dE := sourcePairDisconnSum H beta Jr ∅ ∅
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let a : I -> Real := fun i => sourcePairDisconnSum H beta Jr
    (Si i) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let b : I -> Real := fun i => sourcePairDisconnSum H beta Jr
    (Si i ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let c : I -> I -> Real := fun i j => sourcePairDisconnSum H beta Jr
    (Si i ∆ Si j ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let o : Finset (LPReplicaCurrentVertex V) ->
      Finset (LPReplicaCurrentVertex V) ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real :=
    lpReplicaProfileOrbitMass G sites beta J hf r
  have hOrbitSummable (A B : Finset (LPReplicaCurrentVertex V)) :
      Summable (o A B) :=
    lpReplicaProfileOrbitMass_summable
      G sites beta J hf r hbeta hJ hhf hr A B
  have hprod (A B : Finset (LPReplicaCurrentVertex V)) :
      sourcePairDisconnSum H beta Jr A ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr B ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 = ∑' q, o A B q :=
    lpReplica_sourcePairDisconn_mul_eq_tsum_profileOrbitMass
      G sites beta J hf r hbeta hJ hhf hr A B
  rw [lpMatchingDisconnTwo_eq_offDiag H beta Jr
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by simp
      [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  unfold lpMatchingDisconnTwoOffDiag lpMatchingDisconnZero lpMatchingDisconnOne
  change dE * (∑ i : I, ∑ j : I, if i = j then 0 else c i j) <=
    2 * (∑ i : I, a i) * ∑ j : I, b j
  rw [show dE * (∑ i : I, ∑ j : I, if i = j then 0 else c i j) =
      ∑ i : I, ∑ j : I, if i = j then 0 else dE * c i j by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all]
  rw [show 2 * (∑ i : I, a i) * ∑ j : I, b j =
      ∑ i : I, ∑ j : I, 2 * (a i * b j) by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring]
  have hleftTerm (i j : I) :
      (if i = j then 0 else dE * c i j) =
        ∑' q, if i = j then 0 else o ∅ (Si i ∆ Si j ∆ T) q := by
    by_cases hij : i = j
    · simp [hij]
    · simp only [if_neg hij]
      simpa only [dE, c] using hprod ∅ (Si i ∆ Si j ∆ T)
  have hrightTerm (i j : I) :
      2 * (a i * b j) = ∑' q, 2 * o (Si i) (Si j ∆ T) q := by
    rw [hprod (Si i) (Si j ∆ T)]
    symm
    exact (hOrbitSummable (Si i) (Si j ∆ T)).tsum_mul_left 2
  simp_rw [hleftTerm, hrightTerm]
  let l : I -> I ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real :=
    fun i j q => if i = j then 0 else o ∅ (Si i ∆ Si j ∆ T) q
  let rr : I -> I ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real :=
    fun i j q => 2 * o (Si i) (Si j ∆ T) q
  have hl (i j : I) : Summable (l i j) := by
    by_cases hij : i = j
    · simp [l, hij]
    · simpa [l, hij] using hOrbitSummable ∅ (Si i ∆ Si j ∆ T)
  have hrr (i j : I) : Summable (rr i j) := by
    exact (hOrbitSummable (Si i) (Si j ∆ T)).mul_left 2
  have hswapL : (∑ i : I, ∑ j : I, ∑' q, l i j q) =
      ∑' q, ∑ i : I, ∑ j : I, l i j q := by
    symm
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Summable.tsum_finsetSum fun j _ => hl i j]
    · intro i _
      exact summable_finset_sum_apply Finset.univ (l i) fun j _ => hl i j
  have hswapR : (∑ i : I, ∑ j : I, ∑' q, rr i j q) =
      ∑' q, ∑ i : I, ∑ j : I, rr i j q := by
    symm
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Summable.tsum_finsetSum fun j _ => hrr i j]
    · intro i _
      exact summable_finset_sum_apply Finset.univ (rr i) fun j _ => hrr i j
  rw [hswapL, hswapR]
  apply Summable.tsum_le_tsum
  · simpa only [l, rr, o, Si, T] using horbit
  · exact summable_finset_sum_apply Finset.univ
      (fun i q => ∑ j : I, l i j q) fun i _ =>
        summable_finset_sum_apply Finset.univ (l i) fun j _ => hl i j
  · exact summable_finset_sum_apply Finset.univ
      (fun i q => ∑ j : I, rr i j q) fun i _ =>
        summable_finset_sum_apply Finset.univ (rr i) fun j _ => hrr i j



theorem lpReplica_disconn_fourFunctions_of_fiberwise
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B C D E F : Finset (LPReplicaCurrentVertex V))
    (hfiber : ∀ m,
      lpReplicaRowFiberMass G sites beta J hf r A B m <=
        lpReplicaRowFiberMass G sites beta J hf r C D m +
          lpReplicaRowFiberMass G sites beta J hf r E F m) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr A ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr B ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      sourcePairDisconnSum H beta Jr C ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr D ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 +
      sourcePairDisconnSum H beta Jr E ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr F ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  dsimp only
  rw [lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
      G sites beta J hf r hbeta hJ hhf hr A B,
    lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
      G sites beta J hf r hbeta hJ hhf hr C D,
    lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
      G sites beta J hf r hbeta hJ hhf hr E F]
  have hAB := lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr A B
  have hCD := lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr C D
  have hEF := lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr E F
  rw [← hCD.tsum_add hEF]
  exact Summable.tsum_le_tsum hfiber hAB (hCD.add hEF)





def LPReplicaOffdiagFiberInequality
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (i j : I) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  ∀ m,
    lpReplicaRowFiberMass G sites beta J hf r ∅ (Si ∆ Sj ∆ T) m <=
      lpReplicaRowFiberMass G sites beta J hf r Si (Sj ∆ T) m +
        lpReplicaRowFiberMass G sites beta J hf r Sj (Si ∆ T) m



theorem lpReplica_offdiagFourFunctions_of_fiberwise
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (i j : I)
    (hfiber : LPReplicaOffdiagFiberInequality
      G sites beta J hf r i j) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr (Si ∆ Sj ∆ T) ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      sourcePairDisconnSum H beta Jr Si ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr (Sj ∆ T) ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 +
      sourcePairDisconnSum H beta Jr Sj ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr (Si ∆ T) ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  dsimp only
  apply lpReplica_disconn_fourFunctions_of_fiberwise
    G sites beta J hf r hbeta hJ hhf hr
  exact hfiber



theorem lpReplicaMatchingDisconn_le_of_fiberwise
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hfiber : ∀ i j : I, i ≠ j ->
      LPReplicaOffdiagFiberInequality G sites beta J hf r i j) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnTwo H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      2 * lpMatchingDisconnZero H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnOne H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  apply lpReplicaMatchingDisconn_le_of_offdiagFourFunctions
    G sites beta J hf r hbeta hJ hhf hr
  intro i j hij
  exact lpReplica_offdiagFourFunctions_of_fiberwise
    G sites beta J hf r hbeta hJ hhf hr i j (hfiber i j hij)

end

end StatMech.Ising
