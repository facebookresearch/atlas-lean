/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.LocalizedCrossTree
import Code.OSSS.WiredBoxDifferential
import Code.FK.WiredDomChain
import Code.FK.OffCentreSandwichProof
import Code.OSSS.WiredDenominatorArithmetic

open scoped BigOperators Classical

namespace StatMech
namespace OSSS
namespace WiredBoxLocalized

open Lattice RevealmentConstruction AdaptiveCovLowerGeom
open LocalizedCrossTree WiredBoxDifferential
open FK DecisionTree RevealmentTranslation


def boxActiveEdgeLE (d : Nat) {n m : Nat} (h : n <= m) :
    (boxGraph d n).edgeSet -> (boxGraph d m).edgeSet := fun e =>
  ⟨innerEdgeLE d h e.1, by
    have he : e.1 ∈ (boxGraph d n).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact e.2
    have hout := ocs_innerEdgeLE_mem_edgeFinset d h e.1 he
    rwa [SimpleGraph.mem_edgeFinset] at hout⟩

theorem boxActiveEdgeLE_injective (d : Nat) {n m : Nat} (h : n <= m) :
    Function.Injective (boxActiveEdgeLE d h) := by
  intro e f hef
  apply Subtype.ext
  have hv := congrArg Subtype.val hef
  change innerEdgeLE d h e.1 = innerEdgeLE d h f.1 at hv
  have hvinj : Function.Injective (boxVertInclLE d h) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : boxVerts d m => (z : Site d)) hxy
  exact (Sym2.map.injective hvinj) hv

theorem n_le_two_mul (n : Nat) : n <= 2 * n := by omega



noncomputable def innerCrossInd (d n : Nat) :
    ConfigSpace (boxGraph d (2 * n)).edgeSet -> Real := fun omega =>
  crossIndG (boxActiveEdge d n) 0 n
    (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega)

theorem innerCrossInd_monotone (d n : Nat) : Monotone (innerCrossInd d n) := by
  intro omega eta hle
  apply (connectedToSet_increasing (boxActiveEdge d n) 0
    (vertexBoundary d n)).indicator_monotone
  intro e
  exact hle (boxActiveEdgeLE d (n_le_two_mul n) e)

theorem innerCrossInd_idem (d n : Nat)
    (omega : ConfigSpace (boxGraph d (2 * n)).edgeSet) :
    innerCrossInd d n omega * innerCrossInd d n omega = innerCrossInd d n omega := by
  unfold innerCrossInd crossIndG
  rw [Set.indicator_apply]
  split_ifs <;> norm_num


noncomputable def wiredOuterInnerDenom (d n : Nat) (q beta : Real) : Real :=
  4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
    (fun x => ∑ j ∈ Finset.range n,
      Lindeberg.mean
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (fun omega => if ConnectedToSet d
          (liftCfg (boxActiveEdge d n)
            (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
          x (centeredBoundary x j) then (1 : Real) else 0)) / (n : Real)



noncomputable def wiredOuterInnerConn (d n : Nat) (q beta : Real)
    (x : Site d) (j : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (boxGraph d (2 * n))
      (wiredBoxBoundaryGraph d (2 * n))
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnectedToSet d
      (liftCfg (boxActiveEdge d n)
        (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
      x (centeredBoundary x j) then (1 : Real) else 0)



noncomputable def wiredOuterInnerTheta (d : Nat) (q beta : Real) (k : Nat) : Real :=
  if k = 0 then 1 else
    Lindeberg.mean
      (FK.activeBCProb (boxGraph d (2 * k))
        (wiredBoxBoundaryGraph d (2 * k))
        (FK.betaParams (fun _ => 1) beta) q)
      (innerCrossInd d k)

noncomputable def wiredOuterInnerSig (d n : Nat) (q beta : Real) : Real :=
  ∑ k ∈ Finset.range n, wiredOuterInnerTheta d q beta k

theorem wiredOuterInnerConn_nonneg
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (x : Site d) (j : Nat) :
    0 <= wiredOuterInnerConn d n q beta x j := by
  apply RevealmentTranslation.mean_indicator_nonneg
  intro omega
  exact (FK.activeBCProb_pos _ _
    (FK.betaParams_pos (fun _ => by norm_num) hbeta)
    (FK.betaParams_lt_one (fun _ => 1) beta) (zero_lt_one.trans_le hq) omega).le

theorem wiredOuterInnerConn_le_one
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (x : Site d) (j : Nat) :
    wiredOuterInnerConn d n q beta x j <= 1 := by
  let mu := FK.activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) (zero_lt_one.trans_le hq) omega).le
  have hsum : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) (zero_lt_one.trans_le hq)
  calc
    wiredOuterInnerConn d n q beta x j <=
        Lindeberg.mean mu (fun _ => (1 : Real)) := by
      unfold wiredOuterInnerConn Lindeberg.mean
      apply Finset.sum_le_sum
      intro omega _
      apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
      change (if ConnectedToSet d
        (liftCfg (boxActiveEdge d n)
          (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
        x (centeredBoundary x j) then (1 : Real) else 0) <= 1
      split <;> norm_num
    _ = 1 := Lindeberg.mean_const mu hsum 1

theorem wiredOuterInnerTheta_nonneg
    (d : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) (k : Nat) :
    0 <= wiredOuterInnerTheta d q beta k := by
  by_cases hk : k = 0
  · simp [wiredOuterInnerTheta, hk]
  rw [wiredOuterInnerTheta, if_neg hk]
  unfold innerCrossInd crossIndG Lindeberg.mean
  apply Finset.sum_nonneg
  intro omega _
  apply mul_nonneg
  · change 0 <= (crossEvent (boxActiveEdge d k) 0
      (vertexBoundary d k)).indicator (fun _ => (1 : Real))
        (restrictConfig (boxActiveEdgeLE d (n_le_two_mul k)) omega)
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  · exact (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) (zero_lt_one.trans_le hq) omega).le

theorem wiredOuterInnerConn_antitone
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (x : Site d) : Antitone (wiredOuterInnerConn d n q beta x) := by
  intro j k hjk
  apply ReachBoxCrossing.mean_indicator_mono
  · intro omega
    exact (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) (zero_lt_one.trans_le hq) omega).le
  · intro omega hconn
    obtain ⟨y, hy, hxy⟩ := hconn
    rcases hxy with ⟨w⟩
    change centeredRadius x y = k at hy
    obtain ⟨z, hz, hxz⟩ := openWalk_hits_centeredBoundary w (hjk.trans_eq hy.symm)
    exact ⟨z, hz, hxz⟩

theorem wiredOuterInnerConn_zero
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (x : Site d) : wiredOuterInnerConn d n q beta x 0 = 1 := by
  let mu := FK.activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hsum : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) (zero_lt_one.trans_le hq)
  have hall : (fun omega : ConfigSpace (boxGraph d (2 * n)).edgeSet =>
      if ConnectedToSet d
        (liftCfg (boxActiveEdge d n)
          (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
        x (centeredBoundary x 0) then (1 : Real) else 0) = fun _ => 1 := by
    funext omega
    rw [if_pos]
    exact ⟨x, centeredRadius_self x, connected_refl _ _⟩
  unfold wiredOuterInnerConn
  rw [hall]
  exact Lindeberg.mean_const mu hsum 1

theorem wiredOuterInnerTheta_zero
    (d : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    wiredOuterInnerTheta d q beta 0 = 1 := by
  simp [wiredOuterInnerTheta]



theorem wiredOuterInner_sup_le_two_sig_of_comparison
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k,
      k ∈ Finset.Icc 1 (n / 2) ->
      wiredOuterInnerConn d n q beta x k <=
        wiredOuterInnerTheta d q beta k) :
    (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
        (fun x => ∑ j ∈ Finset.range n,
          wiredOuterInnerConn d n q beta x j) <=
      2 * wiredOuterInnerSig d n q beta := by
  apply Finset.sup'_le
  intro x hx
  exact antitone_sum_range_le_two_profile
    (wiredOuterInnerConn d n q beta x) (wiredOuterInnerTheta d q beta)
    (wiredOuterInnerConn_nonneg d n q beta hq hbeta x)
    (wiredOuterInnerConn_antitone d n q beta hq hbeta x)
    (wiredOuterInnerTheta_nonneg d q beta hq hbeta) n
    (by rw [wiredOuterInnerConn_zero d n q beta hq hbeta x,
      wiredOuterInnerTheta_zero d q beta hq hbeta])
    (hcomp x hx)




theorem wiredOuterInner_sup_le_two_sig_of_strict_comparison
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k,
      k ∈ Finset.Icc 1 (n / 2) -> 2 * k < n ->
      wiredOuterInnerConn d n q beta x k <=
        wiredOuterInnerTheta d q beta k) :
    (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
        (fun x => ∑ j ∈ Finset.range n,
          wiredOuterInnerConn d n q beta x j) <=
      2 * wiredOuterInnerSig d n q beta := by
  apply Finset.sup'_le
  intro x hx
  exact antitone_sum_range_le_two_profile_strict
    (wiredOuterInnerConn d n q beta x) (wiredOuterInnerTheta d q beta)
    (wiredOuterInnerConn_nonneg d n q beta hq hbeta x)
    (wiredOuterInnerConn_antitone d n q beta hq hbeta x)
    (wiredOuterInnerTheta_nonneg d q beta hq hbeta) n
    (by rw [wiredOuterInnerConn_zero d n q beta hq hbeta x,
      wiredOuterInnerTheta_zero d q beta hq hbeta])
    (hcomp x hx)
    (fun k hk => by
      rw [wiredOuterInnerTheta_zero d q beta hq hbeta]
      exact wiredOuterInnerConn_le_one d n q beta hq hbeta x k)

theorem wiredOuterInnerDenom_le_eight_sig_of_comparison
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k,
      k ∈ Finset.Icc 1 (n / 2) ->
      wiredOuterInnerConn d n q beta x k <=
        wiredOuterInnerTheta d q beta k) :
    wiredOuterInnerDenom d n q beta <=
      8 * wiredOuterInnerSig d n q beta / (n : Real) := by
  have hsup := wiredOuterInner_sup_le_two_sig_of_comparison
    d n q beta hq hbeta hcomp
  unfold wiredOuterInnerDenom
  change 4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
      (fun x => ∑ j ∈ Finset.range n,
        wiredOuterInnerConn d n q beta x j) / (n : Real) <= _
  calc
    4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
          (fun x => ∑ j ∈ Finset.range n,
            wiredOuterInnerConn d n q beta x j) / (n : Real)
        <= 4 * (2 * wiredOuterInnerSig d n q beta) / (n : Real) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsup (by norm_num)) (Nat.cast_nonneg n)
    _ = 8 * wiredOuterInnerSig d n q beta / (n : Real) := by ring

theorem wiredOuterInnerDenom_le_eight_sig_of_strict_comparison
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k,
      k ∈ Finset.Icc 1 (n / 2) -> 2 * k < n ->
      wiredOuterInnerConn d n q beta x k <=
        wiredOuterInnerTheta d q beta k) :
    wiredOuterInnerDenom d n q beta <=
      8 * wiredOuterInnerSig d n q beta / (n : Real) := by
  have hsup := wiredOuterInner_sup_le_two_sig_of_strict_comparison
    d n q beta hq hbeta hcomp
  unfold wiredOuterInnerDenom
  change 4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
      (fun x => ∑ j ∈ Finset.range n,
        wiredOuterInnerConn d n q beta x j) / (n : Real) <= _
  calc
    4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
          (fun x => ∑ j ∈ Finset.range n,
            wiredOuterInnerConn d n q beta x j) / (n : Real)
        <= 4 * (2 * wiredOuterInnerSig d n q beta) / (n : Real) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsup (by norm_num)) (Nat.cast_nonneg n)
    _ = 8 * wiredOuterInnerSig d n q beta / (n : Real) := by ring

theorem wiredOuterInnerDenom_pos
    (d n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 < wiredOuterInnerDenom d n q beta := by
  let M := (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
    (fun x => ∑ j ∈ Finset.range n,
      wiredOuterInnerConn d n q beta x j)
  have hsum : 1 <= ∑ j ∈ Finset.range n,
      wiredOuterInnerConn d n q beta 0 j := by
    rw [← wiredOuterInnerConn_zero d n q beta hq hbeta 0]
    apply Finset.single_le_sum
      (fun j _ => wiredOuterInnerConn_nonneg d n q beta hq hbeta 0 j)
    simpa using hn
  have hsup := Finset.le_sup'
    (fun x => ∑ j ∈ Finset.range n,
      wiredOuterInnerConn d n q beta x j)
    (origin_mem_osssBoxFinset d n)
  have hM : 0 < M := by
    change _ <= M at hsup
    linarith
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  unfold wiredOuterInnerDenom
  change 0 < 4 * M / (n : Real)
  positivity

theorem wiredOuterInnerSig_pos
    (d n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 < wiredOuterInnerSig d n q beta := by
  have hzero := wiredOuterInnerTheta_zero d q beta hq hbeta
  have hsum : wiredOuterInnerTheta d q beta 0 <=
      ∑ k ∈ Finset.range n, wiredOuterInnerTheta d q beta k := by
    apply Finset.single_le_sum
      (fun k _ => wiredOuterInnerTheta_nonneg d q beta hq hbeta k)
    simpa using hn
  unfold wiredOuterInnerSig
  linarith




theorem wired_outer_inner_hcov
    (d n : Nat) (hn : 1 <= n) (q beta D : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) (hD : 0 < D)
    (hsum : forall i : (boxGraph d n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (boxActiveEdgeLE d (n_le_two_mul n))
        (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n)
        (k : Nat) i) <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    Lindeberg.mean
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (innerCrossInd d n) *
      (1 - Lindeberg.mean
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (innerCrossInd d n)) / D <=
      ∑ e, Lindeberg.cov
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (innerCrossInd d n) (Lindeberg.coord e) := by
  classical
  let mu := FK.activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let iota := boxActiveEdgeLE d (n_le_two_mul n)
  let disc0 : Nat -> Finset (Site d) := osssBoundaryFinset d
  let l : List (boxGraph d n).edgeSet :=
    (Finset.univ : Finset (boxGraph d n).edgeSet).toList
  have hl : forall i : (boxGraph d n).edgeSet, i ∈ l := by simp [l]
  have hdisc0sub : ∀ k x, x ∈ disc0 k → x ∈ vertexBoundary d k := by
    intro k x hx
    simpa [disc0] using hx
  have hdisc0sup : ∀ k x, x ∈ vertexBoundary d k → x ∈ disc0 k := by
    intro k x hx
    simpa [disc0] using hx
  have hoB : forall k, (0 : Site d) ∉ disc0 k := by
    intro k
    exact origin_not_mem_osssBoundaryFinset d k
  have ho : forall k : Nat, 1 <= k -> (0 : Site d) ∈ box d (k - 1) := by
    intro k hk j
    simp
  have hcompute : forall (k : ↑(Finset.Icc 1 n))
      (omega : ConfigSpace (boxGraph d (2 * n)).edgeSet),
      (crossTree (boxActiveEndU d n) (boxActiveEndV d n) 0
        (vertexBoundary d n) l (disc0 (k : Nat))).evalR
          (restrictConfig iota omega) = innerCrossInd d n omega := by
    intro k omega
    have hk1 := (Finset.mem_Icc.mp k.2).1
    have hkn := (Finset.mem_Icc.mp k.2).2
    have heval := evalR_crossTree_connected
      (boxActiveEdge_injective d n) (boxActiveEdge_eq_endpoints d n)
      (boxActiveEnd_adj d n) (k : Nat) n hk1 hkn 0 (ho (k : Nat) hk1)
      l hl (disc0 (k : Nat)) (hdisc0sup (k : Nat)) (hoB (k : Nat))
      (restrictConfig iota omega)
    simpa [innerCrossInd, iota] using heval
  have hJ : forall e : Sym2 (boxVerts d (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmain := hcov_reindexed_crossTree_mass mu
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_FKGLatticeCondition _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq)
    iota (boxActiveEdgeLE_injective d (n_le_two_mul n))
    (boxActiveEdge_injective d n) (boxActiveEdge_eq_endpoints d n)
    (boxActiveEnd_adj d n) 0 l hl disc0 hdisc0sub n hn
    (innerCrossInd d n) (innerCrossInd_monotone d n)
    (innerCrossInd_idem d n) hcompute D hD
    (by simpa [mu, iota] using hsum)
  simpa [mu] using hmain



theorem wired_outer_inner_hcov_geom
    (d n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    Lindeberg.mean
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (innerCrossInd d n) *
      (1 - Lindeberg.mean
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (innerCrossInd d n)) / wiredOuterInnerDenom d n q beta <=
      ∑ e, Lindeberg.cov
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (innerCrossInd d n) (Lindeberg.coord e) := by
  classical
  let mu := FK.activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let iota := boxActiveEdgeLE d (n_le_two_mul n)
  let Lambda := osssBoxFinset d n
  let conn : Site d -> Nat -> Real := fun x j =>
    Lindeberg.mean mu (fun omega => if ConnectedToSet d
      (liftCfg (boxActiveEdge d n) (restrictConfig iota omega)) x
      (centeredBoundary x j) then (1 : Real) else 0)
  let M := Lambda.sup' ⟨0, origin_mem_osssBoxFinset d n⟩
    (fun x => ∑ j ∈ Finset.range n, conn x j)
  let D := 4 * M / (n : Real)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : forall e : Sym2 (boxVerts d (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0
  have hconn0 : forall x j, 0 <= conn x j := fun x j =>
    RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hMpos : 0 < M := by
    have hconnzero : conn 0 0 = 1 := by
      have hall : (fun omega : ConfigSpace (boxGraph d (2 * n)).edgeSet =>
          if ConnectedToSet d
            (liftCfg (boxActiveEdge d n) (restrictConfig iota omega)) 0
            (centeredBoundary 0 0) then (1 : Real) else 0) = fun _ => 1 := by
        funext omega
        rw [if_pos]
        exact ⟨0, centeredRadius_self 0, connected_refl _ _⟩
      change Lindeberg.mean mu (fun omega => if ConnectedToSet d
        (liftCfg (boxActiveEdge d n) (restrictConfig iota omega)) 0
        (centeredBoundary 0 0) then (1 : Real) else 0) = 1
      rw [hall]
      exact Lindeberg.mean_const mu hmu1 1
    have hs : 1 <= ∑ j ∈ Finset.range n, conn 0 j := by
      rw [← hconnzero]
      apply Finset.single_le_sum (fun j _ => hconn0 0 j)
      simpa using hn
    have hsup := Finset.le_sup'
      (fun x => ∑ j ∈ Finset.range n, conn x j)
      (origin_mem_osssBoxFinset d n)
    change _ <= M at hsup
    linarith
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hDpos : 0 < D := by
    unfold D
    positivity
  have hsum : forall i : (boxGraph d n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal mu iota
        (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n)
        (k : Nat) i) <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro i
    have hu := revealment_sum_bound_lattice_map mu hmu0
      (restrictConfig iota) (boxActiveEdge d n) Lambda
      ⟨0, origin_mem_osssBoxFinset d n⟩ (boxActiveEndU d n i)
      (boxActiveEndU_mem d n i) i.1.out.1.property
    have hv := revealment_sum_bound_lattice_map mu hmu0
      (restrictConfig iota) (boxActiveEdge d n) Lambda
      ⟨0, origin_mem_osssBoxFinset d n⟩ (boxActiveEndV d n i)
      (boxActiveEndV_mem d n i) i.1.out.2.property
    change _ <= 2 * M at hu
    change _ <= 2 * M at hv
    have hsplit :
        (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal mu iota
          (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n)
          (k : Nat) i) =
        (∑ k ∈ Finset.Icc 1 n, Lindeberg.mean mu (fun omega =>
          if ConnectedToSet d
            (liftCfg (boxActiveEdge d n) (restrictConfig iota omega))
            (boxActiveEndU d n i) (vertexBoundary d k)
          then (1 : Real) else 0)) +
        (∑ k ∈ Finset.Icc 1 n, Lindeberg.mean mu (fun omega =>
          if ConnectedToSet d
            (liftCfg (boxActiveEdge d n) (restrictConfig iota omega))
            (boxActiveEndV d n i) (vertexBoundary d k)
          then (1 : Real) else 0)) := by
      rw [Finset.sum_coe_sort (Finset.Icc 1 n)
        (fun k => localizedBoxReveal mu iota (boxActiveEdge d n)
          (boxActiveEndU d n) (boxActiveEndV d n) k i)]
      simp only [localizedBoxReveal, Finset.sum_add_distrib]
    have hncard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [hsplit, hncard]
    change _ <= (n : Real) * (4 * M / (n : Real))
    have hright : (n : Real) * (4 * M / (n : Real)) = 4 * M := by
      field_simp
    rw [hright]
    change _ <= 4 * Lambda.sup' ⟨0, origin_mem_osssBoxFinset d n⟩
      (fun x => ∑ j ∈ Finset.range n, conn x j)
    linarith
  have hmain := wired_outer_inner_hcov d n hn q beta D hq hbeta hDpos
    (by simpa [mu, iota] using hsum)
  simpa [wiredOuterInnerDenom, mu, iota, Lambda, conn, M, D] using hmain



theorem wired_outer_inner_hcov_sharp_of_comparison
    (d n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k,
      k ∈ Finset.Icc 1 (n / 2) ->
      wiredOuterInnerConn d n q beta x k <=
        wiredOuterInnerTheta d q beta k) :
    Lindeberg.mean
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (innerCrossInd d n) *
      (1 - Lindeberg.mean
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (innerCrossInd d n)) /
          (8 * wiredOuterInnerSig d n q beta / (n : Real)) <=
      ∑ e, Lindeberg.cov
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (innerCrossInd d n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let theta := Lindeberg.mean mu (innerCrossInd d n)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : forall e : Sym2 (boxVerts d (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0
  have htheta0 : 0 <= theta := by
    unfold theta Lindeberg.mean
    apply Finset.sum_nonneg
    intro omega _
    apply mul_nonneg
    · unfold innerCrossInd crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    · exact hmu0 omega
  have htheta1 : theta <= 1 := by
    calc
      theta <= Lindeberg.mean mu (fun _ => (1 : Real)) := by
        unfold theta Lindeberg.mean
        apply Finset.sum_le_sum
        intro omega _
        apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
        unfold innerCrossInd crossIndG
        rw [Set.indicator_apply]
        split_ifs <;> norm_num
      _ = 1 := Lindeberg.mean_const mu hmu1 1
  have hnum : 0 <= theta * (1 - theta) := mul_nonneg htheta0 (sub_nonneg.mpr htheta1)
  have hDpos := wiredOuterInnerDenom_pos d n hn q beta hq hbeta
  have hDle := wiredOuterInnerDenom_le_eight_sig_of_comparison
    d n q beta hq hbeta hcomp
  have hfrac : theta * (1 - theta) /
      (8 * wiredOuterInnerSig d n q beta / (n : Real)) <=
      theta * (1 - theta) / wiredOuterInnerDenom d n q beta :=
    div_le_div_of_nonneg_left hnum hDpos hDle
  have hbase := wired_outer_inner_hcov_geom d n hn q beta hq hbeta
  exact hfrac.trans (by simpa [mu, theta] using hbase)




theorem wired_outer_inner_differential_logistic
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n) (q beta D : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) (hD : 0 < D)
    (hsum : forall i : (boxGraph d n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal
        (FK.activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (FK.betaParams (fun _ => 1) beta) q)
        (boxActiveEdgeLE d (n_le_two_mul n))
        (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n)
        (k : Nat) i) <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    exists cR : Real, 0 < cR ∧
      cR * (Lindeberg.mean
          (FK.activeBCProb (boxGraph d (2 * n))
            (wiredBoxBoundaryGraph d (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (innerCrossInd d n) *
        (1 - Lindeberg.mean
          (FK.activeBCProb (boxGraph d (2 * n))
            (wiredBoxBoundaryGraph d (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (innerCrossInd d n)) / D) <=
      deriv (fun b => FK.activeBCMean (boxGraph d (2 * n))
        (wiredBoxBoundaryGraph d (2 * n))
        (FK.betaParams (fun _ => 1) b) q (innerCrossInd d n)) beta := by
  letI : Nonempty (boxGraph d (2 * n)).edgeSet :=
    boxGraph_edgeSet_nonempty d (2 * n) hd (by omega)
  let G := boxGraph d (2 * n)
  let C := wiredBoxBoundaryGraph d (2 * n)
  let J : Sym2 (boxVerts d (2 * n)) -> Real := fun _ => 1
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := innerCrossInd d n
  have hJ : forall e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) / D <=
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
    simpa [G, C, J, mu, f] using
      wired_outer_inner_hcov d n hn q beta D hq hbeta hD hsum
  have hpos : forall omega, 0 < mu omega :=
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hf : Monotone f := innerCrossInd_monotone d n
  have hcov0 : forall e : G.edgeSet,
      0 <= FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← ActiveBoundaryDifferential.cov_activeBC_eq]
    exact LindebergTree.cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := FK.hasDerivAt_activeBCMean_beta_sum G C hJ hbeta hq0 f
  have hderivEq :
      deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta =
        ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
          FK.activeBCCov G C (FK.betaParams J beta) q f
            (Lindeberg.coord e) := by
    rw [hderiv.deriv]
    simp only [FK.betaParams]
  obtain ⟨cR, hcR, hRusso⟩ :=
    RussoPrefactor.rp_differential_lower_weighted_beta
      (fun e : G.edgeSet => J e.1)
      (fun e => FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e)) beta
      (deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta)
      (fun e => hJ e.1) hbeta hcov0 hderivEq
  refine ⟨cR, hcR, ?_⟩
  have hmain := (mul_le_mul_of_nonneg_left hcov hcR.le).trans hRusso
  simpa [G, C, J, mu, f] using hmain

end WiredBoxLocalized
end OSSS
end StatMech
