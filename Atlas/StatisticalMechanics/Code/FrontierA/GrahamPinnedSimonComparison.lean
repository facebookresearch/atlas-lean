/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamPinnedFieldAdapter
import Code.FrontierA.GrahamLemmaOneAlgebra
import Code.FrontierA.GrahamWeightedBridgeGap










open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.GhostCurrentRep
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]




theorem grahamPinnedSimonComparison
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    {j k l m : V}
    (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    (1 - grahamTwoPoint E J k m ^ 2) * grahamBridgeGap E J j l m <=
      grahamTwoPoint E J j l -
        grahamFourPoint E J j l k m * grahamTwoPoint E J k m := by
  let G := grahamGraph E
  let K := grahamAnchorCoupling J m
  let hf := grahamAnchorField E J m
  have hK : ∀ e, 0 <= K e :=
    grahamAnchorCoupling_nonneg J m hJ
  have hhf : ∀ x, 0 <= hf x :=
    grahamAnchorField_nonneg E J m hJ
  have hstrong := grahamImprovedGHS_inhomogeneous_strong
    G K hf hK hhf j l k
  have hedge : G.edgeFinset = E := grahamGraph_edgeFinset E hdiag
  have hstrong' :
      (1 - grahamTwoPoint E J k m ^ 2) *
          (-(grahamFourPoint E J j l k m -
            grahamTwoPoint E J j m * grahamTwoPoint E J l k -
            grahamTwoPoint E J j l * grahamTwoPoint E J k m -
            grahamTwoPoint E J j k * grahamTwoPoint E J l m +
            2 * grahamTwoPoint E J j m *
              grahamTwoPoint E J l m * grahamTwoPoint E J k m)) >=
        2 * grahamTwoPoint E J k m *
          grahamBridgeGap E J j k m * grahamBridgeGap E J l k m := by
    dsimp only [G, K, hf] at hstrong
    unfold grahamInhomOne ghsiCovariance ghsiUrsell3 at hstrong
    rw [grahamGraph_edgeFinset E hdiag,
      grahamAnchor_threePoint_eq E J hdiag hjm hlm hkm,
      grahamAnchor_onePoint_eq E J hdiag hjm,
      grahamAnchor_onePoint_eq E J hdiag hlm,
      grahamAnchor_onePoint_eq E J hdiag hkm,
      grahamAnchor_twoPoint_eq E J hdiag hlm hkm,
      grahamAnchor_twoPoint_eq E J hdiag hjm hlm,
      grahamAnchor_twoPoint_eq E J hdiag hjm hkm] at hstrong
    unfold grahamBridgeGap
    simpa [grahamTwoPoint_comm E J] using hstrong
  have hb : 0 <= grahamTwoPoint E J k m :=
    grahamTwoPoint_nonneg E J (fun e he => hJ e) k m
  have hx : 0 <= grahamBridgeGap E J j k m :=
    grahamBridgeGap_nonneg E J (fun e he => hJ e) j k m
  have hy : 0 <= grahamBridgeGap E J l k m :=
    grahamBridgeGap_nonneg E J (fun e he => hJ e) l k m
  have hv : 0 < 1 - grahamTwoPoint E J k m ^ 2 := by
    have hp := (grahamInhomAgreement_coord_pos_lt_one G K hf k).2
    rw [grahamInhomAgreement_exp_eq G K hf k] at hp
    dsimp only [G, K, hf] at hp
    unfold grahamInhomOne at hp
    rw [hedge, grahamAnchor_onePoint_eq E J hdiag hkm] at hp
    nlinarith
  have hbridgeJ :
      0 <= grahamTwoPoint E J j m *
          (1 - grahamTwoPoint E J k m ^ 2) -
        grahamTwoPoint E J k m * grahamBridgeGap E J j k m := by
    have h := grahamBridgeGap_nonneg E J (fun e he => hJ e) j m k
    unfold grahamBridgeGap at h ⊢
    have hmk := grahamTwoPoint_comm E J m k
    calc
      0 <= grahamTwoPoint E J j m -
          grahamTwoPoint E J j k * grahamTwoPoint E J k m := h
      _ = grahamTwoPoint E J j m *
            (1 - grahamTwoPoint E J k m ^ 2) -
          grahamTwoPoint E J k m *
            (grahamTwoPoint E J j k -
              grahamTwoPoint E J j m * grahamTwoPoint E J m k) := by
        rw [hmk]
        ring
  have hbridgeL :
      0 <= grahamTwoPoint E J l m *
          (1 - grahamTwoPoint E J k m ^ 2) -
        grahamTwoPoint E J k m * grahamBridgeGap E J l k m := by
    have h := grahamBridgeGap_nonneg E J (fun e he => hJ e) l m k
    unfold grahamBridgeGap at h ⊢
    have hmk := grahamTwoPoint_comm E J m k
    calc
      0 <= grahamTwoPoint E J l m -
          grahamTwoPoint E J l k * grahamTwoPoint E J k m := h
      _ = grahamTwoPoint E J l m *
            (1 - grahamTwoPoint E J k m ^ 2) -
          grahamTwoPoint E J k m *
            (grahamTwoPoint E J l k -
              grahamTwoPoint E J l m * grahamTwoPoint E J m k) := by
        rw [hmk]
        ring
  have hfinal := grahamSimonComparison_algebra
    (a := grahamTwoPoint E J j m)
    (b := grahamTwoPoint E J k m)
    (c := grahamTwoPoint E J j l)
    (d := grahamTwoPoint E J l m)
    (e := grahamFourPoint E J j l k m)
    (x := grahamBridgeGap E J j k m)
    (y := grahamBridgeGap E J l k m)
    (v := 1 - grahamTwoPoint E J k m ^ 2)
    hv hb hx hy rfl (by
      unfold grahamBridgeGap at hstrong' ⊢
      have hmk := grahamTwoPoint_comm E J m k
      rw [hmk] at hstrong' ⊢
      calc
        2 * grahamTwoPoint E J k m *
              (grahamTwoPoint E J j k -
                grahamTwoPoint E J j m * grahamTwoPoint E J k m) *
              (grahamTwoPoint E J l k -
                grahamTwoPoint E J l m * grahamTwoPoint E J k m) <=
            (1 - grahamTwoPoint E J k m ^ 2) *
              (-(grahamFourPoint E J j l k m -
                grahamTwoPoint E J j m * grahamTwoPoint E J l k -
                grahamTwoPoint E J j l * grahamTwoPoint E J k m -
                grahamTwoPoint E J j k * grahamTwoPoint E J l m +
                2 * grahamTwoPoint E J j m *
                  grahamTwoPoint E J l m * grahamTwoPoint E J k m)) :=
          hstrong'
        _ = (1 - grahamTwoPoint E J k m ^ 2) *
            (grahamTwoPoint E J l m *
                (grahamTwoPoint E J j k -
                  grahamTwoPoint E J j m * grahamTwoPoint E J k m) +
              grahamTwoPoint E J j m *
                (grahamTwoPoint E J l k -
                  grahamTwoPoint E J l m * grahamTwoPoint E J k m) -
              (grahamFourPoint E J j l k m -
                grahamTwoPoint E J j l * grahamTwoPoint E J k m)) := by
          ring) hbridgeJ hbridgeL
  unfold grahamBridgeGap at hfinal ⊢
  have hml := grahamTwoPoint_comm E J m l
  rw [hml]
  exact hfinal


theorem expectationSwitchingGap_eq_sourcePairDisconn
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A : Finset V)
    {u v : V} (huv : u ≠ v) :
    expectationJ G beta J A -
        expectationJ G beta J (A ∆ {u, v}) *
          expectationJ G beta J {u, v} =
      sourcePairDisconnSum G beta J A ∅ u v /
        currentSum G beta J ∅ ^ 2 := by
  have hgap := gcr_currentSum_ghostRep G beta J A huv
  have hZ : currentSum G beta J ∅ ≠ 0 :=
    (StatMech.Ising.acr_currentSum_empty_pos G beta J).ne'
  rw [current_representation, current_representation,
    current_representation]
  field_simp [hZ]
  ring_nf at hgap ⊢
  exact hgap





theorem grahamPinnedSimonComparison_le_fullDisconnection
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    {j k l m : V}
    (hjl : j ≠ l) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    (1 - grahamTwoPoint E J k m ^ 2) * grahamBridgeGap E J j l m <=
      sourcePairDisconnSum (grahamGraph E) 1 J {j, l} ∅ k m /
        currentSum (grahamGraph E) 1 J ∅ ^ 2 := by
  have hpairJL : grahamPairSupport j l = ({j, l} : Finset V) := by
    ext x
    simp only [grahamPairSupport, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    aesop
  have hpairKM : grahamPairSupport k m = ({k, m} : Finset V) := by
    ext x
    simp only [grahamPairSupport, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    aesop
  have hleft :
      expectationJ (grahamGraph E) 1 J {j, l} =
        grahamTwoPoint E J j l := by
    rw [← hpairJL]
    exact grahamGraph_expectationJ_pair E J hdiag j l
  have hright :
      expectationJ (grahamGraph E) 1 J {k, m} =
        grahamTwoPoint E J k m := by
    rw [← hpairKM]
    exact grahamGraph_expectationJ_pair E J hdiag k m
  have hfour :
      expectationJ (grahamGraph E) 1 J
          (({j, l} : Finset V) ∆ {k, m}) =
        grahamFourPoint E J j l k m := by
    rw [← hpairJL, ← hpairKM]
    change expectationJ (grahamGraph E) 1 J
        (grahamFourSupport j l k m) = _
    rw [grahamGraph_expectationJ_eq_expJ E J hdiag]
    rfl
  have hgap := expectationSwitchingGap_eq_sourcePairDisconn
    (grahamGraph E) 1 J ({j, l} : Finset V) hkm
  rw [hleft, hfour, hright] at hgap
  rw [← hgap]
  exact grahamPinnedSimonComparison E J hdiag hJ hjm hkm hlm




theorem grahamBridgeProduct_le_fullDisconnection
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    {j k l m : V}
    (hjl : j ≠ l) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    grahamBridgeGap E J j k m * grahamBridgeGap E J l k m <=
      sourcePairDisconnSum (grahamGraph E) 1 J {j, l} ∅ k m /
        currentSum (grahamGraph E) 1 J ∅ ^ 2 := by
  exact (grahamBridgeGap_triangle E J (fun e he => hJ e) j k l m).trans
    (grahamPinnedSimonComparison_le_fullDisconnection
      E J hdiag hJ hjl hjm hkm hlm)

end StatMech.FrontierA
