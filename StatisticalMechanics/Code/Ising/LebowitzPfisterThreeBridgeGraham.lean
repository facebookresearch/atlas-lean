/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamAgreementVBGInhomogeneous
import Code.Ising.LebowitzPfisterThreeBridgeObstruction









open Finset SimpleGraph

namespace StatMech.Ising

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem grahamInhomThreePoint_le
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (i j k : V) :
    expJ G.edgeFinset K hf
        (fun s => spin s i * (spin s j * spin s k)) <=
      grahamInhomOne G K hf i *
          expJ G.edgeFinset K hf (fun s => spin s j * spin s k) +
        expJ G.edgeFinset K hf (fun s => spin s i * spin s j) *
          grahamInhomOne G K hf k +
        expJ G.edgeFinset K hf (fun s => spin s i * spin s k) *
          grahamInhomOne G K hf j -
        2 * grahamInhomOne G K hf i * grahamInhomOne G K hf j *
          grahamInhomOne G K hf k -
        2 * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k *
          grahamInhomOne G K hf k := by
  have h := grahamImprovedGHS_inhomogeneous G K hf hK hhf i j k
  unfold ghsiUrsell3 at h
  unfold grahamInhomOne at h ⊢
  linarith




theorem grahamInhomThreePoint_strong_cleared
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (i j k : V) :
    2 * expJ G.edgeFinset K hf (fun s => spin s k) *
        (expJ G.edgeFinset K hf (fun s => spin s i * spin s k) -
          expJ G.edgeFinset K hf (fun s => spin s i) *
            expJ G.edgeFinset K hf (fun s => spin s k)) *
        (expJ G.edgeFinset K hf (fun s => spin s j * spin s k) -
          expJ G.edgeFinset K hf (fun s => spin s j) *
            expJ G.edgeFinset K hf (fun s => spin s k)) <=
      (1 - expJ G.edgeFinset K hf (fun s => spin s k) ^ 2) *
        (expJ G.edgeFinset K hf (fun s => spin s i) *
              expJ G.edgeFinset K hf (fun s => spin s j * spin s k) +
            expJ G.edgeFinset K hf (fun s => spin s i * spin s j) *
              expJ G.edgeFinset K hf (fun s => spin s k) +
            expJ G.edgeFinset K hf (fun s => spin s i * spin s k) *
              expJ G.edgeFinset K hf (fun s => spin s j) -
            2 * expJ G.edgeFinset K hf (fun s => spin s i) *
              expJ G.edgeFinset K hf (fun s => spin s j) *
              expJ G.edgeFinset K hf (fun s => spin s k) -
            expJ G.edgeFinset K hf
              (fun s => spin s i * (spin s j * spin s k))) := by
  have h := grahamImprovedGHS_inhomogeneous_strong G K hf hK hhf i j k
  unfold ghsiUrsell3 ghsiCovariance grahamInhomOne at h
  nlinarith


theorem grahamInhomThreePoint_nonneg
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    0 <= expJ G.edgeFinset K hf
      (fun s => spin s i * (spin s j * spin s k)) := by
  have h := ghsvp_expJ_nonneg G.edgeFinset K hf
    (fun e _ => hK e) hhf ({i, j, k} : Finset V)
  rw [show spinProd ({i, j, k} : Finset V) =
      (fun s => spin s i * (spin s j * spin s k)) by
    funext s
    simp [spinProd, hij, hik, hjk]] at h
  exact h



theorem sq_grahamInhomThreePoint_le
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (expJ G.edgeFinset K hf
        (fun s => spin s i * (spin s j * spin s k))) ^ 2 <=
      (grahamInhomOne G K hf i *
          expJ G.edgeFinset K hf (fun s => spin s j * spin s k) +
        expJ G.edgeFinset K hf (fun s => spin s i * spin s j) *
          grahamInhomOne G K hf k +
        expJ G.edgeFinset K hf (fun s => spin s i * spin s k) *
          grahamInhomOne G K hf j -
        2 * grahamInhomOne G K hf i * grahamInhomOne G K hf j *
          grahamInhomOne G K hf k -
        2 * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k *
          grahamInhomOne G K hf k) ^ 2 := by
  have hnonneg := grahamInhomThreePoint_nonneg G K hf hK hhf hij hik hjk
  have hle := grahamInhomThreePoint_le G K hf hK hhf i j k
  nlinarith

end

end StatMech.Ising
