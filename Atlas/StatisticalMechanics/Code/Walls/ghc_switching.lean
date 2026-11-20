/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Ising.AizenmanSignDominance

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent








variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]














theorem ghc_switching_signDominance (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) (w : Finset ι → ℝ)
    (hwnn : ∀ K, 0 ≤ w K) (hw : ∀ K P, P ⊆ m → K ⊆ m → w (K ∆ P) = w K) :
    ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), w K
      ≤ ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), w K :=
  asd_signDominance ends m hnd A hm huv w hwnn hw











theorem ghc_switching_signedSplit_nonneg (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) (w : Finset ι → ℝ)
    (hwnn : ∀ K, 0 ≤ w K) (hw : ∀ K P, P ⊆ m → K ⊆ m → w (K ∆ P) = w K) :
    0 ≤ (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), w K)
          - ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), w K := by
  have h := ghc_switching_signDominance ends m hnd A hm huv w hwnn hw
  linarith








open StatMech.Ising

variable {W : Type*} [Fintype W] [DecidableEq W]













theorem ghc_switching_signDominance_native (G : SimpleGraph W) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 W → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : StatMech.Ising.Current W) (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (F : ℝ) (hF : 0 ≤ F)
    (A : Finset W) (hm : StatMech.Sharpness.sources G m = A) {u v : W} (huv : u ≠ v)
    (hconn_odd_or_disc :
      StatMech.Ising.connP (StatMech.Ising.oddEdges G.edgeFinset m) u v
        ∨ ¬ StatMech.Ising.connP (StatMech.Ising.posEdges G.edgeFinset m) u v) :
    StatMech.Ising.splitWeightedSum G β J m F (A ∆ {u, v})
      ≤ StatMech.Ising.splitWeightedSum G β J m F A :=
  asd_signDominance_native G β J hβ hJ m hnd F hF A hm huv hconn_odd_or_disc









theorem ghc_switching_signCancel_native (G : SimpleGraph W) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 W → ℝ) (m : StatMech.Ising.Current W)
    {u v : W} (huv : u ≠ v)
    (hconn : StatMech.Ising.connP (StatMech.Ising.oddEdges G.edgeFinset m) u v)
    (F : ℝ) (A : Finset W) :
    StatMech.Ising.splitWeightedSum G β J m F (A ∆ {u, v})
      = StatMech.Ising.splitWeightedSum G β J m F A :=
  asd_signCancel_native G β J m huv hconn F A




theorem ghc_switching_signedSplit_nonneg_native (G : SimpleGraph W) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 W → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : StatMech.Ising.Current W) (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (F : ℝ) (hF : 0 ≤ F)
    (A : Finset W) (hm : StatMech.Sharpness.sources G m = A) {u v : W} (huv : u ≠ v)
    (hconn_odd_or_disc :
      StatMech.Ising.connP (StatMech.Ising.oddEdges G.edgeFinset m) u v
        ∨ ¬ StatMech.Ising.connP (StatMech.Ising.posEdges G.edgeFinset m) u v) :
    0 ≤ StatMech.Ising.splitWeightedSum G β J m F A
          - StatMech.Ising.splitWeightedSum G β J m F (A ∆ {u, v}) := by
  have h := ghc_switching_signDominance_native G β J hβ hJ m hnd F hF A hm huv hconn_odd_or_disc
  linarith

end StatMech.Walls
