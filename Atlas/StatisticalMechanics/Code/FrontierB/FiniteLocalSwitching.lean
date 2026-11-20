/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierB.InfiniteCurrentPairCylinders
import Code.Sharpness.Claim1IsingComplete

open scoped symmDiff

namespace StatMech.FrontierB

open Sharpness
open Finset MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def currentLocalPattern (S : Finset (Sym2 V))
    (Q : (↑S → ℕ) → Prop) (n : Sharpness.Current V) : Prop :=
  Q (fun e => n e.1)

instance currentLocalPattern_decidablePred (S : Finset (Sym2 V))
    (Q : (↑S → ℕ) → Prop) [DecidablePred Q] :
    DecidablePred (currentLocalPattern S Q) :=
  fun n => inferInstanceAs (Decidable (Q (fun e => n e.1)))

open scoped Classical in
theorem gatedSourcePairSum_switching_local
    (beta : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    {u v : V} (huv : u ≠ v) (S : Finset (Sym2 V))
    (Q : (↑S → ℕ) → Prop) [DecidablePred Q] :
    gatedSourcePairSum G beta J (A ∆ ({u, v} : Finset V)) {u, v}
        (currentLocalPattern S Q) =
      gatedSourcePairSum G beta J A ∅
        (fun m => currentLocalPattern S Q m ∧ CurrentConnected G m u v) :=
  gatedSourcePairSum_switching G beta J A huv (currentLocalPattern S Q)

variable {E : Type*} [Countable E]

def currentSuperpositionCylinder (S : Finset E) (A : Set (↑S → ℕ)) :
    Set (InfiniteCurrentConfig E × InfiniteCurrentConfig E) :=
  currentPairCylinder S
    {p | (fun e => p.1 e + p.2 e) ∈ A}

omit [Countable E] in
theorem isClopen_currentSuperpositionCylinder (S : Finset E)
    (A : Set (↑S → ℕ)) :
    IsClopen (currentSuperpositionCylinder S A) :=
  isClopen_currentPairCylinder S _

theorem WeakCurrentConverges.superpositionCylinder
    {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim)
    (S : Finset E) (A : Set (↑S → ℕ)) :
    Filter.Tendsto
      (fun k => (mu k).prod (nu k) (currentSuperpositionCylinder S A))
      Filter.atTop
      (nhds (muLim.prod nuLim (currentSuperpositionCylinder S A))) :=
  hmu.pairCylinder hnu S _

end StatMech.FrontierB

