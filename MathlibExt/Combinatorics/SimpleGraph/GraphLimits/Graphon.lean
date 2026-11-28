/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.HomDensity
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Real

/-!
# Graphons, the cut distance and convergent graph sequences

Following the convention of the repository's finitely forcible graphons
(`IsGraphon` in `MathlibExt.Combinatorics.FinitelyForcibleGraphons`), a graphon
is represented by a function `W : ℝ → ℝ → ℝ` of which only the values on `[0, 1]²` matter.

* `graphonHomDensity F W` is `t(F, W) = ∫_{[0,1]^k} ∏_{ij ∈ E(F)} W(xᵢ, xⱼ) dx`
  (Lovász–Szegedy, *Limits of dense graph sequences*, J. Combin. Theory Ser. B 96 (2006), §2.5).
* `graphonCutNorm W = sup_{S, T ⊆ [0,1]} |∫_{S×T} W|` (Frieze–Kannan; Borgs–Chayes–Lovász–Sós–
  Vesztergombi, *Convergent sequences of dense graphs I*, Adv. Math. 219 (2008), equation (3.3)).
* `cutDistance U W = inf_{φ, ψ} ‖U^φ - W^ψ‖_□` over measure-preserving maps `φ, ψ` of `[0, 1]`
  (BCLSV, Lemma 3.5, equation (3.14)).
* `IsConvergentGraphSequence G`: `t(F, Gₙ)` converges for every simple graph `F` (Lovász–Szegedy,
  §2.2; BCLSV, Definition 2.1).

The Lovász–Szegedy limit theorem is proved in
`MathlibExt.Combinatorics.SimpleGraph.GraphLimits.LimitTheorem`; the other main theorems of the
theory (compactness, uniqueness) are recorded as wanted results in
`WantedExt.Combinatorics.SimpleGraph.GraphLimitsWanted`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.GraphLimits

open MeasureTheory Set Filter Topology

/-- **Homomorphism density in a graphon.** For a simple graph `F` on `Fin k` and a graphon `W`,
`t(F, W) = ∫_{[0,1]^k} ∏_{ij ∈ E(F)} W(xᵢ, xⱼ) dx₁ ⋯ dx_k` (Lovász–Szegedy, *Limits of dense graph
sequences*, J. Combin. Theory Ser. B 96 (2006), §2.5; Borgs–Chayes–Lovász–Sós–Vesztergombi,
*Convergent sequences of dense graphs I*, Adv. Math. 219 (2008), equation (3.1)). Each edge `ij` is
counted once, through its ordered pair `i < j`. -/
noncomputable def graphonHomDensity {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
    (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in Set.univ.pi fun _ : Fin k => Set.Icc (0 : ℝ) 1,
    ∏ i : Fin k, ∏ j : Fin k, if i < j ∧ F.Adj i j then W (x i) (x j) else 1

/-- **Measurable rectangles of the unit square.** The admissible pairs `(S, T)` in the cut norm:
measurable subsets of `[0, 1]`. -/
def CutPair : Type := {p : Set ℝ × Set ℝ //
  MeasurableSet p.1 ∧ MeasurableSet p.2 ∧ p.1 ⊆ Icc 0 1 ∧ p.2 ⊆ Icc 0 1}

/-- **Cut norm of a kernel.** `‖W‖_□ = sup_{S, T ⊆ [0,1]} |∫_{S × T} W(x, y) dx dy|`, the supremum
over measurable `S, T` (Frieze–Kannan; Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences
of dense graphs I*, Adv. Math. 219 (2008), equation (3.3)). It is meant for bounded measurable
kernels, for which the supremum is finite. -/
noncomputable def graphonCutNorm (W : ℝ → ℝ → ℝ) : ℝ :=
  ⨆ p : CutPair, |∫ q in p.1.1 ×ˢ p.1.2, W q.1 q.2|

/-- **Measure-preserving maps of the unit interval.** Maps `ℝ → ℝ` preserving the Lebesgue measure
restricted to `[0, 1]`. -/
def UnitIntervalMP : Type :=
  {φ : ℝ → ℝ // MeasurePreserving φ (volume.restrict (Icc (0 : ℝ) 1))
    (volume.restrict (Icc (0 : ℝ) 1))}

/-- **Cut distance of graphons.** `δ_□(U, W) = inf_{φ, ψ} ‖U^φ - W^ψ‖_□`, the infimum over pairs of
measure-preserving maps `φ, ψ` of `[0, 1]`, where `U^φ(x, y) = U(φ x, φ y)` (Borgs–Chayes–Lovász–
Sós–Vesztergombi, *Convergent sequences of dense graphs I*, Adv. Math. 219 (2008), Lemma 3.5,
equation (3.14)). It is a pseudometric: `δ_□(W, W^φ) = 0`. -/
noncomputable def cutDistance (U W : ℝ → ℝ → ℝ) : ℝ :=
  ⨅ p : UnitIntervalMP × UnitIntervalMP,
    graphonCutNorm fun x y => U (p.1.1 x) (p.1.1 y) - W (p.2.1 x) (p.2.1 y)

/-- **Convergent graph sequence.** A sequence of simple graphs `Gₙ` on `Fin (N n)` is convergent
(left convergent) if the homomorphism density `t(F, Gₙ)` converges as `n → ∞` for every simple
graph `F` (Lovász–Szegedy, *Limits of dense graph sequences*, J. Combin. Theory Ser. B 96 (2006),
§2.2; Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs I*, Definition
2.1). -/
def IsConvergentGraphSequence {N : ℕ → ℕ} (G : ∀ n, SimpleGraph (Fin (N n)))
    [∀ n, DecidableRel (G n).Adj] : Prop :=
  ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
    ∃ t : ℝ, Tendsto (fun n => homDensity F (adjWeight (G n))) atTop (𝓝 t)

end MathlibExt.Combinatorics.SimpleGraph.GraphLimits
