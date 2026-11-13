/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Optimal two-phase conductors for the first eigenvalue (Oberwolfach Reports 57/2012)

Oberwolfach mini-workshop Geometries, Shapes and Topologies in PDE-based Applications (2012), A.
Laurain (with C. Conca and R. Mahadevan): for a bounded domain `Ω ⊆ ℝ^d`, `0 < m < |Ω|` and `0 < α <
β`, does minimizing the first Dirichlet eigenvalue of `-div((α χ_A + β χ_B) ∇u)` over measurable
partitions `Ω = A ∪ B` with `|B| = m` always have a solution?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.TwoPhaseEigenvalueOptimalDesignOWR12180Problem001Wanted

/-!
Source: A. Laurain (with C. Conca and R. Mahadevan), in Mini-Workshop: Geometries, Shapes and
Topologies in PDE-based Applications, Oberwolfach Reports 9 (2012), no. 57, pp. 3407-3408, DOI
10.4171/OWR/2012/57. UnsolvedMath record UM-30002244 (`OWR-12180-001`), dataset ulamai/UnsolvedMath
v1.8.0.

`λ` is the infimum of the Rayleigh quotient `∫ σ |∇u|² / ∫ u²` over nonzero smooth functions with
compact support in `Ω`; they are dense in `H¹₀(Ω)` and the quotient is continuous there for bounded
`σ`, so this is the source's minimum over `H¹₀(Ω)`. The problem is stated in the form in which
Casado-Díaz resolved it: the `α`-phase `A ⊆ Ω` (his `ω`) ranges over the measurable sets with `|A| ≤
κ`, `0 < κ < |Ω|`, while the source fixes the measure `|B| = m` of the `β`-phase `B = Ω \ A`. `Ω`
ranges over bounded domains (connected open sets) as in the source, `d ≥ 1`.
-/

open MeasureTheory
open scoped ContDiff

/-- The first Dirichlet eigenvalue of `-div(σ ∇u)` on the open set `Ω`, as the infimum of the
Rayleigh quotient `∫ σ |∇u|² / ∫ u²` over nonzero smooth functions with compact support in `Ω`
(they are dense in `H¹₀(Ω)` and the quotient is continuous there for bounded `σ`). -/
noncomputable def firstEigenvalue {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (σ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  sInf ((fun u : EuclideanSpace ℝ (Fin d) → ℝ =>
      (∫ x, σ x * ‖fderiv ℝ u x‖ ^ 2) / ∫ x, u x ^ 2) ''
    {u | ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ω ∧ u ≠ 0})

open Classical in
/-- The two-phase conductivity `σ = α χ_A + β (1 - χ_A)`: `α` on `A`, `β` elsewhere (only its
values on `Ω` matter). -/
noncomputable def twoPhase {d : ℕ} (α β : ℝ) (A : Set (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => if x ∈ A then α else β

/-- The two-phase eigenvalue problem in the form Casado-Díaz resolved: for every bounded domain
(connected open set) `Ω ⊆ ℝ^d` (`d ≥ 1`), every `0 < κ < |Ω|` and every `0 < α < β`, the first
Dirichlet eigenvalue of `-div((α χ_A + β (1 - χ_A)) ∇u)` attains its minimum over the measurable
`A ⊆ Ω` with `|A| ≤ κ` (Casado-Díaz's `ω`). -/
def twoPhaseOptimalDesignExists : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ Ω : Set (EuclideanSpace ℝ (Fin d)),
    IsOpen Ω → IsConnected Ω → Bornology.IsBounded Ω →
    ∀ κ α β : ℝ, 0 < κ → κ < (volume Ω).toReal → 0 < α → α < β →
      ∃ A ⊆ Ω, MeasurableSet A ∧ (volume A).toReal ≤ κ ∧
        ∀ A' ⊆ Ω, MeasurableSet A' → (volume A').toReal ≤ κ →
          firstEigenvalue Ω (twoPhase α β A) ≤ firstEigenvalue Ω (twoPhase α β A')

/--
Resolved false: Casado-Díaz proved that for a smooth, simply connected bounded domain `Ω ⊆ ℝ^N` with
connected boundary the problem has a solution if and only if `Ω` is a ball, so a smooth non-ball
such domain, for instance an open ellipse in `ℝ²`, has no optimal `A` for any `0 < κ < |Ω|` and `0 <
α < β`. Source: A. Laurain (with C. Conca and R. Mahadevan), in Mini-Workshop: Geometries, Shapes
and Topologies in PDE-based Applications, Oberwolfach Reports 9 (2012), no. 57, pp. 3407-3408, DOI
10.4171/OWR/2012/57; resolution: J. Casado-Díaz, A characterization result for the existence of a
two-phase material minimizing the first eigenvalue, Ann. Inst. H. Poincaré C Anal. Non Linéaire 34
(2017), no. 5, 1215-1226, DOI 10.1016/j.anihpc.2016.09.006, abstract: for 0 < α < β, 0 < κ < |Ω| and
Ω ⊂ ℝ^N smooth, simply connected and with connected boundary, minimizing the first eigenvalue of u ∈
H¹₀(Ω) ↦ -div((αχ_ω + β(1 - χ_ω))∇u) over measurable ω with |ω| ≤ κ has a solution if and only if Ω
is a ball; an earlier paper of the author shows that the problem has no solution in general,
https://www.sciencedirect.com/science/article/pii/S0294144916300695.
-/
public theorem_wanted twoPhaseOptimalDesignExists_refuted : ¬ twoPhaseOptimalDesignExists

end MathlibExt.Analysis.TwoPhaseEigenvalueOptimalDesignOWR12180Problem001Wanted
