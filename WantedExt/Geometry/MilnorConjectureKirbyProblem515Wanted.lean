/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Milnor's conjecture fails in every dimension at least six (Kirby Problem 5.15)

K3, a new problem list in low-dimensional topology, Problem 5.15: if a manifold `M` carries a
complete Riemannian metric of nonnegative Ricci curvature, is its fundamental group finitely
generated? The list records counterexamples in every dimension starting with six (Bruè, Naber and
Semola) and asks about the remaining dimensions four and five.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import MathlibExt.Geometry.Manifold.Riemannian.Curvature

@[expose] public section

namespace MathlibExt.Geometry.MilnorConjectureKirbyProblem515Wanted

/-!
Source: R. I. Baykur, R. C. Kirby and D. Ruberman (eds.), K3: A New Problem List in
Low-Dimensional Topology, Mathematical Surveys and Monographs 295, Amer. Math. Soc. (2026),
Section 5.3, Problem 5.15 and its Remark (1). UnsolvedMath record UM-00003022 (`KP-5.15`), dataset
ulamai/UnsolvedMath v1.8.0.

A manifold with a complete Riemannian metric is modeled as in `MathlibExt`'s Riemannian layer: a
connected smooth (`C^∞`) manifold `M` without boundary, modeled on `𝓡 n`, with a `C^∞` Riemannian
metric, whose extended distance is the Riemannian distance (`IsRiemannianManifold`), complete for
that distance. Nonnegative Ricci curvature is `RicciGE (𝓡 n) M 0`, the fundamental group is
Mathlib's `FundamentalGroup M x` and finite generation is `Group.FG`. Connectedness makes "the
fundamental group of `M`" independent of the base point; the fundamental group at a base point only
sees its component, so this is no restriction.

Reading choices: the problem is a yes/no question over all dimensions. The list's own remarks
answer it negatively in every dimension `n ≥ 6` (dimension at least 7 by Bruè–Naber–Semola, Ann. of
Math. 2025, and dimension 6 by Bruè–Naber–Semola, J. Eur. Math. Soc. 2025) and keep dimensions 4
and 5 open; the target is that resolved part, stated as the failure of finite generation in each
dimension `n ≥ 6`, which implies the negative answer to the question as posed. Dimensions 4 and 5
are open as far as refereed results go: an unrefereed preprint, N. Wu and Z. Yan, Prüfer 2-group and
Milnor's conjecture on fundamental groups, arXiv:2608.15505 (2026), claims complete examples with
`Ric > 0` and fundamental group the Prüfer 2-group in dimension 4 and any subgroup of `ℚ/ℤ` in
dimension 5. Those dimensions and the questions of Remark (2) about spaces of positive Ricci
curvature metrics on `S² × S²` and `S² × S³` are not formalized here.
-/

open Bundle Manifold
open scoped Manifold ContDiff

/-- Milnor's finite-generation property in dimension `n`: every connected smooth `n`-manifold `M`
without boundary that carries a `C^∞` Riemannian metric which is complete (for the Riemannian
distance) and has nonnegative Ricci curvature has finitely generated fundamental group
`π₁(M, x)`, for every base point `x`. -/
def milnorFiniteGeneration (n : ℕ) : Prop :=
  ∀ (M : Type) [EMetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]
    [IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    [IsRiemannianManifold (𝓡 n) M] [CompleteSpace M] [ConnectedSpace M],
    RicciGE (𝓡 n) M 0 → ∀ x : M, Group.FG (FundamentalGroup M x)

/-- Milnor's finite-generation property (`milnorFiniteGeneration`) holds in some dimension
`n ≥ 6`. Its negation says that in every dimension `n ≥ 6` some connected complete Riemannian
`n`-manifold with nonnegative Ricci curvature has infinitely generated fundamental group. -/
def milnorFiniteGenerationInSomeDimensionAtLeastSix : Prop :=
  ∃ n : ℕ, 6 ≤ n ∧ milnorFiniteGeneration n

/--
Resolved false: in every dimension `n ≥ 6` there is a connected smooth `n`-manifold with a
complete Riemannian metric of nonnegative Ricci curvature whose fundamental group is not finitely
generated, so Milnor's conjecture, the positive answer to Kirby Problem 5.15, fails. Source: R. I.
Baykur, R. C. Kirby and D. Ruberman (eds.), K3: A New Problem List in Low-Dimensional Topology,
Amer. Math. Soc. (2026), Problem 5.15; resolution: the list's Section 5.3 introduction ("there are
counterexamples in every dimension starting with 6") and Remark (1) to Problem 5.15
("Bruè-Naber-Semola construct counterexamples in dimensions at least 7 [BNS25], and 6 [BNS23]"),
citing E. Bruè, A. Naber and D. Semola, Fundamental groups and the Milnor conjecture, Ann. of Math.
(2) 201 (2025), 225-289, doi:10.4007/annals.2025.201.1.4 (a complete `M⁷` with `Ric ≥ 0` and
`π₁(M) = ℚ/ℤ`, infinitely generated), and E. Bruè, A. Naber and D. Semola, Six-dimensional
counterexample to the Milnor conjecture, J. Eur. Math. Soc. (2025), doi:10.4171/jems/1737 (a
smooth complete `M⁶` with `Ric ≥ 0` and `π₁(M⁶) = ℚ/ℤ`),
https://math.berkeley.edu/sites/default/files/surv-295-ruberman-watermarked-author-pdf.pdf.
-/
public theorem_wanted milnorFiniteGenerationInSomeDimensionAtLeastSix_refuted :
    ¬ milnorFiniteGenerationInSomeDimensionAtLeastSix

end MathlibExt.Geometry.MilnorConjectureKirbyProblem515Wanted
