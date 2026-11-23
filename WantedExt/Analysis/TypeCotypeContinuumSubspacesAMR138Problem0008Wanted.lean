/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Continuum many non-isomorphic subspaces away from type and cotype 2 (Dodos-Lopez-Abad Problem 8)

P. Dodos and J. Lopez-Abad, Banach spaces and Ramsey theory: some open problems, Problem 8: let `X`
be a separable Banach space which fails to have type `2 - ε` (or fails to have cotype `2 + ε`) for
some `ε > 0`. Is it true that `X` contains continuum many pairwise non-isomorphic subspaces?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.SetTheory.Cardinal.Continuum

@[expose] public section

namespace MathlibExt.Analysis.TypeCotypeContinuumSubspacesAMR138Problem0008Wanted

/-!
Source: P. Dodos and J. Lopez-Abad, Banach spaces and Ramsey theory: some open problems, RACSAM 104
(2010), arXiv:1006.2668, Problem 8. UnsolvedMath record UM-00800745 (`AMR-138-0008`), dataset
ulamai/UnsolvedMath v1.8.0.

Banach spaces are real. Type and cotype are Rademacher type and cotype with the average `2⁻ⁿ ∑_ε ‖∑ᵢ
εᵢ xᵢ‖` over sign vectors (by Kahane's inequality any `L^r` average gives the same notion). The
record lost the `ε`s; the source reads 'fails to have type `2 - ε` (or fails to have co-type `2 +
ε`) for some `ε > 0`'. Restricting to `ε < 1` loses nothing: every space has type `p` for `p ≤ 1`,
and failing cotype `2 + ε` implies failing cotype `2 + ε'` for every `ε' < ε`; for `ε ≥ 2` the
formula `(∑ ‖xᵢ‖ᵖ)^{1/p}` with `p ≤ 0` is not the norm of `ℓ_p`, so the restriction also keeps
degenerate exponents out. Subspaces are closed linear subspaces, isomorphic means linearly
homeomorphic, and continuum many means a family indexed by a type of cardinality `𝔠`. WantedExt's
`RademacherEnfloTypeWanted.RademacherEnfloType.IsRademacherType` is the `L^p`-moment form of type
with an explicit constant, equivalent by Kahane's inequality; cotype has no existing definition, so
both are stated here in the same `L¹` form.
-/

/-- The Rademacher average `2⁻ⁿ ∑_ε ‖∑ᵢ εᵢ xᵢ‖` over all sign vectors `ε ∈ {-1, 1}ⁿ`. -/
noncomputable def rademacherAverage {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    (x : Fin n → X) : ℝ :=
  (∑ ε : Fin n → Bool, ‖∑ i, (if ε i then (1 : ℝ) else -1) • x i‖) / 2 ^ n

/-- `X` has (Rademacher) type `p`: `2⁻ⁿ ∑_ε ‖∑ᵢ εᵢ xᵢ‖ ≤ C (∑ᵢ ‖xᵢ‖ᵖ)^{1/p}` for all finite
families `(xᵢ)`. -/
def HasType (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (p : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → X), rademacherAverage x ≤ C * (∑ i, ‖x i‖ ^ p) ^ (1 / p)

/-- `X` has (Rademacher) cotype `q`: `(∑ᵢ ‖xᵢ‖^q)^{1/q} ≤ C 2⁻ⁿ ∑_ε ‖∑ᵢ εᵢ xᵢ‖` for all finite
families `(xᵢ)`. -/
def HasCotype (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (q : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → X), (∑ i, ‖x i‖ ^ q) ^ (1 / q) ≤ C * rademacherAverage x

/-- Dodos–Lopez-Abad, Problem 8: every separable real Banach space that fails type `2 - ε` or fails
cotype `2 + ε` for some `ε > 0` contains continuum many pairwise non-isomorphic closed subspaces.
(`ε < 1` loses nothing: every space has type `p` for `p ≤ 1`, and failing cotype `2 + ε` implies
failing cotype `2 + ε'` for every `ε' < ε`.) -/
def continuumManyNonIsomorphicSubspaces : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X],
    (∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (¬ HasType X (2 - ε) ∨ ¬ HasCotype X (2 + ε))) →
      ∃ (ι : Type) (Y : ι → Submodule ℝ X), Cardinal.mk ι = Cardinal.continuum ∧
        (∀ i, IsClosed (Y i : Set X)) ∧ ∀ i j, i ≠ j → IsEmpty (Y i ≃L[ℝ] Y j)

/--
Resolved true: Cuellar Carrera's Theorem 16 says that every separable Banach space that is not near
Hilbert satisfies the Cantorized-Enflo criterion, and his Remark 7 that a space satisfying that
criterion has a continuum of pairwise non-isomorphic subspaces. Near Hilbert means `p(X) = q(X) =
2`, and since type `p` implies type `r` for `r < p` and cotype `q` implies cotype `s` for `s > q`,
failing type `2 - ε` or cotype `2 + ε` for some `ε > 0` is exactly not being near Hilbert. Source:
P. Dodos and J. Lopez-Abad, Banach spaces and Ramsey theory: some open problems, RACSAM 104 (2010),
arXiv:1006.2668, Problem 8; resolution: W. Cuellar Carrera, Non-ergodic Banach spaces are near
Hilbert, Trans. Amer. Math. Soc. 370 (2018), 8691-8707, doi:10.1090/tran/7319, arXiv:1611.05500,
Theorem 16: 'Every separable Banach space non near Hilbert satisfies the Cantorized-Enflo criterion
and therefore is ergodic'; Remark 7 (with proof): 'A Banach space satisfying the Cantorized-Enflo
criterion has a continuum of non isomorphic subspaces'; Section 1: near Hilbert means p(X) = q(X) =
2, where p(X) = sup{p : X has type p} and q(X) = inf{q : X has cotype q},
https://arxiv.org/abs/1611.05500.
-/
public theorem_wanted continuumManyNonIsomorphicSubspaces_holds :
    continuumManyNonIsomorphicSubspaces

end MathlibExt.Analysis.TypeCotypeContinuumSubspacesAMR138Problem0008Wanted
