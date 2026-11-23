/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedBetti

/-!
# Invariance of multigraded Betti numbers across graded free resolutions

This file proves that, given two multigraded free resolutions of the same
target with certified base-change data each, a multidegreewise
chain-homotopy equivalence between their component complexes forces their
`multigradedBettiNumber` values to agree at every multidegree and
homological index.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 866--874. Those lines define `β^R_(i,α)(M)` as the vector-space
dimension of the `i`th homology of the degree-`α` component of `K ⊗ F` for a
graded free resolution `F` of `M`, writing the Betti number without naming a
resolution. Edge 4 removed only the component-presentation choice inside one
fixed resolution; this edge removes the resolution choice once an explicit
degree-preserving comparison is supplied.

The comparison hypothesis is the whole point and is stated conspicuously:
nothing here proves existence of a degree-preserving comparison for every
pair of resolutions, its uniqueness, minimality of either resolution, finite
support, Poincaré polynomiality or rationality, or Hilbert syzygy. Mathlib's
ungraded projective-resolution comparison is not shown to preserve the
multigrading, so unconditional independence would hide an unproved grading
obligation; the `MultigradedResolutionComparison` interface isolates exactly
that obligation.

Main definitions and results:

* `MetaMathlibExt.MultigradedResolutionComparison`: for every multidegree
  `α`, a chain-homotopy equivalence between the two certified degree-`α`
  component complexes.
* `MetaMathlibExt.multigradedBettiNumber_eq_of_resolutionComparison`: such a
  comparison implies equal `multigradedBettiNumber` values for every `α`
  and `i`.
-/

@[expose] public section

namespace MetaMathlibExt

universe u

open HomologicalComplex

/-- **Multigraded resolution comparison.** Let $K$ be a field, let $R = K[x_1, \dots, x_n]$,
and let $M$ be a $\mathbb{Z}^n$-graded $R$-module with two multigraded free resolutions,
each equipped with multigraded base change data, whose degree-$\alpha$ component complexes
are $C^\alpha$ and $D^\alpha$ for $\alpha \in \mathbb{Z}^n$. A comparison between the two
base change data is a choice, for every $\alpha \in \mathbb{Z}^n$, of a chain-homotopy
equivalence between $C^\alpha$ and $D^\alpha$.

A homotopy equivalence, rather than a bare quasi-isomorphism, is the comparison-theorem
input: it induces an isomorphism on homology. Existence and uniqueness of such a
comparison are not claimed here. -/
public structure MultigradedResolutionComparison
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution₁ resolution₂ :
      CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι₁ ι₂ : ℕ → Type u}
    {res₁ : MultigradedFreeResolution K n M targetGraded resolution₁ ι₁}
    {res₂ : MultigradedFreeResolution K n M targetGraded resolution₂ ι₂}
    (data₁ : MultigradedBaseChange targetGraded resolution₁ ι₁ res₁)
    (data₂ : MultigradedBaseChange targetGraded resolution₂ ι₂ res₂) where
  /-- Chain-homotopy equivalence between the degree-`α` component complexes. -/
  componentHomotopyEquiv : ∀ α, HomotopyEquiv (data₁.comp α) (data₂.comp α)

/-- **Betti numbers agree across comparable resolutions.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, and let $M$ be a $\mathbb{Z}^n$-graded $R$-module with two
multigraded free resolutions, each equipped with multigraded base change data, whose
degree-$\alpha$ component complexes are $C^\alpha$ and $D^\alpha$ for $\alpha \in \mathbb{Z}^n$.
If the two are related by a multigraded resolution comparison, that is, for every $\alpha$
a chain-homotopy equivalence between $C^\alpha$ and $D^\alpha$, then the multigraded Betti
numbers defined by the two base change data agree in every multidegree
$\alpha \in \mathbb{Z}^n$ and every homological index $i \in \mathbb{N}$.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 866--874. This is conditional only: it assumes the comparison
and claims no existence, uniqueness, minimality, finite support, Poincaré
polynomiality or rationality, or Hilbert syzygy. -/
public theorem multigradedBettiNumber_eq_of_resolutionComparison
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution₁ resolution₂ :
      CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι₁ ι₂ : ℕ → Type u}
    {res₁ : MultigradedFreeResolution K n M targetGraded resolution₁ ι₁}
    {res₂ : MultigradedFreeResolution K n M targetGraded resolution₂ ι₂}
    {data₁ : MultigradedBaseChange targetGraded resolution₁ ι₁ res₁}
    {data₂ : MultigradedBaseChange targetGraded resolution₂ ι₂ res₂}
    (comparison : MultigradedResolutionComparison data₁ data₂)
    (α : Fin n →₀ Int) (i : ℕ) :
    multigradedBettiNumber data₁ α i = multigradedBettiNumber data₂ α i := by
  -- Install the `HasHomology` instances so that
  -- `HomotopyEquiv.quasiIsoAt_hom` supplies the `IsIso` used below.
  let _ := data₁.hasHom α i
  let _ := data₂.hasHom α i
  let e := comparison.componentHomotopyEquiv α
  have homIso :
      HomologicalComplex.homology (data₁.comp α) i ≅
        HomologicalComplex.homology (data₂.comp α) i := by
    exact CategoryTheory.asIso (HomologicalComplex.homologyMap e.hom i)
  have linEquiv :
      ↥(HomologicalComplex.homology (data₁.comp α) i) ≃ₗ[K]
        ↥(HomologicalComplex.homology (data₂.comp α) i) :=
    CategoryTheory.Iso.toLinearEquiv homIso
  have hFin := LinearEquiv.finrank_eq linEquiv
  unfold multigradedBettiNumber
  exact hFin

end MetaMathlibExt
