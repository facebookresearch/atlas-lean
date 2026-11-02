/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedBettiResolutionInvariance

/-!
# Multigraded Poincaré-series coefficient family

This file records the multigraded Poincaré series of Braun--Davis
extensionally, as the raw coefficient function on homological degree and
multidegree. At `(i, α)`, the value is exactly the edge-3
`multigradedBettiNumber` for the supplied certified base-change data.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 870--874. Those lines define the Poincaré series
`P_R^M(z; t)` as the ordinary generating function for the Betti numbers,
`∑_α ∑_i β_{i,α} z^i t^α`. This edge formalizes only the coefficient
family `(i, α) ↦ β_{i,α}`.

Strict source boundary: the coefficients form a plain function
`ℕ × (Fin n →₀ Int) → ℕ`. This file uses no `Finsupp`,
`AddMonoidAlgebra`, power series, or Hahn series, and asserts no finite
support, convergence, polynomiality, rationality, or existence of
comparison data. Finite support and any polynomial realization belong to
later Hilbert-syzygy edges. Coherence across two resolutions is proved
only under an explicit edge-5 `MultigradedResolutionComparison`.

Main definitions and results:

* `MetaMathlibExt.multigradedPoincareCoefficients`: the raw coefficient
  function `(i, α) ↦ multigradedBettiNumber data α i`.
* `MetaMathlibExt.multigradedPoincareCoefficients_apply`: the application
  equation pinning each value to the corresponding Betti number.
* `MetaMathlibExt.multigradedPoincareCoefficients_eq_of_resolutionComparison`:
  two coefficient functions agree whenever edge 5 supplies a resolution
  comparison.
-/

@[expose] public section

namespace MetaMathlibExt

universe u

/-- **Multigraded Poincaré coefficients.** Let $K$ be a field, let $R = K[x_1, \dots, x_n]$, let
$M$ be a multigraded $R$-module, and let $D$ be base-change data for a multigraded free
resolution of $M$. The multigraded Poincaré coefficient family of $D$ is the function
$\mathbb{N} \times \mathbb{Z}^n \to \mathbb{N}$ sending $(i, \alpha)$ to the multigraded Betti
number $\beta_{i,\alpha}(D)$ of $D$ in homological degree $i$ and multidegree $\alpha$.

A plain function records every coefficient without asserting finite
support, convergence, polynomiality, or rationality. -/
public noncomputable def multigradedPoincareCoefficients
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res) :
    ℕ × (Fin n →₀ Int) → ℕ :=
  fun p => multigradedBettiNumber data p.2 p.1

/-- **Multigraded Poincaré coefficients are Betti numbers.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, let $M$ be a multigraded $R$-module, and let $D$ be base-change data
for a multigraded free resolution of $M$. For every $i \in \mathbb{N}$ and
$\alpha \in \mathbb{Z}^n$, the multigraded Poincaré coefficient family of $D$ takes the value
$\beta_{i,\alpha}(D)$ at $(i, \alpha)$, where $\beta_{i,\alpha}(D)$ is the multigraded Betti
number of $D$ in homological degree $i$ and multidegree $\alpha$. -/
public theorem multigradedPoincareCoefficients_apply
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res)
    (i : ℕ) (α : Fin n →₀ Int) :
    multigradedPoincareCoefficients data (i, α) =
      multigradedBettiNumber data α i :=
  rfl

/-- **Resolution comparisons preserve multigraded Poincaré coefficients.** Let $K$ be a field,
let $R = K[x_1, \dots, x_n]$, let $M$ be a multigraded $R$-module, and let $D$ and $D'$ be
base-change data for two multigraded free resolutions of $M$. Given a multigraded resolution
comparison between $D$ and $D'$, that is, for every $\alpha \in \mathbb{Z}^n$ a chain-homotopy
equivalence between the degree-$\alpha$ component complexes of $D$ and $D'$, the multigraded
Poincaré coefficient families of $D$ and $D'$ are equal.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 870--874. This is conditional only: it assumes the
comparison and claims no existence, unconditional independence, finite
support, polynomiality, rationality, or convergence. -/
public theorem multigradedPoincareCoefficients_eq_of_resolutionComparison
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution₁ resolution₂ : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι₁ ι₂ : ℕ → Type u}
    {res₁ : MultigradedFreeResolution K n M targetGraded resolution₁ ι₁}
    {res₂ : MultigradedFreeResolution K n M targetGraded resolution₂ ι₂}
    {data₁ : MultigradedBaseChange targetGraded resolution₁ ι₁ res₁}
    {data₂ : MultigradedBaseChange targetGraded resolution₂ ι₂ res₂}
    (comparison : MultigradedResolutionComparison data₁ data₂) :
    multigradedPoincareCoefficients data₁ =
      multigradedPoincareCoefficients data₂ := by
  funext p
  cases p with
  | mk i α =>
    unfold multigradedPoincareCoefficients
    exact multigradedBettiNumber_eq_of_resolutionComparison comparison α i

end MetaMathlibExt
