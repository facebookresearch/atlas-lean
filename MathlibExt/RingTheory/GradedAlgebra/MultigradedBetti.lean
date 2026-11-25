/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedFreeResolution
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Multigraded Betti numbers after residue-field base change

This file encodes multigraded Betti numbers via base change of an edge-2
graded free resolution along the canonical augmentation.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 868–873. Those lines say that, for a graded free resolution `F`
of `M`, `β^R_(i,α)(M)` is the vector-space dimension of the `i`th homology
of the degree-`α` component of `K ⊗_R F`.

Deliberately deferred (not claimed here): Poincaré series, finite support
across degrees, eventual vanishing, and polynomiality. This file only
provides the augmentation, the actual base-changed complex, the degree
pieces with their certified decomposition and component complexes, and the
Betti number as the resulting `Module.finrank`.

Main definitions:

* `MetaMathlibExt.zeroEval`: the canonical augmentation
  `MvPolynomial (Fin n) K →+* K` evaluating every variable at zero.
* `MetaMathlibExt.baseChangedComplex`: the actual base-changed chain complex
  obtained from the edge-2 resolution by `ModuleCat.extendScalars`.
* `MetaMathlibExt.baseChangedDegreePiece`: degree pieces spanned by the
  actual base-changed homogeneous basis vectors.
* `MetaMathlibExt.MultigradedBaseChange`: certified direct-sum decomposition
  and restricted component complexes with injective inclusions, homology,
  and finite-dimensionality certificates.
* `MetaMathlibExt.multigradedBettiNumber`: the multigraded Betti number as
  the resulting `Module.finrank`.
-/

@[expose] public section

namespace MetaMathlibExt

universe u

/-- **Augmentation of the polynomial ring.** For a field $K$ and $n \in \mathbb{N}$, the
augmentation $K[x_1, \dots, x_n] \to K$ is the ring homomorphism sending each polynomial
$p$ to its value $p(0, \dots, 0)$: it is the identity on constants and sends every
variable to $0$. -/
public noncomputable def zeroEval {K : Type u} [Field K] {n : ℕ} :
    MvPolynomial (Fin n) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) (0 : Fin n → K)

/-- **Base change of a resolution to the residue field.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, and let $M$ be an $R$-module. Given a projective resolution
$P_\bullet \to M$ over $R$, its base change is the chain complex of $K$-vector spaces
$K \otimes_R P_\bullet$, indexed by $\mathbb{N}$ with differentials lowering the index,
obtained by extending scalars termwise along the augmentation $R \to K$ that sends every
variable to $0$: its $i$th term is $K \otimes_R P_i$ and its differentials are the maps
$\mathrm{id}_K \otimes d$ for the differentials $d$ of $P_\bullet$. -/
public noncomputable def baseChangedComplex {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)) :
    HomologicalComplex (ModuleCat.{u, u} K) (ComplexShape.down ℕ) :=
  letI : Algebra (MvPolynomial (Fin n) K) K := zeroEval.toAlgebra
  (CategoryTheory.Functor.mapHomologicalComplex
    (ModuleCat.extendScalars zeroEval) (ComplexShape.down ℕ)).obj resolution.complex

/-- **Degree pieces of the base-changed resolution.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, and let $M$ be a $\mathbb{Z}^n$-graded $R$-module with a
multigraded free resolution $P_\bullet \to M$, in which each $P_i$ has an $R$-basis
$(e_j)_{j \in J_i}$ with $e_j$ homogeneous of degree $\deg e_j \in \mathbb{Z}^n$. For
$i \in \mathbb{N}$ and $\alpha \in \mathbb{Z}^n$, the degree-$\alpha$ piece of the $i$th
term $K \otimes_R P_i$ of the base-changed complex is the $K$-subspace spanned by the
vectors $1 \otimes e_j$ with $j \in J_i$ and $\deg e_j = \alpha$. -/
public noncomputable def baseChangedDegreePiece {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (i : ℕ) (α : Fin n →₀ Int) :
    Submodule K ↥((baseChangedComplex resolution).X i) :=
  letI : Module K ↥(resolution.complex.X i) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  letI : Algebra (MvPolynomial (Fin n) K) K := zeroEval.toAlgebra
  Submodule.span K
    { y | ∃ j : ι i, (res.termFree i).degree j = α ∧
      y = (res.termFree i).basis.baseChange K j }

/-- **Multigraded base change data.** Let $K$ be a field, let $R = K[x_1, \dots, x_n]$,
and let $M$ be a $\mathbb{Z}^n$-graded $R$-module with a multigraded free resolution
$P_\bullet \to M$. Write $K \otimes_R P_\bullet$ for its base change along the
augmentation $R \to K$ and $(K \otimes_R P_i)_\beta$ for the degree-$\beta$ piece of its
$i$th term. Multigraded base change data for $P_\bullet$ consist of: for each
$i \in \mathbb{N}$, a decomposition of $K \otimes_R P_i$ as the internal direct sum of the
pieces $(K \otimes_R P_i)_\beta$ over $\beta \in \mathbb{Z}^n$, such that for all $i$ and
$\beta$ the differential $K \otimes_R P_{i+1} \to K \otimes_R P_i$ maps
$(K \otimes_R P_{i+1})_\beta$ into $(K \otimes_R P_i)_\beta$; and, for each
$\alpha \in \mathbb{Z}^n$, an $\mathbb{N}$-indexed chain complex $C^\alpha$ of
$K$-vector spaces with a chain map $C^\alpha \to K \otimes_R P_\bullet$ whose $i$th
component is injective with image $(K \otimes_R P_i)_\alpha$ for every $i$, such that
every homology $H_i(C^\alpha)$ exists and is finite-dimensional over $K$. -/
public structure MultigradedBaseChange {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι) where
  /-- Direct-sum decomposition of each base-changed term over the degree pieces. -/
  decomposition : ∀ (i : ℕ), DirectSum.Decomposition
    (fun β => baseChangedDegreePiece targetGraded resolution ι res i β)
  /-- Successor differentials preserve each degree piece. -/
  diffPreserves : ∀ (i : ℕ) (β : Fin n →₀ Int)
    (x : ↥((baseChangedComplex resolution).X (i + 1))),
    x ∈ baseChangedDegreePiece targetGraded resolution ι res (i + 1) β →
      (ModuleCat.Hom.hom ((baseChangedComplex resolution).d (i + 1) i)) x ∈
        baseChangedDegreePiece targetGraded resolution ι res i β
  /-- Component complex for a fixed multidegree `α`. -/
  comp : (α : Fin n →₀ Int) →
    HomologicalComplex (ModuleCat.{u, u} K) (ComplexShape.down ℕ)
  /-- Inclusion of the `α` component complex into the base-changed complex. -/
  incl : ∀ (α : Fin n →₀ Int), HomologicalComplex.Hom (comp α)
    (baseChangedComplex resolution)
  /-- Each inclusion map is injective. -/
  incl_injective :
    ∀ (α : Fin n →₀ Int) (i : ℕ),
      Function.Injective ⇑(ModuleCat.Hom.hom ((incl α).f i))
  /-- The range of each inclusion is exactly the corresponding degree piece. -/
  range_eq : ∀ (α : Fin n →₀ Int) (i : ℕ),
    LinearMap.range (ModuleCat.Hom.hom ((incl α).f i)) =
      baseChangedDegreePiece targetGraded resolution ι res i α
  /-- Each component complex has homology at every index. -/
  hasHom : ∀ (α : Fin n →₀ Int) (i : ℕ),
    HomologicalComplex.HasHomology (comp α) i
  /-- Each component homology is finite-dimensional over `K`. -/
  finiteDim : ∀ (α : Fin n →₀ Int) (i : ℕ)
    [HomologicalComplex.HasHomology (comp α) i],
    Module.Finite K ↥(HomologicalComplex.homology (comp α) i)

/-- **Multigraded Betti number.** Let $K$ be a field, let $R = K[x_1, \dots, x_n]$, and
let $M$ be a $\mathbb{Z}^n$-graded $R$-module with a multigraded free resolution
$P_\bullet \to M$. Fix multigraded base change data for $P_\bullet$; for each
$\alpha \in \mathbb{Z}^n$ they supply a chain complex $C^\alpha$ of $K$-vector spaces
embedded in the base-changed complex $K \otimes_R P_\bullet$ with image its degree-$\alpha$
pieces. For $\alpha \in \mathbb{Z}^n$ and $i \in \mathbb{N}$, the multigraded Betti number
of $M$ in multidegree $\alpha$ and homological index $i$, with respect to these data, is
the dimension over $K$ of the homology $H_i(C^\alpha)$. -/
public noncomputable def multigradedBettiNumber {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res)
    (α : Fin n →₀ Int) (i : ℕ) : ℕ :=
  haveI := data.hasHom α i
  haveI := data.finiteDim α i
  Module.finrank K ↥(HomologicalComplex.homology (data.comp α) i)

end MetaMathlibExt
