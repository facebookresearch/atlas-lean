/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/AlgebraicGeometry/TopologicalReconstruction.lean` (leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, problem `kollar_lieblich_olsson_sawin`, submitter
Junyan Xu): Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). lean-eval ships no `NOTICE` file.
Modification notice: the definitions and docstrings of `projToSpec` and `IsProjectiveHom` are
moved here from `WantedExt/AlgebraicGeometry/TopologicalReconstructionWanted.lean`, whose
declarations of the same names now delegate to these; projective space over a field and the
`Over`-facing projectivity predicate are new.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public noncomputable section

/-!
# Projective space over a field

`projToSpec 𝒜` is the structure morphism `Proj 𝒜 ⟶ Spec R` of the projective
spectrum of a graded `R`-algebra, and `IsProjectiveHom f` says that a morphism
`f : X ⟶ Spec R` factors as a closed immersion into the projective spectrum of
a polynomial ring followed by its structure morphism. Projective space `ℙⁿ_k`
is the projective spectrum of the polynomial ring in `n + 1` variables over
`k`, graded by total degree, as a scheme over `k`, and a scheme over `k` is
projective if its structure morphism is projective.
-/

namespace MathlibExt.AlgebraicGeometry.ProjectiveSpace

open CategoryTheory _root_.AlgebraicGeometry

universe u

/-- **Structure morphism of a projective spectrum.** Let $R$ be a commutative ring and $A$ a
commutative $R$-algebra graded by $R$-submodules $\mathcal{A}_0, \mathcal{A}_1, \dots$. The
structure morphism $\operatorname{Proj} \mathcal{A} \to \operatorname{Spec} R$ is the canonical
morphism $\operatorname{Proj} \mathcal{A} \to \operatorname{Spec} \mathcal{A}_0$ followed by the
morphism $\operatorname{Spec} \mathcal{A}_0 \to \operatorname{Spec} R$ induced by the algebra map
$R \to \mathcal{A}_0$.

For a polynomial ring over $R$ graded by total degree, this is the structure morphism of
projective space over $R$. -/
def projToSpec {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ..))

/-- **Projective morphism to an affine scheme.** Let $R$ be a commutative ring and $X$ a scheme.
A morphism $f : X \to \operatorname{Spec} R$ is projective if there are $n \in \mathbb{N}$ and a
closed immersion $i$ of $X$ into $\operatorname{Proj} R[x_1, \dots, x_n]$, the polynomial ring
graded by total degree, such that $f$ is $i$ followed by the structure morphism
$\operatorname{Proj} R[x_1, \dots, x_n] \to \operatorname{Spec} R$. -/
def IsProjectiveHom {X : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) : Prop :=
  let := @MvPolynomial.gradedAlgebra
  ∃ (n : ℕ) (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin n) R)),
    IsClosedImmersion i ∧ f = i ≫ projToSpec _

/-- Projective space `ℙⁿ_k` over a field `k`: the projective spectrum of the polynomial
ring in `n + 1` variables over `k`, graded by total degree, over `Spec k`. -/
def projectiveSpace (k : Type u) [Field k] (n : ℕ) : Over (Spec (.of k)) :=
  letI := @MvPolynomial.gradedAlgebra
  Over.mk (projToSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

/-- A scheme over a field `k` is projective if its structure morphism is projective:
it has a closed immersion over `k` into some projective space. -/
def IsProjective {k : Type u} [Field k] (X : Over (Spec (.of k))) : Prop :=
  IsProjectiveHom X.hom

end MathlibExt.AlgebraicGeometry.ProjectiveSpace
