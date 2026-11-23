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
Modification notice: the definition and docstring of `projToSpec` are copied from
`WantedExt/AlgebraicGeometry/TopologicalReconstructionWanted.lean`, where the same morphism
is defined, so that `MathlibExt` has a completed copy; projective space over a field and
projectivity are new.
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
spectrum of a graded `R`-algebra. Projective space `ℙⁿ_k` is the projective
spectrum of the polynomial ring in `n + 1` variables over `k`, graded by total
degree, and a scheme over `k` is projective if it has a closed immersion over
`k` into some `ℙⁿ_k`.
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

/-- Projective space `ℙⁿ_k` over a field `k`: the projective spectrum of the polynomial
ring in `n + 1` variables over `k`, graded by total degree, over `Spec k`. -/
def projectiveSpace (k : Type u) [Field k] (n : ℕ) : Over (Spec (.of k)) :=
  letI := @MvPolynomial.gradedAlgebra
  Over.mk (projToSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

/-- A scheme over a field `k` is projective if it has a closed immersion over `k` into
some projective space `ℙⁿ_k`. -/
def IsProjective {k : Type u} [Field k] (X : Over (Spec (.of k))) : Prop :=
  ∃ n : ℕ, ∃ i : X ⟶ projectiveSpace k n, IsClosedImmersion i.left

end MathlibExt.AlgebraicGeometry.ProjectiveSpace
