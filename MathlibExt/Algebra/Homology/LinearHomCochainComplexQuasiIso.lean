/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.HomCochainComplexQuasiIso
public import MathlibExt.Algebra.Homology.LinearHomCochainHomotopyEquiv

/-!
# Linear Hom preserves quasi-isomorphisms between projective chain complexes

Let R be a ring and C an abelian R-linear category, with independent scalar, object and morphism
universes. Let f:K→L be a quasi-isomorphism of nonnegative chain complexes whose terms K_n,L_n
are projective for every n. Such an f is a homotopy equivalence.

For any G∈C, precomposition gives a quasi-isomorphism Hom_C(L,G)→Hom_C(K,G) of nonnegative
R-linear cochain complexes. Their degree-n terms are the Hom modules from L_n or K_n to G in the
morphism universe. The conclusion follows from the induced Hom cochain homotopy equivalence and
requires no injectivity of G.
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

noncomputable section

namespace HomologicalComplex

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. Let f:K→L be a quasi-isomorphism of chain complexes of shape
down ℕ, and assume K_n and L_n are projective objects for every n. For any G∈C, the induced
precomposition map Hom_C(L,G)→Hom_C(K,G) is a quasi-isomorphism of cochain complexes of shape up
ℕ in R-modules with carriers in v. The projective-complex homotopy equivalence of f supplies the
result. -/
theorem linearHomCochainComplexFunctor_map_quasiIso_of_projective
    (R : Type w) [Ring R]
    {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    [QuasiIso f] (G : C) :
    QuasiIso ((HomologicalComplex.linearHomCochainComplexFunctor R C G).map f.op) := by
  have hf : HomologicalComplex.homotopyEquivalences C (ComplexShape.down ℕ) f :=
    (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  obtain ⟨e, he⟩ := hf
  let eG := HomologicalComplex.HomotopyEquiv.mapLinearHomCochainComplex R e G
  have h_eq : eG.hom = (HomologicalComplex.linearHomCochainComplexFunctor R C G).map f.op := by
    change (HomologicalComplex.linearHomCochainComplexFunctor R C G).map e.hom.op =
      (HomologicalComplex.linearHomCochainComplexFunctor R C G).map f.op
    rw [he]
  exact h_eq ▸ (inferInstance : QuasiIso eG.hom)

end HomologicalComplex
