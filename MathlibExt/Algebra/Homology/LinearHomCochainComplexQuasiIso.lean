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
# Linear Hom cochain quasi-isomorphism for projective complexes
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

noncomputable section

namespace HomologicalComplex

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
