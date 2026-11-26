/-
Copyright (c) 2025 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.HomCochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Hom cochains of quasi-isomorphic projective chain complexes

In an abelian category, a quasi-isomorphism between natural-index chain complexes whose terms
are projective is a homotopy equivalence with the same forward map. Contravariant Hom cochains
into any coefficient object therefore send it to a quasi-isomorphism.

The resulting cohomology isomorphisms are natural in the coefficient object, and their forward
maps are the cohomology maps induced by precomposition with the given chain map.
-/

@[expose] public section

open CategoryTheory

universe v u

noncomputable section

namespace HomologicalComplex

/-- Hom cochains preserve quasi-isomorphisms between termwise projective chains.

Let `f : K ⟶ L` be a quasi-isomorphism of natural-index chain complexes in an abelian
category, with every term of both complexes projective. For any coefficient `G`, its
contravariant Hom cochain map is a quasi-isomorphism. -/
theorem homCochainComplexFunctor_map_quasiIso_of_projective
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    [QuasiIso f] (G : C) :
    QuasiIso ((homCochainComplexFunctor C G).map f.op) := by
  have hf : HomologicalComplex.homotopyEquivalences C (ComplexShape.down ℕ) f :=
    (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  obtain ⟨e, he⟩ := hf
  let eG := HomologicalComplex.HomotopyEquiv.mapHomCochainComplex e G
  have h_eq : eG.hom = (homCochainComplexFunctor C G).map f.op := by
    change (homCochainComplexFunctor C G).map e.hom.op =
      (homCochainComplexFunctor C G).map f.op
    rw [he]
  exact h_eq ▸ (inferInstance : QuasiIso eG.hom)

/-- Homotopy equivalence from a projective-chain quasi-isomorphism.

For a quasi-isomorphism `f : K ⟶ L` between termwise projective natural-index chain complexes,
construct a homotopy equivalence `K ≃ L` whose forward map is `f`. -/
noncomputable def homotopyEquivOfQuasiIsoOfProjective
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    [QuasiIso f] : HomotopyEquiv K L :=
  Classical.choose ((ChainComplex.quasiIso_iff_of_projective f).mp inferInstance)

/-- Constructed projective-chain homotopy equivalence retains the given map.

The forward map of `homotopyEquivOfQuasiIsoOfProjective f` equals the quasi-isomorphism `f`. -/
@[simp] theorem homotopyEquivOfQuasiIsoOfProjective_hom
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    [QuasiIso f] :
    (homotopyEquivOfQuasiIsoOfProjective f).hom = f :=
  Classical.choose_spec ((ChainComplex.quasiIso_iff_of_projective f).mp inferInstance)

/-- Projective-chain quasi-isomorphism gives natural Hom cohomology isomorphisms.

For a termwise projective-chain quasi-isomorphism `f : K ⟶ L`, the degree-`n` coefficient
functors `H^n Hom(L,-)` and `H^n Hom(K,-)` are naturally isomorphic. -/
noncomputable def homCochainComplexHomologyNatIsoOfProjectiveQuasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    [QuasiIso f] (n : ℕ) :
    homCochainComplexHomologyFunctor C L n ≅
      homCochainComplexHomologyFunctor C K n :=
  HomotopyEquiv.homCochainComplexHomologyNatIso
    (homotopyEquivOfQuasiIsoOfProjective f) n

/-- Forward projective-chain Hom cohomology comparison is precomposition by f.

At coefficient `G`, the forward natural isomorphism component is the degree-`n` cohomology map
of `(homCochainComplexFunctor C G).map f.op`. -/
@[simp] theorem homCochainComplexHomologyNatIsoOfProjectiveQuasiIso_hom_app
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    [QuasiIso f] (n : ℕ) (G : C) :
    (homCochainComplexHomologyNatIsoOfProjectiveQuasiIso (f := f) (n := n)).hom.app G =
      homologyMap ((homCochainComplexFunctor C G).map f.op) n := by
  change homologyMap ((homCochainComplexFunctor C G).map
      (homotopyEquivOfQuasiIsoOfProjective f).hom.op) n = _
  rw [homotopyEquivOfQuasiIsoOfProjective_hom]

end HomologicalComplex
