/-
Copyright (c) 2025 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.HomCochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Hom cochain quasi-isomorphism for projective chain complexes

For a coefficient object `G` in an abelian category, the contravariant
functor `Hom(-, G)` from `ℕ`-indexed chain complexes to cochain complexes
sends quasi-isomorphisms between degreewise projective complexes to
quasi-isomorphisms. This follows from the identification of such
quasi-isomorphisms with homotopy equivalences and the preservation of
homotopy equivalences by `Hom(-, G)`.
-/

@[expose] public section

open CategoryTheory

universe v u

noncomputable section

namespace HomologicalComplex

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

/-- Homotopy equivalence underlying a quasi-iso of projective complexes. -/
noncomputable def homotopyEquivOfQuasiIsoOfProjective
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    [QuasiIso f] : HomotopyEquiv K L :=
  Classical.choose ((ChainComplex.quasiIso_iff_of_projective f).mp inferInstance)

@[simp] theorem homotopyEquivOfQuasiIsoOfProjective_hom
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    [QuasiIso f] :
    (homotopyEquivOfQuasiIsoOfProjective f).hom = f :=
  Classical.choose_spec ((ChainComplex.quasiIso_iff_of_projective f).mp inferInstance)

/-- Nat iso `Hⁿ(Hom(L,-)) ≅ Hⁿ(Hom(K,-))` from a projective quasi-iso. -/
noncomputable def homCochainComplexHomologyNatIsoOfProjectiveQuasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    [QuasiIso f] (n : ℕ) :
    homCochainComplexHomologyFunctor C L n ≅
      homCochainComplexHomologyFunctor C K n :=
  HomotopyEquiv.homCochainComplexHomologyNatIso
    (homotopyEquivOfQuasiIsoOfProjective f) n

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
