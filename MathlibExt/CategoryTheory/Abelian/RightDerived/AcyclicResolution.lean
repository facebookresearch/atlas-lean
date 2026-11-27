/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolution
public import MathlibExt.CategoryTheory.Abelian.RightDerived.OpDuality
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/- The proof passes to the opposite augmentation and the left-derived acyclic comparison; projective resolutions in the opposite category are constructed locally from injective resolutions. -/

/-!
# Right-derived cohomology computed by acyclic resolutions

Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. A coaugmentation
quasi-isomorphism `X[0] → I` whose terms satisfy
`R^(j+1)F(I^q)=0` for every `q,j` gives a comparison
`R^nF(X) ≅ Hⁿ(F(I))` in every degree. The terms of `I` need not
be injective.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. Let
`ι : X[0] → I` be a quasi-isomorphism of nonnegative cochain complexes
with `R^(j+1)F(I^q)=0` for every `q,j`. There is a comparison `R^nF(X) ≅ Hⁿ(F(I))` in every degree
`n`, computing right derivation from the termwise acyclic coaugmented
complex `I`. -/
noncomputable def rightDerivedObjIsoHomologyOfAcyclicResolution
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (I.X q))) (n : ℕ) :
    (F.rightDerived n).obj X ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n := by
  have : HasProjectiveResolutions Cᵒᵖ :=
    { out Y := ⟨⟨injectiveResolutionOpProj (injectiveResolution Y.unop)⟩⟩ }
  have : PreservesFiniteColimits F.op := preservesFiniteColimits_op F
  let π : I.op ⟶ (ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op X) :=
    (HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map ι.op ≫
      (single₀OpIso X).hom
  have hπ : QuasiIso π := by
    have h₁ : QuasiIso ((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map ι.op) :=
      (HomologicalComplex.quasiIso_opFunctor_map_iff _).mpr inferInstance
    have h₂ : QuasiIso (single₀OpIso X).hom := by
      let _ : IsIso (single₀OpIso X).hom := (single₀OpIso X).isIso_hom
      exact quasiIso_of_isIso _
    exact quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂)
  have hIop : ∀ q j : ℕ, IsZero ((F.op.leftDerived (j + 1)).obj (I.op.X q)) := by
    intro q j
    change IsZero ((F.op.leftDerived (j + 1)).obj (Opposite.op (I.X q)))
    have hu : IsZero (Opposite.unop
        ((F.op.leftDerived (j + 1)).obj (Opposite.op (I.X q)))) :=
      (hI q j).of_iso ((F.rightDerivedOpIso (j + 1)).app (I.X q)).symm
    exact hu.op
  let eL : (F.op.leftDerived n).obj (Opposite.op X) ≅
      ((F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj I.op).homology n := by
    exact @leftDerivedObjIsoHomologyOfAcyclicResolution
      _ _ _ _ _ _ _ F.op _ _ _ I.op π hπ hIop n
  let K : CochainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I
  let eK : (F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj I.op ≅ K.op := Iso.refl _
  let eH := (HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) n).mapIso eK
  exact (F.rightDerivedOpIso n).app X ≪≫ (eL ≪≫ eH ≪≫ K.homologyOp n).unop.symm

end CategoryTheory.Functor
