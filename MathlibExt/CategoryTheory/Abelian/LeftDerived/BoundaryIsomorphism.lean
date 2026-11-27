/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism
public import MathlibExt.CategoryTheory.Abelian.DerivedDeltaFunctor

/-!
# Isomorphisms of left-derived connecting families

An isomorphism of additive functors between abelian categories with
projective resolutions in the source gives an isomorphism of their
left-derived δ-functors. Its degree components are the canonical
left-derived isomorphisms and preserve every short-exact-sequence boundary.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive]

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `e : F ≅ G`. The canonical degree
isomorphisms `L_ne` form an isomorphism of their left-derived
homological δ-functors, including all connecting transformations. -/
def NatIso.leftDerivedDeltaFunctor (e : F ≅ G) :
    letI := Functor.additive_of_iso e
    F.leftDerivedDeltaFunctor ≅ G.leftDerivedDeltaFunctor := by
  letI := Functor.additive_of_iso e
  exact (leftDerivedDeltaFunctorFamily C D).mapIso
    (ObjectProperty.isoMk (additiveFunctor C D) e : AdditiveFunctor.of F ≅ AdditiveFunctor.of G)

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `e : F ≅ G`. The forward degree-`n`
component of the δ-functor isomorphism is the forward natural
transformation of `L_ne : L_nF ≅ L_nG`. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_hom_app (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    HomologicalDeltaFunctor.Hom.app (NatIso.leftDerivedDeltaFunctor e).hom n =
      (NatIso.leftDerived e n).hom := rfl

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `e : F ≅ G`. The inverse degree-`n`
component of the δ-functor isomorphism is the inverse natural
transformation of `L_ne : L_nF ≅ L_nG`. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_inv_app (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    HomologicalDeltaFunctor.Hom.app (NatIso.leftDerivedDeltaFunctor e).inv n =
      (NatIso.leftDerived e n).inv := rfl

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `e : F ≅ G`. Evaluation in degree `n`
recovers precisely the natural isomorphism `L_ne`. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_evaluation (e : F ≅ G) (n : ℕ) :
    letI := Functor.additive_of_iso e
    (HomologicalDeltaFunctor.evaluation C D n).mapIso
        (NatIso.leftDerivedDeltaFunctor e) = NatIso.leftDerived e n := by
  let := Functor.additive_of_iso e
  apply Iso.ext
  rfl

/-- For abelian `C`, `D`, with projective resolutions in `C` and
additive `F : C → D`, the identity functor isomorphism induces
the identity isomorphism of its left-derived δ-functor. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_refl :
    NatIso.leftDerivedDeltaFunctor (Iso.refl F) = Iso.refl F.leftDerivedDeltaFunctor := by
  change (leftDerivedDeltaFunctorFamily C D).mapIso
    (Iso.refl (AdditiveFunctor.of F)) =
      Iso.refl ((leftDerivedDeltaFunctorFamily C D).obj (AdditiveFunctor.of F))
  exact (leftDerivedDeltaFunctorFamily C D).mapIso_refl (AdditiveFunctor.of F)

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `e : F ≅ G`. Reversing `e` reverses
the induced isomorphism of left-derived δ-functors. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_symm (e : F ≅ G) :
    letI := Functor.additive_of_iso e
    NatIso.leftDerivedDeltaFunctor e.symm = (NatIso.leftDerivedDeltaFunctor e).symm := by
  let := Functor.additive_of_iso e
  let a : AdditiveFunctor.of F ≅ AdditiveFunctor.of G := ObjectProperty.isoMk (additiveFunctor C D) e
  change (leftDerivedDeltaFunctorFamily C D).mapIso a.symm =
    ((leftDerivedDeltaFunctorFamily C D).mapIso a).symm
  exact (leftDerivedDeltaFunctorFamily C D).mapIso_symm a

/-- For additive functors `F,G,H : C → D` between abelian categories
with projective resolutions in `C`, the δ-functor isomorphism
induced by `F ≅ G ≅ H` is the composite of the two induced
left-derived δ-functor isomorphisms. -/
@[simp]
theorem NatIso.leftDerivedDeltaFunctor_trans {H : C ⥤ D}
    (e : F ≅ G) (e' : G ≅ H) :
    letI := Functor.additive_of_iso e
    letI := Functor.additive_of_iso e'
    NatIso.leftDerivedDeltaFunctor (e ≪≫ e') =
      NatIso.leftDerivedDeltaFunctor e ≪≫ NatIso.leftDerivedDeltaFunctor e' := by
  let := Functor.additive_of_iso e
  let := Functor.additive_of_iso e'
  let a : AdditiveFunctor.of F ≅ AdditiveFunctor.of G := ObjectProperty.isoMk (additiveFunctor C D) e
  let b : AdditiveFunctor.of G ≅ AdditiveFunctor.of H := ObjectProperty.isoMk (additiveFunctor C D) e'
  change (leftDerivedDeltaFunctorFamily C D).mapIso (a ≪≫ b) =
    (leftDerivedDeltaFunctorFamily C D).mapIso a ≪≫
      (leftDerivedDeltaFunctorFamily C D).mapIso b
  exact (leftDerivedDeltaFunctorFamily C D).mapIso_trans a b

/- Proof implementation note.
The forward canonical derived isomorphism commutes with the boundary of every original short exact
sequence.
-/

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `e : F ≅ G`. For short exact
`S : X₁ → X₂ → X₃`, the forward degree maps commute with
`δ_F,n : L_(n+1)F(X₃) → L_nF(X₁)` and `δ_G,n`. -/
@[reassoc]
theorem NatIso.leftDerived_hom_LDdelta (e : F ≅ G) (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    letI := Functor.additive_of_iso e
    (NatIso.leftDerived e (n + 1)).hom.app S.X₃ ≫ LeftDerivedDelta.LDdelta G n S hS =
      LeftDerivedDelta.LDdelta F n S hS ≫ (NatIso.leftDerived e n).hom.app S.X₁ := by
  let := Functor.additive_of_iso e
  exact LeftDerivedDelta.LDdelta_natural_functor e.hom n S hS

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `e : F ≅ G`. For short exact
`S : X₁ → X₂ → X₃`, the inverse degree maps commute with
`δ_G,n : L_(n+1)G(X₃) → L_nG(X₁)` and `δ_F,n`. -/
@[reassoc]
theorem NatIso.leftDerived_inv_LDdelta (e : F ≅ G) (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    letI := Functor.additive_of_iso e
    (NatIso.leftDerived e (n + 1)).inv.app S.X₃ ≫ LeftDerivedDelta.LDdelta F n S hS =
      LeftDerivedDelta.LDdelta G n S hS ≫ (NatIso.leftDerived e n).inv.app S.X₁ := by
  let := Functor.additive_of_iso e
  exact LeftDerivedDelta.LDdelta_natural_functor e.inv n S hS

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `e : F ≅ G`. For short exact `S`,
the `G` boundary is the `F` boundary conjugated by the
canonical degree-`n+1` inverse and degree-`n` forward comparisons. -/
theorem NatIso.LDdelta_eq_leftDerived_inv_comp (e : F ≅ G) (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    letI := Functor.additive_of_iso e
    LeftDerivedDelta.LDdelta G n S hS =
      (NatIso.leftDerived e (n + 1)).inv.app S.X₃ ≫
        LeftDerivedDelta.LDdelta F n S hS ≫ (NatIso.leftDerived e n).hom.app S.X₁ := by
  let := Functor.additive_of_iso e
  calc
    LeftDerivedDelta.LDdelta G n S hS =
        (LeftDerivedDelta.LDdelta G n S hS ≫ (NatIso.leftDerived e n).inv.app S.X₁) ≫
          (NatIso.leftDerived e n).hom.app S.X₁ := by
      rw [Category.assoc, (NatIso.leftDerived e n).inv_hom_id_app, Category.comp_id]
    _ = ((NatIso.leftDerived e (n + 1)).inv.app S.X₃ ≫
        LeftDerivedDelta.LDdelta F n S hS) ≫ (NatIso.leftDerived e n).hom.app S.X₁ :=
      congrArg (fun f => f ≫ (NatIso.leftDerived e n).hom.app S.X₁)
        (NatIso.leftDerived_inv_LDdelta e n S hS).symm
    _ = _ := Category.assoc _ _ _

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `e : F ≅ G`. For a morphism `S → T`
of short exact sequences, the derived sequence-map square
and forward coefficient-isomorphism boundary square paste
to the same connecting square. -/
@[reassoc]
theorem NatIso.leftDerived_hom_map_LDdelta (e : F ≅ G) (n : ℕ)
    {S T : ShortComplex C} (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact) :
    letI := Functor.additive_of_iso e
    (NatIso.leftDerived e (n + 1)).hom.app S.X₃ ≫
        (G.leftDerived (n + 1)).map φ.τ₃ ≫ LeftDerivedDelta.LDdelta G n T hT =
      LeftDerivedDelta.LDdelta F n S hS ≫ (F.leftDerived n).map φ.τ₁ ≫
        (NatIso.leftDerived e n).hom.app T.X₁ := by
  let := Functor.additive_of_iso e
  rw [LeftDerivedDelta.LDdelta_natural G n T S φ hT hS]
  rw [← Category.assoc, NatIso.leftDerived_hom_LDdelta e n S hS,
    Category.assoc, ← (NatIso.leftDerived e n).hom.naturality φ.τ₁]

end CategoryTheory

end
