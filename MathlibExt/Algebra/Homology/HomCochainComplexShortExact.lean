/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/

module

public import MathlibExt.Algebra.Homology.HomCochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import MathlibExt.Algebra.Homology.HomologySequenceFunctor

/-!
# Short exact sequences of Hom-cochain complexes

This file proves short exactness for degreewise split-monomorphism sequences and for
coefficient short exact sequences when the fixed chain complex is degreewise projective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Apply the contravariant Hom-cochain functor to a short complex of chain
complexes. -/
noncomputable abbrev homCochainShortComplex
    (S : ShortComplex (ChainComplex C ℕ)) (G : C) :
    ShortComplex (CochainComplex AddCommGrpCat.{v} ℕ) :=
  S.op.map (homCochainComplexFunctor C G)

/-- Applying `Hom(-, G)` to a short exact sequence of chain complexes remains
short exact when the first map is split mono in every degree. -/
theorem homCochainShortComplex_shortExact_of_degreewise_splitMono
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact)
    (hsplit : ∀ n, SplitMono ((S.map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).f)) (G : C) :
    (homCochainShortComplex S G).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let S_n : ShortComplex C :=
    S.map (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
  have hS_n : S_n.ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  have hsplit_n : SplitMono S_n.f := hsplit n
  let splitting : S_n.Splitting :=
    ShortComplex.Splitting.ofExactOfRetraction S_n hS_n.exact
      hsplit_n.retraction hsplit_n.id hS_n.epi_g
  let F : Cᵒᵖ ⥤ AddCommGrpCat.{v} := preadditiveYoneda.obj G
  have hMapped : ((S_n.op).map F).ShortExact :=
    (splitting.op.map F).shortExact
  have hEq :
      ((homCochainShortComplex S G).map
        (HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) n)) =
        ((S_n.op).map F) := by
    dsimp [homCochainShortComplex, homCochainComplexFunctor, S_n, F]
    rfl
  rw [hEq]
  exact hMapped

/-- The cochain-complex functor in the coefficient variable associated to a
fixed chain complex `K`. -/
noncomputable def homCochainComplexCoefficientFunctor (K : ChainComplex C ℕ) :
    Functor C (CochainComplex AddCommGrpCat.{v} ℕ) :=
  homCochainComplexBifunctor C ⋙
    (evaluation (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex AddCommGrpCat.{v} ℕ)).obj (Opposite.op K)

noncomputable instance homCochainComplexCoefficientFunctor_additive
    (K : ChainComplex C ℕ) :
    (homCochainComplexCoefficientFunctor K).Additive where
  map_add {X Y} f g := by
    ext n x
    let x' : K.X n ⟶ X := x
    change x' ≫ (f + g) = x' ≫ f + x' ≫ g
    exact @Preadditive.comp_add C _ _ (K.X n) X Y x' f g

private noncomputable def homCochainComplexCoefficientFunctorEval
    (K : ChainComplex C ℕ) (n : ℕ) : Functor C AddCommGrpCat.{v} :=
  homCochainComplexCoefficientFunctor K ⋙
    HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) n

private noncomputable instance homCochainComplexCoefficientFunctorEval_additive
    (K : ChainComplex C ℕ) (n : ℕ) :
    (homCochainComplexCoefficientFunctorEval K n).Additive := by
  dsimp [homCochainComplexCoefficientFunctorEval]
  infer_instance

private noncomputable instance
    homCochainComplexCoefficientFunctorEval_preservesFiniteLimits
    (K : ChainComplex C ℕ) (n : ℕ) :
    PreservesFiniteLimits (homCochainComplexCoefficientFunctorEval K n) := by
  change PreservesFiniteLimits
    (preadditiveCoyoneda.obj (Opposite.op (K.X n)))
  infer_instance

private noncomputable instance
    homCochainComplexCoefficientFunctorEval_preservesFiniteColimits
    (K : ChainComplex C ℕ) (n : ℕ) [Projective (K.X n)] :
    PreservesFiniteColimits (homCochainComplexCoefficientFunctorEval K n) := by
  change PreservesFiniteColimits
    (preadditiveCoyoneda.obj (Opposite.op (K.X n)))
  let F := preadditiveCoyoneda.obj (Opposite.op (K.X n))
  have hEpi : F.PreservesEpimorphisms :=
    (Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj
      (K.X n)).mp inferInstance
  have hHomology : F.PreservesHomology :=
    @Functor.preservesHomology_of_preservesEpis_and_kernels _ _ _ _ _ _ F
      inferInstance hEpi inferInstance
  exact
    @Functor.preservesFiniteColimits_of_preservesHomology _ _ _ _ _ _ F
      inferInstance hHomology inferInstance inferInstance inferInstance

/-- Applying `Hom(K, -)` degreewise to a short exact coefficient sequence
remains short exact when every chain group of `K` is projective. -/
theorem homCochainComplexCoefficientFunctor_map_shortExact_of_projective
    (K : ChainComplex C ℕ) [∀ n, Projective (K.X n)]
    (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map (homCochainComplexCoefficientFunctor K)).ShortExact := by
  let S' : ShortComplex (CochainComplex AddCommGrpCat.{v} ℕ) :=
    S.map (homCochainComplexCoefficientFunctor K)
  change S'.ShortExact
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  have h :
      S'.map
          (HomologicalComplex.eval AddCommGrpCat.{v}
            (ComplexShape.up ℕ) n) =
        S.map (homCochainComplexCoefficientFunctorEval K n) :=
    rfl
  rw [h]
  exact
    ShortComplex.ShortExact.map_of_exact hS
      (homCochainComplexCoefficientFunctorEval K n)

/-- Family Hom-cochain bifunctor at the `Preadditive` layer associated to `K`. -/
noncomputable def homCochainComplexBifunctorOfFunctor
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : Type u'} [Category.{v'} X] (K : X ⥤ ChainComplex C ℕ) :
    C ⥤ Xᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  homCochainComplexBifunctor C ⋙
    (Functor.whiskeringLeft Xᵒᵖ (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex AddCommGrpCat.{v} ℕ)).obj K.op

/-- Additivity of the flipped family Hom-cochain bifunctor at a fixed `x`. -/
noncomputable instance homCochainComplexBifunctorOfFunctor_flip_obj_additive
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : Type u'} [Category.{v'} X]
    (K : X ⥤ ChainComplex C ℕ) (x : Xᵒᵖ) :
    ((homCochainComplexBifunctorOfFunctor K).flip.obj x).Additive where
  map_add {A B} f g := by
    ext n y
    let y' : (K.obj x.unop).X n ⟶ A := y
    change y' ≫ (f + g) = y' ≫ f + y' ≫ g
    exact @Preadditive.comp_add C _ _ _ _ _ y' f g

/-- Fixed-object projective bridge for the family Hom-cochain bifunctor. -/
theorem homCochainComplexBifunctorOfFunctor_map_shortExact_of_projective
    {C : Type u} [Category.{v} C] [Abelian C]
    {X : Type u'} [Category.{v'} X]
    (K : X ⥤ ChainComplex C ℕ)
    (x : Xᵒᵖ) [∀ n : ℕ, Projective ((K.obj x.unop).X n)]
    (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map ((homCochainComplexBifunctorOfFunctor K).flip.obj x)).ShortExact := by
  change (S.map (homCochainComplexCoefficientFunctor (K.obj x.unop))).ShortExact
  exact homCochainComplexCoefficientFunctor_map_shortExact_of_projective
    (K.obj x.unop) S hS

/-- Generic exact-sequence bifunctor from the family Hom-cochain construction. -/
noncomputable def homCochainComplexExactSequenceBifunctor
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : Type u'} [Category.{v'} X]
    (K : X ⥤ ChainComplex C ℕ)
    (hK : ∀ (x : Xᵒᵖ) (S : ShortComplex C), S.ShortExact →
      (S.map ((homCochainComplexBifunctorOfFunctor K).flip.obj x)).ShortExact)
    (n : ℕ) :
    ShortComplex.ShortExactSequences C ⥤
      Xᵒᵖ ⥤ ComposableArrows.ExactSequences AddCommGrpCat.{v} 5 :=
  HomologySequence.exactSequenceBifunctor (homCochainComplexBifunctorOfFunctor K) hK n
    (n + 1) (by simp)

/-- Projective specialization of the family Hom-cochain exact-sequence bifunctor. -/
noncomputable def homCochainComplexExactSequenceBifunctor_of_projective
    {C : Type u} [Category.{v} C] [Abelian C]
    {X : Type u'} [Category.{v'} X]
    (K : X ⥤ ChainComplex C ℕ)
    [∀ (x : X) (n : ℕ), Projective ((K.obj x).X n)]
    (n : ℕ) :
    ShortComplex.ShortExactSequences C ⥤
      Xᵒᵖ ⥤ ComposableArrows.ExactSequences AddCommGrpCat.{v} 5 :=
  homCochainComplexExactSequenceBifunctor K (fun x S hS => by
    let _ (m : ℕ) : Projective ((K.obj x.unop).X m) := inferInstance
    exact homCochainComplexBifunctorOfFunctor_map_shortExact_of_projective K x S hS) n

end HomologicalComplex
