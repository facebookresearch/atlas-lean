/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels

/-!
# Natural derived-stack path, product and fibre models

Path objects retain the actual natural endpoint and diagonal maps and
the injective diagram-fibration lifting property. Their components are
the genuine Kan path models. Stack products and homotopy pullbacks are
the literal native functor-category products/pullbacks; all projections
are computed from those objects.

Filtered-colimit comparisons are the native colimit maps of the actual
algebra diagram. Relative finite presentation is the weak-equivalence
test on its fixed homotopy-pullback comparison. Formal smoothness uses
the previously fixed square-zero comparison and its actual path components.

References: Toën--Vezzosi, HAG II, Part 2; Toën--Vaquié,
arXiv:math/0503269v5, §2.1; PTVV, arXiv:1111.3209v4, conventions.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedStackFibreModels

open CategoryTheory Limits Opposite HomotopicalAlgebra
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels

universe u

variable {k : Type u} [CommRing k]
variable {Q : AlgebraReplacementFunctor k}

/-- Stack maps are actual natural transformations on simplicial algebras. -/
abbrev StackMap (F G : DerivedStack Q) := F.functor ⟶ G.functor

/-- The actual injective diagram-fibration lifting property. -/
def IsInjectiveFibration {F G : Prestack k} (p : F ⟶ G) : Prop :=
  ∀ (A B : Prestack k) (i : A ⟶ B),
    (∀ T, Mono (i.app T) ∧ WeakEquivalence (i.app T)) →
    ∀ (a : A ⟶ F) (b : B ⟶ G), a ≫ p = i ≫ b →
      ∃ l : B ⟶ F, i ≫ l = a ∧ l ≫ p = b

/-- A genuine natural path model in the actual prestack diagram category. -/
structure NaturalPathModel (G : DerivedStack Q) extends PrepathObject G.functor where
  diagonal_weak : ∀ A, WeakEquivalence (ι.app A)
  injective_fibration : IsInjectiveFibration (prod.lift p₀ p₁)
  endpoints_fibration : ∀ A,
    SSet.modelCategoryQuillen.J.rlp (prod.lift (p₀.app A) (p₁.app A))

/-- Components retain the actual diagonal and endpoint maps. -/
def NaturalPathModel.component {G : DerivedStack Q} (P : NaturalPathModel G) (A : SAlg k) :
    KanPathModel (G.functor.obj A) where
  P := P.P.obj A
  p₀ := P.p₀.app A
  p₁ := P.p₁.app A
  ι := P.ι.app A
  ι_p₀ := by
    simpa only [NatTrans.comp_app, NatTrans.id_app] using congrArg (fun f => f.app A) P.ι_p₀
  ι_p₁ := by
    simpa only [NatTrans.comp_app, NatTrans.id_app] using congrArg (fun f => f.app A) P.ι_p₁
  kan := G.kan A
  diagonal_weak := P.diagonal_weak A
  endpoints_fibration := P.endpoints_fibration A

/-- The literal stack product is a native product of prestack functors. -/
structure ProductStackModel (F G : DerivedStack Q) where
  stack : DerivedStack Q
  functor_eq : stack.functor = (F.functor ⨯ G.functor)

/-- The actual diagonal into a normalized product model. -/
def diagonal (F : DerivedStack Q) (M : ProductStackModel F F) : StackMap F M.stack :=
  prod.lift (𝟙 F.functor) (𝟙 F.functor) ≫ eqToHom M.functor_eq.symm

/-- The actual functor-category homotopy pullback of the chosen natural path. -/
def fibreFunctor {F G H : DerivedStack Q} (P : NaturalPathModel H)
    (f : StackMap F H) (g : StackMap G H) : Prestack k :=
  pullback (prod.map f g) (prod.lift P.p₀ P.p₁)

/-- A stack model is constrained to that literal native pullback functor. -/
structure FibreStackModel {F G H : DerivedStack Q} (P : NaturalPathModel H)
    (f : StackMap F H) (g : StackMap G H) where
  stack : DerivedStack Q
  functor_eq : stack.functor = fibreFunctor P f g

/-- The actual first projection from the computed derived fibre. -/
def first {F G H : DerivedStack Q} {P : NaturalPathModel H}
    {f : StackMap F H} {g : StackMap G H} (M : FibreStackModel P f g) : StackMap M.stack F :=
  eqToHom M.functor_eq ≫ pullback.fst _ _ ≫ prod.fst

/-- The actual second projection from the computed derived fibre. -/
def second {F G H : DerivedStack Q} {P : NaturalPathModel H}
    {f : StackMap F H} {g : StackMap G H} (M : FibreStackModel P f g) : StackMap M.stack G :=
  eqToHom M.functor_eq ≫ pullback.fst _ _ ≫ prod.snd

/-- The literal colimit comparison for the actual affine-algebra diagram. -/
def filteredComparison {J : Type u} [Category.{u} J] (F : Prestack k) (D : J ⥤ SAlg k) :
    colimit (D ⋙ F) ⟶ F.obj (colimit D) :=
  colimit.desc (D ⋙ F) (F.mapCocone (colimit.cocone D))

/-- Naturality fixes the square defining relative finite presentation. -/
theorem filteredComparison_naturality {J : Type u} [Category.{u} J]
    {F G : Prestack k} (f : F ⟶ G) (D : J ⥤ SAlg k) :
    filteredComparison F D ≫ f.app (colimit D) =
      colim.map (Functor.whiskerLeft D f) ≫ filteredComparison G D := by
  apply colimit.hom_ext
  intro j
  simp [filteredComparison]

/-- The actual relative filtered-colimit comparison, with no chosen finiteness map. -/
def relativeFilteredComparison {J : Type u} [Category.{u} J]
    {F G : DerivedStack Q} (P : NaturalPathModel G) (f : StackMap F G)
    (D : J ⥤ SAlg k) :
    colimit (D ⋙ F.functor) ⟶
      homotopyPullback (f.app (colimit D)) (filteredComparison G.functor D)
        (P.component (colimit D)) :=
  comparison (f.app (colimit D)) (filteredComparison G.functor D)
    (P.component (colimit D)) (filteredComparison F.functor D)
    (colim.map (Functor.whiskerLeft D f)) (filteredComparison_naturality f D)

/-- Relative local finite presentation is the actual filtered-colimit square test. -/
def IsLocallyOfFinitePresentation {F G : DerivedStack Q} (f : StackMap F G) : Prop :=
  ∀ (J : Type u) [Category.{u} J] [IsFiltered J] (D : J ⥤ SAlg k)
    (P : NaturalPathModel G), WeakEquivalence (relativeFilteredComparison P f D)

/-- Absolute local finite presentation tests the fixed native comparison. -/
def IsLocallyOfFinitePresentationStack (F : DerivedStack Q) : Prop :=
  ∀ (J : Type u) [Category.{u} J] [IsFiltered J] (D : J ⥤ SAlg k),
    WeakEquivalence (filteredComparison F.functor D)

/-- Smooth stack maps use the actual square-zero and filtered-colimit comparisons. -/
def IsSmooth {F G : DerivedStack Q} (f : StackMap F G) : Prop :=
  IsLocallyOfFinitePresentation f ∧
    ∀ P : NaturalPathModel G,
      IsFormallySmooth (fun A => P.component A) f

end MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
