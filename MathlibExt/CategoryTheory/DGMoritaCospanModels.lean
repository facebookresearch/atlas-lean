/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedDGModuli
public import MathlibExt.CategoryTheory.DGRelativeCalabiYauModels
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject

/-!
# Actual DG coproducts and Morita cospan pushout presentations

A coproduct has the actual disjoint object set, fully faithful DG
inclusions and zero cross Hom complexes. Negative-cyclic splitting is
normalized on those same inclusion maps and all outgoing DG functors.

The Morita pushout test uses complete framed mapping spaces into the
native enhanced perfect categories. Its comparison is the actual path
homotopy pullback map, rather than a pushout of sets of H0 morphisms.
General cospans may be represented by explicitly augmented cofibrant
diagrams before taking this strict pushout presentation.

Reference: Brav--Dyckerhoff, arXiv:1606.00619v1, §§2.2/6.1--6.2,
diagram6.4; Toën, arXiv:math/0408337v7, §§3--6.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGMoritaCospanModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.Algebra.Homology.DGCategoryTraceModels

universe u v w x y
variable {k : Type u} [Field k]

/-- The actual disjoint DG coproduct has no extra objects or cross morphism complexes. -/
structure DGCoproductModel (A B : DGCat k) where
  category : DGCat k
  objects : category ≃ A ⊕ B
  inl : A ⟶ category
  inr : B ⟶ category
  inl_object : ∀ a : A, objects (inl.obj a) = Sum.inl a
  inr_object : ∀ b : B, objects (inr.obj b) = Sum.inr b
  inl_fullyFaithful : ∀ a a' : A, IsIso (inl.map a a')
  inr_fullyFaithful : ∀ b b' : B, IsIso (inr.map b b')
  cross_zero : ∀ (a : A) (b : B),
    IsZero (dgHomComplex k (inl.obj a) (inr.obj b)) ∧
      IsZero (dgHomComplex k (inr.obj b) (inl.obj a))

/-- The combined cospan functor is fixed by both actual DG inclusions. -/
structure CoproductFunctorModel {A B X : DGCat k} (P : DGCoproductModel A B)
    (f : A ⟶ X) (g : B ⟶ X) where
  functor : P.category ⟶ X
  inl_eq : P.inl ≫ functor = f
  inr_eq : P.inr ≫ functor = g

/-- The source negative-cyclic coproduct splitting is normalized on all actual maps. -/
structure NegativeCoproductModel {A B : DGCat k} (S : NegativeTraceSystem k)
    (P : DGCoproductModel A B) where
  iso : (S.negative P.category).complex ≅ (S.negative A).complex ⊞ (S.negative B).complex
  inl_eq : (S.map P.inl).map ≫ iso.hom = biprod.inl
  inr_eq : (S.map P.inr).map ≫ iso.hom = biprod.inr
  map_eq : ∀ {X : DGCat k} (f : P.category ⟶ X),
    (S.map f).map = iso.hom ≫ biprod.desc (S.map (P.inl ≫ f)).map (S.map (P.inr ≫ f)).map

/-- Native cone functoriality identifies the relative source with both actual coproduct coefficients. -/
def relativeCoefficientIso {A B X : DGCat k} {S : NegativeTraceSystem k}
    {P : DGCoproductModel A B} (N : NegativeCoproductModel S P) (f : P.category ⟶ X) :
    CochainComplex.mappingCone (S.map f).map ≅
      CochainComplex.mappingCone (biprod.desc (S.map (P.inl ≫ f)).map (S.map (P.inr ≫ f)).map) := by
  let e : ComposableArrows.mk₁ (S.map f).map ≅
      ComposableArrows.mk₁ (biprod.desc (S.map (P.inl ≫ f)).map (S.map (P.inr ≫ f)).map) :=
    ComposableArrows.isoMk₁ N.iso (Iso.refl _) (by simpa using N.map_eq f)
  exact (HomotopyCategory.composableArrowsFunctor (ModuleCat k)).mapIso e

/-- Enriched composition is associative at every actual Hom map, including large targets. -/
theorem enriched_comp_assoc {C : Type v} {D : Type w} {E : Type x} {F : Type y}
    [DGCategory k C] [DGCategory k D] [DGCategory k E] [DGCategory k F]
    (f : EnrichedFunctor (Cochains k) C D) (g : EnrichedFunctor (Cochains k) D E)
    (h : EnrichedFunctor (Cochains k) E F) :
    (f.comp (Cochains k) g).comp (Cochains k) h = f.comp (Cochains k) (g.comp (Cochains k) h) := by
  apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
  intro X Y
  simp [EnrichedFunctor.comp, Category.assoc]

/-- The actual framed precomposition map retains every DG mapping simplex. -/
def framePrecomposition (R : DGFrameSystem k) {A B : DGCat k} (f : A ⟶ B)
    (D : Type (u + 1)) [DGCategory k D] :
    dgMapping (R.frame B) D ⟶ dgMapping (R.frame A) D where
  app n := ↾fun g => ((R.map f).app n.unop).comp (Cochains k) g
  naturality n m a := by
    ext g
    change ((R.map f).app m.unop).comp (Cochains k)
        ((R.frame B).diagram.map a.unop |>.comp (Cochains k) g) =
      ((R.frame A).diagram.map a.unop).comp (Cochains k)
        (((R.map f).app n.unop).comp (Cochains k) g)
    rw [← enriched_comp_assoc, ← enriched_comp_assoc]
    exact congrArg (fun h => h.comp (Cochains k) g) ((R.map f).naturality a.unop).symm

/-- Framed precomposition uses the actual composition of the original DG functors. -/
theorem framePrecomposition_comp (R : DGFrameSystem k) {A B C : DGCat k}
    (f : A ⟶ B) (g : B ⟶ C) (D : Type (u + 1)) [DGCategory k D] :
    framePrecomposition R g D ≫ framePrecomposition R f D = framePrecomposition R (f ≫ g) D := by
  ext n h
  change ((R.map f).app n.unop).comp (Cochains k) (((R.map g).app n.unop).comp (Cochains k) h) =
    ((R.map (f ≫ g)).app n.unop).comp (Cochains k) h
  rw [R.map_comp, NatTrans.comp_app]
  exact (enriched_comp_assoc _ _ _).symm

/-- The canonical Morita mapping-space comparison uses the same strict square and native path model. -/
def moritaPushoutComparison (R : DGFrameSystem k) {B X Y Z : DGCat k}
    (f : B ⟶ X) (g : B ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z) (comm : f ≫ i = g ≫ j)
    (D : DGCat k) (P : KanPathModel (dgMapping (R.frame B) (PerfectDGCategory D))) :
    dgMapping (R.frame Z) (PerfectDGCategory D) ⟶
      homotopyPullback (framePrecomposition R f (PerfectDGCategory D))
        (framePrecomposition R g (PerfectDGCategory D)) P :=
  comparison _ _ P (framePrecomposition R i (PerfectDGCategory D))
    (framePrecomposition R j (PerfectDGCategory D)) (by
      rw [framePrecomposition_comp, framePrecomposition_comp, comm])

/-- The full Morita pushout test is on actual derived mapping spaces into every enhanced Perf. -/
def IsMoritaPushout (R : DGFrameSystem k) {B X Y Z : DGCat k}
    (f : B ⟶ X) (g : B ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z) (comm : f ≫ i = g ≫ j) : Prop :=
  ∀ (D : DGCat k) (P : KanPathModel (dgMapping (R.frame B) (PerfectDGCategory D))),
    WeakEquivalence (moritaPushoutComparison R f g i j comm D P)

/-- A derived pushout presentation keeps its actual maps and full Morita mapping-space test. -/
structure MoritaPushoutModel (R : DGFrameSystem k) {B X Y : DGCat k}
    (f : B ⟶ X) (g : B ⟶ Y) where
  category : DGCat k
  inl : X ⟶ category
  inr : Y ⟶ category
  comm : f ≫ inl = g ≫ inr
  pushout : IsMoritaPushout R f g inl inr comm

/-- A general cospan's derived presentation keeps all three source augmentations and their actual maps. -/
structure CospanResolution {B X Y : DGCat k} (f : B ⟶ X) (g : B ⟶ Y) where
  base : DGCat k
  left : DGCat k
  right : DGCat k
  resolvedF : base ⟶ left
  resolvedG : base ⟶ right
  baseAugmentation : base ⟶ B
  leftAugmentation : left ⟶ X
  rightAugmentation : right ⟶ Y
  base_weak : baseAugmentation.IsQuasiEquivalence
  left_weak : leftAugmentation.IsQuasiEquivalence
  right_weak : rightAugmentation.IsQuasiEquivalence
  f_eq : resolvedF ≫ leftAugmentation = baseAugmentation ≫ f
  g_eq : resolvedG ≫ rightAugmentation = baseAugmentation ≫ g
  base_cofibrant : IsCofibrant base
  f_cofibration : dgCofibrations k resolvedF
  g_cofibration : dgCofibrations k resolvedG

end MathlibExt.CategoryTheory.DGMoritaCospanModels
