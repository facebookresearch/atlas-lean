/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.WittDiscTorsorModels
public import MathlibExt.CategoryTheory.FramePreservingFunctorModels

/-!
# Source-normalized Witt framed-torsor restrictions and quotient comparisons

The original integral and punctured-disc maps determine the native
restriction square. Its underlying sheaf comparison is the actual
over-map pullback compositor and the proved localization square.
Framed restrictions retain the original torsor action and the original
punctured frame through that square, on objects and equivariant maps.

A loop witness is a genuine integral trivialization whose punctured
frame is left multiplication by the original loop on every scheme test.
The quotient comparison uses the original fpqc coequalizer and its actual
sheafification unit, and it is natural for the normalized framed maps.

Source: Zhu, arXiv:1407.8519v3, Lemma 1.3, pp. 8--9.
The dictionary constructors and preservation/coherence proofs are Wanted
endpoints. Their conclusions are not assumptions on the source group.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.WittFramingComparisonModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry
open RelativeWittLoopTests WittDiscTorsorModels
open MathlibExt.CategoryTheory.SheafTorsorGroupoids
open scoped _root_.CategoryTheory.MonObj

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
  (B : Type) [CommRing B] [Algebra (WittVector p k) B] (pi : B)
  (G : Over (Spec (.of B))) [GrpObj G]

/-- The original integral torsor projection of the actual framed groupoid. -/
def frameActions (R : PerfectAlgebra p k) : WittFramedTorsors B G p k pi R ⥤
    Action (topology B (integralTest p k B R))
      (groupSheaf B G (integralTest p k B R)) :=
  CategoryTheory.Limits.CategoricalPullback.π₁
      (torsorActions B G (integralTest p k B R) ⋙ actionPullback G (localization p k B pi R))
      ((Functor.const (Discrete PUnit.{1})).obj (regularAction B G (rationalTest p k B pi R))) ⋙
    torsorActions B G (integralTest p k B R)

/-- The actual constant regular-action target of the original punctured frame. -/
def frameTarget (R : PerfectAlgebra p k) : WittFramedTorsors B G p k pi R ⥤
    Action (topology B (rationalTest p k B pi R))
      (groupSheaf B G (rationalTest p k B pi R)) :=
  CategoryTheory.Limits.CategoricalPullback.π₂
      (torsorActions B G (integralTest p k B R) ⋙ actionPullback G (localization p k B pi R))
      ((Functor.const (Discrete PUnit.{1})).obj (regularAction B G (rationalTest p k B pi R))) ⋙
    (Functor.const (Discrete PUnit.{1})).obj (regularAction B G (rationalTest p k B pi R))

/-- The original actual frame, including its complete arrow compatibility. -/
def framing (R : PerfectAlgebra p k) :
    frameActions p k B pi G R ⋙ actionPullback G (localization p k B pi R) ≅
      frameTarget p k B pi G R :=
  CategoryTheory.CatCommSq.iso
    (CategoryTheory.Limits.CategoricalPullback.π₁ (torsorActions B G (integralTest p k B R) ⋙ actionPullback G (localization p k B pi R))
      ((Functor.const (Discrete PUnit.{1})).obj (regularAction B G (rationalTest p k B pi R))))
    (CategoryTheory.Limits.CategoricalPullback.π₂ (torsorActions B G (integralTest p k B R) ⋙ actionPullback G (localization p k B pi R))
      ((Functor.const (Discrete PUnit.{1})).obj (regularAction B G (rationalTest p k B pi R))))
    (torsorActions B G (integralTest p k B R) ⋙ actionPullback G (localization p k B pi R))
    ((Functor.const (Discrete PUnit.{1})).obj (regularAction B G (rationalTest p k B pi R)))

/-- The restriction square is fixed by the actual native over-map sheaf compositors. -/
def sheafRestrictionSquare {R S : PerfectAlgebra p k} (f : R ⟶ S) :
    (baseTopology B).overMapPullback (Type 1) (integralTestMap p k B f) ⋙
      (baseTopology B).overMapPullback (Type 1) (localization p k B pi S) ≅
    (baseTopology B).overMapPullback (Type 1) (localization p k B pi R) ⋙
      (baseTopology B).overMapPullback (Type 1) (rationalTestMap p k B pi f) := by
  have h := (localizations p k B pi).naturality f.op
  change rationalTestMap p k B pi f ≫ localization p k B pi R =
    localization p k B pi S ≫ integralTestMap p k B f at h
  exact (baseTopology B).overMapPullbackComp (Type 1)
      (localization p k B pi S) (integralTestMap p k B f) ≪≫
    (baseTopology B).overMapPullbackCongr (Type 1) h.symm ≪≫
    ((baseTopology B).overMapPullbackComp (Type 1)
      (rationalTestMap p k B pi f) (localization p k B pi R)).symm

/-- Native action restriction is pinned to the original sheaf restriction square. -/
structure ActionRestrictionSquare {R S : PerfectAlgebra p k} (f : R ⟶ S) where
  comparison : actionPullback G (integralTestMap p k B f) ⋙
      actionPullback G (localization p k B pi S) ≅
    actionPullback G (localization p k B pi R) ⋙
      actionPullback G (rationalTestMap p k B pi f)
  sheaf_hom : ∀ P : Action (topology B (integralTest p k B R))
      (groupSheaf B G (integralTest p k B R)),
    (comparison.hom.app P).val = (sheafRestrictionSquare p k B pi f).hom.app P.sheaf
  sheaf_inv : ∀ P : Action (topology B (integralTest p k B R))
      (groupSheaf B G (integralTest p k B R)),
    (comparison.inv.app P).val = (sheafRestrictionSquare p k B pi f).inv.app P.sheaf

/-- A comparison of the restricted regular action with the regular action is the identity on
sections, in both directions. Stated once as a named predicate, so that the structure below does
not make the kernel recheck these section-level equations in every auxiliary declaration. -/
def IsIdentityOnSections {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (c : (actionPullback G (rationalTestMap p k B pi f)).obj
      (regularAction B G (rationalTest p k B pi R)) ≅
        regularAction B G (rationalTest p k B pi S)) : Prop :=
  (∀ (T : (Site B (rationalTest p k B pi S))ᵒᵖ) (x : ULift.{1} (T.unop.left ⟶ G)),
      c.hom.val.hom.app T x = x) ∧
    ∀ (T : (Site B (rationalTest p k B pi S))ᵒᵖ) (x : ULift.{1} (T.unop.left ⟶ G)),
      c.inv.val.hom.app T x = x

/-- The regular action restricts to the original regular action with identity on sections. -/
structure RegularRestriction {R S : PerfectAlgebra p k} (f : R ⟶ S) where
  comparison : (actionPullback G (rationalTestMap p k B pi f)).obj
      (regularAction B G (rationalTest p k B pi R)) ≅
    regularAction B G (rationalTest p k B pi S)
  identity_on_sections : IsIdentityOnSections p k B pi G f comparison

variable {p k B pi G}

/-- The target restriction uses that same native regular-action comparison. -/
def RegularRestriction.targets {R S : PerfectAlgebra p k} {f : R ⟶ S}
    (E : RegularRestriction p k B pi G f) :
    frameTarget p k B pi G R ⋙ actionPullback G (rationalTestMap p k B pi f) ≅
      (Functor.const (WittFramedTorsors B G p k pi R)).obj
        (regularAction B G (rationalTest p k B pi S)) :=
  NatIso.ofComponents (fun _ ↦ E.comparison) (by
    intro P Q a
    change (actionPullback G (rationalTestMap p k B pi f)).map (𝟙 _) ≫
      E.comparison.hom = E.comparison.hom ≫ 𝟙 _
    rw [_root_.CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])

/-- The target is the original regular action, independently of the framed object. -/
def identifyFrameTarget {R S : PerfectAlgebra p k}
    (F : WittFramedTorsors B G p k pi R ⥤ WittFramedTorsors B G p k pi S) :
    F ⋙ frameTarget p k B pi G S ≅
      (Functor.const (WittFramedTorsors B G p k pi R)).obj
        (regularAction B G (rationalTest p k B pi S)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro P Q a
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rfl)

variable (p k B pi G)

/-- A framed restriction preserves the actual original action and full frame square. -/
abbrev FramedRestriction {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (A : ActionRestrictionSquare p k B pi G f) (E : RegularRestriction p k B pi G f) :=
  MathlibExt.CategoryTheory.FramePreservingFunctorModels.FrameMap
    (actionPullback G (integralTestMap p k B f))
    (actionPullback G (localization p k B pi R))
    (actionPullback G (localization p k B pi S))
    (actionPullback G (rationalTestMap p k B pi f)) A.comparison
    (frameActions p k B pi G R) (frameActions p k B pi G S)
    (frameTarget p k B pi G R) (frameTarget p k B pi G S)
    ((Functor.const (WittFramedTorsors B G p k pi R)).obj
      (regularAction B G (rationalTest p k B pi S)))
    (framing p k B pi G R) (framing p k B pi G S) E.targets identifyFrameTarget

/-- A loop determines the original left-multiplication punctured frame on every test. -/
def RepresentsLoop (R : PerfectAlgebra p k) (g : (loops p k B pi G).obj R)
    (P : WittFramedTorsors B G p k pi R) : Prop :=
  ∃ e : P.fst.of.obj ≅ regularAction B G (integralTest p k B R),
    ∀ (T : (Site B (rationalTest p k B pi R))ᵒᵖ)
      (x : (groupSets (topology B (rationalTest p k B pi R))
        (groupSheaf B G (rationalTest p k B pi R))).obj.obj T),
      P.iso.hom.val.hom.app T
        (((actionPullback G (localization p k B pi R)).map e.inv).val.hom.app T x) =
          ULift.up ((T.unop.hom ≫ g) * (show T.unop.left ⟶ G from x.down))

/-- The loop class uses the actual coequalizer and native fpqc sheafification unit. -/
def loopClass (R : PerfectAlgebra p k) (g : (loops p k B pi G).obj R) :
    (RelativeWittLoopCorrespondences.grassmannian p k B pi G).obj.obj (op (op R)) :=
  (toSheafify (fpqcTopology p k)
    ((opOpEquivalence (PerfectAlgebra p k)).functor ⋙
      RelativeWittLoopCorrespondences.grassmannianPresheaf p k B pi G)).app (op (op R))
    ((RelativeWittLoopCorrespondences.quotient p k B pi G).app R (ULift.up g))

/-- Full source restriction data have actual native framed groupoid maps and coherence. -/
structure RestrictionData where
  square : ∀ {R S : PerfectAlgebra p k} (f : R ⟶ S),
    ActionRestrictionSquare p k B pi G f
  regular : ∀ {R S : PerfectAlgebra p k} (f : R ⟶ S),
    RegularRestriction p k B pi G f
  map : ∀ {R S : PerfectAlgebra p k} (f : R ⟶ S),
    FramedRestriction p k B pi G f (square f) (regular f)
  identity : ∀ R : PerfectAlgebra p k, (map (𝟙 R)).functor ≅ 𝟭 _
  composition : ∀ {R S T : PerfectAlgebra p k} (f : R ⟶ S) (h : S ⟶ T),
    (map f).functor ⋙ (map h).functor ≅ (map (f ≫ h)).functor

/-- The quotient dictionary is natural for the original action/frame restrictions. -/
structure TorsorQuotientComparison (D : RestrictionData p k B pi G) where
  points : ∀ R : PerfectAlgebra p k,
    (RelativeWittLoopCorrespondences.grassmannian p k B pi G).obj.obj (op (op R)) ≃
      WittFramedClasses B G p k pi R
  loop_normalized : ∀ (R : PerfectAlgebra p k) (g : (loops p k B pi G).obj R),
    ∃ P : WittFramedTorsors B G p k pi R, RepresentsLoop p k B pi G R g P ∧
      points R (loopClass p k B pi G R g) = Quotient.mk _ P
  naturality : ∀ {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (P : WittFramedTorsors B G p k pi R),
    points S ((RelativeWittLoopCorrespondences.grassmannian p k B pi G).obj.map f.op.op
      ((points R).symm (Quotient.mk _ P))) =
        Quotient.mk _ ((D.map f).functor.obj P)

end MathlibExt.AlgebraicGeometry.WittFramingComparisonModels
