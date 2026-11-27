/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRawLiftPullbackModels
public import MathlibExt.AlgebraicGeometry.CameralBorelUnramifiedNormalization

/-!
# The universal marked regularizer and its original family pullback

The universal total torsor is the native trivial G torsor over the
actual regular-centralizer parameter scheme. Sigma is the original
adjoint action (g,c) maps to Ad_g(c), and the marked incidence point is
the original G action on the whole universal cameral cover.
The comparison along sigma:P to RegCent uses the actual G-torsor
action relation G times P to P times_X P. Its point normalization fixes
both original torsor factors on every scheme test.
Source: DG math/0005132v3, Sections2/7/16.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralUniversalRegularizerModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRegularizedHiggsModels
open CameralCoverDescentModels CameralRamificationReindexing
open CameralRawLiftPullbackModels CameralBorelAbelianizationCore
open CameralBorelReductionModels GroupTorsorGeometry
open NormalizedTorsorOperations ExpansionParameterModels
open CameralUnramifiedNormalizerModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori)
  (I : IncidenceAction F)

attribute [local instance] centralizerGroupAction

/-- Sigma is the literal native action on the universal centralizer plane. -/
def universalSigma (U : UnitModel G F.centralizers.scheme) :
    U.bundle.torsor.total ⟶ F.centralizers.scheme :=
  U.total.hom ≫ (centralizerGroupAction F).smul

def SigmaEquivariance (U : UnitModel G F.centralizers.scheme) : Prop :=
  U.bundle.torsor.action.smul ≫ universalSigma F U =
    (G ◁ universalSigma F U) ≫ (centralizerGroupAction F).smul

def universalRegularizer (U : UnitModel G F.centralizers.scheme)
    (h : SigmaEquivariance F U) : Regularizer F F.centralizers.scheme where
  torsor := U.bundle.torsor
  map := universalSigma F U
  equivariant := h

structure MarkingSource (U : UnitModel G F.centralizers.scheme)
    (h : SigmaEquivariance F U) where
  descent : CoverDescent F I (universalRegularizer F U h)
  marking : I.incidence.cameral.cover.scheme ≅ descent.cameral.cover.scheme
  weyl : ∀ w, (I.incidence.cameral.cover.action w).asIso.hom ≫ marking.hom =
    marking.hom ≫ (descent.cameral.cover.action w).asIso.hom

def MarkingSource.object {U : UnitModel G F.centralizers.scheme}
    {h : SigmaEquivariance F U} (M : MarkingSource F I U h) :
    Marked F I I.incidence.cameral where
  regularizer := universalRegularizer F U h
  descent := M.descent
  marking := M.marking
  weyl := M.weyl

/-- The full marked cover, including ramification, uses the actual incidence action. -/
structure IncidenceNormalization {U : UnitModel G F.centralizers.scheme}
    {h : SigmaEquivariance F U} (M : MarkingSource F I U h) : Prop where
  points : ∀ (V : Over (Spec (.of ℂ))) (c : V ⟶ total F I.incidence.cameral)
      (p : V ⟶ U.bundle.torsor.total)
      (hp : p ≫ U.bundle.torsor.projection = c ≫ projection F I.incidence.cameral),
    CameralMarkedRegularizers.incidencePoint F I I.incidence.cameral
      (M.object F I) V c p hp =
    CartesianMonoidalCategory.lift (p ≫ U.total.hom ≫ fst G F.centralizers.scheme) c ≫
      I.action.smul

structure UniversalRegularizer where
  unit : UnitModel G F.centralizers.scheme
  sigma : SigmaEquivariance F unit
  marking : MarkingSource F I unit sigma
  incidence : IncidenceNormalization F I marking

def UniversalRegularizer.object (U : UniversalRegularizer F I) :
    Marked F I I.incidence.cameral := U.marking.object F I

variable (U : UniversalRegularizer F I)
  {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C)

/-- The two pulled torsors have the same actual base, the original P_G. -/
structure OriginalActionComparison where
  universal : Reindex G (U.object F I).regularizer.torsor H.regularizer.map
  original : Reindex G H.regularizer.torsor H.regularizer.torsor.projection
  iso : reindexObject G F.centralizers.scheme (U.object F I).regularizer
      H.regularizer.map universal ≅
    reindexObject G F.centralizers.scheme H.regularizer
      H.regularizer.torsor.projection original
  action_relation : ∀ (V : Over (Spec (.of ℂ))) (q : V ⟶ universal.torsor.total),
    q ≫ iso.hom.iso.hom ≫ original.original G =
    CartesianMonoidalCategory.lift
      (q ≫ universal.original G ≫ U.unit.total.hom ≫ fst G F.centralizers.scheme)
      (q ≫ universal.torsor.projection) ≫ H.regularizer.torsor.action.smul
  original_base : iso.hom.iso.hom ≫ original.torsor.projection =
    universal.torsor.projection

/-- Actual original family pulls, with no density assertion on the family. -/
structure OriginalCoverComparison (P : OriginalActionComparison F I U H) where
  universal : ReindexCover F I (U.object F I).regularizer
    (U.object F I).descent H.regularizer.map P.universal
  original : ReindexCover F I H.regularizer H.descent
    H.regularizer.torsor.projection P.original
  cameral : original.pulled.cameral.cover.scheme ≅ universal.pulled.cameral.cover.scheme
  weyl : ∀ w, (original.pulled.cameral.cover.action w).asIso.hom ≫ cameral.hom =
    cameral.hom ≫ (universal.pulled.cameral.cover.action w).asIso.hom
  incidence : ∀ (V : Over (Spec (.of ℂ)))
      (c : V ⟶ total F original.pulled.cameral)
      (p : V ⟶ P.original.torsor.total)
      (hp : c ≫ projection F original.pulled.cameral = p ≫ P.original.torsor.projection)
      (hq : (c ≫ (Over.map H.regularizer.torsor.total.hom).map cameral.hom) ≫
          projection F universal.pulled.cameral =
        (p ≫ P.iso.inv.iso.hom) ≫ P.universal.torsor.projection),
    pullback.lift c p hp ≫
      incidenceMap F I
        (reindexObject G F.centralizers.scheme H.regularizer
          H.regularizer.torsor.projection P.original) original.pulled =
    pullback.lift (c ≫ (Over.map H.regularizer.torsor.total.hom).map cameral.hom)
      (p ≫ P.iso.inv.iso.hom) hq ≫
        incidenceMap F I
          (reindexObject G F.centralizers.scheme (U.object F I).regularizer
            H.regularizer.map P.universal) universal.pulled

/-- The ordinary Cartan locus is defined by the original orbit map. -/
def cartanOrbit (Z : CartanPoint F) : G ⟶ F.centralizers.scheme :=
  CartesianMonoidalCategory.lift (𝟙 G) (toUnit G ≫ Z.point) ≫
    (centralizerGroupAction F).smul

def CartanOpen (Z : CartanPoint F) : Prop := IsOpen (Set.range (cartanOrbit F Z).left)

def cartanOpen (Z : CartanPoint F) (h : CartanOpen F Z) : F.centralizers.scheme.left.Opens :=
  ⟨Set.range (cartanOrbit F Z).left, h⟩

/-- This open belongs only to the actual universal parameter scheme. -/
def cartanOpenScheme (Z : CartanPoint F) (h : CartanOpen F Z) :
    Over (Spec (.of ℂ)) :=
  Over.mk ((cartanOpen F Z h).ι ≫ F.centralizers.scheme.hom)

def cartanOpenInclusion (Z : CartanPoint F) (h : CartanOpen F Z) :
    cartanOpenScheme F Z h ⟶ F.centralizers.scheme :=
  Over.homMk (cartanOpen F Z h).ι rfl

end MathlibExt.AlgebraicGeometry.CameralUniversalRegularizerModels
