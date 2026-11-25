/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralBandAutomorphismModels
public import MathlibExt.AlgebraicGeometry.NormalizedTorsorOperations

/-!
# Native band torsors, contracted twisting and H1

The band action is evaluated through the same sigma-pulled universal
centralizer on every scheme test. Twisting is the actual inverse
diagonal fppf quotient of a band torsor and the original G torsor.
The target sigma and marked incidence maps descend the original ones.
H1 consists of actual band-torsor isomorphism classes; its operations
are the native tensor quotient and inversion pushout. No neutrality or
nonemptiness is asserted for an arbitrary cameral cover.
Source: DG math/0005132v3, Sections3--4/14/16 and Corollary4.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralBandTwistingModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRamificationReindexing
open CameralRegularizedHiggsModels CameralCoverDescentModels
open CameralBorelReductionModels CameralCentralizerBandModels
open CameralBandPullbackModels GroupTorsorGeometry
open ContractedTorsorModels NormalizedTorsorOperations ExpansionParameterModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori)
  (I : IncidenceAction F) (B : BorelGeometry F) (J : CentralizerGroup F)
  {X : Over (Spec (.of ℂ))} (C : Cover F X)

attribute [local instance] centralizerGroupAction

@[instance_reducible] def bandGroup : GrpObj (band F C).scheme := (band F C).group
attribute [local instance] bandGroup

abbrev Marked := CameralMarkedRegularizers.Object F I C
abbrev BandTorsor := Bundle (band F C).scheme (𝟙_ (Over X.left))

def originalPoint (H : Marked F I C) (U : Over X.left)
    (p : U ⟶ relativeTotal F I C H) :
    (Over.map X.hom).obj U ⟶ H.regularizer.torsor.total :=
  (Over.map X.hom).map p ≫ (totalIso F I C H).hom

theorem originalPoint_over (H : Marked F I C) (U : Over X.left)
    (p : U ⟶ relativeTotal F I C H) :
    originalPoint F I C H U p ≫ H.regularizer.torsor.projection =
      Over.homMk U.hom rfl := by
  apply Over.OverMorphism.ext
  simpa [originalPoint, totalIso, relativeTotal] using p.w

def evaluatedActionPoint (H : Marked F I C)
    (V : BandPullbackComparison F I B J C H) (U : Over X.left)
    (s : U ⟶ (band F C).scheme) (p : U ⟶ relativeTotal F I C H) :
    (Over.map X.hom).obj U ⟶ H.regularizer.torsor.total :=
  CartesianMonoidalCategory.lift
    (bandPairPoint F I C H U s (originalPoint F I C H U p)
      (originalPoint_over F I C H U p) ≫ bandElement F I J C H V.iso)
    (originalPoint F I C H U p) ≫ H.regularizer.torsor.action.smul

/-- The action is fixed on every actual scheme-valued band/torsor pair. -/
structure BandAction (H : Marked F I C)
    (V : BandPullbackComparison F I B J C H) where
  action : ModObj (band F C).scheme (relativeTotal F I C H)
  normalized : ∀ (U : Over X.left) (s : U ⟶ (band F C).scheme)
      (p : U ⟶ relativeTotal F I C H),
    originalPoint F I C H U (CartesianMonoidalCategory.lift s p ≫ action.smul) =
      evaluatedActionPoint F I B J C H V U s p

def relativeArrow {H H' : Marked F I C} (a : H ⟶ H') :
    relativeTotal F I C H ⟶ relativeTotal F I C H' :=
  Over.homMk a.map.iso.hom.left (congrArg Over.Hom.left a.map.over)

def inverseDiagonal (P : BandTorsor F C) (H : Marked F I C)
    {V : BandPullbackComparison F I B J C H} (A : BandAction F I B J C H V) :
    (band F C).scheme ⊗ (P.torsor.total ⊗ relativeTotal F I C H) ⟶
      P.torsor.total ⊗ relativeTotal F I C H :=
  CartesianMonoidalCategory.lift
    (((band F C).scheme ◁ fst P.torsor.total (relativeTotal F I C H)) ≫
      P.torsor.action.smul)
    (tensorHom ι[(band F C).scheme]
      (snd P.torsor.total (relativeTotal F I C H)) ≫ A.action.smul)

structure ContractedTwist (P : BandTorsor F C) (H : Marked F I C)
    {V : BandPullbackComparison F I B J C H} (A : BandAction F I B J C H V) where
  object : Marked F I C
  quotient : P.torsor.total ⊗ relativeTotal F I C H ⟶ relativeTotal F I C object
  invariant : inverseDiagonal F I B J C P H A ≫ quotient =
    snd (band F C).scheme (P.torsor.total ⊗ relativeTotal F I C H) ≫ quotient
  [flat : Flat quotient.left]
  [presentation : LocallyOfFinitePresentation quotient.left]
  [surjective : Surjective quotient.left]
  [relation : IsIso (GroupTorsorGeometry.relation (band F C).scheme
    (inverseDiagonal F I B J C P H A) quotient invariant)]
  universal : ∀ (Z : Over X.left) (f : P.torsor.total ⊗ relativeTotal F I C H ⟶ Z),
    inverseDiagonal F I B J C P H A ≫ f =
      snd (band F C).scheme (P.torsor.total ⊗ relativeTotal F I C H) ≫ f →
    ∃! g : relativeTotal F I C object ⟶ Z, quotient ≫ g = f
  sigma : ∀ (U : Over X.left) (q : U ⟶ P.torsor.total)
      (p : U ⟶ relativeTotal F I C H),
    originalPoint F I C object U (CartesianMonoidalCategory.lift q p ≫ quotient) ≫
      object.regularizer.map = originalPoint F I C H U p ≫ H.regularizer.map
  incidence : ∀ (U : Over X.left) (q : U ⟶ P.torsor.total)
      (p : U ⟶ relativeTotal F I C H)
      (c : (Over.map X.hom).obj U ⟶ total F C)
      (hp : originalPoint F I C H U p ≫ H.regularizer.torsor.projection =
        c ≫ projection F C)
      (hq : originalPoint F I C object U
          (CartesianMonoidalCategory.lift q p ≫ quotient) ≫
          object.regularizer.torsor.projection = c ≫ projection F C),
    CameralMarkedRegularizers.incidencePoint F I C object ((Over.map X.hom).obj U) c
      (originalPoint F I C object U (CartesianMonoidalCategory.lift q p ≫ quotient)) hq =
    CameralMarkedRegularizers.incidencePoint F I C H ((Over.map X.hom).obj U) c
      (originalPoint F I C H U p) hp
  group_equivariant : ∀ (U : Over X.left) (q : U ⟶ P.torsor.total)
      (p : U ⟶ relativeTotal F I C H)
      (g : (Over.map X.hom).obj U ⟶ G)
      (p' : U ⟶ relativeTotal F I C H)
      (_hp : originalPoint F I C H U p' =
        CartesianMonoidalCategory.lift g (originalPoint F I C H U p) ≫
          H.regularizer.torsor.action.smul),
    originalPoint F I C object U (CartesianMonoidalCategory.lift q p' ≫ quotient) =
      CartesianMonoidalCategory.lift g
        (originalPoint F I C object U (CartesianMonoidalCategory.lift q p ≫ quotient)) ≫
          object.regularizer.torsor.action.smul

structure BandTorsorOperations where
  tensor : TensorCalculus (band F C).scheme
  [inversionHom : IsMonHom ι[(band F C).scheme]]
  inversion : PushoutFunctor (band F C).scheme (band F C).scheme ι[(band F C).scheme]

def inverseTorsor (O : BandTorsorOperations F C) (P : BandTorsor F C) : BandTorsor F C :=
  (O.inversion.map (𝟙_ (Over X.left))).obj P

/-- Every object and arrow is pinned by the same actual contracted quotient. -/
structure TwistingGeometry where
  comparison : ∀ H : Marked F I C, BandPullbackComparison F I B J C H
  action : ∀ H : Marked F I C, BandAction F I B J C H (comparison H)
  twist : (BandTorsor F C × Marked F I C) ⥤ Marked F I C
  model : ∀ (P : BandTorsor F C) (H : Marked F I C),
    ContractedTwist F I B J C P H (action H)
  objects : ∀ (P : BandTorsor F C) (H : Marked F I C), (model P H).object = twist.obj (P, H)
  arrows : ∀ {P Q : BandTorsor F C} {H H' : Marked F I C}
      (a : P ⟶ Q) (b : H ⟶ H')
      (e : (model P H).object ⟶ (model Q H').object)
      (_he : e = eqToHom (objects P H) ≫ twist.map (a, b) ≫
        eqToHom (objects Q H').symm),
    tensorHom a.iso.hom (relativeArrow F I C b) ≫ (model Q H').quotient =
      (model P H).quotient ≫ relativeArrow F I C e

/-- Unit, tensor and inverse maps are fixed before passing to isomorphism classes. -/
structure QuotientCoherence (O : BandTorsorOperations F C)
    (T : TwistingGeometry F I B J C) where
  unit : ∀ H : Marked F I C,
    (T.model (O.tensor.unit (𝟙_ (Over X.left))).bundle H).object ≅ H
  unit_points : ∀ (H : Marked F I C) (U : Over X.left)
      (p : U ⟶ relativeTotal F I C H),
    CartesianMonoidalCategory.lift
      (unitPoint (band F C).scheme (O.tensor.unit (𝟙_ (Over X.left))) (toUnit U)) p ≫
        (T.model (O.tensor.unit (𝟙_ (Over X.left))).bundle H).quotient ≫
        relativeArrow F I C (unit H).hom = p
  tensor : ∀ (P Q : BandTorsor F C) (H : Marked F I C),
    (T.model (tensorObj (band F C).scheme O.tensor.tensor P Q) H).object ≅
      (T.model P (T.model Q H).object).object
  tensor_points : ∀ (P Q : BandTorsor F C) (H : Marked F I C)
      (U : Over X.left) (p : U ⟶ P.torsor.total) (q : U ⟶ Q.torsor.total)
      (h : p ≫ P.torsor.projection = q ≫ Q.torsor.projection)
      (r : U ⟶ relativeTotal F I C H),
    CartesianMonoidalCategory.lift
      (tensorPoint (O.tensor.tensor.model (𝟙_ (Over X.left)) P Q) p q h) r ≫
        (T.model (tensorObj (band F C).scheme O.tensor.tensor P Q) H).quotient ≫
        relativeArrow F I C (tensor P Q H).hom =
    CartesianMonoidalCategory.lift p
      (CartesianMonoidalCategory.lift q r ≫ (T.model Q H).quotient) ≫
        (T.model P (T.model Q H).object).quotient
  inverse : ∀ (P : BandTorsor F C) (H : Marked F I C),
    (T.model (inverseTorsor F C O P) (T.model P H).object).object ≅ H
  inverse_points : ∀ (P : BandTorsor F C) (H : Marked F I C)
      (U : Over X.left) (q : U ⟶ P.torsor.total)
      (p : U ⟶ relativeTotal F I C H),
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.lift q (toUnit U ≫ η[(band F C).scheme]) ≫
        (O.inversion.diagram (𝟙_ (Over X.left)) P).quotient)
      (CartesianMonoidalCategory.lift q p ≫ (T.model P H).quotient) ≫
        (T.model (inverseTorsor F C O P) (T.model P H).object).quotient ≫
        relativeArrow F I C (inverse P H).hom = p

def pairIso {D : Type _} {E : Type _} [Category D] [Category E]
    {d d' : D} {e e' : E} (a : d ≅ d') (b : e ≅ e') : (d, e) ≅ (d', e') where
  hom := (a.hom, b.hom)
  inv := (a.inv, b.inv)
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

abbrev H1 := Quotient (isIsomorphicSetoid (BandTorsor F C))
abbrev HiggsClasses := Quotient (isIsomorphicSetoid (Marked F I C))

def h1Unit (O : BandTorsorOperations F C) : H1 F C :=
  Quotient.mk _ (O.tensor.unit (𝟙_ (Over X.left))).bundle

def h1Multiply (O : BandTorsorOperations F C) : H1 F C → H1 F C → H1 F C :=
  Quotient.map₂ (fun P Q => tensorObj (band F C).scheme O.tensor.tensor P Q) (by
    intro P P' hP Q Q' hQ
    rcases hP with ⟨a⟩
    rcases hQ with ⟨b⟩
    exact ⟨tensorIso (band F C).scheme O.tensor.tensor a b⟩)

def h1Inverse (O : BandTorsorOperations F C) : H1 F C → H1 F C :=
  Quotient.map (inverseTorsor F C O) (by
    intro P Q h
    rcases h with ⟨a⟩
    exact ⟨(O.inversion.map (𝟙_ (Over X.left))).mapIso a⟩)

def twistClasses (T : TwistingGeometry F I B J C) :
    H1 F C → HiggsClasses F I C → HiggsClasses F I C :=
  Quotient.map₂ (fun P H => T.twist.obj (P, H)) (by
    intro P P' hP H H' hH
    rcases hP with ⟨a⟩
    rcases hH with ⟨b⟩
    exact ⟨T.twist.mapIso (pairIso a b)⟩)

structure H1GroupLaws (O : BandTorsorOperations F C) : Prop where
  assoc : ∀ a b c, h1Multiply F C O (h1Multiply F C O a b) c =
    h1Multiply F C O a (h1Multiply F C O b c)
  unit_left : ∀ a, h1Multiply F C O (h1Unit F C O) a = a
  unit_right : ∀ a, h1Multiply F C O a (h1Unit F C O) = a
  inverse_left : ∀ a, h1Multiply F C O (h1Inverse F C O a) a = h1Unit F C O
  commutative : ∀ a b, h1Multiply F C O a b = h1Multiply F C O b a

@[instance_reducible] def h1Group (O : BandTorsorOperations F C)
    (L : H1GroupLaws F C O) : CommGroup (H1 F C) where
  mul := h1Multiply F C O
  one := h1Unit F C O
  inv := h1Inverse F C O
  mul_assoc := L.assoc
  one_mul := L.unit_left
  mul_one := L.unit_right
  inv_mul_cancel := L.inverse_left
  mul_comm := L.commutative

/-- The source action law refers to the fixed native quotient operations. -/
structure TwistingCoherence (O : BandTorsorOperations F C)
    (T : TwistingGeometry F I B J C) : Prop where
  unit : ∀ H : HiggsClasses F I C, twistClasses F I B J C T (h1Unit F C O) H = H
  tensor : ∀ (a b : H1 F C) (H : HiggsClasses F I C),
    twistClasses F I B J C T (h1Multiply F C O a b) H =
      twistClasses F I B J C T a (twistClasses F I B J C T b H)

@[instance_reducible] def h1Action (O : BandTorsorOperations F C)
    (L : H1GroupLaws F C O) (T : TwistingGeometry F I B J C)
    (A : TwistingCoherence F I B J C O T) :
    letI := h1Group F C O L
    MulAction (H1 F C) (HiggsClasses F I C) := by
  letI := h1Group F C O L
  exact { smul := twistClasses F I B J C T, one_smul := A.unit, mul_smul := A.tensor }

/-- An actual base object supplies the nonempty fibre in Corollary4.6. -/
def SimplyTransitiveFrom (T : TwistingGeometry F I B J C) (H : Marked F I C) : Prop :=
  ∀ y : HiggsClasses F I C, ∃! a : H1 F C,
    twistClasses F I B J C T a (Quotient.mk _ H) = y

end MathlibExt.AlgebraicGeometry.CameralBandTwistingModels
