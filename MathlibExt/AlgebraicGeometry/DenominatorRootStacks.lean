/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImageFunctors
public import MathlibExt.AlgebraicGeometry.EtaleMonoidCoherence
public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry

/-!
# General denominator-root stacks with normalized family maps

The fibre over an actual scheme T is the core of the actual category of
DF extensions of the native inverse-image monoid sheaves. Restriction
uses native scheme and sheaf pullback, including the actual adjoint
composition isomorphism. The comparison squares retain the prescribed
root restriction, all local sections, tensor products and module arrows.

The fppf stack and its algebraicity are construction/proof endpoints,
with these fixed fibres and maps. Fibres can be empty. No Artin, DM,
parabolic equivalence or universal root line is assumed by the input.

Source: Niels Borne and Angelo Vistoli, *Parabolic sheaves on logarithmic
schemes*, https://arxiv.org/abs/1001.0466v2, Definitions 3.1/4.16 and
Proposition 4.19. Native scheme/sheaf inverse-image maps and adjoint
coherence use Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679
(Apache License 2.0), as credited in EtaleMonoidCoherence.lean.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DenominatorRootStacks
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootFamilies
open MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImages
open MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImageFunctors
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
open MathlibExt.AlgebraicGeometry.MonoidSheafCharts

universe u

/-- The trivial-kernel condition. Every `Structure` satisfies it (`isDeligneFaltings`), since
its charts are Deligne--Faltings charts. -/
def IsDeligneFaltings {X : Scheme.{u}}
    {A : DeligneFaltingsSheaves.MonoidSheaf X} (D : Structure A) : Prop :=
  ∀ (U : X.Etale) (a : A.obj.obj (op U)), IsIso ((D.chart U).sectionMap a) → a = 1

/-- Every structure satisfies the trivial-kernel condition. -/
theorem isDeligneFaltings {X : Scheme.{u}}
    {A : DeligneFaltingsSheaves.MonoidSheaf X} (D : Structure A) : IsDeligneFaltings D :=
  fun U a h => (D.chart U).trivial_kernel a ⟨(asIso ((D.chart U).sectionMap a)).symm, by simp⟩

variable [∀ (T X : Scheme.{u}) (f : T ⟶ X), HasInverseImage f]

/-- Implementations of the fixed native DF inverse-image functors. -/
abbrev NativeDFImages := ∀ (T X : Scheme.{u}) (f : T ⟶ X)
  (A : DeligneFaltingsSheaves.MonoidSheaf X), InverseImageFunctor f A

variable {X : Scheme.{u}} (I : NativeDFImages.{u})
  {A B : DeligneFaltingsSheaves.MonoidSheaf X} (D : Structure A) (j : A ⟶ B)

abbrev pulledMonoids (T : Over X) (M : DeligneFaltingsSheaves.MonoidSheaf X) :=
  (monoidPullback T.hom).obj M

abbrev pulledStructure (T : Over X) := (I T.left X T.hom A).object D |>.pulled

abbrev rootsAt (T : Over X) :=
  RootFibre ((monoidPullback T.hom).map j) (pulledStructure I D T)

/-- The actual change from iterated to direct inverse-image monoids over X. -/
def monoidOverComparison (M : DeligneFaltingsSheaves.MonoidSheaf X)
    {T U : Over X} (f : T ⟶ U) :
    (monoidPullback f.left).obj (pulledMonoids U M) ≅ pulledMonoids T M :=
  (EtaleMonoidCoherence.composition f.left U.hom).app M ≪≫
    eqToIso (congrArg (fun h => (monoidPullback h).obj M) (Over.w f))

/-- The matching literal comparison of iterated and direct small-etale schemes. -/
def siteOverComparison {T U : Over X} (f : T ⟶ U) (V : X.Etale) :
    (etaleBaseChange f.left).obj ((etaleBaseChange U.hom).obj V) ≅
      (etaleBaseChange T.hom).obj V :=
  (EtaleBaseChangeCoherence.composition f.left U.hom).app V ≪≫
    (eqToIso (congrArg etaleBaseChange (Over.w f))).app V

/-- The direct and iterated native DF pullbacks are compared on every
original line/section generator, not by an arbitrary base identification. -/
structure OverCompositionNormalization {T U : Over X} (f : T ⟶ U)
    (c : ComparisonAlong (monoidOverComparison A f).hom
      ((I T.left U.left f.left (pulledMonoids U A)).object
        (pulledStructure I D U)).pulled (pulledStructure I D T)) where
  projection_eq : ∀ V : X.Etale,
    projection f.left ((etaleBaseChange U.hom).obj V) ≫ projection U.hom V =
      (siteOverComparison f V).hom.left ≫ projection T.hom V
  generator_eq : ∀ (V : X.Etale) (a : A.obj.obj (op V)),
    (monoidOverComparison A f).hom.hom.app
      (op ((etaleBaseChange f.left).obj ((etaleBaseChange U.hom).obj V)))
      (generator f.left (pulledMonoids U A) ((etaleBaseChange U.hom).obj V)
        (generator U.hom A V a)) =
    (pulledMonoids T A).obj.map (siteOverComparison f V).hom.op (generator T.hom A V a)
  normalization : ∀ (V : X.Etale) (a : A.obj.obj (op V)),
    (Scheme.Modules.pullback (projection f.left ((etaleBaseChange U.hom).obj V))).map
      (((I U.left X U.hom A).object D).comparison V a).hom ≫
      (((I T.left U.left f.left (pulledMonoids U A)).object
        (pulledStructure I D U)).comparison ((etaleBaseChange U.hom).obj V)
          (generator U.hom A V a)).hom ≫
      (c.comparison ((etaleBaseChange f.left).obj ((etaleBaseChange U.hom).obj V))
        (generator f.left (pulledMonoids U A) ((etaleBaseChange U.hom).obj V)
          (generator U.hom A V a))).hom =
    (Scheme.Modules.pullbackComp (projection f.left ((etaleBaseChange U.hom).obj V))
      (projection U.hom V)).hom.app ((D.chart V).module a) ≫
      eqToHom (congrArg (fun h => (Scheme.Modules.pullback h).obj ((D.chart V).module a))
        (projection_eq V)) ≫
      (Scheme.Modules.pullbackComp (siteOverComparison f V).hom.left
        (projection T.hom V)).inv.app ((D.chart V).module a) ≫
      (Scheme.Modules.pullback (siteOverComparison f V).hom.left).map
        (((I T.left X T.hom A).object D).comparison V a).hom ≫
      ((pulledStructure I D T).reindex (siteOverComparison f V).hom
        (generator T.hom A V a)).hom ≫
      eqToHom (congrArg ((pulledStructure I D T).chart
        ((etaleBaseChange f.left).obj ((etaleBaseChange U.hom).obj V))).module
          (generator_eq V a).symm)

/-- Pulling a comparison along a monoid map must preserve every actual generator. -/
structure PullbackComparison {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {M N : DeligneFaltingsSheaves.MonoidSheaf Z} (k : M ⟶ N)
    (P : Structure M) (Q : Structure N) (h : ComparisonAlong k P Q) where
  comparison : ComparisonAlong ((monoidPullback f).map k)
    ((I Y Z f M).object P).pulled ((I Y Z f N).object Q).pulled
  generator_map : ∀ (U : Z.Etale) (a : M.obj.obj (op U)),
    ((monoidPullback f).map k).hom.app (op ((etaleBaseChange f).obj U))
      (generator f M U a) = generator f N U (k.hom.app (op U) a)
  normalization : ∀ (U : Z.Etale) (a : M.obj.obj (op U)),
    (Scheme.Modules.pullback (projection f U)).map (h.comparison U a).hom ≫
      (((I Y Z f N).object Q).comparison U (k.hom.app (op U) a)).hom =
    (((I Y Z f M).object P).comparison U a).hom ≫
      (comparison.comparison ((etaleBaseChange f).obj U) (generator f M U a)).hom ≫
      eqToHom (congrArg (((I Y Z f N).object Q).pulled.chart
        ((etaleBaseChange f).obj U)).module (generator_map U a))

/-- A literal commuting square of DF comparisons on all local generators. -/
def ComparisonSquare {Y : Scheme.{u}}
    {M N M' N' : DeligneFaltingsSheaves.MonoidSheaf Y}
    {k : M ⟶ N} {k' : M' ⟶ N'} {l : M ⟶ M'} {r : N ⟶ N'}
    {P : Structure M} {Q : Structure N} {P' : Structure M'} {Q' : Structure N'}
    (h : ComparisonAlong k P Q) (h' : ComparisonAlong k' P' Q')
    (a : ComparisonAlong l P P') (b : ComparisonAlong r Q Q') : Prop :=
  ∃ e : l ≫ k' = k ≫ r,
    ∀ (U : Y.Etale) (m : M.obj.obj (op U)),
      (a.comparison U m).hom ≫ (h'.comparison U (l.hom.app (op U) m)).hom =
      (h.comparison U m).hom ≫ (b.comparison U (k.hom.app (op U) m)).hom ≫
        eqToHom (congrArg ((Q'.chart U).module)
          ((ConcreteCategory.congr_hom (congrArg (fun s => s.hom.app (op U)) e) m).symm))

/-- Actual root-family restriction, including the preserved original DF comparison. -/
structure RootReindexing {T U : Over X} (f : T ⟶ U) where
  functor : rootsAt I D j U ⥤ rootsAt I D j T
  baseComparison : ComparisonAlong (monoidOverComparison A f).hom
    ((I T.left U.left f.left (pulledMonoids U A)).object
      (pulledStructure I D U)).pulled (pulledStructure I D T)
  base_normalization : OverCompositionNormalization I D f baseComparison
  rootComparison : ∀ E : rootsAt I D j U,
    ComparisonAlong (monoidOverComparison B f).hom
      ((I T.left U.left f.left (pulledMonoids U B)).object E.of.extended).pulled
      (functor.obj E).of.extended
  pulledRestriction : ∀ E : rootsAt I D j U,
    PullbackComparison I f.left ((monoidPullback U.hom).map j)
      (pulledStructure I D U) E.of.extended E.of.restriction
  restriction_square : ∀ E : rootsAt I D j U,
    ComparisonSquare (pulledRestriction E).comparison (functor.obj E).of.restriction
      baseComparison (rootComparison E)
  map_normalization : ∀ {E F : rootsAt I D j U} (h : E ⟶ F)
      (V : T.left.Etale) (b : ((monoidPullback f.left).obj (pulledMonoids U B)).obj.obj (op V)),
    (((I T.left U.left f.left (pulledMonoids U B)).map h.iso.hom.hom).comparison V b).hom ≫
      ((rootComparison F).comparison V b).hom =
    ((rootComparison E).comparison V b).hom ≫
      (((functor.map h).iso.hom.hom).comparison V
        ((monoidOverComparison B f).hom.hom.app (op V) b)).hom

/-- The actual root stack after arbitrary parameter-scheme base change b:Y→X. -/
structure Model {Y : Scheme.{u}} (b : Y ⟶ X) where
  stack : GeneralStackGeometry.RelativeStack Y
  fibre : ∀ T : Over Y, stack.Fibre T ≌ rootsAt I D j ((Over.map b).obj T)
  reindexing : ∀ {T U : Over Y} (f : T ⟶ U),
    RootReindexing I D j ((Over.map b).map f)
  mapComparison : ∀ {T U : Over Y} (f : T ⟶ U),
    (stack.toPseudofunctor.map f.op.toLoc).toFunctor ⋙ (fibre T).functor ≅
      (fibre U).functor ⋙ (reindexing f).functor
  identity : ∀ T : Over Y, (reindexing (𝟙 T)).functor ≅ 𝟭 _
  composition : ∀ {T U V : Over Y} (f : T ⟶ U) (g : U ⟶ V),
    (reindexing g).functor ⋙ (reindexing f).functor ≅ (reindexing (f ≫ g)).functor
  identity_normalization : ∀ (T : Over Y) (E : stack.Fibre T),
    (mapComparison (𝟙 T)).hom.app E ≫ (identity T).hom.app ((fibre T).functor.obj E) =
      (fibre T).functor.map
        ((Cat.Hom.toNatIso (stack.toPseudofunctor.mapId (.mk (op T)))).hom.app E)
  composition_normalization : ∀ {T U V : Over Y} (f : T ⟶ U) (g : U ⟶ V)
      (E : stack.Fibre V),
    (mapComparison (f ≫ g)).hom.app E =
      (fibre T).functor.map
        ((Cat.Hom.toNatIso (stack.toPseudofunctor.mapComp g.op.toLoc f.op.toLoc)).hom.app E) ≫
      (mapComparison f).hom.app ((stack.toPseudofunctor.map g.op.toLoc).toFunctor.obj E) ≫
      (reindexing f).functor.map ((mapComparison g).hom.app E) ≫
      (composition f g).hom.app ((fibre V).functor.obj E)

/-- A local power condition for the DM conclusion, not needed for the parabolic equivalence:
a multiple of each section of `B`, with an exponent invertible locally, comes from `A`. This is
a sufficient condition, stronger than Borne--Vistoli's criterion (Proposition 4.19: the order of
`B_x^gp / A_x^gp` is invertible at every geometric point), and differs from it for unsaturated
denominator systems. -/
def PrimeToCharacteristics (k : A ⟶ B) : Prop :=
  ∀ (U : X.Etale) (b : B.obj.obj (op U)),
    ∃ (J : Type u) (V : J → X.Etale) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
      ∀ i, ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ((V i).left, ⊤)) ∧
        ∃ a : A.obj.obj (op (V i)), k.hom.app (op (V i)) a = (B.obj.map (f i).op b) ^ n

end MathlibExt.AlgebraicGeometry.DenominatorRootStacks
