/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleKummerFunctoriality

/-!
# Normalized Tate coefficient and derived restriction maps

Tate coefficient maps are fixed by the actual constant coefficient unit,
the actual Kummer kernel map, and every pure tensor before sheafification.
The ordinary global-section comparison is evaluation along the actual
terminal base-change isomorphism. The derived comparison is normalized
on every cochain by both native derived units.

Restriction is then computed from the coefficient map, native single
comparison, derived pushforward unit and normalized RΓ composition.
No field cohomology carrier or restriction operator is freely supplied.
Generic Tate functoriality, sheafification and Leray composition are
completed source integration, not newly requested generic laws.

Sources: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
AlgebraicGeometry/EtaleCohomology/KummerTheory and sheaf cohomology
functoriality (Apache 2.0); Stacks étale cohomology.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmallEtaleTateRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleDerivedCohomology
open MathlibExt.AlgebraicGeometry.SmallEtaleKummerFunctoriality
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

abbrev FiniteCoefficient (l : ℕ) := ULift.{1} (ZMod l)

instance finiteCoefficientModule (l : ℕ) : Module Scalar (FiniteCoefficient l) :=
  Module.compHom _ (ULift.ringEquiv : Scalar ≃+* ℤ).toRingHom

variable {Y X : Scheme.{0}} (f : Y ⟶ X)
  [(baseChange f).IsContinuous X.smallEtaleTopology Y.smallEtaleTopology]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{1} Scalar)]
  [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{1} Scalar)]

/-- Actual base-change terminal isomorphism, unique because its target is terminal. -/
structure TerminalComparison where
  comparison : (baseChange f).obj (⊤_ X.Etale) ≅ ⊤_ Y.Etale

/-- Actual coefficient restrictions; all maps are fixed on their sheafification generators. -/
structure TatePushforward (GX : MultiplicativeNormalization X)
    (GY : MultiplicativeNormalization Y) (l : ℕ)
    (h : IsIso (kernelComparison (powerMap Y GY l) (pushforward f))) where
  map : ∀ j : ℕ, tateTwist X GX l j ⟶ (pushforward f).obj (tateTwist Y GY l j)
  zero_normalized : ∀ (U : X.Etaleᵒᵖ) (a : FiniteCoefficient l),
    (map 0).hom.app U
      ((((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{1} Scalar)).unit.app
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of Scalar (FiniteCoefficient l)))).app U) a) =
    (((sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{1} Scalar)).unit.app
      ((Functor.const Y.Etaleᵒᵖ).obj (ModuleCat.of Scalar (FiniteCoefficient l)))).app
        ((baseChange f).op.obj U)) a
  one_normalized : map 1 = rootsPushforward f GX GY l h
  tensor_normalized : ∀ (j : ℕ) (U : X.Etaleᵒᵖ)
    (a : (tateTwist X GX l (j+1)).obj.obj U) (b : (rootsSheaf X GX l).obj.obj U),
    (map (j+2)).hom.app U
      ((((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{1} Scalar)).unit.app
        ((tateTwist X GX l (j+1)).obj ⊗ (rootsSheaf X GX l).obj)).app U)
          (a ⊗ₜ[Scalar] b)) =
    (((sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{1} Scalar)).unit.app
      ((tateTwist Y GY l (j+1)).obj ⊗ (rootsSheaf Y GY l).obj)).app
        ((baseChange f).op.obj U))
      (((map (j+1)).hom.app U a) ⊗ₜ[Scalar]
        ((rootsPushforward f GX GY l h).hom.app U b))

/-- Global sections of a pushforward are evaluated through the actual terminal comparison. -/
structure SectionsPushforward (T : TerminalComparison f) where
  comparison : pushforward f ⋙ sections X ≅ sections Y
  normalized : ∀ F : Coefficients Y,
    comparison.hom.app F = F.obj.map T.comparison.inv.op

/-- The actual cochain direct-image source. -/
def pushSource : Cochains Y ⥤ D X :=
  (pushforward f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

class HasDerivedPushforward : Prop where
  existsDerived : (pushSource f).HasRightDerivedFunctor (quasiIso Y)

attribute [instance] HasDerivedPushforward.existsDerived
variable [HasDerivedPushforward f]

/-- Native derived direct image of the actual continuous coefficient functor. -/
def derivedPush : D Y ⥤ D X :=
  (pushSource f).totalRightDerived DerivedCategory.Q (quasiIso Y)

def pushUnit : pushSource f ⟶ DerivedCategory.Q ⋙ derivedPush f :=
  (pushSource f).totalRightDerivedUnit DerivedCategory.Q (quasiIso Y)

/-- Ordinary cochain global-section comparison, computed degreewise from the fixed map. -/
def cochainSectionsIso {T : TerminalComparison f} (S : SectionsPushforward f T)
    (K : Cochains Y) :
    ((sections X).mapHomologicalComplex (.up ℤ)).obj
      (((pushforward f).mapHomologicalComplex (.up ℤ)).obj K) ≅
        ((sections Y).mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun j => S.comparison.app (K.X j))
    (fun i j _ => (S.comparison.hom.naturality (K.d i j)).symm)

variable [HasDerivedSections X] [HasDerivedSections Y]

/-- Actual composite derived unit before applying a Leray comparison. -/
def compositeUnit {T : TerminalComparison f} (S : SectionsPushforward f T) (K : Cochains Y) :
    (sectionsSource Y).obj K ⟶
      (derivedSections X).obj ((derivedPush f).obj (DerivedCategory.Q.obj K)) :=
  DerivedCategory.Q.map (cochainSectionsIso f S K).inv ≫
    (derivedSectionsUnit X).app (((pushforward f).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (derivedSections X).map ((pushUnit f).app K)

/-- A Leray isomorphism $R\Gamma(X, -) \circ Rf_* \cong R\Gamma(Y, -)$ for a morphism of schemes
$f : Y \to X$, on derived categories of étale sheaves of abelian groups on the small étale sites
(the derived functors being assumed to exist), normalized on every cochain complex $K$ on $Y$: its
component at $QK$, precomposed with the composite
$Q\Gamma(Y, K) \to Q\Gamma(X, f_*K) \to R\Gamma(X, Q(f_*K)) \to R\Gamma(X, Rf_*(QK))$
(`compositeUnit`: the inverse of the comparison `S` of global sections, then the canonical maps of
the derived functors), is the canonical map $Q\Gamma(Y, K) \to R\Gamma(Y, QK)$. Here $Q$ is the
localization functor and $f_*$, $\Gamma$ act termwise. -/
structure DerivedSectionsPushforward {T : TerminalComparison f} (S : SectionsPushforward f T) where
  comparison : derivedPush f ⋙ derivedSections X ≅ derivedSections Y
  normalized : ∀ K : Cochains Y,
    compositeUnit f S K ≫ comparison.hom.app (DerivedCategory.Q.obj K) =
      (derivedSectionsUnit Y).app K

/-- The coefficient arrow into derived pushforward is the native single map and derived unit. -/
def coefficientDerivedMap {A : Coefficients X} {B : Coefficients Y}
    (β : A ⟶ (pushforward f).obj B) :
    (DerivedCategory.singleFunctor (Coefficients X) 0).obj A ⟶
      (derivedPush f).obj ((DerivedCategory.singleFunctor (Coefficients Y) 0).obj B) :=
  (DerivedCategory.singleFunctor (Coefficients X) 0).map β ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (pushforward f) (.up ℤ) 0).inv.app B) ≫
      (pushUnit f).app ((CochainComplex.singleFunctor (Coefficients Y) 0).obj B)

/-- Derived restriction fixed by the actual coefficient and native unit diagrams. -/
def derivedRestriction {T : TerminalComparison f} {S : SectionsPushforward f T}
    (P : DerivedSectionsPushforward f S) {A : Coefficients X} {B : Coefficients Y}
    (β : A ⟶ (pushforward f).obj B) : globalObject X A ⟶ globalObject Y B :=
  (derivedSections X).map (coefficientDerivedMap f β) ≫
    P.comparison.hom.app ((DerivedCategory.singleFunctor (Coefficients Y) 0).obj B)

/-- Actual cohomology restriction, by postcomposition with that computed derived arrow. -/
def restriction {T : TerminalComparison f} {S : SectionsPushforward f T}
    (P : DerivedSectionsPushforward f S) {A : Coefficients X} {B : Coefficients Y}
    (β : A ⟶ (pushforward f).obj B) (i : ℤ) :
    SmallEtaleDerivedCohomology.Cohomology X A i →+
      SmallEtaleDerivedCohomology.Cohomology Y B i where
  toFun e := e ≫ derivedRestriction f P β
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

end MathlibExt.AlgebraicGeometry.SmallEtaleTateRestriction
