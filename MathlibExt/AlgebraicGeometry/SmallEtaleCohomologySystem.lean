/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleTateRestriction
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Functorial actual torsion cohomology and localization cone models

All cohomology objects are the fixed native small-étale RΓ of the actual
Tate coefficient sheaf. Universal source assumptions record completed
sheafification/derived-existence and geometric-morphism integration.
Coefficient maps and RΓ composition are the normalized source diagrams.

A localization model is an actual cochain representative of those fixed
objects, and its arrow represents the computed restriction. Its cone
and connecting map are native mappingCone constructions. No cohomology
group, localization arrow or residual carrier is freely supplied.

Sources: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
EtaleCohomology/KummerTheory and derived functoriality (Apache 2.0).
Primary reference: Schreieder, arXiv1801.05397v5, §2.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleDerivedCohomology
open MathlibExt.AlgebraicGeometry.SmallEtaleKummerFunctoriality
open MathlibExt.AlgebraicGeometry.SmallEtaleTateRestriction
attribute [local instance] HasDerivedCategory.standard

class AllSheafificationSources : Prop where
  source : ∀ X : Scheme.{0}, HasWeakSheafify X.smallEtaleTopology (ModuleCat.{1} Scalar)
attribute [instance] AllSheafificationSources.source
variable [AllSheafificationSources]

class AllContinuousSources : Prop where
  source : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X),
    (baseChange f).IsContinuous X.smallEtaleTopology Y.smallEtaleTopology
attribute [instance] AllContinuousSources.source
variable [AllContinuousSources]

class AllDerivedSectionsSources : Prop where
  source : ∀ X : Scheme.{0}, HasDerivedSections X
attribute [instance] AllDerivedSectionsSources.source
variable [AllDerivedSectionsSources]

class AllDerivedPushSources : Prop where
  source : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), HasDerivedPushforward f
attribute [instance] AllDerivedPushSources.source
variable [AllDerivedPushSources]

/-- Data for étale cohomology with coefficients in the Tate twists $\mu_l^{\otimes j}$ and its
restriction maps, for $l \in \mathbb{N}$, assuming for all schemes and morphisms that sheafification
exists on small étale sites, that étale base change is continuous, and that derived global sections
and derived direct images exist. For every scheme $X$: $\mathbb{G}_m$ is a sheaf on the small étale
site of $X$. For every morphism $f : Y \to X$: $f_*$ preserves the kernel $\mu_l$ of the $l$-th
power map of $\mathbb{G}_m$ on $Y$; maps $\mu_l^{\otimes j} \to f_* \mu_l^{\otimes j}$ for all $j$,
given on generators (the canonical map of constant sheaves $\mathbb{Z}/l$ for $j = 0$, restriction
of roots of unity for $j = 1$, tensor products of these for $j \ge 2$); an isomorphism from the
base change of the terminal étale $X$-scheme to the terminal étale $Y$-scheme; the isomorphism
$\Gamma(X, f_* F) \cong \Gamma(Y, F)$, natural in $F$, that it induces; and an isomorphism
$R\Gamma(X, Rf_* K) \cong R\Gamma(Y, K)$, natural in $K$, compatible with the units of the derived
functors. -/
structure Data (l : ℕ) where
  gm : ∀ X : Scheme.{0}, MultiplicativeNormalization X
  kernel : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X),
    IsIso (kernelComparison (powerMap Y (gm Y) l) (pushforward f))
  tate : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X),
    TatePushforward f (gm X) (gm Y) l (kernel f)
  terminal : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), TerminalComparison f
  sections : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), SectionsPushforward f (terminal f)
  derived : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), DerivedSectionsPushforward f (sections f)

namespace Data
variable {l : ℕ} (S : Data l)

abbrev coefficient (X : Scheme.{0}) (j : ℕ) := tateTwist X (S.gm X) l j

abbrev H (X : Scheme.{0}) (i : ℤ) (j : ℕ) :=
  SmallEtaleDerivedCohomology.Cohomology X (S.coefficient X j) i

def restriction {Y X : Scheme.{0}} (f : Y ⟶ X) (i : ℤ) (j : ℕ) :
    S.H X i j →+ S.H Y i j :=
  SmallEtaleTateRestriction.restriction f (S.derived f) ((S.tate f).map j) i

def restrictionObject {Y X : Scheme.{0}} (f : Y ⟶ X) (j : ℕ) :
    globalObject X (S.coefficient X j) ⟶ globalObject Y (S.coefficient Y j) :=
  derivedRestriction f (S.derived f) ((S.tate f).map j)

end Data

/-- Functoriality proofs on the computed source maps, without changing any carrier or operator. -/
structure System (l : ℕ) extends Data l where
  identity : ∀ (X : Scheme.{0}) (i : ℤ) (j : ℕ) (a : toData.H X i j),
    toData.restriction (𝟙 X) i j a = a
  composition : ∀ {Z Y X : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y) (i : ℤ) (j : ℕ)
    (a : toData.H X i j),
    toData.restriction g i j (toData.restriction f i j a) =
      toData.restriction (g ≫ f) i j a

/-- Cochain representatives of the actual localization arrow, with its quotient map fixed. -/
structure LocalizationModel {l : ℕ} (S : Data l) {Y X : Scheme.{0}} (f : Y ⟶ X) (j : ℕ) where
  source : CochainComplex (ModuleCat.{1} Scalar) ℤ
  target : CochainComplex (ModuleCat.{1} Scalar) ℤ
  sourceIso : DerivedCategory.Q.obj source ≅ globalObject X (S.coefficient X j)
  targetIso : DerivedCategory.Q.obj target ≅ globalObject Y (S.coefficient Y j)
  map : source ⟶ target
  normalized : DerivedCategory.Q.map map =
    sourceIso.hom ≫ S.restrictionObject f j ≫ targetIso.inv

def localizationCone {l : ℕ} {S : Data l} {Y X : Scheme.{0}} {f : Y ⟶ X} {j : ℕ}
    (M : LocalizationModel S f j) := CochainComplex.mappingCone M.map

/-- Native localization connecting arrow from the fixed generic-fibre RΓ object. -/
def coneBoundary {l : ℕ} {S : Data l} {Y X : Scheme.{0}} {f : Y ⟶ X} {j : ℕ}
    (M : LocalizationModel S f j) :
    globalObject Y (S.coefficient Y j) ⟶ DerivedCategory.Q.obj (localizationCone M) :=
  M.targetIso.inv ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.inr M.map)

end MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
