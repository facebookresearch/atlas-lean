/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Actual signed Tate coefficient sheaves

Negative twists are the actual internal module-Hom from the positive
Tate tensor coefficient to the constant Z/l coefficient. Both are
l-torsion, so integer-linearity is the same as Z/l-linearity.
The internal Hom is the native enriched presheaf Hom, which is a sheaf.

This supplies coefficients in every integer twist without selecting a
root of unity or a new cohomology carrier. Generic dual pullback and
coefficient functoriality remain completed source-integration inputs;
the existing generic RΓ restriction/transfer constructors apply to
these actual coefficient objects.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.SmallEtaleSignedTateCoefficients

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Enriched.FunctorCategory
open scoped CategoryTheory.MonoidalClosed
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleDerivedCohomology
open MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem

variable [AllSheafificationSources] [AllContinuousSources]
  [AllDerivedSectionsSources] [AllDerivedPushSources]

/-- Native sheaf of integer-module Hom, using its actual slice-wise enriched presheaf. -/
def coefficientHom (X : Scheme.{0}) (F G : Coefficients X) : Coefficients X :=
  ⟨functorEnrichedHom (ModuleCat.{1} Scalar) F.obj G.obj,
    Presheaf.isSheaf_functorEnrichedHom F.obj G.obj G.property⟩

def signedTwist {l : ℕ} (S : Data l) (X : Scheme.{0}) : ℤ → Coefficients X
  | .ofNat j => S.coefficient X j
  | .negSucc j => coefficientHom X (S.coefficient X (j+1)) (S.coefficient X 0)

/-- Actual derived cohomology of the signed Tate coefficient, on the same fixed RΓ. -/
abbrev Cohomology {l : ℕ} (S : Data l) (X : Scheme.{0}) (i j : ℤ) :=
  SmallEtaleDerivedCohomology.Cohomology X (signedTwist S X j) i


/-- Actual evaluation of a local internal Hom section at a local coefficient section. -/
def localHomEvaluation (X : Scheme.{0}) (F G : Coefficients X) (U : X.Etaleᵒᵖ)
    (φ : (coefficientHom X F G).obj.obj U) (a : F.obj.obj U) : G.obj.obj U :=
  ((enrichedHomπ (ModuleCat.{1} Scalar)
    (Under.forget U ⋙ F.obj) (Under.forget U ⋙ G.obj) (Under.mk (𝟙 U))).hom φ).hom a

/-- A pullback map on a negative Tate twist along a morphism of schemes $f : Y \to X$, for the given
Tate data `S` and $j \in \mathbb{N}$: a map from the twist $\mathbb{Z}/l(-(j+1))$ on $X$, the
internal Hom from $\mathbb{Z}/l(j+1)$ to $\mathbb{Z}/l(0)$ (`signedTwist`), to the direct image
under $f$ of the same twist on $Y$, compatible with evaluation: for every étale $U \to X$, every
section $\varphi$ of $\mathbb{Z}/l(-(j+1))$ and every section $a$ of $\mathbb{Z}/l(j+1)$ over $U$,
the image of $\varphi$, evaluated over $U \times_X Y$ at the pullback of $a$, is the pullback of
$\varphi(a)$, the pullbacks being the Tate maps `S.tate f`. -/
structure NegativePullback {l : ℕ} (S : Data l) {Y X : Scheme.{0}} (f : Y ⟶ X) (j : ℕ) where
  map : signedTwist S X (.negSucc j) ⟶
    (SmallEtaleKummerFunctoriality.pushforward f).obj (signedTwist S Y (.negSucc j))
  normalized : ∀ (U : X.Etaleᵒᵖ)
    (φ : (signedTwist S X (.negSucc j)).obj.obj U)
    (a : (S.coefficient X (j+1)).obj.obj U),
    localHomEvaluation Y (S.coefficient Y (j+1)) (S.coefficient Y 0)
      ((SmallEtaleKummerFunctoriality.baseChange f).op.obj U) ((map.hom.app U) φ)
        (((S.tate f).map (j+1)).hom.app U a) =
    (((S.tate f).map 0).hom.app U)
      (localHomEvaluation X (S.coefficient X (j+1)) (S.coefficient X 0) U φ a)

/-- Signed Tate maps on the actual coefficient-invertible schemes.
The negative maps are constrained by the actual Hom/evaluation square. -/
structure SignedMaps {l : ℕ} (S : Data l) where
  negative : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X),
    IsUnit (l : Γ(X, ⊤)) → IsUnit (l : Γ(Y, ⊤)) → ∀ j, NegativePullback S f j

def SignedMaps.coefficientMap {l : ℕ} {S : Data l} (D : SignedMaps S)
    {Y X : Scheme.{0}} (f : Y ⟶ X)
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤))) :
    (j : ℤ) → signedTwist S X j ⟶
      (SmallEtaleKummerFunctoriality.pushforward f).obj (signedTwist S Y j)
  | .ofNat j => (S.tate f).map j
  | .negSucc j => (D.negative f hX hY j).map

/-- The signed restriction uses the same native coefficient/derived-unit construction. -/
def SignedMaps.restriction {l : ℕ} {S : Data l} (D : SignedMaps S)
    {Y X : Scheme.{0}} (f : Y ⟶ X)
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤))) (i j : ℤ) :
    Cohomology S X i j →+ Cohomology S Y i j :=
  SmallEtaleTateRestriction.restriction f (S.derived f) (D.coefficientMap f hX hY j) i

end MathlibExt.AlgebraicGeometry.SmallEtaleSignedTateCoefficients
