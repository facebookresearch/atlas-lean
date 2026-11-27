/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineCriticalKernelModels
public import MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# Actual smooth critical charts and coefficient-function sheaves

The ambient scheme is any smooth scheme over the coefficient field. Its
critical ideal is fixed on every affine open by all linear evaluations
of the actual universal differential. Quotient presentations and chart
refinements keep the actual scheme embeddings, including nilpotents.
Function sheaves are the native structure modules with scalars restricted
along the actual structure morphism; no O-linear derivative is asserted.

Reference: Joyce, arXiv:1304.4508v3, Theorem 2.1 and Definition 2.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CriticalSchemeCharts

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open AlgebraicDifferentialSheaves CoherentCurveLinearSeries

variable {k : Type} [Field k]

/-- The actual coefficient-valued structure sheaf on all Zariski opens. -/
def coefficientFunctions (X : Over (Spec (.of k))) :
    Sheaf (Opens.grothendieckTopology X.left) (ModuleCat k) :=
  (sheafCompose _ (ModuleCat.restrictScalars (globalScalarMap X.hom))).obj
    ((SheafOfModules.forgetToSheafModuleCat X.left.ringCatSheaf (op ⊤)
      isTerminalTop.op).obj (structureModule X.left))

/-- The genuine reduction, not the set of closed or field-valued points. -/
abbrev reduction (X : Scheme) : Scheme :=
  ((⊥ : X.IdealSheafData).radical).subscheme

def reductionMap (X : Scheme) : reduction X ⟶ X :=
  ((⊥ : X.IdealSheafData).radical).subschemeι

/-- Arbitrary affine embeddings use every smooth coefficient algebra. -/
structure AffineEmbedding (X : Over (Spec (.of k))) where
  domain : X.left.Opens
  algebra : CommAlgCat k
  smooth : Algebra.Smooth k algebra
  ideal : Ideal algebra
  inclusion : Over.mk (domain.ι ≫ X.hom) ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k algebra)))
  [closed : IsClosedImmersion inclusion.left]
  quotientIso : domain.toScheme ≅ Spec (.of (algebra ⧸ ideal))
  quotient_square : quotientIso.hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ideal)) = inclusion.left

attribute [instance] AffineEmbedding.closed

/-- The actual open/refinement square determines the coefficient map. -/
structure AffineRefinement {X : Over (Spec (.of k))} (E F : AffineEmbedding X) where
  domain_le : F.domain ≤ E.domain
  algebraMap : E.algebra →ₐ[k] F.algebra
  ideal_map : E.ideal.map algebraMap.toRingHom ≤ F.ideal
  embedding_square : F.inclusion.left ≫ Spec.map (CommRingCat.ofHom algebraMap.toRingHom) =
    X.left.homOfLE domain_le ≫ E.inclusion.left

/-- The actual ambient function restricted to the embedded open scheme. -/
def embeddedFunction {X : Over (Spec (.of k))} (E : AffineEmbedding X)
    (f : E.algebra) : Γ(X.left,E.domain) :=
  E.domain.topIso.hom.hom
    (E.inclusion.left.appTop.hom ((Scheme.ΓSpecIso (.of E.algebra)).inv.hom f))

/-- The regular function df is tested against every actual cotangent dual. -/
def zeroDifferentialIdeal (P : CommAlgCat k) (f : P) : Ideal P :=
  Ideal.span (Set.range fun l : Ω[P⁄k] →ₗ[P] P => l (KaehlerDifferential.D k P f))

/-- A chart can have a non-affine smooth ambient scheme. Its image ideal
is the zero scheme of df on every affine ambient open. -/
structure CriticalChart (X : Over (Spec (.of k))) where
  domain : X.left.Opens
  ambient : Over (Spec (.of k))
  [smooth : Smooth ambient.hom]
  function : Γ(ambient.left, ⊤)
  inclusion : Over.mk (domain.ι ≫ X.hom) ⟶ ambient
  [closed : IsClosedImmersion inclusion.left]
  critical : ∀ U : ambient.left.affineOpens,
    letI : Algebra k Γ(ambient.left,U) :=
      ((scalarMap k ambient).app (op U.1)).hom.toAlgebra
    inclusion.left.ker.ideal U =
      Ideal.span (Set.range fun l : Ω[Γ(ambient.left,U)⁄k] →ₗ[Γ(ambient.left,U)]
        Γ(ambient.left,U) => l (KaehlerDifferential.D k Γ(ambient.left,U)
          ((ambient.left.presheaf.map (homOfLE le_top).op).hom function)))

attribute [instance] CriticalChart.smooth CriticalChart.closed

/-- Refinements retain the actual embedding, restriction and function. The ambient map
is a locally closed immersion (Joyce, Definition 2.18), so restrictions of a chart to
open subcharts are refinements. -/
structure ChartRefinement {X : Over (Spec (.of k))} (E F : CriticalChart X) where
  domain_le : E.domain ≤ F.domain
  ambientMap : E.ambient ⟶ F.ambient
  [immersion : IsImmersion ambientMap.left]
  embedding_square : E.inclusion.left ≫ ambientMap.left =
    X.left.homOfLE domain_le ≫ F.inclusion.left
  function_eq : (ambientMap.left.appTop).hom F.function = E.function

attribute [instance] ChartRefinement.immersion

end MathlibExt.AlgebraicGeometry.CriticalSchemeCharts
