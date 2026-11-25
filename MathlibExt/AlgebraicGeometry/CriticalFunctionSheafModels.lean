/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CriticalSchemeCharts

/-!
# Source-normalized critical-function sheaves and d-critical sections

The sheaf is a sheaf of coefficient modules on the actual Zariski space.
Its comparisons quantify every smooth affine embedding and every actual
refinement square. They identify the fixed O/I² kernel and its actual
reduction map. S_X⁰ is the native sheaf kernel of reduction, rather than
a freely assigned sheaf or an O-module. All chart classes use literal
function representatives. Sheaf construction and paper-internal gluing
remain Wanted outputs.

Reference: Joyce, arXiv:1304.4508v3, Theorem 2.1 and Definition 2.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CriticalFunctionSheafModels

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open CriticalSchemeCharts AffineCriticalFunctions AffineCriticalKernelModels

variable {k : Type} [Field k]

/-- Generic native restriction, fixed by every actual scheme app map. -/
structure FunctionRestriction {X Y : Over (Spec (.of k))} (f : Y ⟶ X) where
  map : coefficientFunctions X ⟶
    (TopCat.Sheaf.pushforward (ModuleCat k) f.left.base).obj (coefficientFunctions Y)
  normalized : ∀ (U : X.left.Opens) (a : Γ(X.left,U)),
    (map.hom.app (op U)).hom a = (f.left.app U).hom a

def reducedOver (X : Over (Spec (.of k))) : Over (Spec (.of k)) :=
  Over.mk (reductionMap X.left ≫ X.hom)

def reductionArrow (X : Over (Spec (.of k))) : reducedOver X ⟶ X :=
  Over.homMk (reductionMap X.left) rfl

/-- The exact local kernels and maps characterize the actual S_X sheaf. The
domains of affine embeddings cover `X` (as they do when `X` is locally of finite
type) and are stable under principal shrinking, so they form a basis on which the
sheaf, its restrictions and `beta` are fixed. -/
structure CriticalSheafModel (X : Over (Spec (.of k))) where
  sheaf : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat k)
  beta : sheaf ⟶ coefficientFunctions X
  covers : ∀ x : X.left, ∃ E : AffineEmbedding X, x ∈ E.domain
  affine : ∀ E : AffineEmbedding X,
    sheaf.obj.obj (op E.domain) ≅ ModuleCat.of k (localCriticalModule k E.algebra E.ideal)
  beta_normalized : ∀ (E : AffineEmbedding X) (f : criticalFunctions k E.algebra E.ideal),
    (beta.hom.app (op E.domain)).hom
      ((affine E).inv.hom ((squareDenominator k E.algebra E.ideal).mkQ f)) =
        embeddedFunction E f
  refinement : ∀ (E F : AffineEmbedding X) (r : AffineRefinement E F),
    sheaf.obj.map (homOfLE r.domain_le).op ≫ (affine F).hom =
      (affine E).hom ≫ ModuleCat.ofHom (localMap r.algebraMap r.ideal_map)

/-- The zero-critical sheaf is computed by the native sheaf kernel. -/
def zeroSheaf {X : Over (Spec (.of k))} (B : CriticalSheafModel X)
    (R : FunctionRestriction (reductionArrow X)) :
    Sheaf (Opens.grothendieckTopology X.left) (ModuleCat k) :=
  kernel (B.beta ≫ R.map)

/-- The kernel comparison retains literal representatives and every refinement. -/
structure ZeroCriticalSheafModel {X : Over (Spec (.of k))} (B : CriticalSheafModel X)
    (R : FunctionRestriction (reductionArrow X)) where
  affine : ∀ E : AffineEmbedding X,
    (zeroSheaf B R).obj.obj (op E.domain) ≅
      ModuleCat.of k (localZeroCriticalModule k E.algebra E.ideal)
  inclusion : ∀ (E : AffineEmbedding X) (f : E.algebra)
    (hd : KaehlerDifferential.D k E.algebra f ∈ idealDifferentials k E.algebra E.ideal)
    (hr : f ∈ E.ideal.radical),
    ((kernel.ι (B.beta ≫ R.map)).hom.app (op E.domain)).hom
      ((affine E).inv.hom (criticalClass E.ideal f hd hr)) =
    (B.affine E).inv.hom ((squareDenominator k E.algebra E.ideal).mkQ ⟨f, hd⟩)
  refinement : ∀ (E F : AffineEmbedding X) (r : AffineRefinement E F),
    (zeroSheaf B R).obj.map (homOfLE r.domain_le).op ≫ (affine F).hom =
      (affine E).hom ≫ ModuleCat.ofHom
        (AffineCriticalFunctionMaps.localZeroMap r.algebraMap r.ideal_map)

/-- Critical affine charts use all smooth algebras, including nonpolynomial ones. -/
structure AffineCriticalChart (X : Over (Spec (.of k))) extends AffineEmbedding X where
  function : algebra
  critical : ideal = zeroDifferentialIdeal algebra function
  differential_zero : KaehlerDifferential.D k algebra function ∈ idealDifferentials k algebra ideal
  reduction_zero : function ∈ ideal.radical

def AffineCriticalChart.functionClass {X : Over (Spec (.of k))} (E : AffineCriticalChart X) :
    localZeroCriticalModule k E.algebra E.ideal :=
  criticalClass E.ideal E.function E.differential_zero E.reduction_zero

/-- The actual section is locally the class of f modulo I², on a genuine open cover. -/
structure DCriticalStructure {X : Over (Spec (.of k))} (B : CriticalSheafModel X)
    (R : FunctionRestriction (reductionArrow X)) (Z : ZeroCriticalSheafModel B R) where
  sectionValue : (zeroSheaf B R).obj.obj (op ⊤)
  criticalCover : ∀ x : X.left, ∃ E : AffineCriticalChart X, x ∈ E.domain ∧
    (Z.affine E.toAffineEmbedding).hom.hom
      (((zeroSheaf B R).obj.map (homOfLE le_top).op).hom sectionValue) = E.functionClass

def CompatibleChart {X : Over (Spec (.of k))} {B : CriticalSheafModel X}
    {R : FunctionRestriction (reductionArrow X)} {Z : ZeroCriticalSheafModel B R}
    (D : DCriticalStructure B R Z) (E : AffineCriticalChart X) : Prop :=
  (Z.affine E.toAffineEmbedding).hom.hom
    (((zeroSheaf B R).obj.map (homOfLE le_top).op).hom D.sectionValue) = E.functionClass

end MathlibExt.AlgebraicGeometry.CriticalFunctionSheafModels
