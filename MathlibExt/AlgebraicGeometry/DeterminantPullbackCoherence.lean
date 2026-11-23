/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from AxiomMath/Stacks (https://github.com/AxiomMath/Stacks),
revision c496df0d9beea9deaeabcea8492605f9a0a2313b, licensed under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0). The source files carry no
individual copyright or author notice.

* `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/CompositionOnComplexesAnyModel.lean`
* `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/CompositionCoherence.lean`

Modifications: the existing native scheme-module cochain and total left derived operators
are used with their exact cochain counits; the identity, composition and higher-coherence
normalizations are kept as data.
-/
module

public import MathlibExt.AlgebraicGeometry.FourierMukai
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Native derived pullback coherence for affine determinant descent

Ordinary cochain maps use the actual native scheme-module pullback
identity/composition. The derived comparisons are fixed by the full native
counit diagrams on every actual cochain. Their identity, composition and
cocycle equations retain the source normalization used to glue determinants.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DeterminantPullbackCoherence

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open FourierMukai

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The actual ordinary module pullback in every cochain degree. -/
def pulledComplex {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Cochains Y) : Cochains X :=
  ((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- Native identity pullback in every degree, with actual differential naturality. -/
def identityComplexIso (X : Scheme.{u}) (P : Cochains X) : pulledComplex (𝟙 X) P ≅ P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (Scheme.Modules.pullbackId X).app (P.X i))
    (by intro i j _; exact ((Scheme.Modules.pullbackId X).hom.naturality (P.d i j)).symm)

/-- Native composed pullback in every degree, including every actual module map. -/
def compositionComplexIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (P : Cochains Z) :
    pulledComplex f (pulledComplex g P) ≅ pulledComplex (f ≫ g) P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (Scheme.Modules.pullbackComp f g).app (P.X i))
    (by intro i j _; exact ((Scheme.Modules.pullbackComp f g).hom.naturality (P.d i j)).symm)

variable [HasDerivedPullbacks.{u}]

/-- Completed-source derived identity, fixed by the native cochain counit. -/
structure IdentityData (X : Scheme.{u}) where
  comparison : derivedPullback (𝟙 X) ≅ 𝟭 (FourierMukai.D X)
  normalization : ∀ P : Cochains X,
    comparison.hom.app (DerivedCategory.Q.obj P) =
      (derivedPullbackCounit (𝟙 X)).app P ≫ DerivedCategory.Q.map (identityComplexIso X P).hom

/-- Completed-source derived composition, fixed by the complete native counit square. -/
structure CompositionData {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) where
  comparison : derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g)
  normalization : ∀ P : Cochains Z,
    comparison.hom.app (DerivedCategory.Q.obj P) ≫ (derivedPullbackCounit (f ≫ g)).app P =
      (derivedPullback f).map ((derivedPullbackCounit g).app P) ≫
        (derivedPullbackCounit f).app (pulledComplex g P) ≫
        DerivedCategory.Q.map (compositionComplexIso f g P).hom

/-- Full actual derived pullback coherence. All operations are the native
operators above; this is conditional integration of the completed source laws. -/
structure Coherence where
  identity : ∀ X : Scheme.{u}, IdentityData X
  composition : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), CompositionData f g
  associativity : ∀ {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (K : FourierMukai.D W),
    (composition f g).comparison.hom.app ((derivedPullback h).obj K) ≫
      (composition (f ≫ g) h).comparison.hom.app K ≫
      eqToHom (congrArg (fun m : X ⟶ W => (derivedPullback m).obj K) (Category.assoc f g h)) =
    (derivedPullback f).map ((composition g h).comparison.hom.app K) ≫
      (composition f (g ≫ h)).comparison.hom.app K
  left_identity : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (K : FourierMukai.D Y),
    (composition (𝟙 X) f).comparison.hom.app K ≫
      eqToHom (congrArg (fun m : X ⟶ Y => (derivedPullback m).obj K) (Category.id_comp f)) =
      (identity X).comparison.hom.app ((derivedPullback f).obj K)
  right_identity : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (K : FourierMukai.D Y),
    (composition f (𝟙 Y)).comparison.hom.app K ≫
      eqToHom (congrArg (fun m : X ⟶ Y => (derivedPullback m).obj K) (Category.comp_id f)) =
      (derivedPullback f).map ((identity Y).comparison.hom.app K)

end MathlibExt.AlgebraicGeometry.DeterminantPullbackCoherence
