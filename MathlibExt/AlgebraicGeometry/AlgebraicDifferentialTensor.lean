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

* `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SectionwiseAlgebras.lean` (section ExtPowAlgebra)

Modifications: the native tensor morphism is constructed directly, using the proved native
sheafification-unit tensor comparison.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
public import MathlibExt.AlgebraicGeometry.NativeTensorComparisons

/-! # The actual wedge of algebraic differential-form sheaves

The map is sheafification of multiplication in the actual exterior algebra,
conjugated by the canonical tensor/sheafification comparison. No map
called wedge or associator is supplied as an oracle.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AlgebraicDifferentialTensor
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.NativeTensorComparisons

/-- Actual multiplication in the graded exterior algebra. -/
def exteriorMultiply {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    (p q : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) : ⋀[R]^(p+q) M :=
  ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
open MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves

/-- The source exterior product is a native presheaf tensor morphism. -/
def presheafWedge (p q : ℕ) :
    formsPresheaf R X p ⊗ formsPresheaf R X q ⟶ formsPresheaf R X (p+q) :=
  PresheafOfModules.tensorMk
    (fun U x y => exteriorMultiply p q x y)
    (fun _ _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun _ _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ _ => Subtype.ext (mul_add _ _ _))
    (fun _ _ _ _ => Subtype.ext (mul_smul_comm _ _ _))
    (by intro U V f x y; exact Subtype.ext (map_mul _ _ _))

/-- The actual wedge map on sheaves of algebraic differential forms. -/
def wedge (p q : ℕ) :
    moduleTensor X.left (forms R X p) (forms R X q) ⟶ forms R X (p+q) :=
  (asIso (pairComparison X.left (formsPresheaf R X p) (formsPresheaf R X q))).inv ≫
    (sheafifyModules X.left).map (presheafWedge R X p q)

end MathlibExt.AlgebraicGeometry.AlgebraicDifferentialTensor
