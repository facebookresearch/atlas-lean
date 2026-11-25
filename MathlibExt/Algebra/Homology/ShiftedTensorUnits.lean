/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModelContracts
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Source-normalized tensor with a shifted coefficient unit

The comparison X⊗k[t]→X[t] is fixed on every nonzero homogeneous
unit summand. Its (-1)^(t*p) sign is the native cochain tensor/shift
sign. No arbitrary target-shift isomorphism is accepted.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.ShiftedTensorUnits

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts

universe u
variable {R : Type u} [CommRing R]

/-- The actual coefficient unit in its unique nonzero shifted degree. -/
def shiftedUnit (t : ℤ) (r : R) : ((𝟙_ (Cochains R))⟦t⟧).X (-t) :=
  ((CochainComplex.shiftFunctorObjXIso (𝟙_ (Cochains R)) t (-t) 0 (by omega)).inv).hom
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv r)

/-- The comparison uses the actual native unit and source tensor/shift sign in every degree. -/
structure UnitTensorModel (X : Cochains R) (t : ℤ) where
  comparison : X ⊗ (𝟙_ (Cochains R))⟦t⟧ ≅ X⟦t⟧
  normalized : ∀ (p : ℤ) (x : X.X p) (r : R),
    (((HomologicalComplex.ιTensorObj X ((𝟙_ (Cochains R))⟦t⟧) p (-t) (p - t) (by omega)) ≫
      (comparison.hom.f (p - t)) ≫
        (CochainComplex.shiftFunctorObjXIso X t (p - t) p (by omega)).hom).hom
      (TensorProduct.tmul R x (shiftedUnit t r))) = (t * p).negOnePow • (r • x)

end MathlibExt.Algebra.Homology.ShiftedTensorUnits
