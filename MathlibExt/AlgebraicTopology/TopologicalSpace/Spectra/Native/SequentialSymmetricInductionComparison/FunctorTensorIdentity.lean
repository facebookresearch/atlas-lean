/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionModuleObjects

/-!
# Tensor identities for external products

Records the identity tensor map at an external-product object and cancellation of identity factors in a monoidal category. These formulas apply to arbitrary functor pairs and morphisms.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory
open scoped ExternalProduct

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison.FunctorTensorIdentity
universe uV vV uC vC
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C]

/-- Every complete original functor pair has its identity tensor at the actual external-product object. -/
private theorem tensorIdentity (F G : C ⥤ V) (a b : C) :
    (tensorIso (Iso.refl (F.obj a)) (Iso.refl (G.obj b))).hom =
      𝟙 ((F ⊠ G).obj (a,b)) :=
  id_tensorHom_id _ _

/-- Identity erasure is proved before any native object, module or arrow is selected. -/
private theorem erase {Z T : V} (p q : Z ⟶ T)
    (h : p ≫ 𝟙 T = 𝟙 Z ≫ q) : p = q :=
by
  have ht := congrArg (fun f => f ▷ (𝟙_ V)) h
  rw [comp_whiskerRight, comp_whiskerRight, id_whiskerRight, id_whiskerRight,
    Category.comp_id, Category.id_comp] at ht
  apply (cancel_epi (ρ_ Z).hom).1
  exact (rightUnitor_naturality p).symm.trans
    ((congrArg (fun f => f ≫ (ρ_ T).hom) ht).trans (rightUnitor_naturality q))

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison.FunctorTensorIdentity
