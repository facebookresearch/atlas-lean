/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedBaseChangeComposition

/-!
# Actual chosen composition comparison over the original Q arrow

The comparison uses the stock direct-to-nested pullback isomorphism on the
whole original fibers. Its forward arrow is an actual identity-R lift.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace MathlibExtTest.LocalizedBaseChangeComposition

open AlgebraicKTheory AlgebraicKTheory.LocalizedBaseChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- The actual stock hom formula and its vertical lift are retained together. -/
theorem actual_chosen_composition_hom_identity_lift
    {R S T : QuillenQ C} (f : R ⟶ S) (g : S ⟶ T)
    (a : Functor.Fiber (projection (C := C)) T) :
    ((baseChangeCompositionNatIso f g).hom.app a).val =
        (Functor.IsFibered.pullbackPullbackIso
          (p := projection (C := C)) a.property g f).hom ∧
      Functor.IsHomLift (projection (C := C)) (𝟙 R)
        ((baseChangeCompositionNatIso f g).hom.app a).val :=
  ⟨baseChangeCompositionNatIso_hom_val f g a,
    ((baseChangeCompositionNatIso f g).hom.app a).property⟩

#print axioms actual_chosen_composition_hom_identity_lift

end MathlibExtTest.LocalizedBaseChangeComposition

end
