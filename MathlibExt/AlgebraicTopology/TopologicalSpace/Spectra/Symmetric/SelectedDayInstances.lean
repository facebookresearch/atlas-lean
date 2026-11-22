/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory

/-!
# Selected Day structures on symmetric sequences

The monoidal structure on `PointedCGWH` symmetric sequences is named using
the displayed tensor and unit Kan-extension and preservation families.
It retains the full `DayFunctor.inst` data, including tensor maps and coherence.
The corresponding braided and symmetric structures come from the finite-set
index and pointed-smash symmetry.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory MonoidalCategory Limits
open scoped ExternalProduct

namespace PointedCGWH

/-- The original selected native Day monoidal instance, without repeating its synthesis. -/
@[instance_reducible]
def originalSymmetricSequenceMonoidal : MonoidalCategory (SymmetricSequence.{u, v}) :=
  let tensorExtensions : ∀ (F G : Operad.SmallFinBijGroupoid ⥤ PointedCGWH.{u, v}),
      (tensor Operad.SmallFinBijGroupoid).HasPointwiseLeftKanExtension (F ⊠ G) := by
    intro F G Y
    infer_instance
  let unitExtensions :
      (Functor.fromPUnit.{0} (𝟙_ Operad.SmallFinBijGroupoid)).HasPointwiseLeftKanExtension
        (Functor.fromPUnit.{0} (𝟙_ PointedCGWH.{u, v})) := by
    intro Y
    infer_instance
  let leftTensorShape : ∀ (v : PointedCGWH.{u, v}) (d : Operad.SmallFinBijGroupoid),
      PreservesColimitsOfShape (CostructuredArrow (tensor Operad.SmallFinBijGroupoid) d)
        (tensorLeft v) := by
    intro v d
    infer_instance
  let rightTensorShape : ∀ (v : PointedCGWH.{u, v}) (d : Operad.SmallFinBijGroupoid),
      PreservesColimitsOfShape (CostructuredArrow (tensor Operad.SmallFinBijGroupoid) d)
        (tensorRight v) := by
    intro v d
    infer_instance
  let leftUnitShape : ∀ (v : PointedCGWH.{u, v}) (d : Operad.SmallFinBijGroupoid),
      PreservesColimitsOfShape
        (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ Operad.SmallFinBijGroupoid)) d)
        (tensorLeft v) := by
    intro v d
    infer_instance
  let rightUnitShape : ∀ (v : PointedCGWH.{u, v}) (d : Operad.SmallFinBijGroupoid),
      PreservesColimitsOfShape
        (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ Operad.SmallFinBijGroupoid)) d)
        (tensorRight v) := by
    intro v d
    infer_instance
  let rightMixedUnitShape : ∀ (v : PointedCGWH.{u, v})
      (d : Operad.SmallFinBijGroupoid × Operad.SmallFinBijGroupoid),
      PreservesColimitsOfShape
        (CostructuredArrow ((𝟭 Operad.SmallFinBijGroupoid).prod
          (Functor.fromPUnit.{0} (𝟙_ Operad.SmallFinBijGroupoid))) d) (tensorRight v) := by
    intro v d
    infer_instance
  let rightTripleShape : ∀ (v : PointedCGWH.{u, v})
      (d : Operad.SmallFinBijGroupoid × Operad.SmallFinBijGroupoid),
      PreservesColimitsOfShape
        (CostructuredArrow ((tensor Operad.SmallFinBijGroupoid).prod
          (𝟭 Operad.SmallFinBijGroupoid)) d) (tensorRight v) := by
    intro v d
    infer_instance
  @DayFunctor.inst Operad.SmallFinBijGroupoid _ PointedCGWH.{u, v} _ _ _
    tensorExtensions unitExtensions leftTensorShape rightTensorShape leftUnitShape rightUnitShape
    rightMixedUnitShape rightTripleShape

/-- All original Day tensor objects, maps, unit and coherence values remain identical. -/
private theorem originalSymmetricSequenceMonoidal_namedProviders_eq_original :
    originalSymmetricSequenceMonoidal.{u, v} =
      @DayFunctor.inst Operad.SmallFinBijGroupoid _ PointedCGWH.{u, v} _ _ _
        (fun (_F _G : Operad.SmallFinBijGroupoid ⥤ PointedCGWH.{u, v})
          (_d : Operad.SmallFinBijGroupoid) => inferInstance)
        (fun (_d : Operad.SmallFinBijGroupoid) => inferInstance)
        (fun (_X : PointedCGWH.{u, v}) (_d : Operad.SmallFinBijGroupoid) => inferInstance)
        (fun (_X : PointedCGWH.{u, v}) (_d : Operad.SmallFinBijGroupoid) => inferInstance)
        (fun (_X : PointedCGWH.{u, v}) (_d : Operad.SmallFinBijGroupoid) => inferInstance)
        (fun (_X : PointedCGWH.{u, v}) (_d : Operad.SmallFinBijGroupoid) => inferInstance)
        (fun (_X : PointedCGWH.{u, v})
          (_d : Operad.SmallFinBijGroupoid × Operad.SmallFinBijGroupoid) => inferInstance)
        (fun (_X : PointedCGWH.{u, v})
          (_d : Operad.SmallFinBijGroupoid × Operad.SmallFinBijGroupoid) => inferInstance) := rfl

attribute [local instance] originalSymmetricSequenceMonoidal

/-- The actual selected Day braiding on the original native symmetric sequences. -/
@[instance_reducible]
def originalSymmetricSequenceBraided : BraidedCategory (SymmetricSequence.{u, v}) :=
  inferInstance

attribute [local instance] originalSymmetricSequenceBraided

/-- The actual Day symmetry, derived from the original index and pointed smash symmetry. -/
@[instance_reducible]
def originalSymmetricSequenceSymmetric : SymmetricCategory (SymmetricSequence.{u, v}) :=
  inferInstance

end PointedCGWH
