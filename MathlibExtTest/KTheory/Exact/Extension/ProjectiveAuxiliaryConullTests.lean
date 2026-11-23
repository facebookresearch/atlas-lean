/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ProjectiveAuxiliaryConull

/-!
# Public all-ring projective auxiliary tests

The three named tests consume the native and ordinary positive-group
conclusions at arbitrary realized points and the literal terminal map of
the original auxiliary nerve.

They use the original associative unital ring `R` and the given finitely
generated projective quotient module `X`. Ring, module and compact-probe
universes stay independent. The owning auxiliary module is their sole
public import.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uRing vModule wProbe

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial Topology Topology.Homotopy

namespace CanonicalProjectiveAuxiliaryConsumers

/-- The native positive-group conclusion holds at arbitrary points, not just vertices.
The compact-probe universe remains independent of the ring and module universes. -/
theorem allRing_native_positive_groups_at_arbitrary_points
    {R : Type uRing} [Ring R] (X : FGProjectiveCat.{vModule} R) (n : ℕ)
    (y : AlgebraicKTheory.AuxiliaryExtension.auxiliaryCGWH.{wProbe}
      (FGProjectiveCat.{vModule} R) X) :
    Subsingleton (HomotopyGroup.Pi (n + 1)
      (AlgebraicKTheory.AuxiliaryExtension.auxiliaryCGWH.{wProbe}
        (FGProjectiveCat.{vModule} R) X) y) :=
  AlgebraicKTheory.AuxiliaryExtension.projectiveAuxiliary_positiveGroup_subsingleton_at.{wProbe}
    X n y

/-- The actual native-to-ordinary Iso transports to the original nerve realization
at every realized point. No vertex-only hypothesis is introduced. -/
theorem allRing_original_realization_positive_groups_at_arbitrary_points
    {R : Type uRing} [Ring R] (X : FGProjectiveCat.{vModule} R) (n : ℕ)
    (y : AlgebraicKTheory.AuxiliaryExtension.auxiliarySpace (FGProjectiveCat.{vModule} R) X) :
    Subsingleton (HomotopyGroup.Pi (n + 1)
      (AlgebraicKTheory.AuxiliaryExtension.auxiliarySpace (FGProjectiveCat.{vModule} R) X) y) :=
  AlgebraicKTheory.AuxiliaryExtension.projectiveAuxiliary_realization_positiveGroup_subsingleton_at
    X n y

/-- For every associative unital ring, the literal terminal map of the original
auxiliary nerve is weak. All geometric and projective inputs are derived in
the actual provider; no desired full result is passed as a consumer argument. -/
theorem allRing_original_auxiliary_terminal_map_is_weak
    {R : Type uRing} [Ring R] (X : FGProjectiveCat.{vModule} R) :
    SSet.realizationWeakEquivalences
      (terminal.from
        (nerve
          (AlgebraicKTheory.AuxiliaryExtension.Auxiliary (FGProjectiveCat.{vModule} R) X))) :=
  AlgebraicKTheory.AuxiliaryExtension.projectiveAuxiliary_conull_mem_realizationWeakEquivalences X

end CanonicalProjectiveAuxiliaryConsumers

end
