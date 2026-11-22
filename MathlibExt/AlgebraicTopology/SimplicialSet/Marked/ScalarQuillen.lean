/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ModelCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverScalarInitialCorner
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# The actual scalar tensor/cotensor adjunctions are Quillen for both marked models

The original empty-parameter corner comparison retains each whole fixed
scalar tensor map. Native scalar-mono weak-corner closure proves trivial
cofibration preservation, and original monicity proves cofibration
preservation. Thus the actual original pullback cotensor adjunction is
Quillen for both genuine marked models. Its same right adjoint preserves
all original intrinsic targets, with no Kan condition on the scalar.
No higher-height Cartesian law or straightening equivalence is asserted.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace SSet.Marked

/-- Every whole fixed-scalar tensor map of an original Cartesian weak marked mono is again a full weak marked mono. -/
theorem overScalarTensor_cartesian_weakMono {B : SSet.{u}} [Quasicategory B] {X Y : Over (max B)}
    (i : X ⟶ Y) (hi : cartesianTestingTrivialCofibrations B i) (K : SSet.{u}) :
    cartesianTestingTrivialCofibrations B ((overScalarTensor (max B) K).map i) := by
  let _ : Mono (initial.to K) := inferInstance
  have hc := cartesianWeakMono_parameter_closed i hi (initial.to K)
  rw [← cartesianTestingFibrations_llp B]
  intro E F p hp
  exact (HasLiftingProperty.iff_of_arrow_iso_left (overScalarTensorMapInitialCornerIso i K) p).mpr (hp _ hc)

/-- The native dual scalar action retains every original weak marked mono in its complete mapping class. -/
theorem overScalarTensor_cocartesian_weakMono {B : SSet.{u}} [Quasicategory B] {X Y : Over (max B)}
    (i : X ⟶ Y) (hi : cocartesianTestingTrivialCofibrations B i) (K : SSet.{u}) :
    cocartesianTestingTrivialCofibrations B ((overScalarTensor (max B) K).map i) := by
  let _ : Mono (initial.to K) := inferInstance
  have hc := cocartesianWeakMono_parameter_closed i hi (initial.to K)
  rw [← cocartesianTestingFibrations_llp B]
  intro E F p hp
  exact (HasLiftingProperty.iff_of_arrow_iso_left (overScalarTensorMapInitialCornerIso i K) p).mpr (hp _ hc)

/-- The same original scalar tensor and native pullback cotensor give a genuine Quillen adjunction for the
  exact Cartesian marked model. -/
theorem cartesianMarkedScalar_isQuillen (B : SSet.{u}) [Quasicategory B] (K : SSet.{u}) :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    (overScalarTensorAdjunction (max B) K).IsQuillenAdjunction := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  dsimp only
  refine { preservesCofibrations := ?_, preservesTrivialCofibrations := ?_ }
  · intro X Y i hi
    change Mono i at hi
    let _ : Mono i := hi
    exact overScalarTensorMap_mono i K
  · intro X Y i hi
    change cartesianTestingTrivialCofibrations B i at hi
    exact overScalarTensor_cartesian_weakMono i hi K

/-- The exact same original tensor/cotensor maps form the genuine dual Quillen adjunction on all original
  value universes. -/
theorem cocartesianMarkedScalar_isQuillen (B : SSet.{u}) [Quasicategory B] (K : SSet.{u}) :
    let _ := markedCofibrationStructure (max B)
    let _ := cocartesianMarkedFibrationStructure B
    let _ := cocartesianMarkedWeakStructure B
    let _ := cocartesianMarkedModelCategory B
    (overScalarTensorAdjunction (max B) K).IsQuillenAdjunction := by
  let _ := markedCofibrationStructure (max B)
  let _ := cocartesianMarkedFibrationStructure B
  let _ := cocartesianMarkedWeakStructure B
  let _ := cocartesianMarkedModelCategory B
  dsimp only
  refine { preservesCofibrations := ?_, preservesTrivialCofibrations := ?_ }
  · intro X Y i hi
    change Mono i at hi
    let _ : Mono i := hi
    exact overScalarTensorMap_mono i K
  · intro X Y i hi
    change cocartesianTestingTrivialCofibrations B i at hi
    exact overScalarTensor_cocartesian_weakMono i hi K

/-- The ACTUAL original pullback cotensor of any intrinsic Cartesian target remains intrinsically marked for
  every original scalar, including non-Kan scalars. -/
theorem overCotensor_cartesian_intrinsic {B : SSet.{u}} [Quasicategory B] (K : SSet.{u})
    (Y : Over (max B)) (hY : cartesianObjects B Y) :
    cartesianObjects B ((overCotensor (max B) K).obj Y) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := cartesianMarkedScalar_isQuillen B K
  have hF : IsFibrant Y := (cartesianMarkedModel_fibrant_iff B Y).mpr hY
  have hR : IsFibrant ((overCotensor (max B) K).obj Y) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := overScalarTensorAdjunction (max B) K) hF
  exact (cartesianMarkedModel_fibrant_iff B _).mp hR

/-- The native original dual cotensor has the same intrinsic-target closure under every full scalar parameter. -/
theorem overCotensor_cocartesian_intrinsic {B : SSet.{u}} [Quasicategory B] (K : SSet.{u})
    (Y : Over (max B)) (hY : cocartesianObjects B Y) :
    cocartesianObjects B ((overCotensor (max B) K).obj Y) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cocartesianMarkedFibrationStructure B
  let _ := cocartesianMarkedWeakStructure B
  let _ := cocartesianMarkedModelCategory B
  let _ := cocartesianMarkedScalar_isQuillen B K
  have hF : IsFibrant Y := (cocartesianMarkedModel_fibrant_iff B Y).mpr hY
  have hR : IsFibrant ((overCotensor (max B) K).obj Y) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := overScalarTensorAdjunction (max B) K) hF
  exact (cocartesianMarkedModel_fibrant_iff B _).mp hR

end SSet.Marked
