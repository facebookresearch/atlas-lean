/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositive
public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Bounded

/-!
# Access to the actual CP slices of asymptotic families

The existing CP and CPC carriers provide a completely positive map witness
for each time. The accessors choose only from that supplied evidence and
retain the raw value. A CPC slice has its supplied pointwise contraction and
therefore a continuous linear map of operator norm at most one.

No carrier, quotient, homotopy, global instance or boundedness field changes.
No source representative-existence theorem is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AsymptoticMorphism

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

namespace CompletelyPositiveFamily

/-- A CP slice chosen only from the given family's actual finite-time
complete-positivity evidence. -/
def slice (phi : CompletelyPositiveFamily A B) (t : AsymptoticTime) :
    CompletelyPositiveMap.Canonical A B := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact Classical.choose (phi.completelyPositive t)

/-- The chosen CP witness has exactly the original raw slice values. -/
@[simp]
theorem slice_apply (phi : CompletelyPositiveFamily A B)
    (t : AsymptoticTime) (a : A) :
    slice phi t a = phi.toAsymptoticMorphism t a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact Classical.choose_spec (phi.completelyPositive t) a

/-- Each actual broad CP slice has the upstream continuous linear adapter,
without a contraction assumption. -/
def sliceContinuousLinearMap (phi : CompletelyPositiveFamily A B)
    (t : AsymptoticTime) : A →L[ℂ] B := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact CompletelyPositiveMap.toContinuousLinearMap (slice phi t)

/-- Continuous access retains every raw value. -/
@[simp]
theorem sliceContinuousLinearMap_apply (phi : CompletelyPositiveFamily A B)
    (t : AsymptoticTime) (a : A) :
    sliceContinuousLinearMap phi t a = phi.toAsymptoticMorphism t a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  rw [sliceContinuousLinearMap, CompletelyPositiveMap.toContinuousLinearMap_apply,
    slice_apply]

end CompletelyPositiveFamily

namespace CompletelyPositiveContraction

/-- A CP slice chosen only from the supplied CP-contraction evidence.
The norm evidence is retained by the characteristic theorem below. -/
def slice (phi : CompletelyPositiveContraction A B) (t : AsymptoticTime) :
    CompletelyPositiveMap.Canonical A B := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact Classical.choose (phi.completelyPositiveContraction t)

/-- The chosen CP witness has exactly the original raw slice values. -/
@[simp]
theorem slice_apply (phi : CompletelyPositiveContraction A B)
    (t : AsymptoticTime) (a : A) :
    slice phi t a = phi.toAsymptoticMorphism t a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact (Classical.choose_spec (phi.completelyPositiveContraction t)).2 a

/-- The chosen slice retains its supplied pointwise contraction. -/
theorem norm_slice_apply_le (phi : CompletelyPositiveContraction A B)
    (t : AsymptoticTime) (a : A) :
    ‖slice phi t a‖ ≤ ‖a‖ := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact (Classical.choose_spec (phi.completelyPositiveContraction t)).1 a

/-- The continuous linear map of an actual CPC slice, with unchanged values. -/
def sliceContinuousLinearMap (phi : CompletelyPositiveContraction A B)
    (t : AsymptoticTime) : A →L[ℂ] B := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact CompletelyPositiveMap.toContinuousLinearMap (slice phi t)

/-- Continuous access retains every raw value. -/
@[simp]
theorem sliceContinuousLinearMap_apply (phi : CompletelyPositiveContraction A B)
    (t : AsymptoticTime) (a : A) :
    sliceContinuousLinearMap phi t a = phi.toAsymptoticMorphism t a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  rw [sliceContinuousLinearMap, CompletelyPositiveMap.toContinuousLinearMap_apply,
    slice_apply]

/-- The actual continuous linear slice has operator norm at most one. -/
theorem norm_sliceContinuousLinearMap_le_one
    (phi : CompletelyPositiveContraction A B) (t : AsymptoticTime) :
    ‖sliceContinuousLinearMap phi t‖ ≤ 1 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact CompletelyPositiveMap.norm_toContinuousLinearMap_le_one (slice phi t)
    (norm_slice_apply_le phi t)

end CompletelyPositiveContraction

end AsymptoticMorphism
