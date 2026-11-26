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
# Completely positive slices as bounded linear maps

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. Each slice defines a completely positive map and a bounded
complex linear operator A→B with the same coefficient values. For a CP-contractive family, its
pointwise norm bound is ‖φ_t(a)‖≤‖a‖ and the linear operator norm is at most 1.
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

/-- **Completely positive map of a time slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For t≥1, CompletelyPositiveFamily.slice φ t is the completely
positive map s_t:A→B with s_t(a)=φ_t(a).
-/
def slice (phi : CompletelyPositiveFamily A B) (t : AsymptoticTime) :
    CompletelyPositiveMap.Canonical A B := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact Classical.choose (phi.completelyPositive t)

/-- **Value of a completely positive slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For t≥1 and a∈A, CompletelyPositiveFamily.slice φ t a=φ_t(a).
-/
@[simp]
theorem slice_apply (phi : CompletelyPositiveFamily A B)
    (t : AsymptoticTime) (a : A) :
    slice phi t a = phi.toAsymptoticMorphism t a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact Classical.choose_spec (phi.completelyPositive t) a

/-- **Bounded complex linear map of a CP slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For t≥1, CompletelyPositiveFamily.sliceContinuousLinearMap φ
t:A→L[ℂ]B is the bounded linear map a↦φ_t(a).
-/
def sliceContinuousLinearMap (phi : CompletelyPositiveFamily A B)
    (t : AsymptoticTime) : A →L[ℂ] B := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact CompletelyPositiveMap.toContinuousLinearMap (slice phi t)

/-- **Value of the bounded linear CP slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For t≥1 and a∈A,
CompletelyPositiveFamily.sliceContinuousLinearMap φ t a=φ_t(a).
-/
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

/-- **Completely positive map of a contractive slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For t≥1, CompletelyPositiveContraction.slice φ t:A→B is the
completely positive map a↦φ_t(a).
-/
def slice (phi : CompletelyPositiveContraction A B) (t : AsymptoticTime) :
    CompletelyPositiveMap.Canonical A B := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact Classical.choose (phi.completelyPositiveContraction t)

/-- **Value of a completely positive contraction slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For t≥1 and a∈A, CompletelyPositiveContraction.slice φ t
a=φ_t(a).
-/
@[simp]
theorem slice_apply (phi : CompletelyPositiveContraction A B)
    (t : AsymptoticTime) (a : A) :
    slice phi t a = phi.toAsymptoticMorphism t a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact (Classical.choose_spec (phi.completelyPositiveContraction t)).2 a

/-- **Pointwise norm bound for a CP contraction slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For t≥1 and a∈A, ‖CompletelyPositiveContraction.slice φ t
a‖≤‖a‖.
-/
theorem norm_slice_apply_le (phi : CompletelyPositiveContraction A B)
    (t : AsymptoticTime) (a : A) :
    ‖slice phi t a‖ ≤ ‖a‖ := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact (Classical.choose_spec (phi.completelyPositiveContraction t)).1 a

/-- **Bounded linear map of a CP contraction slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For t≥1,
CompletelyPositiveContraction.sliceContinuousLinearMap φ t:A→L[ℂ]B is the bounded complex
linear map a↦φ_t(a).
-/
def sliceContinuousLinearMap (phi : CompletelyPositiveContraction A B)
    (t : AsymptoticTime) : A →L[ℂ] B := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact CompletelyPositiveMap.toContinuousLinearMap (slice phi t)

/-- **Value of the bounded linear contraction slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For t≥1 and a∈A,
CompletelyPositiveContraction.sliceContinuousLinearMap φ t a=φ_t(a).
-/
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

/-- **Operator norm of a CP contraction slice.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For t≥1,
‖CompletelyPositiveContraction.sliceContinuousLinearMap φ t‖≤1.
-/
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
