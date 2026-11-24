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

public import MathlibExt.Analysis.CStarAlgebra.NonUnitalRepresentation
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarRegularCovariantModel

/-!
# The canonical regular Haar pair from the strict nonunital GN construction

Select the actual same-universe Hilbert representation supplied by the
proved nonunital Gelfand--Naimark construction. Its original dictionaries,
injective coefficient map share the single neutral GN packet and choice.
The original coefficient norm follows from the neutral norm theorem. The
verified original regular construction then gives the coefficient and
Haar translation pair on that selected Hilbert space's actual Lp carrier.

The canonical endpoint has no coefficient-representation or regular-model
input. The group and coefficient universes remain independent, and zero
coefficient algebras are permitted. Independence of the resulting source
model and raw-core faithfulness remain separate theorem obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped CStarAlgebra

namespace PointNormCStarAction

open MathlibExt.Analysis.CStarAlgebra.NonUnitalRepresentation

noncomputable section

universe uG uA

/-- The actual source-sized coefficient Hilbert space selected from strict GN data. -/
abbrev CanonicalCoefficientSpace (A : Type uA) [NonUnitalCStarAlgebra A] : Type uA :=
  (faithfulHilbertRepresentationData A).space

instance instCanonicalCoefficientNormed (A : Type uA) [NonUnitalCStarAlgebra A] :
    NormedAddCommGroup (CanonicalCoefficientSpace A) := (faithfulHilbertRepresentationData A).normed

instance instCanonicalCoefficientInner (A : Type uA) [NonUnitalCStarAlgebra A] :
    InnerProductSpace ℂ (CanonicalCoefficientSpace A) := (faithfulHilbertRepresentationData A).inner

instance instCanonicalCoefficientComplete (A : Type uA) [NonUnitalCStarAlgebra A] :
    CompleteSpace (CanonicalCoefficientSpace A) := (faithfulHilbertRepresentationData A).complete

/-- The canonical coefficient representation is the actual selected strict GN map. -/
def canonicalCoefficientRepresentation (A : Type uA) [NonUnitalCStarAlgebra A] :
    A →⋆ₙₐ[ℂ] (CanonicalCoefficientSpace A →L[ℂ] CanonicalCoefficientSpace A) :=
  (faithfulHilbertRepresentationData A).representation

/-- The canonical selected coefficient map is genuinely faithful. -/
theorem canonicalCoefficientRepresentation_injective (A : Type uA) [NonUnitalCStarAlgebra A] :
    Function.Injective (canonicalCoefficientRepresentation A) :=
  (faithfulHilbertRepresentationData A).injective_representation

/-- The canonical coefficient operator retains the original algebra norm. -/
theorem norm_canonicalCoefficientRepresentation (A : Type uA) [NonUnitalCStarAlgebra A] (a : A) :
    ‖canonicalCoefficientRepresentation A a‖ = ‖a‖ :=
  (faithfulHilbertRepresentationData A).norm_representation a

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.Regular] [μ.IsHaarMeasure] (α : PointNormCStarAction G A)

/-- The actual original Haar L2 carrier of the internally selected canonical GN coefficient space. -/
abbrev CanonicalRegularSpace := Lp (CanonicalCoefficientSpace A) 2 μ

/-- The actual canonical regular covariant pair, with no external coefficient-model input. -/
def canonicalRegularCovariantRepresentation : CovariantRepresentation α (CanonicalRegularSpace (A := A) μ) :=
  α.regularCovariantRepresentation (canonicalCoefficientRepresentation A) μ

/-- The canonical regular coefficient keeps the original inverse-action formula on every vector. -/
theorem canonicalRegularCoefficient_ae_eq (a : A) (ξ : CanonicalRegularSpace (A := A) μ) :
    (canonicalRegularCovariantRepresentation μ α).algebra a ξ =ᵐ[μ]
      fun s : G => canonicalCoefficientRepresentation A (α s⁻¹ a) (ξ s) :=
  α.regularCoefficientOperator_ae_eq (canonicalCoefficientRepresentation A) μ a ξ

/-- The canonical group's actual vector action is the original Haar inverse left translation. -/
theorem canonicalRegularGroup_ae_eq (g : G) (ξ : CanonicalRegularSpace (A := A) μ) :
    ((canonicalRegularCovariantRepresentation μ α).group g :
        CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) ξ =ᵐ[μ]
      fun s : G => ξ (g⁻¹ * s) :=
  StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G μ (CanonicalCoefficientSpace A) g ξ

end

end PointNormCStarAction
