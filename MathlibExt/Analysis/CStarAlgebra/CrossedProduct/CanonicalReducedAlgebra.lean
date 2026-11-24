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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.CanonicalHaarRegularModel
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarCovariantSeminorm
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Topology.Constructions

/-!
# Actual reduced operator closure for the fixed canonical regular pair

Use the strictly constructed canonical GN coefficient space and original
regular Haar covariant pair. Its literal integrated image is a nonunital
star subalgebra of the original bounded L2 operators. Take the actual
operator-norm topological closure and its inherited nonunital C-star data.
The original core map is literal codomain restriction with the same norm.

No Hilbert witness, coefficient representation, reduced model, norm or
comparison equivalence is supplied as a constructor input. Independence
from other faithful coefficient representations is a separate source
statement and is not used as data here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped CStarAlgebra

namespace PointNormCStarAction

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.Regular] [μ.IsHaarMeasure] (α : PointNormCStarAction G A)

/-- The original bounded operators on the canonical regular Hilbert space have their stock C-star structure. -/
local instance : CStarAlgebra
    (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) :=
  inferInstance

/-- The original integrated homomorphism of the internally constructed canonical regular pair. -/
def canonicalRegularIntegratedHom : HaarTwistedCore.Carrier μ α →⋆ₙₐ[ℂ]
    (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) :=
  CovariantRepresentation.haarIntegratedHom μ (canonicalRegularCovariantRepresentation μ α)

/-- The actual canonical regular integrated norm as the existing C-star seminorm pullback. -/
def canonicalRegularSeminorm : CStarSeminorm (HaarTwistedCore.Carrier μ α) :=
  CovariantRepresentation.haarIntegratedCStarSeminorm μ (canonicalRegularCovariantRepresentation μ α)

/-- Every canonical regular seminorm value is the literal original integrated operator norm. -/
@[simp]
theorem canonicalRegularSeminorm_apply (f : HaarTwistedCore.Carrier μ α) :
    canonicalRegularSeminorm μ α f = ‖canonicalRegularIntegratedHom μ α f‖ := rfl

/-- The original full maximal norm bounds each actual canonical regular integrated value. -/
theorem canonicalRegularSeminorm_le_maximal (f : HaarTwistedCore.Carrier μ α) :
    canonicalRegularSeminorm μ α f ≤ HaarTwistedCore.maximalCStarSeminorm μ α f :=
  HaarTwistedCore.le_maximalCStarSeminorm μ α
    (CovariantRepresentation.haarIntegratedCStarSeminorm_mem_admissible μ
      (canonicalRegularCovariantRepresentation μ α)) f

/-- The literal operator-norm closure of the original canonical regular integrated image. -/
def canonicalReducedSubalgebra : NonUnitalStarSubalgebra ℂ
    (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) :=
  (canonicalRegularIntegratedHom μ α).range.topologicalClosure

/-- The actual reduced operator subalgebra is closed in the original bounded-operator norm. -/
instance isClosed_canonicalReducedSubalgebra :
    IsClosed (canonicalReducedSubalgebra μ α :
      Set (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ)) :=
  (canonicalRegularIntegratedHom μ α).range.isClosed_topologicalClosure

/-- The actual reduced C-star carrier is that same closed operator subalgebra. -/
abbrev CanonicalReducedAlgebra := ↥(canonicalReducedSubalgebra μ α)

/-- The inherited actual nonunital C-star dictionaries on the same reduced operator closure. -/
instance canonicalReducedCStarAlgebra : NonUnitalCStarAlgebra (CanonicalReducedAlgebra μ α) :=
  inferInstanceAs (NonUnitalCStarAlgebra (canonicalReducedSubalgebra μ α))

/-- The original source coefficient map into its actual canonical reduced operator closure. -/
def toCanonicalReducedAlgebra : HaarTwistedCore.Carrier μ α →⋆ₙₐ[ℂ] CanonicalReducedAlgebra μ α :=
  (canonicalRegularIntegratedHom μ α).codRestrict (canonicalReducedSubalgebra μ α)
    fun f => (canonicalRegularIntegratedHom μ α).range.le_topologicalClosure
      ((canonicalRegularIntegratedHom μ α).mem_range_self f)

/-- The original core map is dense in its literal canonical reduced operator closure. -/
theorem denseRange_toCanonicalReducedAlgebra : DenseRange (toCanonicalReducedAlgebra μ α) := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  change closure (Set.range (canonicalRegularIntegratedHom μ α)) ⊆
    closure (Set.range (canonicalRegularIntegratedHom μ α))
  exact fun _ hx => hx

/-- The original inclusion of the reduced operator closure into its actual L2 operators. -/
def canonicalReducedAlgebraInclusion : CanonicalReducedAlgebra μ α →⋆ₙₐ[ℂ]
    (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) :=
  NonUnitalStarSubalgebraClass.subtype (canonicalReducedSubalgebra μ α)

/-- Every original reduced image has exactly its original canonical regular integrated value. -/
@[simp]
theorem toCanonicalReducedAlgebra_apply (f : HaarTwistedCore.Carrier μ α) :
    canonicalReducedAlgebraInclusion μ α (toCanonicalReducedAlgebra μ α f) =
      canonicalRegularIntegratedHom μ α f := rfl

/-- The original reduced coefficient image has the exact actual canonical regular seminorm. -/
theorem norm_toCanonicalReducedAlgebra (f : HaarTwistedCore.Carrier μ α) :
    ‖toCanonicalReducedAlgebra μ α f‖ = canonicalRegularSeminorm μ α f := rfl

end

end PointNormCStarAction
