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
# The canonical reduced Haar crossed-product algebra

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). The closed
nonunital star subalgebra Rred is a nonunital complex C-star algebra. Its coefficient
homomorphism f↦Ireg(f) has dense range and norm qreg(f)=‖Ireg(f)‖, bounded by the maximal
L¹-dominated C-star seminorm.
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

/-- **C-star algebra of canonical regular operators.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. On
K=CanonicalRegularSpace μ=L²(G,μ;CanonicalCoefficientSpace A), the bounded complex linear
operators B(K) form a C-star algebra with composition, operator adjoint and operator norm.
-/
local instance : CStarAlgebra
    (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) :=
  inferInstance

/-- **Canonical regular integrated homomorphism.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). The nonunital
complex star homomorphism canonicalRegularIntegratedHom μ α:Carrier μ α→B(K) is f↦Ireg(f).
-/
def canonicalRegularIntegratedHom : HaarTwistedCore.Carrier μ α →⋆ₙₐ[ℂ]
    (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) :=
  CovariantRepresentation.haarIntegratedHom μ (canonicalRegularCovariantRepresentation μ α)

/-- **Canonical regular C-star seminorm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). The C-star
seminorm canonicalRegularSeminorm μ α on the twisted coefficient core is qreg(f)=‖Ireg(f)‖.
-/
def canonicalRegularSeminorm : CStarSeminorm (HaarTwistedCore.Carrier μ α) :=
  CovariantRepresentation.haarIntegratedCStarSeminorm μ (canonicalRegularCovariantRepresentation μ α)

/-- **Value of the canonical regular seminorm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). For f∈Carrier μ
α, canonicalRegularSeminorm μ α f=‖canonicalRegularIntegratedHom μ α f‖=‖Ireg(f)‖.
-/
@[simp]
theorem canonicalRegularSeminorm_apply (f : HaarTwistedCore.Carrier μ α) :
    canonicalRegularSeminorm μ α f = ‖canonicalRegularIntegratedHom μ α f‖ := rfl

/-- **The maximal seminorm bounds the canonical regular one.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). For a core
coefficient f, qreg(f)=‖Ireg(f)‖≤pmax(f), where pmax is the supremum of all C-star seminorms p
with p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k.
-/
theorem canonicalRegularSeminorm_le_maximal (f : HaarTwistedCore.Carrier μ α) :
    canonicalRegularSeminorm μ α f ≤ HaarTwistedCore.maximalCStarSeminorm μ α f :=
  HaarTwistedCore.le_maximalCStarSeminorm μ α
    (CovariantRepresentation.haarIntegratedCStarSeminorm_mem_admissible μ
      (canonicalRegularCovariantRepresentation μ α)) f

/-- **Closed operator subalgebra generated by regular coefficients.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). The nonunital
complex star subalgebra canonicalReducedSubalgebra μ α is Rred=closure(range Ireg), where
closure is taken in the operator norm on B(K).
-/
def canonicalReducedSubalgebra : NonUnitalStarSubalgebra ℂ
    (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) :=
  (canonicalRegularIntegratedHom μ α).range.topologicalClosure

/-- **Closedness of the reduced regular operator algebra.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). The subalgebra
canonicalReducedSubalgebra μ α=Rred is closed in the operator-norm topology of B(K).
-/
instance isClosed_canonicalReducedSubalgebra :
    IsClosed (canonicalReducedSubalgebra μ α :
      Set (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ)) :=
  (canonicalRegularIntegratedHom μ α).range.isClosed_topologicalClosure

/-- **Canonical reduced C-star algebra carrier.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K).
CanonicalReducedAlgebra μ α is the closed subalgebra Rred, equipped with the algebraic
operations and norm inherited from B(K).
-/
abbrev CanonicalReducedAlgebra := ↥(canonicalReducedSubalgebra μ α)

/-- **C-star structure of the reduced regular closure.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). The algebra
CanonicalReducedAlgebra μ α=Rred is a nonunital complex C-star algebra: ‖star(x)*x‖=‖x‖² for
x∈Rred.
-/
instance canonicalReducedCStarAlgebra : NonUnitalCStarAlgebra (CanonicalReducedAlgebra μ α) :=
  inferInstanceAs (NonUnitalCStarAlgebra (canonicalReducedSubalgebra μ α))

/-- **Core coefficient map into the canonical reduced algebra.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). The nonunital
complex star homomorphism toCanonicalReducedAlgebra μ α:Carrier μ α→Rred sends f to Ireg(f),
viewed as an element of the closed regular operator subalgebra.
-/
def toCanonicalReducedAlgebra : HaarTwistedCore.Carrier μ α →⋆ₙₐ[ℂ] CanonicalReducedAlgebra μ α :=
  (canonicalRegularIntegratedHom μ α).codRestrict (canonicalReducedSubalgebra μ α)
    fun f => (canonicalRegularIntegratedHom μ α).range.le_topologicalClosure
      ((canonicalRegularIntegratedHom μ α).mem_range_self f)

/-- **Density of the canonical reduced coefficient map.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). The map
toCanonicalReducedAlgebra μ α:f↦Ireg(f) has dense range in Rred for the inherited operator
norm.
-/
theorem denseRange_toCanonicalReducedAlgebra : DenseRange (toCanonicalReducedAlgebra μ α) := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  change closure (Set.range (canonicalRegularIntegratedHom μ α)) ⊆
    closure (Set.range (canonicalRegularIntegratedHom μ α))
  exact fun _ hx => hx

/-- **Inclusion of the canonical reduced algebra into regular operators.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). The nonunital
complex star homomorphism canonicalReducedAlgebraInclusion μ α:Rred→B(K) is the inclusion of
the closed regular operator subalgebra.
-/
def canonicalReducedAlgebraInclusion : CanonicalReducedAlgebra μ α →⋆ₙₐ[ℂ]
    (CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) :=
  NonUnitalStarSubalgebraClass.subtype (canonicalReducedSubalgebra μ α)

/-- **Reduced coefficient images as regular integrated operators.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). For f∈Carrier μ
α, canonicalReducedAlgebraInclusion μ α (toCanonicalReducedAlgebra μ α
f)=canonicalRegularIntegratedHom μ α f=Ireg(f).
-/
@[simp]
theorem toCanonicalReducedAlgebra_apply (f : HaarTwistedCore.Carrier μ α) :
    canonicalReducedAlgebraInclusion μ α (toCanonicalReducedAlgebra μ α f) =
      canonicalRegularIntegratedHom μ α f := rfl

/-- **Norm of a canonical reduced coefficient image.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For the canonical
regular pair (Π,λ) on K=L²(G,μ;CanonicalCoefficientSpace A), put Ireg(f)ξ=∫ s, Π(f(s))(λ_s ξ)
∂μ. Let Rred be the operator-norm closure of {Ireg(f):f∈Carrier μ α} in B(K). For f∈Carrier μ
α, ‖toCanonicalReducedAlgebra μ α f‖=canonicalRegularSeminorm μ α f=‖Ireg(f)‖.
-/
theorem norm_toCanonicalReducedAlgebra (f : HaarTwistedCore.Carrier μ α) :
    ‖toCanonicalReducedAlgebra μ α f‖ = canonicalRegularSeminorm μ α f := rfl

end

end PointNormCStarAction
