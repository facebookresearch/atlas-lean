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
# Canonical Haar regular covariant representation

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let
H_A=CanonicalCoefficientSpace A and π_A=canonicalCoefficientRepresentation A be the faithful
Hilbert representation given by the nonunital Gelfand–Naimark construction. If A:Type uA, then
H_A:Type uA. Put K=L²(G,μ;H_A)=CanonicalRegularSpace μ. The regular pair has
(Π(a)ξ)(s)=π_A(α_(s⁻¹)(a))ξ(s) and (λ_g ξ)(s)=ξ(g⁻¹*s), with equality of L² representatives
understood μ-almost everywhere. The pair (Π,λ) is a covariant representation of α on K. The
coefficient representation π_A is injective and isometric.
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

/-- **Canonical Hilbert space for a C-star algebra.**

For a nonunital complex C-star algebra A:Type uA, CanonicalCoefficientSpace A is the complete
complex Hilbert space H_A:Type uA chosen by the faithful nonunital Gelfand–Naimark
representation.
-/
abbrev CanonicalCoefficientSpace (A : Type uA) [NonUnitalCStarAlgebra A] : Type uA :=
  (faithfulHilbertRepresentationData A).space

instance instCanonicalCoefficientNormed (A : Type uA) [NonUnitalCStarAlgebra A] :
    NormedAddCommGroup (CanonicalCoefficientSpace A) := (faithfulHilbertRepresentationData A).normed

instance instCanonicalCoefficientInner (A : Type uA) [NonUnitalCStarAlgebra A] :
    InnerProductSpace ℂ (CanonicalCoefficientSpace A) := (faithfulHilbertRepresentationData A).inner

instance instCanonicalCoefficientComplete (A : Type uA) [NonUnitalCStarAlgebra A] :
    CompleteSpace (CanonicalCoefficientSpace A) := (faithfulHilbertRepresentationData A).complete

/-- **Canonical faithful coefficient representation.**

For a nonunital complex C-star algebra A, canonicalCoefficientRepresentation A:A→B(H_A), with
H_A=CanonicalCoefficientSpace A, is the nonunital complex star homomorphism from the faithful
Gelfand–Naimark construction.
-/
def canonicalCoefficientRepresentation (A : Type uA) [NonUnitalCStarAlgebra A] :
    A →⋆ₙₐ[ℂ] (CanonicalCoefficientSpace A →L[ℂ] CanonicalCoefficientSpace A) :=
  (faithfulHilbertRepresentationData A).representation

/-- **Faithfulness of the canonical coefficient representation.**

For a nonunital complex C-star algebra A and H_A=CanonicalCoefficientSpace A, the homomorphism
π_A=canonicalCoefficientRepresentation A:A→B(H_A) is injective.
-/
theorem canonicalCoefficientRepresentation_injective (A : Type uA) [NonUnitalCStarAlgebra A] :
    Function.Injective (canonicalCoefficientRepresentation A) :=
  (faithfulHilbertRepresentationData A).injective_representation

/-- **Norm preservation of the canonical coefficient representation.**

For a nonunital complex C-star algebra A, a∈A and H_A=CanonicalCoefficientSpace A,
‖canonicalCoefficientRepresentation A a‖=‖a‖, with the operator norm on B(H_A).
-/
theorem norm_canonicalCoefficientRepresentation (A : Type uA) [NonUnitalCStarAlgebra A] (a : A) :
    ‖canonicalCoefficientRepresentation A a‖ = ‖a‖ :=
  (faithfulHilbertRepresentationData A).norm_representation a

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.Regular] [μ.IsHaarMeasure] (α : PointNormCStarAction G A)

/-- **Hilbert space of the canonical Haar regular representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let
H_A=CanonicalCoefficientSpace A and π_A=canonicalCoefficientRepresentation A be the faithful
Hilbert representation given by the nonunital Gelfand–Naimark construction. If A:Type uA, then
H_A:Type uA. CanonicalRegularSpace μ is K=L²(G,μ;H_A), with its vector-valued L² inner product
and norm.
-/
abbrev CanonicalRegularSpace := Lp (CanonicalCoefficientSpace A) 2 μ

/-- **Canonical regular covariant pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let
H_A=CanonicalCoefficientSpace A and π_A=canonicalCoefficientRepresentation A be the faithful
Hilbert representation given by the nonunital Gelfand–Naimark construction. If A:Type uA, then
H_A:Type uA. Put K=L²(G,μ;H_A)=CanonicalRegularSpace μ. The regular pair has
(Π(a)ξ)(s)=π_A(α_(s⁻¹)(a))ξ(s) and (λ_g ξ)(s)=ξ(g⁻¹*s), with equality of L² representatives
understood μ-almost everywhere. The pair canonicalRegularCovariantRepresentation μ α=(Π,λ)
satisfies λ_g Π(a) λ_g*=Π(α_g(a)).
-/
def canonicalRegularCovariantRepresentation :
    CovariantRepresentation α (CanonicalRegularSpace (A := A) μ) :=
  α.regularCovariantRepresentation (canonicalCoefficientRepresentation A) μ

/-- **Canonical regular coefficient action almost everywhere.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let
H_A=CanonicalCoefficientSpace A and π_A=canonicalCoefficientRepresentation A be the faithful
Hilbert representation given by the nonunital Gelfand–Naimark construction. If A:Type uA, then
H_A:Type uA. On K=CanonicalRegularSpace μ=L²(G,μ;H_A),
(canonicalRegularCovariantRepresentation μ α).algebra a ξ agrees μ-almost everywhere with
s↦π_A(α_(s⁻¹)(a))ξ(s).
-/
theorem canonicalRegularCoefficient_ae_eq (a : A) (ξ : CanonicalRegularSpace (A := A) μ) :
    (canonicalRegularCovariantRepresentation μ α).algebra a ξ =ᵐ[μ]
      fun s : G => canonicalCoefficientRepresentation A (α s⁻¹ a) (ξ s) :=
  α.regularCoefficientOperator_ae_eq (canonicalCoefficientRepresentation A) μ a ξ

/-- **Canonical regular group action almost everywhere.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let
H_A=CanonicalCoefficientSpace A and π_A=canonicalCoefficientRepresentation A be the faithful
Hilbert representation given by the nonunital Gelfand–Naimark construction. If A:Type uA, then
H_A:Type uA. On K=CanonicalRegularSpace μ=L²(G,μ;H_A), the group operator of
canonicalRegularCovariantRepresentation μ α at g sends ξ to a representative equal μ-almost
everywhere to s↦ξ(g⁻¹*s).
-/
theorem canonicalRegularGroup_ae_eq (g : G) (ξ : CanonicalRegularSpace (A := A) μ) :
    ((canonicalRegularCovariantRepresentation μ α).group g :
        CanonicalRegularSpace (A := A) μ →L[ℂ] CanonicalRegularSpace (A := A) μ) ξ =ᵐ[μ]
      fun s : G => ξ (g⁻¹ * s) :=
  StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq
    G μ (CanonicalCoefficientSpace A) g ξ

end

end PointNormCStarAction
