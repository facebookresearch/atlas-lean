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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarCovariantSeminorm
public import MathlibExt.Analysis.CStarAlgebra.EssentialNondegeneracy
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.GramIntegratedIdentity

/-!
# The full covariant norm and its C-star completion

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let N be the family of
seminorms f↦‖Iρ(f)‖ obtained from nondegenerate covariant representations ρ=(π,U) on complex
Hilbert spaces K:Type(max uG uA), where G:Type uG, A:Type uA, Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ,
and nondegeneracy means the closed span of π(A)K is K. The family N equals the family of
L¹-dominated C-star seminorms on the core. Hence the full covariant norm is
pmax(f)=sup{p(f):p∈N}, and its separated completion is a nonunital complex C-star algebra. The
canonical coefficient map ι has dense range and ‖ι(f)‖=pmax(f).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace HaarTwistedCore

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

/-- **Seminorms of nondegenerate covariant representations.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let N be the family of
seminorms f↦‖Iρ(f)‖ obtained from nondegenerate covariant representations ρ=(π,U) on complex
Hilbert spaces K:Type(max uG uA), where G:Type uG, A:Type uA, Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ,
and nondegeneracy means the closed span of π(A)K is K. This is the set
nondegenerateCovariantCStarSeminorms μ α.
-/
def nondegenerateCovariantCStarSeminorms : Set (CStarSeminorm (Carrier μ α)) :=
  {p | ∃ (K : Type (max uG uA)) (_hK1 : NormedAddCommGroup K)
      (_hK2 : InnerProductSpace ℂ K) (_hK3 : CompleteSpace K)
      (π : CovariantRepresentation α K),
      π.algebra.essentialSpace = ⊤ ∧
        CovariantRepresentation.haarIntegratedCStarSeminorm μ π = p}

/-- **Covariant seminorms equal the L¹-admissible family.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let N be the family of
seminorms f↦‖Iρ(f)‖ obtained from nondegenerate covariant representations ρ=(π,U) on complex
Hilbert spaces K:Type(max uG uA), where G:Type uG, A:Type uA, Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ,
and nondegeneracy means the closed span of π(A)K is K. Let S be the family of C-star seminorms
p on the core satisfying p(f)≤∫ s, ‖f(s)‖ ∂μ for every core coefficient f. Then N=S: each
L¹-dominated C-star seminorm is the integrated operator norm of a nondegenerate covariant
representation, and each such integrated norm is L¹-dominated.
-/
theorem nondegenerateCovariantCStarSeminorms_eq_admissible :
    nondegenerateCovariantCStarSeminorms μ α = admissibleCStarSeminorms μ α := by
  ext p
  constructor
  · rintro ⟨K, hK1, hK2, hK3, π, _hNondegenerate, hπ⟩
    let _ : NormedAddCommGroup K := hK1
    let _ : InnerProductSpace ℂ K := hK2
    let _ : CompleteSpace K := hK3
    rw [← hπ]
    exact CovariantRepresentation.haarIntegratedCStarSeminorm_mem_admissible μ π
  · intro hp
    obtain ⟨K, hK1, hK2, hK3, π, hNorm, hNondegenerate⟩ :=
      exists_admissibleCovariantNormModel_essentialSpace_eq_top μ α p hp
    let _ : NormedAddCommGroup K := hK1
    let _ : InnerProductSpace ℂ K := hK2
    let _ : CompleteSpace K := hK3
    refine ⟨K, hK1, hK2, hK3, π, hNondegenerate, ?_⟩
    apply CStarSeminorm.ext
    intro f
    exact (CovariantRepresentation.haarIntegratedCStarSeminorm_apply μ π f).trans (hNorm f)

/-- **An arbitrary covariant seminorm has a nondegenerate realization.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space in any independent universe and ρ=(π,U) a covariant representation of α on H.
Let N be the family of seminorms f↦‖Iρ(f)‖ obtained from nondegenerate covariant
representations ρ=(π,U) on complex Hilbert spaces K:Type(max uG uA), where G:Type uG, A:Type
uA, Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ, and nondegeneracy means the closed span of π(A)K is K. Its
seminorm f↦‖Iρ(f)‖ belongs to N; the realization in N need not use H itself.
-/
theorem haarIntegratedCStarSeminorm_mem_nondegenerateCovariantFamily
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : CovariantRepresentation α H) :
    CovariantRepresentation.haarIntegratedCStarSeminorm μ ρ ∈
      nondegenerateCovariantCStarSeminorms μ α := by
  rw [nondegenerateCovariantCStarSeminorms_eq_admissible]
  exact CovariantRepresentation.haarIntegratedCStarSeminorm_mem_admissible μ ρ

/-- **Full covariant norm of a core coefficient.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let N be the family of
seminorms f↦‖Iρ(f)‖ obtained from nondegenerate covariant representations ρ=(π,U) on complex
Hilbert spaces K:Type(max uG uA), where G:Type uG, A:Type uA, Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ,
and nondegeneracy means the closed span of π(A)K is K. The value fullCovariantNorm μ α f is
sup{p(f):p∈N}, equivalently the maximal L¹-dominated C-star seminorm at f.
-/
def fullCovariantNorm (f : Carrier μ α) : ℝ := maximalCStarSeminorm μ α f

/-- **Supremum formula for the full covariant norm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let N be the family of
seminorms f↦‖Iρ(f)‖ obtained from nondegenerate covariant representations ρ=(π,U) on complex
Hilbert spaces K:Type(max uG uA), where G:Type uG, A:Type uA, Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ,
and nondegeneracy means the closed span of π(A)K is K. For each f∈Carrier μ α,
fullCovariantNorm μ α f=sup{p(f):p∈N}, the real supremum of the nondegenerate integrated
representation norms.
-/
theorem fullCovariantNorm_eq_sSup (f : Carrier μ α) :
    fullCovariantNorm μ α f =
      SupSet.sSup ((fun p : CStarSeminorm (Carrier μ α) => p f) ''
        nondegenerateCovariantCStarSeminorms μ α) := by
  rw [nondegenerateCovariantCStarSeminorms_eq_admissible]
  exact maximalCStarSeminorm_apply μ α f

/-- **The full covariant C-star completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Write pmax(f)=sup{p(f):p
is a C-star seminorm on the core and p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k}. Let
X=FullCovariantCompletion μ α be the separated completion in pmax, with dense map ι. The
completed algebra is the completion for the full covariant norm, equal to pmax; this is
FullCovariantCompletion μ α.
-/
abbrev FullCovariantCompletion := (maximalCStarSeminorm μ α).NonUnitalCompletion

/-- **C-star algebra structure on the full completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Write pmax(f)=sup{p(f):p
is a C-star seminorm on the core and p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k}. Let
X=FullCovariantCompletion μ α be the separated completion in pmax, with dense map ι. The
algebra X is a nonunital complex C-star algebra with ‖ι(f)‖=pmax(f) on the core and
‖star(x)*x‖=‖x‖² for x∈X.
-/
@[instance_reducible]
def fullCovariantCompletionCStarAlgebra : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
  (maximalCStarSeminorm μ α).nonUnitalCompletionCStarAlgebra

/-- **Canonical coefficient map into the full completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Write pmax(f)=sup{p(f):p
is a C-star seminorm on the core and p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k}. Let
X=FullCovariantCompletion μ α be the separated completion in pmax, with dense map ι. The map
toFullCovariantCompletion μ α:Carrier μ α→X is the nonunital complex star homomorphism ι
sending a core coefficient to its separated completion class.
-/
def toFullCovariantCompletion :
    let _ : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
      fullCovariantCompletionCStarAlgebra μ α
    Carrier μ α →⋆ₙₐ[ℂ] FullCovariantCompletion μ α :=
  (maximalCStarSeminorm μ α).toNonUnitalCompletion

omit [μ.Regular] in
/-- **Norm of a dense full covariant coefficient class.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Write pmax(f)=sup{p(f):p
is a C-star seminorm on the core and p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k}. Let
X=FullCovariantCompletion μ α be the separated completion in pmax, with dense map ι. For every
f∈Carrier μ α, ‖toFullCovariantCompletion μ α f‖=fullCovariantNorm μ α f=pmax(f).
-/
theorem norm_toFullCovariantCompletion (f : Carrier μ α) :
    let _ : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
      fullCovariantCompletionCStarAlgebra μ α
    ‖toFullCovariantCompletion μ α f‖ = fullCovariantNorm μ α f := by
  let _ : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
    fullCovariantCompletionCStarAlgebra μ α
  exact (maximalCStarSeminorm μ α).norm_toNonUnitalCompletion f

omit [μ.Regular] in
/-- **Density of full covariant coefficient classes.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Write pmax(f)=sup{p(f):p
is a C-star seminorm on the core and p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k}. Let
X=FullCovariantCompletion μ α be the separated completion in pmax, with dense map ι. The range
of toFullCovariantCompletion μ α is dense in X in its C-star norm.
-/
theorem denseRange_toFullCovariantCompletion :
    let _ : NonUnitalCStarAlgebra (FullCovariantCompletion μ α) :=
      fullCovariantCompletionCStarAlgebra μ α
    DenseRange (toFullCovariantCompletion μ α) :=
  (maximalCStarSeminorm μ α).denseRange_toNonUnitalCompletion

end

end HaarTwistedCore
