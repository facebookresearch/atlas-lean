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

public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.EssentialCovariantRepresentation
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarIntegratedForm
public import MathlibExt.Analysis.InnerProductSpace.EssentialRestrictionNorm
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Essential restriction preserves Haar integrated norms

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. Let E be the closed
complex span of {π(a)ξ:a∈A,ξ∈H}, and let ρE be the coefficient and group representation
restricted to this invariant Hilbert subspace. Every Iρ(f) maps H into E. The integrated
operator of ρE is Iρ(f) restricted to E and has the same operator norm: ‖IρE(f)‖=‖Iρ(f)‖.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter

namespace CovariantRepresentation

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {α : PointNormCStarAction G A} (ρ : CovariantRepresentation α H)

/-- **Integrated vectors belong to the essential coefficient space.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. Let E be the closed
complex span of {π(a)ξ:a∈A,ξ∈H}, and let ρE be the coefficient and group representation
restricted to this invariant Hilbert subspace. For f∈Carrier μ α and ξ∈H, Iρ(f)ξ belongs to E.
-/
theorem haarIntegratedHom_mem_essentialSpace (f : HaarTwistedCore.Carrier μ α) (ξ : H) :
    haarIntegratedHom μ ρ f ξ ∈ ρ.algebra.essentialSpace := by
  let φ : G → ρ.algebra.essentialSpace := fun s =>
    ⟨ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ),
      ρ.algebra.range_mem_essentialSpace (f s) _⟩
  have hTransport : (∫ s : G, (φ s : H) ∂μ) =
      ρ.algebra.essentialSpace.subtypeₗᵢ (∫ s : G, φ s ∂μ) :=
    ρ.algebra.essentialSpace.subtypeₗᵢ.integral_comp_comm (μ := μ) φ
  rw [haarIntegratedHom_apply_vector]
  change (∫ s : G, (φ s : H) ∂μ) ∈ ρ.algebra.essentialSpace
  exact hTransport.symm ▸ (∫ s : G, φ s ∂μ).property

/-- **Integrated vector action after essential restriction.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. Let E be the closed
complex span of {π(a)ξ:a∈A,ξ∈H}, and let ρE be the coefficient and group representation
restricted to this invariant Hilbert subspace. For ξ∈E, the inclusion into H of IρE(f)ξ equals
Iρ(f)ξ.
-/
theorem essentialCovariantRepresentation_haarIntegratedHom_apply_coe
    (f : HaarTwistedCore.Carrier μ α) (ξ : ρ.algebra.essentialSpace) :
    (haarIntegratedHom μ ρ.essentialCovariantRepresentation f ξ : H) =
      haarIntegratedHom μ ρ f (ξ : H) := by
  let φ : G → ρ.algebra.essentialSpace := fun s =>
    ρ.essentialCovariantRepresentation.algebra (f s)
      ((ρ.essentialCovariantRepresentation.group s :
        ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace) ξ)
  have hTransport : (∫ s : G, ρ.algebra.essentialSpace.subtypeₗᵢ (φ s) ∂μ) =
      ρ.algebra.essentialSpace.subtypeₗᵢ (∫ s : G, φ s ∂μ) :=
    ρ.algebra.essentialSpace.subtypeₗᵢ.integral_comp_comm (μ := μ) φ
  calc
    (haarIntegratedHom μ ρ.essentialCovariantRepresentation f ξ : H) =
        ρ.algebra.essentialSpace.subtypeₗᵢ (∫ s : G, φ s ∂μ) := rfl
    _ = ∫ s : G, ρ.algebra.essentialSpace.subtypeₗᵢ (φ s) ∂μ := hTransport.symm
    _ = haarIntegratedHom μ ρ f (ξ : H) := by
      rw [haarIntegratedHom_apply_vector]
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => rfl

/-- **Integrated operator is the restriction to the essential space.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. Let E be the closed
complex span of {π(a)ξ:a∈A,ξ∈H}, and let ρE be the coefficient and group representation
restricted to this invariant Hilbert subspace. For every core coefficient f, the operator
IρE(f):E→E is the restriction of Iρ(f):H→H, with both domain and range restricted to E.
-/
theorem essentialCovariantRepresentation_haarIntegratedHom_eq
    (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ.essentialCovariantRepresentation f =
      ((haarIntegratedHom μ ρ f).domRestrict ρ.algebra.essentialSpace).codRestrict
        ρ.algebra.essentialSpace (fun ξ => haarIntegratedHom_mem_essentialSpace μ ρ f ξ) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  exact essentialCovariantRepresentation_haarIntegratedHom_apply_coe μ ρ f ξ

/-- **Integrated operator norm is preserved by essential restriction.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. Let E be the closed
complex span of {π(a)ξ:a∈A,ξ∈H}, and let ρE be the coefficient and group representation
restricted to this invariant Hilbert subspace. For every core coefficient f,
‖haarIntegratedHom μ ρ.essentialCovariantRepresentation f‖=‖haarIntegratedHom μ ρ f‖,
equivalently ‖IρE(f)‖=‖Iρ(f)‖.
-/
theorem norm_essentialCovariantRepresentation_haarIntegratedHom
    (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ.essentialCovariantRepresentation f‖ = ‖haarIntegratedHom μ ρ f‖ := by
  have hStarRange (ξ : H) : star (haarIntegratedHom μ ρ f) ξ ∈ ρ.algebra.essentialSpace := by
    rw [← map_star]
    exact haarIntegratedHom_mem_essentialSpace μ ρ (star f) ξ
  rw [essentialCovariantRepresentation_haarIntegratedHom_eq]
  exact ContinuousLinearMap.norm_domRestrict_codRestrict_eq_of_range_star
    (haarIntegratedHom μ ρ f) ρ.algebra.essentialSpace
    (fun ξ => haarIntegratedHom_mem_essentialSpace μ ρ f ξ) hStarRange

end

end CovariantRepresentation
