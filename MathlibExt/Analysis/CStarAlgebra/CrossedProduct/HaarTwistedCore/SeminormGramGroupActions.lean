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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.SeminormGroupActions
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Group invariance of finite represented Gram sums

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let H be a complex Hilbert space in an independent universe and σ:Xp→B(H)
a nonunital complex star homomorphism. Put T(f)=σ(ιp(f)) and L_g f(s)=α_g(f(g⁻¹*s)).
Translating every coefficient by the same g preserves the pairwise inner products ⟪T(L_g
f)ξ,T(L_g h)η⟫=⟪T(f)ξ,T(h)η⟫. Consequently inner products and norms of arbitrary finite
complex-weighted sums of these vectors are unchanged.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace HaarTwistedCore

noncomputable section

universe uG uA uH uI uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α)) (H : Type uH)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- **Pairwise represented Gram invariance.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let H be a complex Hilbert space in an independent universe and σ:Xp→B(H)
a nonunital complex star homomorphism. Put T(f)=σ(ιp(f)) and L_g f(s)=α_g(f(g⁻¹*s)). For g∈G,
core coefficients f,h and ξ,η∈H, ⟪T(L_g f)ξ,T(L_g h)η⟫_ℂ=⟪T(f)ξ,T(h)η⟫_ℂ.
-/
theorem completedRepresentation_groupLeft_inner (g : G) (f h : Carrier μ α) (ξ η : H) :
    ⟪σ (p.toNonUnitalCompletion (groupLeft μ α g f)) ξ,
      σ (p.toNonUnitalCompletion (groupLeft μ α g h)) η⟫_ℂ =
      ⟪σ (p.toNonUnitalCompletion f) ξ, σ (p.toNonUnitalCompletion h) η⟫_ℂ := by
  have hGram (a b : Carrier μ α) (x y : H) :
      ⟪σ (p.toNonUnitalCompletion a) x, σ (p.toNonUnitalCompletion b) y⟫_ℂ =
        ⟪x, σ (p.toNonUnitalCompletion (star a * b)) y⟫_ℂ := by
    have hproduct : σ (p.toNonUnitalCompletion (star a * b)) =
        star (σ (p.toNonUnitalCompletion a)) * σ (p.toNonUnitalCompletion b) := by
      rw [map_mul, map_mul, map_star, map_star]
    rw [hproduct]
    change ⟪σ (p.toNonUnitalCompletion a) x, σ (p.toNonUnitalCompletion b) y⟫_ℂ =
      ⟪x, star (σ (p.toNonUnitalCompletion a)) (σ (p.toNonUnitalCompletion b) y)⟫_ℂ
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  calc
    ⟪σ (p.toNonUnitalCompletion (groupLeft μ α g f)) ξ,
        σ (p.toNonUnitalCompletion (groupLeft μ α g h)) η⟫_ℂ =
      ⟪ξ, σ (p.toNonUnitalCompletion (star (groupLeft μ α g f) * groupLeft μ α g h)) η⟫_ℂ :=
        hGram _ _ _ _
    _ = ⟪ξ, σ (p.toNonUnitalCompletion (star f * h)) η⟫_ℂ := by
      rw [star_groupLeft_mul_groupLeft]
    _ = ⟪σ (p.toNonUnitalCompletion f) ξ, σ (p.toNonUnitalCompletion h) η⟫_ℂ :=
      (hGram f h ξ η).symm

/-- **Inner products of two finite translated Gram sums.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let H be a complex Hilbert space in an independent universe and σ:Xp→B(H)
a nonunital complex star homomorphism. Put T(f)=σ(ιp(f)) and L_g f(s)=α_g(f(g⁻¹*s)). Let s⊂I
and t⊂J be finite sets, c:I→ℂ, d:J→ℂ, f:I→Carrier μ α, h:J→Carrier μ α, ξ:I→H and η:J→H. Then
⟪∑i∈s c_i•T(L_g f_i)ξ_i,∑j∈t d_j•T(L_g h_j)η_j⟫ equals ⟪∑i∈s c_i•T(f_i)ξ_i,∑j∈t
d_j•T(h_j)η_j⟫. The finite index types may lie in independent universes.
-/
theorem inner_sum_completedRepresentation_groupLeft
    {ι : Type uI} {κ : Type uJ} (g : G) (s : Finset ι) (t : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ) (f : ι → Carrier μ α) (h : κ → Carrier μ α)
    (ξ : ι → H) (η : κ → H) :
    ⟪∑ i ∈ s, c i • σ (p.toNonUnitalCompletion (groupLeft μ α g (f i))) (ξ i),
      ∑ j ∈ t, d j • σ (p.toNonUnitalCompletion (groupLeft μ α g (h j))) (η j)⟫_ℂ =
      ⟪∑ i ∈ s, c i • σ (p.toNonUnitalCompletion (f i)) (ξ i),
        ∑ j ∈ t, d j • σ (p.toNonUnitalCompletion (h j)) (η j)⟫_ℂ := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun z : ℂ => d i * z)
  apply Finset.sum_congr rfl
  intro j _
  rw [completedRepresentation_groupLeft_inner μ α p H σ g]

/-- **Norm of a finite translated Gram sum.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let H be a complex Hilbert space in an independent universe and σ:Xp→B(H)
a nonunital complex star homomorphism. Put T(f)=σ(ιp(f)) and L_g f(s)=α_g(f(g⁻¹*s)). For a
finite set s⊂I, weights c:I→ℂ, coefficients f:I→Carrier μ α and vectors ξ:I→H, ‖∑i∈s c_i•T(L_g
f_i)ξ_i‖=‖∑i∈s c_i•T(f_i)ξ_i‖. This includes the empty sum and zero Hilbert space.
-/
theorem norm_sum_completedRepresentation_groupLeft
    {ι : Type uI} (g : G) (s : Finset ι) (c : ι → ℂ) (f : ι → Carrier μ α) (ξ : ι → H) :
    ‖∑ i ∈ s, c i • σ (p.toNonUnitalCompletion (groupLeft μ α g (f i))) (ξ i)‖ =
      ‖∑ i ∈ s, c i • σ (p.toNonUnitalCompletion (f i)) (ξ i)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hInner := inner_sum_completedRepresentation_groupLeft μ α p H σ g s s c c f f ξ ξ
  simpa only [norm_sq_eq_re_inner (𝕜 := ℂ)] using congrArg (RCLike.re : ℂ → ℝ) hInner

end

end HaarTwistedCore
