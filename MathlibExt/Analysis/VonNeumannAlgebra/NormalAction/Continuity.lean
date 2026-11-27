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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Real.Sqrt

/-!
# Vector continuity of a normal predual action

Let `G` be a topological group and `α` a normal action on a concrete von Neumann algebra `M ⊆
B(H)`, where `H` is a complete complex Hilbert space. Norm continuity of inverse predual orbits
implies continuity of `g ↦ φ(α_g(x))` for every `φ ∈ M_*` and `x ∈ M`.

For each fixed `x ∈ M`, the vector action `(g,ξ) ↦ α_g(x)ξ` is jointly continuous in the group
topology and Hilbert norm. No local compactness or separability of the group is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra
namespace NormalAction

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- **Normal coefficient continuity of a forward action orbit.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such
that `g ↦ φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. assume additionally
that `G` is a topological group. For `φ ∈ M_*` and `x ∈ M`, `g ↦ φ(α_g(x))` is continuous
in `ℂ`. -/
theorem continuous_normalFunctional_apply (α : NormalAction G M)
    (φ : normalFunctionalSpace M) (x : M) :
    Continuous fun g : G => (φ : StrongDual ℂ M) (α g x) := by
  have h := (ContinuousLinearMap.apply ℂ ℂ x).continuous.comp
    (continuous_subtype_val.comp ((α.predualAction_continuous φ).comp continuous_inv))
  have heq :
      (fun g : G => (α.predualAction g⁻¹ φ : StrongDual ℂ M) x) =
        (fun g : G => (φ : StrongDual ℂ M) (α g x)) := by
    funext g
    rw [predualAction_apply, map_inv]
    change (φ : StrongDual ℂ M) ((α g).symm.symm x) = (φ : StrongDual ℂ M) (α g x)
    rw [NormalStarAlgEquiv.symm_symm]
  change Continuous (fun g : G => (α.predualAction g⁻¹ φ : StrongDual ℂ M) x) at h
  rw [heq] at h
  exact h

/-- **Norm-continuous vector orbit of a normal action.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such
that `g ↦ φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. assume `G` is a
topological group. For `x ∈ M` and `ξ ∈ H`, `g ↦ (α_g(x) : B(H))ξ` is norm-continuous in
`H`. -/
theorem continuous_vector_apply (α : NormalAction G M) (x : M) (ξ : H) :
    Continuous fun g : G => (α g x : H →L[ℂ] H) ξ := by
  let F : G → H := fun g => (α g x : H →L[ℂ] H) ξ
  change Continuous F
  rw [continuous_iff_continuousAt]
  intro g₀
  change Tendsto F (𝓝 g₀) (𝓝 (F g₀))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let w : H := F g₀
  let φ₁ : normalFunctionalSpace M :=
    ⟨vectorFunctional M ξ ξ, vectorFunctional_mem_normalFunctionalSpace M ξ ξ⟩
  let φ₂ : normalFunctionalSpace M :=
    ⟨vectorFunctional M w ξ, vectorFunctional_mem_normalFunctionalSpace M w ξ⟩
  have hdiag (g : G) :
      ((φ₁ : StrongDual ℂ M) (α g (star x * x))).re = ‖F g‖ ^ 2 := by
    change (vectorFunctional M ξ ξ (α g (star x * x))).re = ‖F g‖ ^ 2
    rw [map_mul, map_star, vectorFunctional_apply]
    change (⟪ξ, ((ContinuousLinearMap.adjoint (α g x : H →L[ℂ] H)) ∘L
        (α g x : H →L[ℂ] H)) ξ⟫_ℂ).re = ‖(α g x : H →L[ℂ] H) ξ‖ ^ 2
    exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right
      (α g x : H →L[ℂ] H) ξ).symm
  have hcross (g : G) :
      ((φ₂ : StrongDual ℂ M) (α g x)).re = (⟪F g, w⟫_ℂ).re := by
    change (vectorFunctional M w ξ (α g x)).re = (⟪F g, w⟫_ℂ).re
    rw [vectorFunctional_apply]
    exact inner_re_symm (𝕜 := ℂ) w (F g)
  have heq :
      (fun g : G => ‖F g - w‖ ^ 2) =
        (fun g : G => ((φ₁ : StrongDual ℂ M) (α g (star x * x))).re -
          2 * ((φ₂ : StrongDual ℂ M) (α g x)).re + ‖w‖ ^ 2) := by
    funext g
    rw [norm_sub_sq (𝕜 := ℂ), RCLike.re_eq_complex_re, hdiag g, hcross g]
  have hsquare : Continuous fun g : G => ‖F g - w‖ ^ 2 := by
    rw [heq]
    exact ((Complex.continuous_re.comp
        (continuous_normalFunctional_apply α φ₁ (star x * x))).sub
      (continuous_const.mul (Complex.continuous_re.comp
        (continuous_normalFunctional_apply α φ₂ x)))).add continuous_const
  have hnorm : Continuous fun g : G => ‖F g - w‖ := by
    have hroot : (fun g : G => Real.sqrt (‖F g - w‖ ^ 2)) =
        (fun g : G => ‖F g - w‖) := by
      funext g
      exact Real.sqrt_sq (norm_nonneg (F g - w))
    rw [← hroot]
    exact Real.continuous_sqrt.comp hsquare
  simpa only [w, sub_self, norm_zero] using hnorm.tendsto g₀

/-- **Joint group and vector continuity of a normal action.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such
that `g ↦ φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. assume `G` is a
topological group. For fixed `x ∈ M`, the map `(g,ξ) ↦ (α_g(x) : B(H))ξ` is continuous
from `G×H` to `H` with its Hilbert norm. -/
theorem continuous_vector_action (α : NormalAction G M) (x : M) :
    Continuous fun p : G × H => (α p.1 x : H →L[ℂ] H) p.2 := by
  let F : G → H →L[ℂ] H := fun g => (α g x : H →L[ℂ] H)
  have hnorm (g : G) : ‖F g‖ = ‖x‖ := by
    change ‖α g x‖ = ‖x‖
    exact StarAlgEquiv.norm_map (α g).toStarAlgEquiv x
  change Continuous fun p : G × H => F p.1 p.2
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, ξ₀⟩
  change Tendsto (fun p : G × H => F p.1 p.2) (𝓝 (g₀, ξ₀)) (𝓝 (F g₀ ξ₀))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hfirst : Tendsto (fun p : G × H => ‖x‖ * ‖p.2 - ξ₀‖)
      (𝓝 (g₀, ξ₀)) (𝓝 0) := by
    have hc : Continuous (fun p : G × H => ‖x‖ * ‖p.2 - ξ₀‖) :=
      (continuous_const : Continuous (fun _ : G × H => ‖x‖)).mul
        (((continuous_snd : Continuous (fun p : G × H => p.2)).sub
          (continuous_const : Continuous (fun _ : G × H => ξ₀))).norm)
    simpa only [sub_self, norm_zero, mul_zero] using
      hc.tendsto (g₀, ξ₀)
  have hsecond : Tendsto (fun p : G × H => ‖F p.1 ξ₀ - F g₀ ξ₀‖)
      (𝓝 (g₀, ξ₀)) (𝓝 0) := by
    have hv : Continuous (fun p : G × H => F p.1 ξ₀) :=
      (continuous_vector_apply α x ξ₀).comp
        (continuous_fst : Continuous (fun p : G × H => p.1))
    have hc : Continuous (fun p : G × H => ‖F p.1 ξ₀ - F g₀ ξ₀‖) :=
      (hv.sub (continuous_const : Continuous (fun _ : G × H => F g₀ ξ₀))).norm
    simpa only [sub_self, norm_zero] using
      hc.tendsto (g₀, ξ₀)
  have hbound (p : G × H) :
      ‖F p.1 p.2 - F g₀ ξ₀‖ ≤ ‖x‖ * ‖p.2 - ξ₀‖ + ‖F p.1 ξ₀ - F g₀ ξ₀‖ := by
    calc
      ‖F p.1 p.2 - F g₀ ξ₀‖ = ‖F p.1 (p.2 - ξ₀) + (F p.1 ξ₀ - F g₀ ξ₀)‖ := by
        rw [map_sub, sub_add_sub_cancel]
      _ ≤ ‖F p.1 (p.2 - ξ₀)‖ + ‖F p.1 ξ₀ - F g₀ ξ₀‖ := norm_add_le _ _
      _ ≤ ‖F p.1‖ * ‖p.2 - ξ₀‖ + ‖F p.1 ξ₀ - F g₀ ξ₀‖ :=
        add_le_add ((F p.1).le_opNorm (p.2 - ξ₀)) le_rfl
      _ = ‖x‖ * ‖p.2 - ξ₀‖ + ‖F p.1 ξ₀ - F g₀ ξ₀‖ := by rw [hnorm]
  exact squeeze_zero (fun p => norm_nonneg (F p.1 p.2 - F g₀ ξ₀)) hbound
    (by simpa only [zero_add] using hfirst.add hsecond)

end NormalAction
end VonNeumannAlgebra
