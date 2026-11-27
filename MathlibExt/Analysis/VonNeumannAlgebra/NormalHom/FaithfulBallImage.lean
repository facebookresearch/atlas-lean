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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.CompactBallImage
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Norm balls in the range of an injective normal map

Let `f : M → N` be an injective normal unital complex star homomorphism. Its C-star isometry
gives `f({x : ‖x‖≤r})=range(f) ∩ {y : ‖y‖≤r}` for every real `r`.

This intersection is compact in the target ultraweak topology. The norms are the inherited
operator norms, and no global closed-range or normal-inverse hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- **Source norm-ball image equals the bounded range intersection.** Let `M,N` be concrete
von Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach
spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
topologies are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star
homomorphism that is ultraweakly continuous. Assume `f` is injective. for every `r : ℝ`,
`f({x ∈ M : ‖x‖≤r})=range(f)∩{y ∈ N : ‖y‖≤r}`, as subsets of ultraweak `N`. -/
theorem ultraweak_ball_image_eq_range_inter (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (r : ℝ) :
    f.ultraweakMap '' {x : Ultraweak M | ‖ultraweakLinearEquiv M x‖ ≤ r} =
      Set.range f.ultraweakMap ∩ {y : Ultraweak N | ‖ultraweakLinearEquiv N y‖ ≤ r} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Set.mem_range_self x, ?_⟩
    change ‖ultraweakLinearEquiv N (f.ultraweakMap x)‖ ≤ r
    rw [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply]
    change ‖f.toStarAlgHom (ultraweakLinearEquiv M x)‖ ≤ r
    rw [NonUnitalStarAlgHom.norm_map f.toStarAlgHom hf]
    exact hx
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    change ‖ultraweakLinearEquiv M x‖ ≤ r
    have hnorm : ‖ultraweakLinearEquiv N (f.ultraweakMap x)‖ = ‖ultraweakLinearEquiv M x‖ := by
      rw [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply]
      exact NonUnitalStarAlgHom.norm_map f.toStarAlgHom hf _
    rw [← hnorm]
    exact hx

/-- **Ultraweak compactness of bounded normal-map range intersections.** Let `M,N` be concrete
von Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach
spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
topologies are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star
homomorphism that is ultraweakly continuous. Assume `f` is injective. for every `r : ℝ`,
`range(f)∩{y ∈ N : ‖y‖≤r}` is compact in `σ(N,N_*)`. -/
theorem ultraweak_range_inter_ball_isCompact (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (r : ℝ) :
    IsCompact (Set.range f.ultraweakMap ∩ {y : Ultraweak N | ‖ultraweakLinearEquiv N y‖ ≤ r}) := by
  rw [← f.ultraweak_ball_image_eq_range_inter hf r]
  exact f.ultraweak_ball_image_isCompact r

end

end VonNeumannAlgebra.NormalStarAlgHom
