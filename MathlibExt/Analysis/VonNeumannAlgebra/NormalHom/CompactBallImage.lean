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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom
public import MathlibExt.Analysis.VonNeumannAlgebra.UltraweakOrder

/-!
# Compact ultraweak images of source norm balls

For a normal unital complex star homomorphism `f : M → N` of concrete von Neumann algebras, the
image of every closed operator-norm ball `{x ∈ M : ‖x‖≤r}` is compact in the ultraweak topology
of `N`.

This uses ultraweak compactness of the source ball and continuity of `f`. Injectivity is not
required, and the radius `r` is any real number; negative radii give empty sets.
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

/-- **Ultraweak compact image of a normal map's norm ball.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. for every `r : ℝ`, `f({x ∈ M : ‖x‖≤r})` is compact in the
ultraweak topology of `N`. Injectivity and nonnegativity of `r` are not assumed. -/
theorem ultraweak_ball_image_isCompact (f : NormalStarAlgHom M N) (r : ℝ) :
    IsCompact ((fun x : Ultraweak M =>
      (ultraweakLinearEquiv N).symm (f (ultraweakLinearEquiv M x))) ''
        {x : Ultraweak M | ‖ultraweakLinearEquiv M x‖ ≤ r}) := by
  exact (ultraweakClosedBall_isCompact M r).image f.continuous_ultraweak

end

end VonNeumannAlgebra.NormalStarAlgHom
