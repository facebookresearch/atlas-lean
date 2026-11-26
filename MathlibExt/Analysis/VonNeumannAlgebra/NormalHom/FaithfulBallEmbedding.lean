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
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Closed embeddings of norm balls under injective normal maps

An injective normal unital complex star homomorphism `f : M → N` restricts to a closed
topological embedding on every source norm ball `{x ∈ M : ‖x‖≤r}`, with the source and target
ultraweak topologies.

Thus the inverse on that ball's image is continuous. The radius may be any real number, and the
assertion does not assume a globally normal inverse or a pre-existing closed-range property.
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

/-- **Closed ultraweak embedding of an injective normal map's ball.** Let `M,N` be concrete
von Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach
spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
topologies are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star
homomorphism that is ultraweakly continuous. Assume `f` is injective. for every `r : ℝ`,
the restriction `f : {x ∈ Ultraweak M : ‖x‖≤r} → Ultraweak N` is a topological embedding
with closed image. -/
theorem ultraweak_ball_isClosedEmbedding (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (r : ℝ) :
    Topology.IsClosedEmbedding (fun x : {x : Ultraweak M | ‖ultraweakLinearEquiv M x‖ ≤ r} =>
      f.ultraweakMap x.val) := by
  let B : Set (Ultraweak M) := {x | ‖ultraweakLinearEquiv M x‖ ≤ r}
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (show IsCompact B from ultraweakClosedBall_isCompact M r)
  have hcontinuous : Continuous (fun x : B => f.ultraweakMap x.val) :=
    f.ultraweakMap.continuous.comp continuous_subtype_val
  apply hcontinuous.isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  apply (ultraweakLinearEquiv M).injective
  apply hf
  have hvalue := congrArg (ultraweakLinearEquiv N) hxy
  simpa only [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply] using hvalue

end

end VonNeumannAlgebra.NormalStarAlgHom
