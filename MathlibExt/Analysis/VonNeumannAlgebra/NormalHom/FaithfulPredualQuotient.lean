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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulPredualDual
public import MathlibExt.Analysis.Normed.Operator.DualSurjective

/-!
# The actual predual pullback of a faithful normal map is surjective and a quotient

The original faithful normal map makes the literal dual of its constructed
predual pullback isometric. The strict Banach preimage theorem applies to
that actual norm inequality and constructs genuine preimages. Thus the
original pullback is surjective; the stock Banach open mapping theorem
gives its quotient topology. No quotient, range-closure, surjectivity or
normal inverse/model certificate is an input.
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

/-- The original predual pullback has actual preimages under faithfulness, with no quotient certificate. -/
theorem predualPullback_surjective_of_injective (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) : Function.Surjective f.predualPullback := by
  apply ContinuousLinearMap.surjective_of_dual_lower_bound
  intro G
  have hnorm := f.predualPullback_dual_norm hf G
  change ‖G.comp f.predualPullback‖ = ‖G‖ at hnorm
  exact hnorm.symm.le

/-- The same original predual pullback has the actual Banach quotient topology. -/
theorem predualPullback_isQuotientMap_of_injective (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) : Topology.IsQuotientMap f.predualPullback :=
  f.predualPullback.isQuotientMap (f.predualPullback_surjective_of_injective hf)

end

end VonNeumannAlgebra.NormalStarAlgHom
