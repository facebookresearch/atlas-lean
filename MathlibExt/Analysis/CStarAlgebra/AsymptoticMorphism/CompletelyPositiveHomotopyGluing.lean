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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositiveHomotopy
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositivePostcomp

/-!
# Gluing preserves CP-contractive homotopy slices

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. Let H be a CP-contractive homotopy from φ to ψ and K one from ψ to χ. Their pair
M_t(a)=(H_t(a),K_t(a)) lies in MatchingPaths B={(F,G)∈C([0,1],B)²:F(1)=G(0)}, with norm
max(‖F‖∞,‖G‖∞). Its glued path is F_t(a)(s)=H_t(a)(2s) for s≤1/2 and F_t(a)(s)=K_t(a)(2s-1)
for s>1/2, with common value ψ_t(a) at the midpoint. For every time t, a↦F_t(a) is a
completely positive contraction into C([0,1],B), with ‖F_t(a)‖∞≤‖a‖.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace AsymptoticMorphism
namespace CompletelyPositiveContraction
namespace Homotopy

open ContinuousMap.IntervalGluing

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {phi psi chi : CompletelyPositiveContraction A B}

/-- **Complete positivity and contraction of a glued homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. Let H be a CP-contractive homotopy from φ to ψ and K one from ψ to χ. Their pair
M_t(a)=(H_t(a),K_t(a)) lies in MatchingPaths B={(F,G)∈C([0,1],B)²:F(1)=G(0)}, with norm
max(‖F‖∞,‖G‖∞). Its glued path is F_t(a)(s)=H_t(a)(2s) for s≤1/2 and F_t(a)(s)=K_t(a)(2s-1)
for s>1/2, with common value ψ_t(a) at the midpoint. The asymptotic family of the concatenated
ordinary homotopy H.toAsymptoticHomotopy.trans K.toAsymptoticHomotopy has completely positive
contraction slices at every t≥1.
-/
theorem trans_family_isCompletelyPositiveContraction
    (H : Homotopy phi psi) (K : Homotopy psi chi) :
    IsCompletelyPositiveContraction
      ((H.toAsymptoticHomotopy.trans K.toAsymptoticHomotopy).family) := by
  let glued := (H.matchingPairFamily K).postcomp
    (ContinuousMap.IntervalGluing.glueHom (B := B))
  have hCPC := glued.completelyPositiveContraction
  change IsCompletelyPositiveContraction
    (AsymptoticMorphism.postcomp
      (AsymptoticMorphism.Homotopy.pairFamily
        H.toAsymptoticHomotopy K.toAsymptoticHomotopy)
      (ContinuousMap.IntervalGluing.glueHom (B := B)))
  simpa only [glued,
    CompletelyPositiveContraction.postcomp_toAsymptoticMorphism,
    matchingPairFamily_toAsymptoticMorphism] using hCPC

end Homotopy
end CompletelyPositiveContraction
end AsymptoticMorphism
