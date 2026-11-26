/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ThickBhSets
import Mathlib.Data.List.Basic

namespace MathlibExtTest.Combinatorics.Additive.ThickBhSets

open MetaMathlibExt

/-- The construction over the two-element field gives three points in `ZMod 7`. -/
public theorem singerSet_two_card {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hK : Module.finrank (ZMod 2) K = 3) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly (ZMod 2) (θ ^ b)).natDegree = 3) :
    (singerSet (ZMod 2) 2 θ b).ncard = 3 := by
  simpa using (isBhSet_singerSet (F := ZMod 2) (h := 2) (by decide) hK hθ hb).2

/-- Equal two-term sums determine the same summands, allowing repetitions. -/
public theorem singerSet_two_perm {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hK : Module.finrank (ZMod 2) K = 3) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly (ZMod 2) (θ ^ b)).natDegree = 3)
    {a₁ a₂ c₁ c₂ : ZMod 7}
    (ha₁ : a₁ ∈ singerSet (ZMod 2) 2 θ b) (ha₂ : a₂ ∈ singerSet (ZMod 2) 2 θ b)
    (hc₁ : c₁ ∈ singerSet (ZMod 2) 2 θ b) (hc₂ : c₂ ∈ singerSet (ZMod 2) 2 θ b)
    (he : a₁ + a₂ = c₁ + c₂) : [a₁, a₂].Perm [c₁, c₂] := by
  have hBh := (isBhSet_singerSet (F := ZMod 2) (h := 2) (by decide) hK hθ hb).1
  apply hBh.2.2 [a₁, a₂] [c₁, c₂]
    (by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · exact hx ▸ ha₁
      · exact (List.mem_singleton.mp hx) ▸ ha₂)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · exact hx ▸ hc₁
      · exact (List.mem_singleton.mp hx) ▸ hc₂)
    rfl rfl (by simp) (by simp)
  change a₁ + a₂ = c₁ + c₂
  exact he

end MathlibExtTest.Combinatorics.Additive.ThickBhSets
