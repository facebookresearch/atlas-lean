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

public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

/-!
# Integer index of a product of linear maps

Use the existing kernel-minus-cokernel integer index. Finiteness is required
only for the two kernels and two cokernels, not for the four ambient stages.
The scalar can be a DivisionRing; no topology, norm or completeness is used.
The quotient identification is proved from the actual quotient maps.
-/

@[expose] public section

namespace LinearMap

universe u𝕜 uE₀ uE₁ uF₀ uF₁

variable {k : Type u𝕜} [DivisionRing k]
variable {E₀ : Type uE₀} {E₁ : Type uE₁} {F₀ : Type uF₀} {F₁ : Type uF₁}
variable [AddCommGroup E₀] [Module k E₀]
variable [AddCommGroup E₁] [Module k E₁]
variable [AddCommGroup F₀] [Module k F₀]
variable [AddCommGroup F₁] [Module k F₁]

/-- The integer index is additive for products with finite kernels and cokernels.
No finite-dimensional assumption is imposed on an ambient source or target. -/
@[simp]
theorem index_prodMap (S : E₀ →ₗ[k] F₀) (T : E₁ →ₗ[k] F₁)
    [FiniteDimensional k S.ker] [FiniteDimensional k T.ker]
    [FiniteDimensional k (F₀ ⧸ S.range)] [FiniteDimensional k (F₁ ⧸ T.range)] :
    (S.prodMap T).index = S.index + T.index := by
  have hKer : Module.finrank k (S.prodMap T).ker =
      Module.finrank k S.ker + Module.finrank k T.ker := by
    rw [ker_prodMap, (Submodule.prodEquiv S.ker T.ker).finrank_eq,
      Module.finrank_prod]
  let q : F₀ × F₁ →ₗ[k] (F₀ ⧸ S.range) × (F₁ ⧸ T.range) :=
    S.range.mkQ.prodMap T.range.mkQ
  have hq : q.ker = (S.prodMap T).range := by
    change (S.range.mkQ.prodMap T.range.mkQ).ker = (S.prodMap T).range
    simp only [ker_prodMap, Submodule.ker_mkQ, range_prodMap]
  have hqSurj : Function.Surjective q := by
    rintro ⟨y₀, y₁⟩
    obtain ⟨x₀, hx₀⟩ := S.range.mkQ_surjective y₀
    obtain ⟨x₁, hx₁⟩ := T.range.mkQ_surjective y₁
    refine ⟨(x₀, x₁), ?_⟩
    change (S.range.mkQ x₀, T.range.mkQ x₁) = (y₀, y₁)
    exact Prod.ext hx₀ hx₁
  have hCoker : Module.finrank k ((F₀ × F₁) ⧸ (S.prodMap T).range) =
      Module.finrank k (F₀ ⧸ S.range) + Module.finrank k (F₁ ⧸ T.range) := by
    rw [← hq, (q.quotKerEquivOfSurjective hqSurj).finrank_eq,
      Module.finrank_prod]
  rw [index_eq_finrank_sub, index_eq_finrank_sub, index_eq_finrank_sub,
    hKer, hCoker, Nat.cast_add, Nat.cast_add]
  abel

end LinearMap
