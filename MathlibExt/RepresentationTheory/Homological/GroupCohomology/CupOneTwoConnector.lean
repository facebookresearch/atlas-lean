/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOne
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductLowDegree
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductConnector

/-!
# Right connecting homomorphisms and low-degree cups

Let `k` be a commutative ring, `G` a group, `A` a representation, and `0 → S₁ → S₂ → S₃ → 0` a
short exact sequence of representations. Assume its tensor product on the left with `A` is
also short exact. For `a ∈ H¹(G,A)` and `b ∈ H¹(G,S₃)`, the connecting maps satisfy `a ∪
δ_S(b) = -δ_{A⊗S}(a ∪ b)` in `H³(G,A ⊗ S₁)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Chapter I, §4, Proposition 1.4.3 and Exercise 3.
* P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Proposition 3.4.8.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency false

/-- Let `k` be a commutative ring, `G` a group, `A : Rep k G`, and `S` a short exact sequence `0 →
S₁ → S₂ → S₃ → 0`. Assume `A ⊗ S` is also short exact. For `a ∈ H¹(G,A)` and `b ∈ H¹(G,S₃)`,
`cupOneTwo A S₁ a (δ_S^1 b) = -δ_{A⊗S}^2 (cupOneOne A S₃ a b)` in `H³(G,A ⊗ S₁)`. Here `δ_S^1
: H¹(G,S₃) → H²(G,S₁)` and `δ_{A⊗S}^2 : H²(G,A ⊗ S₃) → H³(G,A ⊗ S₁)` are the coefficient
connecting maps. -/
theorem cupOneTwo_δ_right
    (A : Rep k G) (S : ShortComplex (Rep k G)) (hS : S.ShortExact)
    (hAS : (S.map (tensorLeft A)).ShortExact)
    (a : H1 A) (b : H1 S.X₃) :
    cupOneTwo A S.X₁ a ((δ hS 1 2 rfl).hom b) =
      -(δ hAS 2 3 rfl).hom (cupOneOne A S.X₃ a b) := by
  have h := ConcreteCategory.congr_hom
    (cup_delta_right A S hS hAS 1 1) (a ⊗ₜ[k] b)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simp only [Nat.reduceAdd, HomologicalComplex.homologyIsoOfEq,
    Iso.refl_hom, id_tensorHom,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    cup_one_two_eq_cupOneTwo, ShortComplex.map_X₁,
    curriedTensor_obj_obj, Int.reduceNeg, pow_one, neg_smul, one_smul,
    ModuleCat.hom_neg, ModuleCat.hom_comp, LinearMap.neg_apply,
    LinearMap.coe_comp, Function.comp_apply,
    cup_one_one_eq_cupOneOne] at h
  have hid :
      (ModuleCat.Hom.hom
        (𝟙 ((inhomogeneousCochains (A ⊗ S.X₁)).homology 3)))
          (cupOneTwo A S.X₁ a ((δ hS 1 2 rfl).hom b)) =
        cupOneTwo A S.X₁ a ((δ hS 1 2 rfl).hom b) := rfl
  erw [hid] at h
  exact h

end groupCohomology
