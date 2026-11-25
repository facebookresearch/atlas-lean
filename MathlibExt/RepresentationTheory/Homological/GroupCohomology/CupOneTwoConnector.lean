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
# Low-degree cup/connector compatibility

The arbitrary-degree Alexander--Whitney cup satisfies the right connector
law with Koszul sign `(-1)^p`.  Specializing to `p = q = 1` and using the
comparison with the descended low-degree cups gives

`a ∪ δ(b) = -δ(a ∪ b)`.

Thus the low-degree API is a direct corollary of the arbitrary-degree
connector theorem rather than a separate cocycle calculation.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*,
  Chapter I, §4, Proposition 1.4.3 and Exercise 3.
* P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*,
  Proposition 3.4.8.

No continuous cup, Hochschild--Serre edge map, residue, VM2, or norm-residue
statement is asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency false

/-- A degree-one class cups with the right coefficient connector according
to the Koszul sign: `a ∪ δ(b) = -δ(a ∪ b)`. -/
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
