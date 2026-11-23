/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.HomologyEquivalence
public import MathlibExt.AlgebraicTopology.LocalCoefficient.ProductHomologyEquivalence
public import MathlibExt.Topology.Homotopy.FundamentalGroupProduct

/-!
# Products of the original plus maps

The map is the literal pair of the given continuous maps. Its acyclicity
comes from the actual all-integer-local-coefficient product theorem, whose
fiber projection is a derived trivial fibration. The kernel is calibrated
by the original projection maps on fundamental groups. Normality and
perfectness of the product subgroup are derived from the given subgroups.
No product-fiber homology, kernel, or model comparison is supplied as input.
-/

noncomputable section

open CategoryTheory

universe u v

namespace TopCat

/-- The product of the two specified subgroups in the original fundamental
group of the product, through the actual projection equivalence. -/
public abbrev productPlusSubgroup
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y)
    (P : Subgroup (FundamentalGroup X x)) (Q : Subgroup (FundamentalGroup Y y)) :
    Subgroup (FundamentalGroup (X × Y) (x, y)) :=
  (P.prod Q).comap (FundamentalGroup.productMulEquiv x y).toMonoidHom

/-- The original product subgroup is normal. -/
public theorem productPlusSubgroup_normal
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y)
    (P : Subgroup (FundamentalGroup X x)) (Q : Subgroup (FundamentalGroup Y y))
    [P.Normal] [Q.Normal] : (productPlusSubgroup x y P Q).Normal := by
  infer_instance

/-- Perfectness transfers through the original product equivalence. This
instance is derived solely from perfectness of the two given subgroups. -/
public instance productPlusSubgroup_isPerfect
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y)
    (P : Subgroup (FundamentalGroup X x)) (Q : Subgroup (FundamentalGroup Y y))
    [Group.IsPerfect P] [Group.IsPerfect Q] :
    Group.IsPerfect (productPlusSubgroup x y P Q) := by
  let : Group.IsPerfect (P.prod Q) := Subgroup.isPerfect_iff.mpr (by
    rw [Subgroup.commutator_prod_prod, Subgroup.commutator_eq_self,
      Subgroup.commutator_eq_self])
  change Group.IsPerfect ((P.prod Q).comap
    (FundamentalGroup.productMulEquiv x y).toMonoidHom)
  rw [Subgroup.comap_equiv_eq_map_symm']
  exact Group.IsPerfect.map (FundamentalGroup.productMulEquiv x y).symm.toMonoidHom

namespace IsPlusConstructionAt

variable {X Y A B : TopCat.{u}} {f : X ⟶ A} {g : Y ⟶ B}
  {x : X} {y : Y} {a : A} {b : B} {hfa : f x = a} {hgb : g y = b}
  {P : Subgroup (FundamentalGroup X x)} {Q : Subgroup (FundamentalGroup Y y)}
  [P.Normal] [Q.Normal] [Group.IsPerfect P] [Group.IsPerfect Q]

/-- The product of two plus maps is an actual plus map on the original
product subgroup. The target factors and the second source are path
connected, as for the independently constructed BGL-plus spaces. -/
public theorem prodContinuousMap
    [PathConnectedSpace Y] [PathConnectedSpace A] [PathConnectedSpace B]
    (hf : TopCat.IsPlusConstructionAt f x a hfa P)
    (hg : TopCat.IsPlusConstructionAt g y b hgb Q) :
    TopCat.IsPlusConstructionAt (TopCat.ofHom (f.hom.prodMap g.hom))
      (x, y) (a, b)
      ((TopCat.ofHom_apply (f.hom.prodMap g.hom) (x, y)).trans
        (FundamentalGroup.productMap_point_eq (x := x) (y := y) (a := a) (b := b)
          f.hom g.hom hfa hgb)) (productPlusSubgroup x y P Q) := by
  have hlocal : TopCat.IsLocalCoefficientHomologyEquivalence
      (TopCat.ofHom (f.hom.prodMap g.hom)) :=
    hf.localCoefficientHomologyEquivalence.prodContinuousMap
      hg.localCoefficientHomologyEquivalence
  refine ⟨TopCat.isAcyclicMapAt_of_localCoefficientHomologyEquivalence
    _ hlocal (a, b), ?_⟩
  have hk := FundamentalGroup.ker_mapOfEq_prodMap
    (x := x) (y := y) (a := a) (b := b) f.hom g.hom hfa hgb
  simpa only [TopCat.hom_ofHom, hf.kernel_eq, hg.kernel_eq] using hk

/-- The product retains the actual surjectivity of the two given quotient
maps. This is a statement about the original based map on the product. -/
public theorem prodContinuousMap_pi1_surjective
    (hf : Function.Surjective (FundamentalGroup.mapOfEq f.hom hfa))
    (hg : Function.Surjective (FundamentalGroup.mapOfEq g.hom hgb)) :
    Function.Surjective
      (FundamentalGroup.mapOfEq (f.hom.prodMap g.hom)
        (FundamentalGroup.productMap_point_eq (x := x) (y := y) (a := a) (b := b)
          f.hom g.hom hfa hgb)) :=
  FundamentalGroup.mapOfEq_prodMap_surjective f.hom g.hom hfa hgb hf hg

end IsPlusConstructionAt

end TopCat

end
