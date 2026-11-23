/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.Product
public import MathlibExt.AlgebraicTopology.PlusConstruction.CWTypeMapping
public import MathlibExt.Topology.CWComplex.ProductModels
public import MathlibExt.Topology.Category.TopCat.ProductParameterHomotopy
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition

/-!
# Whole parameterized plus extensions and original mapping-space kernels

The actual product plus map and the actual product CW models derive a
whole extension triangle. Currying this triangle proves killing in the
fundamental group of the RAW compact-open mapping space, with its actual
image-point trace. Thus the later loop filler is one mapping-space
nullhomotopy, not a collection of unrelated pointwise nullhomotopies.
Neither a factor, product CW model, based triangle nor filler is an input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory

universe u

namespace TopCat

private theorem identityPlusAt (A : TopCat.{u}) (a : A) :
    TopCat.IsPlusConstructionAt (𝟙 A) a a rfl
      (⊥ : Subgroup (FundamentalGroup A a)) := by
  refine ⟨TopCat.isAcyclicMapAt_of_localCoefficientHomologyEquivalence
    (𝟙 A) (TopCat.isLocalCoefficientHomologyEquivalence_id A) a, ?_⟩
  change MonoidHom.ker
    (FundamentalGroup.mapOfEq (ContinuousMap.id A) rfl) = ⊥
  have hId :
      FundamentalGroup.mapOfEq (ContinuousMap.id A)
        (rfl : (ContinuousMap.id A) a = a) = MonoidHom.id (FundamentalGroup A a) :=
    FundamentalGroup.mapOfEq_id (X := A) a (rfl : (ContinuousMap.id A) a = a)
  have hKernel : (MonoidHom.id (FundamentalGroup A a)).ker =
      (⊥ : Subgroup (FundamentalGroup A a)) := MonoidHom.ker_id
  exact (congrArg (fun m : FundamentalGroup A a →* FundamentalGroup A a => m.ker) hId).trans
    hKernel

namespace IsPlusConstructionAt

/-- The whole original product-family triangle derives the ORIGINAL
curried-map subgroup killing condition. All three selected point
cofibrations are structural; the product CW models are constructed
internally. No cofibration of the product map or expected filler is used. -/
public theorem exists_product_parameter_extension
    {A X B C : TopCat.{u}}
    [PathConnectedSpace A] [PathConnectedSpace X] [PathConnectedSpace B]
    (a : A) (x : X)
    [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A)]
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    {j : X ⟶ B}
    [Cofibration (TopCat.const (j x) : TopCat.of PUnit.{u + 1} ⟶ B)]
    {P : Subgroup (FundamentalGroup X x)} [P.Normal] [Group.IsPerfect P]
    (hj : TopCat.IsPlusConstructionAt j x (j x) rfl P)
    (φ : TopCat.of (A × X) ⟶ C)
    (hkill : ∀ p ∈ TopCat.productPlusSubgroup a x
      (⊥ : Subgroup (FundamentalGroup A a)) P,
      FundamentalGroup.mapOfEq φ.hom rfl p = 1) :
    ∃ F : TopCat.of (A × B) ⟶ C,
      ∃ K : TopCat.Homotopy
        (TopCat.ofHom ((ContinuousMap.id A).prodMap j.hom) ≫ F) φ,
        ∀ p ∈ P, FundamentalGroup.mapOfEq
          (TopCat.curriedProductMap φ).hom rfl p = 1 := by
  have hid := identityPlusAt A a
  have hprod := hid.prodContinuousMap hj
  have hsource := Topology.CWComplex.cwType_product_of_cofibrant_points A X a x
  have htarget := Topology.CWComplex.cwType_product_of_cofibrant_points A B a (j x)
  obtain ⟨F, hK, _⟩ :=
    hprod.exists_extension_of_cwType hsource htarget C φ hkill
  let K := hK.some
  let cF := TopCat.curriedProductMap F
  let cφ := TopCat.curriedProductMap φ
  have he :
      (TopCat.curriedProductMap
        (TopCat.ofHom ((ContinuousMap.id A).prodMap j.hom) ≫ F)).hom =
      (j ≫ cF).hom :=
    congrArg (fun m => m.hom) (TopCat.curriedProductMap_comp_second j F)
  let KC : TopCat.Homotopy (j ≫ cF) cφ :=
    (TopCat.curriedProductHomotopy K).cast he rfl
  refine ⟨F, K, ?_⟩
  intro p hp
  have hjp : FundamentalGroup.mapOfEq j.hom rfl p = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hj.kernel_eq]
    exact hp
  have hcomp : FundamentalGroup.mapOfEq (j ≫ cF).hom rfl p = 1 := by
    rw [TopCat.hom_comp]
    rw [FundamentalGroup.mapOfEq_comp j.hom cF.hom rfl rfl rfl]
    change FundamentalGroup.mapOfEq cF.hom rfl
      (FundamentalGroup.mapOfEq j.hom rfl p) = 1
    exact (congrArg (FundamentalGroup.mapOfEq cF.hom rfl) hjp).trans
      (map_one (FundamentalGroup.mapOfEq cF.hom rfl))
  exact (FundamentalGroup.mapOfEq_eq_one_iff_of_homotopy KC x p).mp hcomp

end IsPlusConstructionAt

end TopCat

end
