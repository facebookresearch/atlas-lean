/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCoefficientContractions
import MathlibExt.AlgebraicTopology.SimplicialSpace.CategoricalPowerHomotopy
import MathlibExt.AlgebraicTopology.SimplicialSpace.IntrinsicDKSaturation
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingFaithfulness
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Intrinsic DK of every original full-J power operator

The coefficient operator is the original full-J map.  Its two categorical
inverse homotopies are constructed at v and delta(v), transposed through
the native true power, and used in the original intrinsic DK theorem.
Only an original Reedy-fibrant Segal space is supplied; completeness,
homotopy data, weak equivalences and DK outcomes are not caller inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian
open scoped SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkPowerOperatorDK
open RezkCoefficientContractions WalkingEUnit CategoricalPowerHomotopy

/-- The power is the SAME native Cartesian exponential by the literal D(Jn). -/
def power (n : SimplexCategory) (W : SimplicialSpace.{u}) : SimplicialSpace.{u} :=
  (ihom (coefficient.{u} n)).obj W

/-- An original simplex operator acts by actual contravariant precomposition. -/
def powerMap {n m : SimplexCategory} (δ : n ⟶ m) (W : SimplicialSpace.{u}) :
    power m W ⟶ power n W := (pre (coefficientMap.{u} δ)).app W

/-- The reverse power map uses the SAME internally constructed original vertex constant. -/
def reversePowerMap (n m : SimplexCategory) (v : Fin (n.len + 1))
    (W : SimplicialSpace.{u}) : power n W ⟶ power m W :=
  (pre (reverseMap.{u} n m v)).app W

/-- Both powers are RF and Segal by the genuine original product-spine Cartesian theorem. -/
theorem power_segal (n : SimplexCategory) (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    segalSpaces (power n W) := by
  change segalSpaces ((ihom (discreteInnerFunctor.obj
    (SSet.FreeGroupoidSimplex.J.{u}.obj n))).obj W)
  exact SegalExponentRawAssembly.outerPower_segal
    (SSet.FreeGroupoidSimplex.J.{u}.obj n) W hW

/-- The actual homotopy on the target power is transposed from the source-vertex contraction. -/
def targetPowerHomotopy (n : SimplexCategory) (v : Fin (n.len + 1))
    (W : SimplicialSpace.{u}) : coherentSpace.{u} ⊗ power n W ⟶ power n W :=
  homotopyPrecomp (coefficientContraction.{u} n v) W

/-- The target-power endpoints are the original reverse composite and identity, in that order. -/
theorem targetPowerHomotopy_endpoints {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) (W : SimplicialSpace.{u}) :
    spaceEndpoint (power n W) SSet.coherentIso.x₀ ≫ targetPowerHomotopy n v W =
        reversePowerMap n m v W ≫ powerMap δ W ∧
    spaceEndpoint (power n W) SSet.coherentIso.x₁ ≫ targetPowerHomotopy n v W =
        𝟙 (power n W) := by
  have h := operator_inverse_homotopies.{u} δ v
  have ht := homotopyPrecomp_endpoints (coefficientMap δ ≫ reverseMap n m v)
    (𝟙 (coefficient n)) (coefficientContraction n v) h.1 h.2.1 W
  constructor
  · exact ht.1.trans (congrArg (fun η => η.app W)
      (pre_map (coefficientMap δ) (reverseMap n m v)))
  · exact ht.2.trans (congrArg (fun η => η.app W) (pre_id (coefficient n)))

/-- The actual homotopy on the source power is transposed at the actual target vertex delta(v). -/
def sourcePowerHomotopy {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) (W : SimplicialSpace.{u}) :
    coherentSpace.{u} ⊗ power m W ⟶ power m W :=
  homotopyPrecomp (coefficientContraction.{u} m (δ v)) W

/-- The source-power endpoints retain the SAME forward map and original reverse constant. -/
theorem sourcePowerHomotopy_endpoints {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) (W : SimplicialSpace.{u}) :
    spaceEndpoint (power m W) SSet.coherentIso.x₀ ≫ sourcePowerHomotopy δ v W =
        powerMap δ W ≫ reversePowerMap n m v W ∧
    spaceEndpoint (power m W) SSet.coherentIso.x₁ ≫ sourcePowerHomotopy δ v W =
        𝟙 (power m W) := by
  have h := operator_inverse_homotopies.{u} δ v
  have ht := homotopyPrecomp_endpoints (reverseMap n m v ≫ coefficientMap δ)
    (𝟙 (coefficient m)) (coefficientContraction m (δ v)) h.2.2.1 h.2.2.2 W
  constructor
  · exact ht.1.trans (congrArg (fun η => η.app W)
      (pre_map (reverseMap n m v) (coefficientMap δ)))
  · exact ht.2.trans (congrArg (fun η => η.app W) (pre_id (coefficient m)))

private theorem rawHomotopy_endpoint {A B : SimplicialSpace.{u}}
    (H : coherentSpace.{u} ⊗ A ⟶ B) (f : A ⟶ B)
    (e : SSet.coherentIso.{u} _⦋0⦌) (he : spaceEndpoint A e ≫ H = f) :
    CategoricalHomotopyPrism.tensorEndpoint A e ≫ H.hom = f.hom := by
  have h := congrArg (fun k : A ⟶ B => k.hom) he
  change (spaceEndpoint A e).hom ≫ H.hom = f.hom at h
  exact (congrArg (fun endpoint => endpoint ≫ H.hom)
    (spaceEndpoint_laws A e).2.2).symm.trans h

/-- Every original coefficient operator induces intrinsic DK on the SAME full true powers. -/
theorem powerMap_intrinsicDK {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IntrinsicDK.isEquivalence (powerMap δ W) (power_segal m W hW) (power_segal n W hW) := by
  have ht := targetPowerHomotopy_endpoints.{u} δ v W
  have hs := sourcePowerHomotopy_endpoints.{u} δ v W
  exact IntrinsicDK.of_categorical_equivalence (powerMap δ W)
    (reversePowerMap n m v W) (reversePowerMap n m v W)
    (power_segal m W hW) (power_segal n W hW)
    (targetPowerHomotopy n v W).hom (sourcePowerHomotopy δ v W).hom
    (rawHomotopy_endpoint _ _ _ ht.1) (rawHomotopy_endpoint _ _ _ ht.2)
    (rawHomotopy_endpoint _ _ _ hs.1) (rawHomotopy_endpoint _ _ _ hs.2)

/-- Full weakness holds on EVERY original ordered mapping-fibre pair of the source power. -/
theorem powerMap_mappingFibre_weak {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : ((power m W).diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (mappingFibre.map (powerMap δ W) (x := x) (y := y) rfl rfl) :=
  (powerMap_intrinsicDK δ v W hW).1 x y

/-- Essential surjectivity belongs to the SAME actual intrinsic Ho functor on both true powers. -/
theorem powerMap_HoEssSurj {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (SegalHomotopy.map (powerMap δ W) (power_segal m W hW) (power_segal n W hW)).EssSurj :=
  (powerMap_intrinsicDK δ v W hW).2

/-- The SAME full endpoint comparison is weak by its genuine all-mapping-fibre criterion. -/
theorem powerMap_endpointComparison_weak {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (mappingEndpointComparison (powerMap δ W)) := by
  let _ : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  exact (mappingEndpointComparison_realizationWeak_iff (powerMap δ W)
    (power_segal m W hW).1 (power_segal n W hW).1).mpr
      (powerMap_mappingFibre_weak δ v W hW)

/-- The weak endpoint comparison retains BOTH original pullback projections and ordered zero map. -/
theorem powerMap_endpointComparison_legs {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) :
    mappingEndpointComparison (powerMap δ W) ≫
        pullback.fst (mappingEndpoint (power n W))
          (prod.map ((powerMap δ W).hom.app (op ⦋0⦌))
            ((powerMap δ W).hom.app (op ⦋0⦌))) =
      (powerMap δ W).hom.app (op ⦋1⦌) ∧
    mappingEndpointComparison (powerMap δ W) ≫
        pullback.snd (mappingEndpoint (power n W))
          (prod.map ((powerMap δ W).hom.app (op ⦋0⦌))
            ((powerMap δ W).hom.app (op ⦋0⦌))) = mappingEndpoint (power m W) :=
  ⟨mappingEndpointComparison_fst _, mappingEndpointComparison_snd _⟩

/-- The binary endpoint square maps to the SAME named native homotopy pullback. -/
def endpointHomotopyComparison {n m : SimplexCategory} (δ : n ⟶ m)
    (W : SimplicialSpace.{u}) :
    (power m W).diagram _⦋1⦌ ⟶
      (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).obj
        (cospan (mappingEndpoint (power n W))
          (prod.map ((powerMap δ W).hom.app (op ⦋0⦌))
            ((powerMap δ W).hom.app (op ⦋0⦌)))) :=
  mappingEndpointComparison (powerMap δ W) ≫
    (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
      (cospan (mappingEndpoint (power n W))
        (prod.map ((powerMap δ W).hom.app (op ⦋0⦌))
          ((powerMap δ W).hom.app (op ⦋0⦌))))

/-- Full binary endpoint homotopy-cartesianness follows from the actual endpoint fibration. -/
theorem endpointHomotopyComparison_weak {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (endpointHomotopyComparison δ W) := by
  let _ : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let F := cospan (mappingEndpoint (power n W))
    (prod.map ((powerMap δ W).hom.app (op ⦋0⦌))
      ((powerMap δ W).hom.app (op ⦋0⦌)))
  let _ : HomotopicalAlgebra.Fibration (F.map WalkingCospan.Hom.inl) := by
    change HomotopicalAlgebra.Fibration (mappingEndpoint (power n W))
    exact ReedyModel.mappingEndpoint_fibration (power n W) (power_segal n W hW).1
  let _ : HomotopicalAlgebra.WeakEquivalence
      ((HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app F) :=
    HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_rightProper_inl F
  let _ : HomotopicalAlgebra.WeakEquivalence (mappingEndpointComparison (powerMap δ W)) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (powerMap_endpointComparison_weak δ v W hW)
  change SSet.realizationWeakEquivalences
    (mappingEndpointComparison (powerMap δ W) ≫
      (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app F)
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (powerMap_endpointComparison_weak δ v W hW)
    ((HomotopicalAlgebra.weakEquivalence_iff
      ((HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app F)).mp
        (inferInstance : HomotopicalAlgebra.WeakEquivalence
          ((HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app F)))

end SimplicialSpace.RezkPowerOperatorDK
