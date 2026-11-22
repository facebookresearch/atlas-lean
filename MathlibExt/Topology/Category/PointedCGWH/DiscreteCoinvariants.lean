/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.DiscreteSmash
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Actual native balanced discrete smash coinvariants
-/

set_option autoImplicit false
noncomputable section

universe u v w wH wG

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace PointedCGWH

/-- The literal coefficient map is native smash with the coefficient morphism. -/
def nativeSmashCoefficientMap (I : Type w)
    (Z Z' : PointedCGWH.{u, max v w}) (f : Z ⟶ Z') :
    discreteSmashObj.{u, v, w} I Z ⟶ discreteSmashObj.{u, v, w} I Z' :=
  𝟙 (basedDiscreteObj.{u, v, w} I) ⊗ₘ f

/-- Its literal generator law uses the actual freely based point and native unitor. -/
theorem nativeSmashCoefficientMap_generator (I : Type w)
    (Z Z' : PointedCGWH.{u, max v w}) (f : Z ⟶ Z') (i : I) :
    discreteSmashIncl.{u, v, w} I Z i ≫
        nativeSmashCoefficientMap.{u, v, w} I Z Z' f =
      f ≫ discreteSmashIncl.{u, v, w} I Z' i := by
  let U : PointedCGWH.{u, max v w} :=
    (Under.costar CGWH.point.{u, max v w}).obj CGWH.point
  let B := basedDiscreteObj.{u, v, w} I
  let a : U ⟶ B := basedDiscreteIncl.{u, v, w} I i
  have hTensor : (a ⊗ₘ 𝟙 Z) ≫ (𝟙 B ⊗ₘ f) =
      (𝟙 U ⊗ₘ f) ≫ (a ⊗ₘ 𝟙 Z') := by
    calc
      _ = a ⊗ₘ f :=
        (tensorHom_comp_tensorHom a (𝟙 Z) (𝟙 B) f).trans
          (by rw [Category.comp_id, Category.id_comp])
      _ = (𝟙 U ⊗ₘ f) ≫ (a ⊗ₘ 𝟙 Z') :=
        ((tensorHom_comp_tensorHom (𝟙 U) f a (𝟙 Z')).trans
          (by rw [Category.id_comp, Category.comp_id])).symm
  have hUnit : (λ_ Z).inv ≫ (𝟙 U ⊗ₘ f) = f ≫ (λ_ Z').inv :=
    (congrArg
      (fun g : U ⊗ Z ⟶ U ⊗ Z' => (λ_ Z).inv ≫ g)
      (id_tensorHom U f)).trans (leftUnitor_inv_naturality f).symm
  calc
    discreteSmashIncl.{u, v, w} I Z i ≫
        nativeSmashCoefficientMap.{u, v, w} I Z Z' f =
        (λ_ Z).inv ≫ ((a ⊗ₘ 𝟙 Z) ≫ (𝟙 B ⊗ₘ f)) := by
      change ((λ_ Z).inv ≫ (a ⊗ₘ 𝟙 Z)) ≫ (𝟙 B ⊗ₘ f) = _
      exact Category.assoc _ _ _
    _ = (λ_ Z).inv ≫ ((𝟙 U ⊗ₘ f) ≫ (a ⊗ₘ 𝟙 Z')) :=
      congrArg (fun g : U ⊗ Z ⟶ B ⊗ Z' => (λ_ Z).inv ≫ g) hTensor
    _ = f ≫ (λ_ Z').inv ≫ (a ⊗ₘ 𝟙 Z') :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g : Z ⟶ U ⊗ Z' => g ≫ (a ⊗ₘ 𝟙 Z')) hUnit).trans
          (Category.assoc _ _ _))
    _ = f ≫ discreteSmashIncl.{u, v, w} I Z' i := rfl


variable (H : Type wH) (G : Type wG) [Monoid H] [Group G]
variable (Z : PointedCGWH.{u, max v (max wH wG)})
variable (rho : H →* End Z) (iota : H →* G)

/-- The actual native pair has a coequalizer before any selected dictionary input. -/
theorem nativeBalancedHasCoequalizer :
    HasCoequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho) := by
  infer_instance

variable [HasCoproduct (fun _ : G => Z)]
variable [HasCoproduct (fun _ : H × G => Z)]
variable [HasCoproduct (fun _ : G × H => Z)]
variable [HasCoequalizer (ActionCategory.coefficientSource H G Z)
  (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)]
variable [HasCoequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
  (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)]

/-- The actual native balanced pointed object is this literal coequalizer. -/
abbrev nativeBalancedSmash : PointedCGWH.{u, max v (max wH wG)} :=
  coequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
    (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)

/-- Its literal coefficient generator retains the original native projection. -/
def nativeBalancedGenerator (g : G) :
    Z ⟶ nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota :=
  discreteSmashIncl.{u, max v (max wH wG), wG} G Z g ≫
    coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)

/-- Transport the existing inverse-right cofork to the actual native pair. -/
def nativeBalancedCofork :
    Cofork (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho) :=
  Cofork.ofπ
    ((discreteSmashCoproductIso.{u, max v (max wH wG), wG} G Z).hom ≫
      (ActionCategory.balancedCoefficientCofork H G Z rho iota).π) (by
        rw [← Category.assoc, ← smashBalancingGroup_comparison.{u, v, wH, wG},
          ← Category.assoc, ← smashBalancingCoefficient_comparison.{u, v, wH, wG},
          Category.assoc, Category.assoc]
        exact congrArg
          (fun f =>
            (discreteSmashCoproductIso.{u, max v (max wH wG), max wG wH}
              (G × H) Z).hom ≫ f)
          (ActionCategory.balancedCoefficientCofork H G Z rho iota).condition)

/-- The transported actual native cofork has its full universal property. -/
def nativeBalancedCoforkIsColimit :
    IsColimit (nativeBalancedCofork.{u, v, wH, wG} H G Z rho iota) :=
  (Cofork.isColimitEquivOfIsos
    (nativeBalancedCofork.{u, v, wH, wG} H G Z rho iota)
    (ActionCategory.balancedCoefficientCofork H G Z rho iota)
    (discreteSmashCoproductIso.{u, max v (max wH wG), max wG wH} (G × H) Z)
    (discreteSmashCoproductIso.{u, max v (max wH wG), wG} G Z)
    (Iso.refl _)
    (smashBalancingGroup_comparison.{u, v, wH, wG} H G Z iota)
    (smashBalancingCoefficient_comparison.{u, v, wH, wG} H G Z rho)
    (by
      simp only [nativeBalancedCofork, Cofork.π_ofπ, Iso.refl_hom,
        Category.comp_id, Iso.inv_hom_id_assoc])).symm
    (ActionCategory.balancedCoefficientCoforkIsColimit H G Z rho iota)

/-- The original chosen inverse-right quotient identifies with the actual native one. -/
def nativeBalancedIso :
    ActionCategory.inverseRightCoinvariants H G Z rho iota ≅
      nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota :=
  (nativeBalancedCoforkIsColimit.{u, v, wH, wG} H G Z rho iota).coconePointUniqueUpToIso
    (colimit.isColimit
        (parallelPair (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
          (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)))

/-- That comparison retains each literal coefficient generator. -/
theorem nativeBalancedIso_generator (g : G) :
    ActionCategory.inverseRightGenerator H G Z rho iota g ≫
        (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom =
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g := by
  have h := (nativeBalancedCoforkIsColimit.{u, v, wH, wG}
    H G Z rho iota).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit
        (parallelPair (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
          (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)))
      WalkingParallelPair.one
  change (discreteSmashCoproductIso.{u, max v (max wH wG), wG} G Z).hom ≫
      (ActionCategory.balancedCoefficientCofork H G Z rho iota).π ≫
      (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom =
    coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho) at h
  unfold nativeBalancedGenerator ActionCategory.inverseRightGenerator
  rw [← discreteSmashCoproductIso_generator.{u, max v (max wH wG), wG}
    G Z g, Category.assoc]
  exact congrArg
    (fun f => discreteSmashIncl.{u, max v (max wH wG), wG} G Z g ≫ f) h

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- Maps out of the actual native quotient are determined by coefficient generators. -/
theorem nativeBalanced_hom_ext
    {Y : PointedCGWH.{u, max v (max wH wG)}}
    {f g : nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota ⟶ Y}
    (h : ∀ x, nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota x ≫ f =
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota x ≫ g) : f = g := by
  apply coequalizer.hom_ext
  apply discreteSmash_hom_ext.{u, max v (max wH wG), wG} G Z
  intro x
  exact (Category.assoc _ _ _).symm.trans
    ((h x).trans (Category.assoc _ _ _))

section DirectNativeLeft

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- Literal left translation descends through only the actual native coequalizer. -/
def nativeBalancedLeftMap (k : G) :
    nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota ⟶
      nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota :=
  coequalizer.desc
    (discreteSmashLeft.{u, max v (max wH wG), wG} G Z k ≫
      coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
        (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)) (by
      let s := smashBalancingSourceLeft.{u, v, wH, wG} H G Z k
      let a := smashBalancingGroup.{u, v, wH, wG} H G Z iota
      let b := smashBalancingCoefficient.{u, v, wH, wG} H G Z rho
      let l := discreteSmashLeft.{u, max v (max wH wG), wG} G Z k
      let q := coequalizer.π a b
      have hA : s ≫ a = a ≫ l :=
        smashBalancingGroup_left.{u, v, wH, wG} H G Z iota k
      have hB : s ≫ b = b ≫ l :=
        smashBalancingCoefficient_left.{u, v, wH, wG} H G Z rho k
      have hQ : a ≫ q = b ≫ q := coequalizer.condition a b
      change a ≫ (l ≫ q) = b ≫ (l ≫ q)
      calc
        _ = (a ≫ l) ≫ q := (Category.assoc _ _ _).symm
        _ = (s ≫ a) ≫ q := congrArg (fun f => f ≫ q) hA.symm
        _ = s ≫ (a ≫ q) := Category.assoc _ _ _
        _ = s ≫ (b ≫ q) := congrArg (fun f => s ≫ f) hQ
        _ = (s ≫ b) ≫ q := (Category.assoc _ _ _).symm
        _ = (b ≫ l) ≫ q := congrArg (fun f => f ≫ q) hB
        _ = b ≫ (l ≫ q) := Category.assoc _ _ _)

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- The direct quotient action has the literal native projection square. -/
theorem nativeBalancedLeftMap_projection (k : G) :
    coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
        (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho) ≫
      nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k =
    discreteSmashLeft.{u, max v (max wH wG), wG} G Z k ≫
      coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
        (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho) :=
  coequalizer.π_desc _ _

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- The same original coefficient injection receives the actual left multiplication label. -/
theorem nativeBalancedLeftMap_generator (k g : G) :
    nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g ≫
        nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k =
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota (k * g) := by
  let j := discreteSmashIncl.{u, max v (max wH wG), wG} G Z g
  let q := coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
    (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)
  let l := discreteSmashLeft.{u, max v (max wH wG), wG} G Z k
  have hp : q ≫ nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k = l ≫ q :=
    nativeBalancedLeftMap_projection.{u, v, wH, wG} H G Z rho iota k
  have hj : j ≫ l =
      discreteSmashIncl.{u, max v (max wH wG), wG} G Z (k * g) :=
    discreteSmashLeft_generator.{u, max v (max wH wG), wG} G Z k g
  change (j ≫ q) ≫ nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => j ≫ f) hp).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ q) hj)))

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- Native identity translation is the actual quotient identity. -/
theorem nativeBalancedLeftMap_one :
    nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota 1 = 𝟙 _ := by
  apply nativeBalanced_hom_ext.{u, v, wH, wG} H G Z rho iota
  intro g
  exact (nativeBalancedLeftMap_generator.{u, v, wH, wG} H G Z rho iota 1 g).trans
    (by rw [one_mul, Category.comp_id])

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- Source-first quotient composition has the actual target group multiplication order. -/
theorem nativeBalancedLeftMap_mul (k l : G) :
    nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota (k * l) =
      nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota l ≫
        nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k := by
  apply nativeBalanced_hom_ext.{u, v, wH, wG} H G Z rho iota
  intro g
  have h0 := nativeBalancedLeftMap_generator.{u, v, wH, wG} H G Z rho iota (k * l) g
  have h1 := nativeBalancedLeftMap_generator.{u, v, wH, wG} H G Z rho iota l g
  have h2 := nativeBalancedLeftMap_generator.{u, v, wH, wG} H G Z rho iota k (l * g)
  have hR : nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g ≫
      (nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota l ≫
        nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k) =
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota (k * (l * g)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫
        nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k) h1).trans h2)
  have hAssoc :
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota ((k * l) * g) =
        nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota (k * (l * g)) :=
    congrArg (nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota) (mul_assoc k l g)
  exact h0.trans (hAssoc.trans hR.symm)

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- The directly descended translations have their actual group inverses. -/
theorem nativeBalancedLeftMap_hom_inv_id (k : G) :
    nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k ≫
        nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k⁻¹ = 𝟙 _ := by
  rw [← nativeBalancedLeftMap_mul, inv_mul_cancel, nativeBalancedLeftMap_one]

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- The other inverse composite is likewise the actual quotient identity. -/
theorem nativeBalancedLeftMap_inv_hom_id (k : G) :
    nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k⁻¹ ≫
        nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k = 𝟙 _ := by
  rw [← nativeBalancedLeftMap_mul, mul_inv_cancel, nativeBalancedLeftMap_one]

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- Full native left multiplication uses only the original native quotient dictionary. -/
def nativeBalancedLeftAut :
    G →* Aut (nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota) where
  toFun k := Aut.of
    { hom := nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k
      inv := nativeBalancedLeftMap.{u, v, wH, wG} H G Z rho iota k⁻¹
      hom_inv_id := nativeBalancedLeftMap_hom_inv_id.{u, v, wH, wG} H G Z rho iota k
      inv_hom_id := nativeBalancedLeftMap_inv_hom_id.{u, v, wH, wG} H G Z rho iota k }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact nativeBalancedLeftMap_one.{u, v, wH, wG} H G Z rho iota
  map_mul' k l := by
    apply Aut.ext
    apply Iso.ext
    exact nativeBalancedLeftMap_mul.{u, v, wH, wG} H G Z rho iota k l

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- The descended full left action retains the actual native coefficient generator. -/
theorem nativeBalancedLeftAut_generator (k g : G) :
    nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g ≫
        (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom =
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota (k * g) :=
  nativeBalancedLeftMap_generator.{u, v, wH, wG} H G Z rho iota k g

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)] in
/-- The automorphism is the quotient of the actual native permutation smash map. -/
theorem nativeBalancedLeftAut_projection (k : G) :
    discreteSmashLeft.{u, max v (max wH wG), wG} G Z k ≫
      coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
        (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho) =
    coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho) ≫
        (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom :=
  (nativeBalancedLeftMap_projection.{u, v, wH, wG} H G Z rho iota k).symm

/-- The optional generic quotient comparison retains its genuine stronger dictionaries. -/
theorem nativeBalancedIso_left (k : G) :
    ActionCategory.inverseRightLeftMap H G Z rho iota k ≫
        (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom =
      (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom ≫
        (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro g
  simp only [← Category.assoc]
  have hL := ActionCategory.inverseRightLeftMap_generator H G Z rho iota k g
  have hG := nativeBalancedIso_generator.{u, v, wH, wG} H G Z rho iota g
  have hKG := nativeBalancedIso_generator.{u, v, wH, wG} H G Z rho iota (k * g)
  have hN := nativeBalancedLeftAut_generator.{u, v, wH, wG} H G Z rho iota k g
  have hLeft :
      (ActionCategory.inverseRightGenerator H G Z rho iota g ≫
        ActionCategory.inverseRightLeftMap H G Z rho iota k) ≫
        (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom =
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota (k * g) :=
    (congrArg (fun f => f ≫ (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom) hL).trans hKG
  have hRight :
      (ActionCategory.inverseRightGenerator H G Z rho iota g ≫
        (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom) ≫
        (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom =
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota (k * g) :=
    (congrArg (fun f => f ≫
      (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom) hG).trans hN
  change
    (ActionCategory.inverseRightGenerator H G Z rho iota g ≫
      ActionCategory.inverseRightLeftMap H G Z rho iota k) ≫
        (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom =
      (ActionCategory.inverseRightGenerator H G Z rho iota g ≫
        (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom) ≫
        (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom
  exact hLeft.trans hRight.symm

end DirectNativeLeft

variable [HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)]

/-- The original chosen inverse-right action colimit compares to the actual native quotient. -/
def nativeBalancedColimitIso :
    colimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota) ≅
      nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota :=
  ActionCategory.inverseRightColimitIso H G Z rho iota ≪≫
    nativeBalancedIso.{u, v, wH, wG} H G Z rho iota

/-- Every original action-colimit leg becomes its literal native coefficient generator. -/
theorem nativeBalancedColimitIso_generator (g : G) :
    let _ := ActionCategory.inverseRightMulAction H G iota
    colimit.ι (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)
      (g : ActionCategory H G) ≫
        (nativeBalancedColimitIso.{u, v, wH, wG} H G Z rho iota).hom =
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g := by
  let _ := ActionCategory.inverseRightMulAction H G iota
  let _ : HasColimit (ActionCategory.coefficientDiagram H G Z rho) := by
    change HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)
    infer_instance
  let _ : HasCoequalizer (ActionCategory.coefficientSource H G Z)
      (ActionCategory.coefficientTarget H G Z rho) := by
    change HasCoequalizer (ActionCategory.coefficientSource H G Z)
      (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)
    infer_instance
  have hg := ActionCategory.coefficientColimitIso_generator H G Z rho g
  change colimit.ι (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)
      (g : ActionCategory H G) ≫
      (ActionCategory.inverseRightColimitIso H G Z rho iota).hom =
    ActionCategory.inverseRightGenerator H G Z rho iota g at hg
  change _ ≫ ((ActionCategory.inverseRightColimitIso H G Z rho iota).hom ≫
    (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom) = _
  rw [← Category.assoc, hg]
  exact nativeBalancedIso_generator.{u, v, wH, wG} H G Z rho iota g

/-- The chosen colimit comparison intertwines the actual full left action. -/
theorem nativeBalancedColimitIso_left (k : G) :
    ActionCategory.inverseRightLeftColimitMap H G Z rho iota k ≫
      (nativeBalancedColimitIso.{u, v, wH, wG} H G Z rho iota).hom =
    (nativeBalancedColimitIso.{u, v, wH, wG} H G Z rho iota).hom ≫
      (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom := by
  let c := (ActionCategory.inverseRightColimitIso H G Z rho iota).hom
  let e := (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom
  let l := ActionCategory.inverseRightLeftColimitMap H G Z rho iota k
  let q := ActionCategory.inverseRightLeftMap H G Z rho iota k
  let n := (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom
  have hC : l ≫ c = c ≫ q :=
    ActionCategory.inverseRightColimitIso_left H G Z rho iota k
  have hQ : q ≫ e = e ≫ n :=
    nativeBalancedIso_left.{u, v, wH, wG} H G Z rho iota k
  change l ≫ (c ≫ e) = (c ≫ e) ≫ n
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ e) hC).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => c ≫ f) hQ).trans (Category.assoc _ _ _).symm)))

section CoefficientMaps

variable (Z' : PointedCGWH.{u, max v (max wH wG)}) (rho' : H →* End Z')
variable (f : Z ⟶ Z') (hf : ∀ a, End.asHom (rho a) ≫ f = f ≫ End.asHom (rho' a))
variable [HasCoproduct (fun _ : G => Z')]
variable [HasCoproduct (fun _ : H × G => Z')]
variable [HasCoproduct (fun _ : G × H => Z')]
variable [HasCoequalizer (ActionCategory.coefficientSource H G Z')
  (ActionCategory.inverseRightCoefficientTarget H G Z' rho' iota)]
variable [HasCoequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z' iota)
  (smashBalancingCoefficient.{u, v, wH, wG} H G Z' rho')]

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoproduct (fun _ : G => Z')]
  [HasCoproduct (fun _ : H × G => Z')]
  [HasCoproduct (fun _ : G × H => Z')] in
/-- The actual group arrow commutes with literal coefficient smash maps. -/
theorem nativeBalancingGroup_coefficientMap :
    smashBalancingGroup.{u, v, wH, wG} H G Z iota ≫
      nativeSmashCoefficientMap.{u, max v (max wH wG), wG} G Z Z' f =
    nativeSmashCoefficientMap.{u, max v (max wH wG), max wG wH} (G × H) Z Z' f ≫
      smashBalancingGroup.{u, v, wH, wG} H G Z' iota := by
  apply discreteSmash_hom_ext.{u, max v (max wH wG), max wG wH} (G × H) Z
  intro ga
  rw [← Category.assoc, smashBalancingGroup_generator.{u, v, wH, wG},
    nativeSmashCoefficientMap_generator, ← Category.assoc,
    nativeSmashCoefficientMap_generator, Category.assoc,
    smashBalancingGroup_generator.{u, v, wH, wG}]

omit [Group G]
  [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoproduct (fun _ : G => Z')]
  [HasCoproduct (fun _ : H × G => Z')]
  [HasCoproduct (fun _ : G × H => Z')] in
include hf in
/-- The actual End coefficient arrow commutes with those tensor maps under equivariance. -/
theorem nativeBalancingCoefficient_coefficientMap :
    smashBalancingCoefficient.{u, v, wH, wG} H G Z rho ≫
      nativeSmashCoefficientMap.{u, max v (max wH wG), wG} G Z Z' f =
    nativeSmashCoefficientMap.{u, max v (max wH wG), max wG wH} (G × H) Z Z' f ≫
      smashBalancingCoefficient.{u, v, wH, wG} H G Z' rho' := by
  apply discreteSmash_hom_ext.{u, max v (max wH wG), max wG wH} (G × H) Z
  intro ga
  have hRight :
      discreteSmashIncl.{u, max v (max wH wG), max wG wH} (G × H) Z ga ≫
          nativeSmashCoefficientMap.{u, max v (max wH wG), max wG wH}
            (G × H) Z Z' f ≫ smashBalancingCoefficient.{u, v, wH, wG} H G Z' rho' =
        f ≫ End.asHom (rho' ga.2) ≫
          discreteSmashIncl.{u, max v (max wH wG), wG} G Z' ga.1 := by
    rw [← Category.assoc, nativeSmashCoefficientMap_generator,
      Category.assoc, smashBalancingCoefficient_generator.{u, v, wH, wG}]
  rw [← Category.assoc, smashBalancingCoefficient_generator.{u, v, wH, wG},
    Category.assoc, nativeSmashCoefficientMap_generator, ← Category.assoc, hf ga.2]
  exact (Category.assoc _ _ _).trans hRight.symm

/-- The literal coefficient tensor map descends through the actual native coequalizer. -/
def nativeBalancedMap :
    nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota ⟶
      nativeBalancedSmash.{u, v, wH, wG} H G Z' rho' iota :=
  coequalizer.desc
    (nativeSmashCoefficientMap.{u, max v (max wH wG), wG} G Z Z' f ≫
      coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z' iota)
        (smashBalancingCoefficient.{u, v, wH, wG} H G Z' rho'))
    (by
      rw [← Category.assoc, nativeBalancingGroup_coefficientMap.{u, v, wH, wG},
        Category.assoc, coequalizer.condition,
        ← Category.assoc, ← nativeBalancingCoefficient_coefficientMap.{u, v, wH, wG}
          H G Z rho Z' rho' f hf,
        Category.assoc])

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoproduct (fun _ : G => Z')]
  [HasCoproduct (fun _ : H × G => Z')]
  [HasCoproduct (fun _ : G × H => Z')]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z')
    (ActionCategory.inverseRightCoefficientTarget H G Z' rho' iota)]
  [HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)] in
/-- The actual coefficient quotient map retains its literal projection characteristic. -/
theorem nativeBalancedMap_projection :
    coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
        (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho) ≫
      nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf =
    nativeSmashCoefficientMap.{u, max v (max wH wG), wG} G Z Z' f ≫
      coequalizer.π (smashBalancingGroup.{u, v, wH, wG} H G Z' iota)
        (smashBalancingCoefficient.{u, v, wH, wG} H G Z' rho') := by
  unfold nativeBalancedMap
  rw [coequalizer.π_desc]

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoproduct (fun _ : G => Z')]
  [HasCoproduct (fun _ : H × G => Z')]
  [HasCoproduct (fun _ : G × H => Z')]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z')
    (ActionCategory.inverseRightCoefficientTarget H G Z' rho' iota)]
  [HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)] in
/-- The descended map retains every coefficient generator and original f. -/
theorem nativeBalancedMap_generator (g : G) :
    nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g ≫
      nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf =
    f ≫ nativeBalancedGenerator.{u, v, wH, wG} H G Z' rho' iota g := by
  unfold nativeBalancedGenerator
  rw [Category.assoc, nativeBalancedMap_projection.{u, v, wH, wG}, ← Category.assoc,
    nativeSmashCoefficientMap_generator, Category.assoc]

omit [HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)]
  [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoproduct (fun _ : G => Z')]
  [HasCoproduct (fun _ : H × G => Z')]
  [HasCoproduct (fun _ : G × H => Z')]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z')
    (ActionCategory.inverseRightCoefficientTarget H G Z' rho' iota)] in
/-- Native coefficient maps commute with the full actual left action. -/
theorem nativeBalancedMap_left (k : G) :
    (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom ≫
      nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf =
    nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf ≫
      (nativeBalancedLeftAut.{u, v, wH, wG} H G Z' rho' iota k).asIso.hom := by
  apply nativeBalanced_hom_ext.{u, v, wH, wG} H G Z rho iota
  intro g
  rw [← Category.assoc, nativeBalancedLeftAut_generator.{u, v, wH, wG},
    nativeBalancedMap_generator.{u, v, wH, wG}, ← Category.assoc,
    nativeBalancedMap_generator.{u, v, wH, wG}, Category.assoc,
    nativeBalancedLeftAut_generator.{u, v, wH, wG}]

/-- The generic inverse-right coefficient map retains the same local action dictionary. -/
def nativeInverseRightCoefficientMap :
    ActionCategory.inverseRightCoinvariants H G Z rho iota ⟶
      ActionCategory.inverseRightCoinvariants H G Z' rho' iota := by
  letI := ActionCategory.inverseRightMulAction H G iota
  letI : HasCoequalizer (ActionCategory.coefficientSource H G Z)
      (ActionCategory.coefficientTarget H G Z rho) := by
    change HasCoequalizer (ActionCategory.coefficientSource H G Z)
      (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)
    infer_instance
  letI : HasCoequalizer (ActionCategory.coefficientSource H G Z')
      (ActionCategory.coefficientTarget H G Z' rho') := by
    change HasCoequalizer (ActionCategory.coefficientSource H G Z')
      (ActionCategory.inverseRightCoefficientTarget H G Z' rho' iota)
    infer_instance
  exact ActionCategory.coefficientCoequalizerMap H G Z Z' rho rho' f hf

omit [HasCoproduct (fun _ : G × H => Z)]
  [HasCoproduct (fun _ : G × H => Z')]
  [HasCoequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
    (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)]
  [HasCoequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z' iota)
    (smashBalancingCoefficient.{u, v, wH, wG} H G Z' rho')]
  [HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)] in
/-- The exact chosen generic coefficient map has its original generator law. -/
theorem nativeInverseRightCoefficientMap_generator (g : G) :
    ActionCategory.inverseRightGenerator H G Z rho iota g ≫
      nativeInverseRightCoefficientMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf =
    f ≫ ActionCategory.inverseRightGenerator H G Z' rho' iota g := by
  let _ := ActionCategory.inverseRightMulAction H G iota
  let _ : HasCoequalizer (ActionCategory.coefficientSource H G Z)
      (ActionCategory.coefficientTarget H G Z rho) := by
    change HasCoequalizer (ActionCategory.coefficientSource H G Z)
      (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)
    infer_instance
  let _ : HasCoequalizer (ActionCategory.coefficientSource H G Z')
      (ActionCategory.coefficientTarget H G Z' rho') := by
    change HasCoequalizer (ActionCategory.coefficientSource H G Z')
      (ActionCategory.inverseRightCoefficientTarget H G Z' rho' iota)
    infer_instance
  exact ActionCategory.coefficientCoequalizerMap_generator H G Z Z' rho rho' f hf g

omit [HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)] in
/-- The original inverse-right quotient comparison is natural for every coefficient map. -/
theorem nativeBalancedIso_naturality :
    nativeInverseRightCoefficientMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf ≫
      (nativeBalancedIso.{u, v, wH, wG} H G Z' rho' iota).hom =
    (nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom ≫
      nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro g
  change ActionCategory.inverseRightGenerator H G Z rho iota g ≫
      (nativeInverseRightCoefficientMap.{u, v, wH, wG}
        H G Z rho iota Z' rho' f hf ≫
        (nativeBalancedIso.{u, v, wH, wG} H G Z' rho' iota).hom) =
    ActionCategory.inverseRightGenerator H G Z rho iota g ≫
      ((nativeBalancedIso.{u, v, wH, wG} H G Z rho iota).hom ≫
        nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf)
  rw [← Category.assoc, nativeInverseRightCoefficientMap_generator,
    Category.assoc, nativeBalancedIso_generator.{u, v, wH, wG}, ← Category.assoc,
    nativeBalancedIso_generator.{u, v, wH, wG}, nativeBalancedMap_generator.{u, v, wH, wG}]

variable [HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z' rho' iota)]

/-- The original action-coefficient diagram map keeps the selected inverse-right action. -/
def nativeInverseRightCoefficientNatTrans :
    ActionCategory.inverseRightCoefficientDiagram H G Z rho iota ⟶
      ActionCategory.inverseRightCoefficientDiagram H G Z' rho' iota := by
  letI := ActionCategory.inverseRightMulAction H G iota
  exact ActionCategory.coefficientNatTrans H G Z Z' rho rho' f hf

/-- The full original action-colimit/native-smash comparison is coefficient-natural. -/
theorem nativeBalancedColimitIso_naturality :
    colimMap (nativeInverseRightCoefficientNatTrans.{u, v, wH, wG}
      H G Z rho iota Z' rho' f hf) ≫
      (nativeBalancedColimitIso.{u, v, wH, wG} H G Z' rho' iota).hom =
    (nativeBalancedColimitIso.{u, v, wH, wG} H G Z rho iota).hom ≫
      nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf := by
  let _ := ActionCategory.inverseRightMulAction H G iota
  apply colimit.hom_ext
  intro e
  obtain ⟨g, hg⟩ := (ActionCategory.objEquiv H G).surjective e
  rw [← hg]
  let x : ActionCategory H G := (ActionCategory.objEquiv H G) g
  let L := colimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)
  let L' := colimit (ActionCategory.inverseRightCoefficientDiagram H G Z' rho' iota)
  let Q := nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota
  let Q' := nativeBalancedSmash.{u, v, wH, wG} H G Z' rho' iota
  let l : Z ⟶ L :=
    colimit.ι (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota) x
  let l' : Z' ⟶ L' :=
    colimit.ι (ActionCategory.inverseRightCoefficientDiagram H G Z' rho' iota) x
  let cmp : L ⟶ Q := (nativeBalancedColimitIso.{u, v, wH, wG} H G Z rho iota).hom
  let cmp' : L' ⟶ Q' := (nativeBalancedColimitIso.{u, v, wH, wG} H G Z' rho' iota).hom
  let lm : L ⟶ L' := colimMap (nativeInverseRightCoefficientNatTrans.{u, v, wH, wG}
    H G Z rho iota Z' rho' f hf)
  let qm : Q ⟶ Q' := nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf
  let qg : Z ⟶ Q := nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g
  let qg' : Z' ⟶ Q' := nativeBalancedGenerator.{u, v, wH, wG} H G Z' rho' iota g
  have hMap : l ≫ lm = f ≫ l' :=
    ι_colimMap (nativeInverseRightCoefficientNatTrans.{u, v, wH, wG}
      H G Z rho iota Z' rho' f hf) x
  have hCompare : l ≫ cmp = qg :=
    nativeBalancedColimitIso_generator.{u, v, wH, wG} H G Z rho iota g
  have hCompare' : l' ≫ cmp' = qg' :=
    nativeBalancedColimitIso_generator.{u, v, wH, wG} H G Z' rho' iota g
  have hGenerator : qg ≫ qm = f ≫ qg' :=
    nativeBalancedMap_generator.{u, v, wH, wG} H G Z rho iota Z' rho' f hf g
  have hLeft : (l ≫ lm) ≫ cmp' = f ≫ qg' :=
    (congrArg (fun k : Z ⟶ L' => k ≫ cmp') hMap).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k : Z' ⟶ Q' => f ≫ k) hCompare'))
  have hRight : (l ≫ cmp) ≫ qm = f ≫ qg' :=
    (congrArg (fun k : Z ⟶ Q => k ≫ qm) hCompare).trans hGenerator
  change l ≫ (lm ≫ cmp') = l ≫ (cmp ≫ qm)
  exact (Category.assoc _ _ _).symm.trans
    (hLeft.trans (hRight.symm.trans (Category.assoc _ _ _)))

end CoefficientMaps

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)]
  [HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)] in
/-- Identity coefficients induce the actual quotient identity. -/
theorem nativeBalancedMap_id :
    nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z rho (𝟙 Z)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) =
    𝟙 (nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota) := by
  apply nativeBalanced_hom_ext.{u, v, wH, wG} H G Z rho iota
  intro g
  rw [nativeBalancedMap_generator.{u, v, wH, wG}, Category.id_comp, Category.comp_id]

omit [HasCoproduct (fun _ : G => Z)]
  [HasCoproduct (fun _ : H × G => Z)]
  [HasCoproduct (fun _ : G × H => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource H G Z)
    (ActionCategory.inverseRightCoefficientTarget H G Z rho iota)]
  [HasColimit (ActionCategory.inverseRightCoefficientDiagram H G Z rho iota)] in
/-- Actual coefficient composition descends as categorical map composition. -/
theorem nativeBalancedMap_comp
    (Z' Z'' : PointedCGWH.{u, max v (max wH wG)})
    (rho' : H →* End Z') (rho'' : H →* End Z'')
    (f : Z ⟶ Z') (hf : ∀ a, End.asHom (rho a) ≫ f = f ≫ End.asHom (rho' a))
    (g : Z' ⟶ Z'') (hg : ∀ a, End.asHom (rho' a) ≫ g = g ≫ End.asHom (rho'' a))
    [HasCoequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z' iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z' rho')]
    [HasCoequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z'' iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z'' rho'')] :
    nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z'' rho'' (f ≫ g)
      (fun a => (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ g) (hf a)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun h => f ≫ h) (hg a)).trans (Category.assoc _ _ _).symm)))) =
    nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf ≫
      nativeBalancedMap.{u, v, wH, wG} H G Z' rho' iota Z'' rho'' g hg := by
  apply nativeBalanced_hom_ext.{u, v, wH, wG} H G Z rho iota
  intro x
  have hRight :
      nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota x ≫
          (nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf ≫
            nativeBalancedMap.{u, v, wH, wG} H G Z' rho' iota Z'' rho'' g hg) =
        f ≫ g ≫ nativeBalancedGenerator.{u, v, wH, wG} H G Z'' rho'' iota x := by
    rw [← Category.assoc, nativeBalancedMap_generator.{u, v, wH, wG},
      Category.assoc, nativeBalancedMap_generator.{u, v, wH, wG}]
  rw [nativeBalancedMap_generator.{u, v, wH, wG}]
  exact (Category.assoc _ _ _).trans hRight.symm

end PointedCGWH
