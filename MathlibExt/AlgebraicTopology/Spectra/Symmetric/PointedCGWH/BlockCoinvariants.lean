/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Action.CoefficientIndex
import MathlibExt.CategoryTheory.Operad.FinBijBlockSubgroup
import MathlibExt.Topology.Category.PointedCGWH.DiscreteCoinvariants

/-!
# Block-torsor coefficient colimits and actual native balanced quotients
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid

namespace PointedCGWH

variable (R N M : CategoryTheory.Operad.SmallFinBijGroupoid) (b : R ⊗ N ≅ M)
variable (Z : PointedCGWH.{u, v}) (rho : Aut R →* End Z)

/-- The chosen block-action coefficient diagram retains every actual automorphism label. -/
def blockCoefficientDiagram :
    letI := blockMulAction R N M
    ActionCategory (Aut R) (R ⊗ N ≅ M) ⥤ PointedCGWH.{u, v} := by
  letI := blockMulAction R N M
  exact ActionCategory.coefficientDiagram (Aut R) (R ⊗ N ≅ M) Z rho

variable [HasColimit (blockCoefficientDiagram R N M Z rho)]
variable [HasColimit (ActionCategory.inverseRightCoefficientDiagram
  (Aut R) (Aut M) Z rho (blockAutHom R N M b))]

/-- The exact block torsor identifies the two chosen action-coefficient colimits. -/
def blockCoefficientIndexIso :
    colimit (blockCoefficientDiagram R N M Z rho) ≅
      colimit (ActionCategory.inverseRightCoefficientDiagram
        (Aut R) (Aut M) Z rho (blockAutHom R N M b)) := by
  letI := blockMulAction R N M
  letI := ActionCategory.inverseRightMulAction (Aut R) (Aut M) (blockAutHom R N M b)
  letI : HasColimit
      (ActionCategory.coefficientDiagram (Aut R) (R ⊗ N ≅ M) Z rho) := by
    change HasColimit (blockCoefficientDiagram R N M Z rho)
    infer_instance
  letI : HasColimit (ActionCategory.coefficientDiagram (Aut R) (Aut M) Z rho) := by
    change HasColimit (ActionCategory.inverseRightCoefficientDiagram
      (Aut R) (Aut M) Z rho (blockAutHom R N M b))
    infer_instance
  exact ActionCategory.coefficientColimitIndexIso
    (Aut R) (R ⊗ N ≅ M) (Aut M) Z rho
    (blockIsoEquivAut R N M b) (fun a e => blockIsoEquivAut_smul R N M b e a)

/-- This comparison sends each actual block label to its literal target automorphism. -/
theorem blockCoefficientIndexIso_generator (e : R ⊗ N ≅ M) :
    letI := blockMulAction R N M
    letI := ActionCategory.inverseRightMulAction (Aut R) (Aut M) (blockAutHom R N M b)
    colimit.ι (blockCoefficientDiagram R N M Z rho)
        (e : ActionCategory (Aut R) (R ⊗ N ≅ M)) ≫
      (blockCoefficientIndexIso R N M b Z rho).hom =
    colimit.ι (ActionCategory.inverseRightCoefficientDiagram
      (Aut R) (Aut M) Z rho (blockAutHom R N M b))
      (blockIsoEquivAut R N M b e : ActionCategory (Aut R) (Aut M)) := by
  let := blockMulAction R N M
  let := ActionCategory.inverseRightMulAction (Aut R) (Aut M) (blockAutHom R N M b)
  let : HasColimit
      (ActionCategory.coefficientDiagram (Aut R) (R ⊗ N ≅ M) Z rho) := by
    change HasColimit (blockCoefficientDiagram R N M Z rho)
    infer_instance
  let : HasColimit (ActionCategory.coefficientDiagram (Aut R) (Aut M) Z rho) := by
    change HasColimit (ActionCategory.inverseRightCoefficientDiagram
      (Aut R) (Aut M) Z rho (blockAutHom R N M b))
    infer_instance
  exact ActionCategory.coefficientColimitIndexIso_generator
    (Aut R) (R ⊗ N ≅ M) (Aut M) Z rho
    (blockIsoEquivAut R N M b) (fun a e => blockIsoEquivAut_smul R N M b e a) e

/-- Full target postcomposition acts on the chosen block coefficient colimit. -/
def blockCoefficientLeftMap (k : Aut M) :
    colimit (blockCoefficientDiagram R N M Z rho) ⟶
      colimit (blockCoefficientDiagram R N M Z rho) := by
  letI := blockMulAction R N M
  letI : HasColimit
      (ActionCategory.coefficientDiagram (Aut R) (R ⊗ N ≅ M) Z rho) := by
    change HasColimit (blockCoefficientDiagram R N M Z rho)
    infer_instance
  exact ActionCategory.coefficientColimitReindex (Aut R) (R ⊗ N ≅ M) Z rho
    (fun e => e ≪≫ k.asIso) (fun a e => (blockMulAction_postcompose R N M a e k).symm)

/-- The block-torsor comparison preserves the full target action on the chosen colimits. -/
theorem blockCoefficientIndexIso_left (k : Aut M) :
    blockCoefficientLeftMap R N M Z rho k ≫ (blockCoefficientIndexIso R N M b Z rho).hom =
      (blockCoefficientIndexIso R N M b Z rho).hom ≫
        ActionCategory.inverseRightLeftColimitMap
          (Aut R) (Aut M) Z rho (blockAutHom R N M b) k := by
  let := blockMulAction R N M
  let := ActionCategory.inverseRightMulAction (Aut R) (Aut M) (blockAutHom R N M b)
  let : HasColimit
      (ActionCategory.coefficientDiagram (Aut R) (R ⊗ N ≅ M) Z rho) := by
    change HasColimit (blockCoefficientDiagram R N M Z rho)
    infer_instance
  let : HasColimit (ActionCategory.coefficientDiagram (Aut R) (Aut M) Z rho) := by
    change HasColimit (ActionCategory.inverseRightCoefficientDiagram
      (Aut R) (Aut M) Z rho (blockAutHom R N M b))
    infer_instance
  exact ActionCategory.coefficientColimitIndexMap_reindex
    (Aut R) (R ⊗ N ≅ M) (Aut M) Z rho
    (blockIsoEquivAut R N M b) (fun a e => blockIsoEquivAut_smul R N M b e a)
    (fun e => e ≪≫ k.asIso) (fun a e => (blockMulAction_postcompose R N M a e k).symm)
    (fun g => k * g)
    (ActionCategory.inverseRightMulAction_left_commute
      (Aut R) (Aut M) (blockAutHom R N M b) k)
    (fun e => blockIsoEquivAut_postcompose R N M b e k)

variable [HasCoproduct (fun _ : Aut M => Z)]
variable [HasCoproduct (fun _ : Aut R × Aut M => Z)]
variable [HasCoproduct (fun _ : Aut M × Aut R => Z)]
variable [HasCoequalizer (ActionCategory.coefficientSource (Aut R) (Aut M) Z)
  (ActionCategory.inverseRightCoefficientTarget
    (Aut R) (Aut M) Z rho (blockAutHom R N M b))]
variable [HasCoequalizer
  (smashBalancingGroup.{u, v, 0, 0} (Aut R) (Aut M) Z (blockAutHom R N M b))
  (smashBalancingCoefficient.{u, v, 0, 0} (Aut R) (Aut M) Z rho)]

/-- The block-action coefficient colimit is the actual native subgroup-balanced smash. -/
def blockCoefficientNativeIso :
    colimit (blockCoefficientDiagram R N M Z rho) ≅
      nativeBalancedSmash.{u, v, 0, 0}
        (Aut R) (Aut M) Z rho (blockAutHom R N M b) :=
  blockCoefficientIndexIso R N M b Z rho ≪≫
    nativeBalancedColimitIso.{u, v, 0, 0}
      (Aut R) (Aut M) Z rho (blockAutHom R N M b)

/-- The native comparison retains the literal block generator and full target label. -/
theorem blockCoefficientNativeIso_generator (e : R ⊗ N ≅ M) :
    letI := blockMulAction R N M
    colimit.ι (blockCoefficientDiagram R N M Z rho)
        (e : ActionCategory (Aut R) (R ⊗ N ≅ M)) ≫
      (blockCoefficientNativeIso R N M b Z rho).hom =
    nativeBalancedGenerator.{u, v, 0, 0}
      (Aut R) (Aut M) Z rho (blockAutHom R N M b) (blockIsoEquivAut R N M b e) := by
  let := blockMulAction R N M
  let := ActionCategory.inverseRightMulAction (Aut R) (Aut M) (blockAutHom R N M b)
  change _ ≫ ((blockCoefficientIndexIso R N M b Z rho).hom ≫
    (nativeBalancedColimitIso.{u, v, 0, 0}
      (Aut R) (Aut M) Z rho (blockAutHom R N M b)).hom) = _
  rw [← Category.assoc, blockCoefficientIndexIso_generator]
  exact nativeBalancedColimitIso_generator.{u, v, 0, 0}
    (Aut R) (Aut M) Z rho (blockAutHom R N M b) (blockIsoEquivAut R N M b e)

/-- The actual native block comparison is equivariant for the full target automorphisms. -/
theorem blockCoefficientNativeIso_left (k : Aut M) :
    blockCoefficientLeftMap R N M Z rho k ≫ (blockCoefficientNativeIso R N M b Z rho).hom =
      (blockCoefficientNativeIso R N M b Z rho).hom ≫
        (nativeBalancedLeftAut.{u, v, 0, 0}
          (Aut R) (Aut M) Z rho (blockAutHom R N M b) k).asIso.hom := by
  let p := (blockCoefficientIndexIso R N M b Z rho).hom
  let q := (nativeBalancedColimitIso.{u, v, 0, 0}
    (Aut R) (Aut M) Z rho (blockAutHom R N M b)).hom
  let t := blockCoefficientLeftMap R N M Z rho k
  let s := ActionCategory.inverseRightLeftColimitMap
    (Aut R) (Aut M) Z rho (blockAutHom R N M b) k
  let a := (nativeBalancedLeftAut.{u, v, 0, 0}
    (Aut R) (Aut M) Z rho (blockAutHom R N M b) k).asIso.hom
  have hp : t ≫ p = p ≫ s := blockCoefficientIndexIso_left R N M b Z rho k
  have hq : s ≫ q = q ≫ a :=
    nativeBalancedColimitIso_left.{u, v, 0, 0}
      (Aut R) (Aut M) Z rho (blockAutHom R N M b) k
  change t ≫ (p ≫ q) = (p ≫ q) ≫ a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ q) hp).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => p ≫ f) hq).trans (Category.assoc _ _ _).symm)))

section CoefficientMaps

variable (Z' : PointedCGWH.{u, v}) (rho' : Aut R →* End Z')
variable (f : Z ⟶ Z') (hf : ∀ a, (rho a).asHom ≫ f = f ≫ (rho' a).asHom)
variable [HasColimit (blockCoefficientDiagram R N M Z' rho')]
variable [HasColimit (ActionCategory.inverseRightCoefficientDiagram
  (Aut R) (Aut M) Z' rho' (blockAutHom R N M b))]
variable [HasCoproduct (fun _ : Aut M => Z')]
variable [HasCoproduct (fun _ : Aut R × Aut M => Z')]
variable [HasCoproduct (fun _ : Aut M × Aut R => Z')]
variable [HasCoequalizer (ActionCategory.coefficientSource (Aut R) (Aut M) Z')
  (ActionCategory.inverseRightCoefficientTarget
    (Aut R) (Aut M) Z' rho' (blockAutHom R N M b))]
variable [HasCoequalizer
  (smashBalancingGroup.{u, v, 0, 0} (Aut R) (Aut M) Z' (blockAutHom R N M b))
  (smashBalancingCoefficient.{u, v, 0, 0} (Aut R) (Aut M) Z' rho')]

/-- Coefficient maps retain the chosen block-index diagram and actual End equivariance. -/
def blockCoefficientNatTrans :
    blockCoefficientDiagram R N M Z rho ⟶ blockCoefficientDiagram R N M Z' rho' := by
  letI := blockMulAction R N M
  exact ActionCategory.coefficientNatTrans
    (Aut R) (R ⊗ N ≅ M) Z Z' rho rho' f hf

omit [HasCoproduct (fun _ : Aut M => Z)]
  [HasCoproduct (fun _ : Aut R × Aut M => Z)]
  [HasCoproduct (fun _ : Aut M × Aut R => Z)]
  [HasCoequalizer (ActionCategory.coefficientSource (Aut R) (Aut M) Z)
    (ActionCategory.inverseRightCoefficientTarget
      (Aut R) (Aut M) Z rho (blockAutHom R N M b))]
  [HasCoequalizer
    (smashBalancingGroup.{u, v, 0, 0} (Aut R) (Aut M) Z (blockAutHom R N M b))
    (smashBalancingCoefficient.{u, v, 0, 0} (Aut R) (Aut M) Z rho)]
  [HasCoproduct (fun _ : Aut M => Z')]
  [HasCoproduct (fun _ : Aut R × Aut M => Z')]
  [HasCoproduct (fun _ : Aut M × Aut R => Z')]
  [HasCoequalizer (ActionCategory.coefficientSource (Aut R) (Aut M) Z')
    (ActionCategory.inverseRightCoefficientTarget
      (Aut R) (Aut M) Z' rho' (blockAutHom R N M b))]
  [HasCoequalizer
    (smashBalancingGroup.{u, v, 0, 0} (Aut R) (Aut M) Z' (blockAutHom R N M b))
    (smashBalancingCoefficient.{u, v, 0, 0} (Aut R) (Aut M) Z' rho')] in
/-- The block-index comparison is natural in every actual equivariant coefficient map. -/
theorem blockCoefficientIndexIso_naturality :
    colimMap (blockCoefficientNatTrans R N M Z rho Z' rho' f hf) ≫
        (blockCoefficientIndexIso R N M b Z' rho').hom =
      (blockCoefficientIndexIso R N M b Z rho).hom ≫
        colimMap (nativeInverseRightCoefficientNatTrans.{u, v, 0, 0}
          (Aut R) (Aut M) Z rho (blockAutHom R N M b) Z' rho' f hf) := by
  let := blockMulAction R N M
  let := ActionCategory.inverseRightMulAction (Aut R) (Aut M) (blockAutHom R N M b)
  let : HasColimit
      (ActionCategory.coefficientDiagram (Aut R) (R ⊗ N ≅ M) Z rho) := by
    change HasColimit (blockCoefficientDiagram R N M Z rho)
    infer_instance
  let : HasColimit
      (ActionCategory.coefficientDiagram (Aut R) (R ⊗ N ≅ M) Z' rho') := by
    change HasColimit (blockCoefficientDiagram R N M Z' rho')
    infer_instance
  let : HasColimit (ActionCategory.coefficientDiagram (Aut R) (Aut M) Z rho) := by
    change HasColimit (ActionCategory.inverseRightCoefficientDiagram
      (Aut R) (Aut M) Z rho (blockAutHom R N M b))
    infer_instance
  let : HasColimit (ActionCategory.coefficientDiagram (Aut R) (Aut M) Z' rho') := by
    change HasColimit (ActionCategory.inverseRightCoefficientDiagram
      (Aut R) (Aut M) Z' rho' (blockAutHom R N M b))
    infer_instance
  exact ActionCategory.coefficientColimitIndexMap_naturality
    (Aut R) (R ⊗ N ≅ M) (Aut M) Z rho Z' rho' f hf
    (blockIsoEquivAut R N M b) (fun a e => blockIsoEquivAut_smul R N M b e a)

/-- The actual native balanced comparison retains complete coefficient naturality. -/
theorem blockCoefficientNativeIso_naturality :
    colimMap (blockCoefficientNatTrans R N M Z rho Z' rho' f hf) ≫
        (blockCoefficientNativeIso R N M b Z' rho').hom =
      (blockCoefficientNativeIso R N M b Z rho).hom ≫
        nativeBalancedMap.{u, v, 0, 0}
          (Aut R) (Aut M) Z rho (blockAutHom R N M b) Z' rho' f hf := by
  let p := (blockCoefficientIndexIso R N M b Z rho).hom
  let p' := (blockCoefficientIndexIso R N M b Z' rho').hom
  let q := (nativeBalancedColimitIso.{u, v, 0, 0}
    (Aut R) (Aut M) Z rho (blockAutHom R N M b)).hom
  let q' := (nativeBalancedColimitIso.{u, v, 0, 0}
    (Aut R) (Aut M) Z' rho' (blockAutHom R N M b)).hom
  let m := colimMap (blockCoefficientNatTrans R N M Z rho Z' rho' f hf)
  let n := colimMap (nativeInverseRightCoefficientNatTrans.{u, v, 0, 0}
    (Aut R) (Aut M) Z rho (blockAutHom R N M b) Z' rho' f hf)
  let z := nativeBalancedMap.{u, v, 0, 0}
    (Aut R) (Aut M) Z rho (blockAutHom R N M b) Z' rho' f hf
  have hp : m ≫ p' = p ≫ n :=
    blockCoefficientIndexIso_naturality R N M b Z rho Z' rho' f hf
  have hq : n ≫ q' = q ≫ z :=
    nativeBalancedColimitIso_naturality.{u, v, 0, 0}
      (Aut R) (Aut M) Z rho (blockAutHom R N M b) Z' rho' f hf
  change m ≫ (p' ≫ q') = (p ≫ q) ≫ z
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ q') hp).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => p ≫ f) hq).trans (Category.assoc _ _ _).symm)))

end CoefficientMaps

end PointedCGWH
