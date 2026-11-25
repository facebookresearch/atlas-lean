/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.SplitWords
public import Mathlib.Algebra.DirectSum.Module

/-!
# Finite sums of split-word coordinates

The finite direct-sum/product equivalence
and split-word coordinates give coefficient
coordinate equivalences. Their summand maps
and inverse coordinates are the original
ideal and quotient maps.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct DirectSum NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- The native finite direct sum of all original colour tensors reconstructs the ambient tensor. -/
def splitWordDirectSumEquiv (splitting : I.KSplit) (N : ℕ) :
    (⨁ colour : Fin N → Bool, splitWordTensor k A I colour) ≃ₗ[k] TensorPower k N A :=
  (DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
    (fun colour => splitWordTensor k A I colour)).trans
      (splitWordCoordinatesEquiv k A I splitting N)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Each native direct-sum inclusion maps by precisely its original section/inclusion tensor map. -/
theorem splitWordDirectSumEquiv_lof (splitting : I.KSplit) (N : ℕ)
    (colour : Fin N → Bool) (x : splitWordTensor k A I colour) :
    splitWordDirectSumEquiv k A I splitting N
        (DirectSum.lof k (Fin N → Bool)
          (fun c => splitWordTensor k A I c) colour x) =
      splitWordToAmbient k A I splitting colour x := by
  classical
  rw [splitWordDirectSumEquiv, LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_lof, splitWordCoordinatesEquiv_apply]
  simp_rw [LinearMap.apply_single]
  simp

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Each inverse native direct-sum coordinate is precisely the original quotient/projection tensor map. -/
theorem splitWordDirectSumEquiv_symm_apply (splitting : I.KSplit) (N : ℕ)
    (x : TensorPower k N A) (colour : Fin N → Bool) :
    (splitWordDirectSumEquiv k A I splitting N).symm x colour =
      splitAmbientToWord k A I splitting colour x := by
  change ((DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
      (fun c => splitWordTensor k A I c)).symm
        ((splitWordCoordinatesEquiv k A I splitting N).symm x)) colour = _
  exact congrArg (fun f => f colour)
    ((DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
      (fun c => splitWordTensor k A I c)).apply_symm_apply
        ((splitWordCoordinatesEquiv k A I splitting N).symm x))

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- The native finite coefficient direct sum reconstructs the original arbitrary-coefficient ambient tensor. -/
def coefficientSplitWordDirectSumEquiv (splitting : I.KSplit) (N : ℕ) :
    (⨁ colour : Fin N → Bool, V ⊗[k] splitWordTensor k A I colour) ≃ₗ[k]
      V ⊗[k] TensorPower k N A :=
  (DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
    (fun colour => V ⊗[k] splitWordTensor k A I colour)).trans
      (coefficientSplitWordCoordinatesEquiv k A I V splitting N)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Each coefficient direct-sum inclusion retains precisely the original identity and position maps. -/
theorem coefficientSplitWordDirectSumEquiv_lof (splitting : I.KSplit) (N : ℕ)
    (colour : Fin N → Bool) (x : V ⊗[k] splitWordTensor k A I colour) :
    coefficientSplitWordDirectSumEquiv k A I V splitting N
        (DirectSum.lof k (Fin N → Bool)
          (fun c => V ⊗[k] splitWordTensor k A I c) colour x) =
      coefficientSplitWordToAmbient k A I V splitting colour x := by
  classical
  rw [coefficientSplitWordDirectSumEquiv, LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_lof, coefficientSplitWordCoordinatesEquiv_apply]
  simp_rw [LinearMap.apply_single]
  simp

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Each inverse coefficient direct-sum coordinate retains precisely the original identity and coordinates. -/
theorem coefficientSplitWordDirectSumEquiv_symm_apply (splitting : I.KSplit) (N : ℕ)
    (x : V ⊗[k] TensorPower k N A) (colour : Fin N → Bool) :
    (coefficientSplitWordDirectSumEquiv k A I V splitting N).symm x colour =
      coefficientSplitAmbientToWord k A I V splitting colour x := by
  change ((DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
      (fun c => V ⊗[k] splitWordTensor k A I c)).symm
        ((coefficientSplitWordCoordinatesEquiv k A I V splitting N).symm x)) colour = _
  exact congrArg (fun f => f colour)
    ((DirectSum.linearEquivFunOnFintype k (Fin N → Bool)
      (fun c => V ⊗[k] splitWordTensor k A I c)).apply_symm_apply
        ((coefficientSplitWordCoordinatesEquiv k A I V splitting N).symm x))

end ModuleCat.Algebra.Hochschild.NonUnital
