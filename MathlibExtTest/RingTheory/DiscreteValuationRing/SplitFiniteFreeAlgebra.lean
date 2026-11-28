/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.SplitFiniteFreeAlgebra

#check @Algebra.TensorProduct.surjective_algebraMap_quotient_of_splits
#check @IsDiscreteValuationRing.exists_finite_extension_forall_isMaximal_surjective

open scoped TensorProduct

universe w

-- For `H = O ⊗ O`, free of rank one, the conclusion gives a discrete valuation ring `O'` whose
-- maximal ideal meets `O` in its maximal ideal, inside a finite extension of `K`.
example {O : Type*} (K : Type w) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] :
    ∃ (K' : Type w) (_ : Field K') (_ : Algebra K K') (O' : Subring K')
      (_ : IsDiscreteValuationRing O') (ι : O →+* O'), FiniteDimensional K K' ∧
      (IsLocalRing.maximalIdeal O').comap ι = IsLocalRing.maximalIdeal O := by
  obtain ⟨K', hF, hA, -, -, O', hD, ι, hfin, -, -, hm, -⟩ :=
    IsDiscreteValuationRing.exists_finite_extension_forall_isMaximal_surjective (O := O) (H := O) K
  exact ⟨K', hF, hA, O', hD, ι, hfin, hm⟩

-- After any further extension of the scalars the residue fields stay the scalars: the minimal
-- polynomials still split.
example {K L L' B : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra L L']
    [Algebra K L'] [IsScalarTower K L L'] [CommRing B] [Algebra K B] [FiniteDimensional K B]
    {ι : Type*} (b : Module.Basis ι K B) (h : ∀ i, ((minpoly K (b i)).map (algebraMap K L)).Splits)
    (Q : Ideal (L' ⊗[K] B)) [Q.IsMaximal] :
    Function.Surjective (algebraMap L' ((L' ⊗[K] B) ⧸ Q)) := by
  refine Algebra.TensorProduct.surjective_algebraMap_quotient_of_splits b (fun i => ?_) Q
  rw [IsScalarTower.algebraMap_eq K L L', ← Polynomial.map_map]
  exact (h i).map _
