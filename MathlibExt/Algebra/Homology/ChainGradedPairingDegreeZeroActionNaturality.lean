/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairing

@[expose] public section

open CategoryTheory MonoidalCategory

open scoped TensorProduct

universe u

namespace HomologicalComplex

/-- Naturality of the degree-zero graded-pairing action. -/
@[reassoc]
public theorem chainGradedPairingDegreeZeroAction_naturality
    (R : Type u) [CommRing R] (A A' : ModuleCat R)
    (K K' L L' : ChainComplex (ModuleCat R) ℕ)
    (B : ChainGradedPairing ((ChainComplex.single₀ (ModuleCat R)).obj A) K L)
    (B' : ChainGradedPairing ((ChainComplex.single₀ (ModuleCat R)).obj A') K' L')
    (a : A ⟶ A') (f : K ⟶ K') (g : L ⟶ L')
    (hcompat : HomologicalComplex.tensorHom
      ((ChainComplex.single₀ (ModuleCat R)).map a) f ≫ B' = B ≫ g)
    (q : ℕ) :
    chainGradedPairingDegreeZeroAction R B q ≫ g.f q =
      (a ⊗ₘ f.f q) ≫ chainGradedPairingDegreeZeroAction R B' q := by
  rw [chainGradedPairingDegreeZeroAction_normalization,
    chainGradedPairingDegreeZeroAction_normalization]
  simp only [Category.assoc]
  have hpair := ChainGradedPairing.pair_naturality B B'
    ((ChainComplex.single₀ (ModuleCat R)).map a) f g hcompat 0 q
  have hX : (L.XIsoOfEq (Nat.zero_add q)).hom ≫ g.f q =
      g.f (0 + q) ≫ (L'.XIsoOfEq (Nat.zero_add q)).hom := by
    rw [XIsoOfEq_hom_naturality]
  have hwhisker : (a ⊗ₘ f.f q) ≫
      ((singleObjXSelf (ComplexShape.down ℕ) 0 A').inv ▷ K'.X q) =
      ((singleObjXSelf (ComplexShape.down ℕ) 0 A).inv ▷ K.X q) ≫
        ((((ChainComplex.single₀ (ModuleCat R)).map a).f 0) ⊗ₘ f.f q) := by
    simp
  calc ((singleObjXSelf (ComplexShape.down ℕ) 0 A).inv ▷ K.X q) ≫
        B.pair 0 q ≫ (L.XIsoOfEq (Nat.zero_add q)).hom ≫ g.f q
      = ((singleObjXSelf (ComplexShape.down ℕ) 0 A).inv ▷ K.X q) ≫
        B.pair 0 q ≫ g.f (0 + q) ≫
        (L'.XIsoOfEq (Nat.zero_add q)).hom := by
        rw [hX]
    _ = ((singleObjXSelf (ComplexShape.down ℕ) 0 A).inv ▷ K.X q) ≫
        (((((ChainComplex.single₀ (ModuleCat R)).map a).f 0) ⊗ₘ f.f q) ≫
          B'.pair 0 q) ≫ (L'.XIsoOfEq (Nat.zero_add q)).hom := by
        rw [← Category.assoc (B.pair 0 q) (g.f (0 + q))
          ((L'.XIsoOfEq (Nat.zero_add q)).hom), ← hpair]
    _ = ((a ⊗ₘ f.f q) ≫
        ((singleObjXSelf (ComplexShape.down ℕ) 0 A').inv ▷ K'.X q)) ≫
        B'.pair 0 q ≫ (L'.XIsoOfEq (Nat.zero_add q)).hom := by
        rw [Category.assoc _ (B'.pair 0 q)
          ((L'.XIsoOfEq (Nat.zero_add q)).hom),
          ← Category.assoc _ _
            (B'.pair 0 q ≫ (L'.XIsoOfEq (Nat.zero_add q)).hom),
          ← hwhisker]
    _ = (a ⊗ₘ f.f q) ≫ ((singleObjXSelf (ComplexShape.down ℕ) 0 A').inv ▷
        K'.X q) ≫ B'.pair 0 q ≫ (L'.XIsoOfEq (Nat.zero_add q)).hom := by
        simp only [Category.assoc]

end HomologicalComplex

end
