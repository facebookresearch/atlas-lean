/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.HomotopyCofiber.Homology
public import MathlibExt.CategoryTheory.Functor.Effaceable

/-!
# Effacement of positive cochain cohomology

Let C be a preadditive category. For a nonnegative cochain complex K whose
identity map has a homotopy cofiber, define Eff(K)=Cofib(1_K) and take
the canonical cofiber inclusion e:K → Eff(K). This map is monic.
If the source and target have homology in degree n+1, then Hⁿ⁺¹(e)=0.

When C has binary biproducts and homology, this construction gives, for every
K, a monomorphism that kills its cohomology in a specified positive degree.
Consequently the degree-(n+1) cochain cohomology functor is effaceable for
every n∈ℕ.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- For a nonnegative cochain complex K in a preadditive category C, assuming
the homotopy cofiber of its identity exists, the effacement complex
Eff(K)=Cofib(1_K). -/
def positiveEffacement (K : CochainComplex C ℕ) [HasHomotopyCofiber (𝟙 K)] :
    CochainComplex C ℕ :=
  homotopyCofiber (𝟙 K)

/-- For a nonnegative cochain complex K in a preadditive category C whose
identity has a homotopy cofiber, the canonical cofiber inclusion
e:K → Eff(K)=Cofib(1_K). -/
def positiveEffacementMap (K : CochainComplex C ℕ) [HasHomotopyCofiber (𝟙 K)] :
    K ⟶ positiveEffacement K :=
  homotopyCofiber.inr (𝟙 K)

/-- In a preadditive category C, for a nonnegative cochain complex K whose
identity has a homotopy cofiber, the canonical inclusion
K → Eff(K)=Cofib(1_K) is a monomorphism of cochain complexes. -/
theorem positiveEffacementMap_mono (K : CochainComplex C ℕ)
    [HasHomotopyCofiber (𝟙 K)] :
    Mono (positiveEffacementMap K) :=
  homotopyCofiber.mono_inr (𝟙 K)

/-- Let C be preadditive, K a nonnegative cochain complex, and n∈ℕ.
Assume the homotopy cofiber Eff(K)=Cofib(1_K) exists and both K and
Eff(K) have the chosen homology objects in degree n+1. The map induced
by the canonical inclusion e:K → Eff(K) on that cohomology is zero:
Hⁿ⁺¹(e)=0. -/
theorem positiveEffacementMap_homology_succ_eq_zero (K : CochainComplex C ℕ) (n : ℕ)
    [HasHomotopyCofiber (𝟙 K)]
    [K.HasHomology (n + 1)] [(positiveEffacement K).HasHomology (n + 1)] :
    homologyMap (positiveEffacementMap K) (n + 1) = 0 := by
  rename_i hCF hK hE
  change (homotopyCofiber (𝟙 K)).HasHomology (n + 1) at hE
  letI : (homotopyCofiber (𝟙 K)).HasHomology (n + 1) := hE
  change homologyMap (homotopyCofiber.inr (𝟙 K)) (n + 1) = 0
  rw [← Category.id_comp (homotopyCofiber.inr (𝟙 K))]
  exact @homotopyCofiber.homologyMap_comp_inr_eq_zero C _ _ ℕ (ComplexShape.up ℕ) _
    K K (𝟙 K) hCF n (n + 1) (by rfl) hK hE

/-- For a preadditive category C with binary biproducts and homology, the
degree-(n+1) cohomology functor on nonnegative cochain complexes is
effaceable for every n∈ℕ. Each K admits the monomorphism
K → Cofib(1_K) whose induced map on Hⁿ⁺¹ is zero. -/
theorem homologyFunctor_isEffaceable_succ
    [HasBinaryBiproducts C] [CategoryWithHomology C] (n : ℕ) :
    (homologyFunctor C (ComplexShape.up ℕ) (n + 1)).IsEffaceable := by
  intro K
  exact ⟨positiveEffacement K, positiveEffacementMap K,
    positiveEffacementMap_mono K, positiveEffacementMap_homology_succ_eq_zero K n⟩

end CochainComplex
