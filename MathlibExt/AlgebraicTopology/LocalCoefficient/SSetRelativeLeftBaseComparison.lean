/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetRelativeSquareMap

/-!
# Original relative chains under a change of the source subspace

Both relative arrows have the same original ambient coefficient complex.
The actual source map over that ambient base gives their cokernel map. A
weak actual source comparison makes it a quasi-isomorphism, with the two
horizontal monos and the whole original projection retained.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace SSet

variable {A B T : SSet.{u}}

private theorem relativeLeftBaseSquare
    (f : A ⟶ B) (b : B ⟶ T) (a : A ⟶ T) (ha : a = f ≫ b)
    (L : SSet.LocalSystem ℤ T) :
    localCoefficientPullbackChainMap a L ≫ 𝟙 _ =
      localCoefficientChainMapOver f b a ha L ≫ localCoefficientPullbackChainMap b L := by
  rw [Category.comp_id]
  exact (localCoefficientChainMapOver_comp f b a ha L).symm

/-- The same original ambient relative map, through its actual source
comparison. No relative chain comparison is supplied. -/
public def localCoefficientRelativeLeftBaseMap
    (f : A ⟶ B) (b : B ⟶ T) (a : A ⟶ T) (ha : a = f ≫ b)
    (L : SSet.LocalSystem ℤ T) :
    cokernel (localCoefficientPullbackChainMap a L) ⟶
      cokernel (localCoefficientPullbackChainMap b L) :=
  cokernel.map _ _ (localCoefficientChainMapOver f b a ha L) (𝟙 _)
    (relativeLeftBaseSquare f b a ha L)

@[reassoc]
public theorem localCoefficientRelativeLeftBaseMap_π
    (f : A ⟶ B) (b : B ⟶ T) (a : A ⟶ T) (ha : a = f ≫ b)
    (L : SSet.LocalSystem ℤ T) :
    cokernel.π (localCoefficientPullbackChainMap a L) ≫
        localCoefficientRelativeLeftBaseMap f b a ha L =
      cokernel.π (localCoefficientPullbackChainMap b L) := by
  unfold localCoefficientRelativeLeftBaseMap
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

/-- The ACTUAL weak source comparison gives the relative QI on arbitrary
components and every target integer system, without any flatness input. -/
public theorem localCoefficientRelativeLeftBaseMap_quasiIso_of_weak
    (f : A ⟶ B) (hf : realizationWeakEquivalences f)
    (b : B ⟶ T) [Mono b] (a : A ⟶ T) [Mono a] (ha : a = f ≫ b)
    (L : SSet.LocalSystem ℤ T) :
    QuasiIso (localCoefficientRelativeLeftBaseMap f b a ha L) := by
  let m := localCoefficientPullbackChainMap a L
  let n := localCoefficientPullbackChainMap b L
  let s := localCoefficientChainMapOver f b a ha L
  let : Mono m := localCoefficientPullbackChainMap_mono_of_mono a L
  let : Mono n := localCoefficientPullbackChainMap_mono_of_mono b L
  let P := MorphismProperty.monomorphisms (ChainComplex (ModuleCat.{u} ℤ) ℕ)
  let M : P.Arrow ⊤ ⊤ := MorphismProperty.Arrow.mk m (inferInstance : Mono m)
  let N : P.Arrow ⊤ ⊤ := MorphismProperty.Arrow.mk n (inferInstance : Mono n)
  have hs : m ≫ 𝟙 _ = s ≫ n := relativeLeftBaseSquare f b a ha L
  let φ : M ⟶ N := MorphismProperty.Arrow.homMk s (𝟙 _) hs.symm
  have hLeft : QuasiIso φ.left :=
    localCoefficientChainMapOver_quasiIso_of_weak_allComponents f hf b a ha L
  have hRight : QuasiIso φ.right := by
    change QuasiIso (𝟙 (localCoefficientChainComplex L))
    infer_instance
  have h := HomologicalComplex.HomologySequence.quasiIso_coker_map φ hLeft hRight
  change QuasiIso (cokernel.map m n s (𝟙 _) hs) at h
  exact h

end SSet

end
