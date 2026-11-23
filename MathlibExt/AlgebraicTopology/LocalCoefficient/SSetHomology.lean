/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.SSetFunctoriality
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetConstant
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Homology with local coefficients on a simplicial set

The unnormalized local-coefficient chain complex defines a homology object in
each degree.  A natural transformation of local systems induces the homology
map of the landed chain map, with identity and composition laws, and hence a
functor from local systems on one fixed simplicial set to modules.

For a constant local system, applying homology to the landed chain-complex
isomorphism gives the corresponding ordinary simplicial homology isomorphism.
This file does not vary the base simplicial set and makes no topological,
acyclicity, local-coefficient-equivalence, or plus-construction claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R]
variable {X : SSet.{uX}}
variable {L K P : SSet.LocalSystem R X}

/-- Homology in degree `n` of the unnormalized chain complex associated to a
local system. -/
noncomputable abbrev localCoefficientHomology
    (L : SSet.LocalSystem R X) (n : ℕ) :
    ModuleCat.{max uR uX} R :=
  (localCoefficientChainComplex L).homology n

/-- The local-coefficient homology map induced by a natural transformation
of local systems. -/
noncomputable def localCoefficientHomologyMap
    (alpha : L ⟶ K) (n : ℕ) :
    localCoefficientHomology L n ⟶
      localCoefficientHomology K n :=
  HomologicalComplex.homologyMap (localCoefficientChainMap alpha) n

/-- Identity natural transformations induce identity homology maps. -/
@[simp]
theorem localCoefficientHomologyMap_id (n : ℕ) :
    localCoefficientHomologyMap (𝟙 L) n = 𝟙 _ := by
  unfold localCoefficientHomologyMap
  rw [localCoefficientChainMap_id,
    HomologicalComplex.homologyMap_id]

/-- Composition of natural transformations induces composition of homology
maps. -/
@[reassoc]
theorem localCoefficientHomologyMap_comp
    (alpha : L ⟶ K) (beta : K ⟶ P) (n : ℕ) :
    localCoefficientHomologyMap (alpha ≫ beta) n =
      localCoefficientHomologyMap alpha n ≫
        localCoefficientHomologyMap beta n := by
  unfold localCoefficientHomologyMap
  rw [localCoefficientChainMap_comp,
    HomologicalComplex.homologyMap_comp]

/-- Local-coefficient homology in degree `n` as a functor of the local
system on a fixed simplicial set. -/
noncomputable def localCoefficientHomologyFunctor (n : ℕ) :
    SSet.LocalSystem R X ⥤ ModuleCat.{max uR uX} R where
  obj L := localCoefficientHomology L n
  map alpha := localCoefficientHomologyMap alpha n
  map_id _ := localCoefficientHomologyMap_id n
  map_comp alpha beta := localCoefficientHomologyMap_comp alpha beta n

@[simp]
theorem localCoefficientHomologyFunctor_obj
    (L : SSet.LocalSystem R X) (n : ℕ) :
    (localCoefficientHomologyFunctor n).obj L =
      localCoefficientHomology L n :=
  rfl

@[simp]
theorem localCoefficientHomologyFunctor_map
    (alpha : L ⟶ K) (n : ℕ) :
    (localCoefficientHomologyFunctor n).map alpha =
      localCoefficientHomologyMap alpha n :=
  rfl

/-- Constant local-coefficient homology is canonically ordinary simplicial
homology with the same coefficient module. -/
noncomputable def constantLocalCoefficientHomologyIso
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    localCoefficientHomology
        (constantLocalSystem (X := X) M) n ≅
      X.homology M n :=
  HomologicalComplex.homologyMapIso
    (constantLocalCoefficientChainIso (X := X) M) n

@[simp]
theorem constantLocalCoefficientHomologyIso_hom
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    (constantLocalCoefficientHomologyIso (X := X) M n).hom =
      HomologicalComplex.homologyMap
        (constantLocalCoefficientChainIso (X := X) M).hom n :=
  rfl

@[simp]
theorem constantLocalCoefficientHomologyIso_inv
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    (constantLocalCoefficientHomologyIso (X := X) M n).inv =
      HomologicalComplex.homologyMap
        (constantLocalCoefficientChainIso (X := X) M).inv n :=
  rfl

end SSet
