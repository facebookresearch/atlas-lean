/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetHomology
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatConstant

/-!
# Homology with local coefficients on a topological space

A natural transformation of topological local systems can be whiskered by
the canonical singular fundamental-groupoid functor.  Applying the landed
simplicial-set local-coefficient homology map gives homology maps, their
identity and composition laws, and a fixed-degree functor.  Applying homology
to the constant-chain comparison identifies native constant local-
coefficient homology with the existing singular homology object.

This file does not vary the base space and introduces no pullback map,
local-coefficient-equivalence predicate, acyclicity, or plus construction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uX

namespace TopCat

namespace LocalSystem

variable {R : Type uR} [CommRing R] {X : TopCat.{uX}}
variable {L K P : TopCat.LocalSystem R X}

/-- Whisker a natural transformation of topological local systems by the
canonical singular fundamental-groupoid functor. -/
noncomputable def toSingularMap (alpha : L ⟶ K) :
    L.toSingular ⟶ K.toSingular :=
  Functor.whiskerLeft
    (TopCat.singularFundamentalGroupoidFunctor X) alpha

@[simp]
theorem toSingularMap_app (alpha : L ⟶ K)
    (x : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (toSingularMap alpha).app x =
      alpha.app ((TopCat.singularFundamentalGroupoidFunctor X).obj x) :=
  rfl

/-- Whiskering preserves the identity natural transformation. -/
@[simp]
theorem toSingularMap_id :
    toSingularMap (𝟙 L) = 𝟙 L.toSingular :=
  rfl

/-- Whiskering preserves composition of natural transformations. -/
@[simp]
theorem toSingularMap_comp (alpha : L ⟶ K) (beta : K ⟶ P) :
    toSingularMap (alpha ≫ beta) =
      toSingularMap alpha ≫ toSingularMap beta :=
  rfl

end LocalSystem

section Homology

variable {R : Type uR} [CommRing R] {X : TopCat.{uX}}
variable {L K P : TopCat.LocalSystem R X}

/-- Homology in degree `n` of the singular chain complex associated to a
topological local system. -/
noncomputable abbrev localCoefficientHomology
    (L : TopCat.LocalSystem R X) (n : ℕ) :
    ModuleCat.{max uR uX} R :=
  SSet.localCoefficientHomology L.toSingular n

/-- The local-coefficient homology map induced by a natural transformation
of topological local systems. -/
noncomputable def localCoefficientHomologyMap
    (alpha : L ⟶ K) (n : ℕ) :
    localCoefficientHomology L n ⟶
      localCoefficientHomology K n :=
  SSet.localCoefficientHomologyMap
    (TopCat.LocalSystem.toSingularMap alpha) n

/-- Identity natural transformations induce identity homology maps. -/
@[simp]
theorem localCoefficientHomologyMap_id (n : ℕ) :
    localCoefficientHomologyMap (𝟙 L) n = 𝟙 _ := by
  unfold localCoefficientHomologyMap
  rw [TopCat.LocalSystem.toSingularMap_id,
    SSet.localCoefficientHomologyMap_id]

/-- Composition of natural transformations induces composition of homology
maps. -/
@[reassoc]
theorem localCoefficientHomologyMap_comp
    (alpha : L ⟶ K) (beta : K ⟶ P) (n : ℕ) :
    localCoefficientHomologyMap (alpha ≫ beta) n =
      localCoefficientHomologyMap alpha n ≫
        localCoefficientHomologyMap beta n := by
  unfold localCoefficientHomologyMap
  rw [TopCat.LocalSystem.toSingularMap_comp,
    SSet.localCoefficientHomologyMap_comp]

/-- Topological local-coefficient homology in degree `n` as a functor of the
local system on one fixed space. -/
noncomputable def localCoefficientHomologyFunctor (n : ℕ) :
    TopCat.LocalSystem R X ⥤ ModuleCat.{max uR uX} R where
  obj L := localCoefficientHomology L n
  map alpha := localCoefficientHomologyMap alpha n
  map_id _ := localCoefficientHomologyMap_id n
  map_comp alpha beta := localCoefficientHomologyMap_comp alpha beta n

@[simp]
theorem localCoefficientHomologyFunctor_obj
    (L : TopCat.LocalSystem R X) (n : ℕ) :
    (localCoefficientHomologyFunctor n).obj L =
      localCoefficientHomology L n :=
  rfl

@[simp]
theorem localCoefficientHomologyFunctor_map
    (alpha : L ⟶ K) (n : ℕ) :
    (localCoefficientHomologyFunctor n).map alpha =
      localCoefficientHomologyMap alpha n :=
  rfl

end Homology

section Constant

variable {R : Type uR} [CommRing R] {X : TopCat.{uX}}

/-- Native constant local-coefficient homology agrees with the existing
singular homology object. -/
noncomputable def constantLocalCoefficientHomologyIso
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    localCoefficientHomology
        (TopCat.constantLocalSystem (X := X) M) n ≅
      ((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{max uR uX} R) n).obj M).obj X := by
  change (TopCat.localCoefficientChainComplex
      (TopCat.constantLocalSystem (X := X) M)).homology n ≅
    (((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{max uR uX} R)).obj M).obj X).homology n
  exact HomologicalComplex.homologyMapIso
    (TopCat.constantLocalCoefficientChainIso (X := X) M) n

@[simp]
theorem constantLocalCoefficientHomologyIso_hom
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    (constantLocalCoefficientHomologyIso (X := X) M n).hom =
      HomologicalComplex.homologyMap
        (TopCat.constantLocalCoefficientChainIso (X := X) M).hom n :=
  rfl

@[simp]
theorem constantLocalCoefficientHomologyIso_inv
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    (constantLocalCoefficientHomologyIso (X := X) M n).inv =
      HomologicalComplex.homologyMap
        (TopCat.constantLocalCoefficientChainIso (X := X) M).inv n :=
  rfl

end Constant

end TopCat
