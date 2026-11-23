/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarSimplicial
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveEquiv
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Local-coefficient chains on a simplicial set

A covariant local system on a simplicial set is a module-valued functor on
its fundamental groupoid.  The fundamental-groupoid/nerve equivalence gives
a canonical simplicial map from the simplicial set to the nerve of that
groupoid.  Pulling the coefficient bar back along this map produces a
simplicial module and its unnormalized alternating-face chain complex.

The canonical map sends an edge to its forward fundamental-groupoid
generator, with no inverse.  This file stops before functoriality in the local
system or simplicial set, normalized chains, homology, constant-coefficient
comparison, and topological specialization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace SSet

/-- A covariant local system of `R`-modules on a simplicial set.  The module
universe is large enough for coproducts indexed by all simplices of `X`. -/
abbrev LocalSystem (R : Type uR) [CommRing R] (X : SSet.{uX}) :=
  SSet.FundamentalGroupoid X ⥤ ModuleCat.{max uR uX} R

/-- The canonical map from a simplicial set to the nerve of its fundamental
groupoid. -/
noncomputable def fundamentalGroupoidNerveUnit (X : SSet.{uX}) :
    X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid X) :=
  SSet.fundamentalGroupoidNerveEquiv X _
    (𝟭 (SSet.FundamentalGroupoid X))

/-- On vertices, the fundamental-groupoid nerve unit is the corresponding
fundamental-groupoid object. -/
@[simp]
theorem fundamentalGroupoidNerveUnit_app_zero
    (X : SSet.{uX}) (x : X _⦋0⦌) :
    (fundamentalGroupoidNerveUnit X).app _ x =
      CategoryTheory.nerveEquiv.symm
        (SSet.FundamentalGroupoid.mk x) := by
  simpa [fundamentalGroupoidNerveUnit] using
    SSet.fundamentalGroupoidNerveEquiv_app_zero X
      (SSet.FundamentalGroupoid X)
      (𝟭 (SSet.FundamentalGroupoid X)) x

/-- On an edge, the fundamental-groupoid nerve unit is its forward generator.
In particular, no inverse occurs in this formula. -/
@[simp]
theorem fundamentalGroupoidNerveUnit_app_edge
    (X : SSet.{uX}) {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (fundamentalGroupoidNerveUnit X).app _ e.edge =
      ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e) := by
  simpa [fundamentalGroupoidNerveUnit] using
    SSet.fundamentalGroupoidNerveEquiv_app_edge X
      (SSet.FundamentalGroupoid X)
      (𝟭 (SSet.FundamentalGroupoid X)) e

section Coefficients

variable {R : Type uR} [CommRing R]
variable {X : SSet.{uX}}

/-- The coefficient object attached to each degree-`n` simplex by a local
system. -/
noncomputable abbrev localCoefficientFamily
    (L : SSet.LocalSystem R X) (n : ℕ) :
    X _⦋n⦌ → ModuleCat.{max uR uX} R :=
  nervePullbackCoefficientFamily (fundamentalGroupoidNerveUnit X) L n

/-- In degree zero, the coefficient family evaluates the local system at the
fundamental-groupoid object represented by the vertex. -/
@[simp]
theorem localCoefficientFamily_zero
    (L : SSet.LocalSystem R X) (x : X _⦋0⦌) :
    localCoefficientFamily L 0 x =
      L.obj (SSet.FundamentalGroupoid.mk x) := by
  change L.obj (CategoryTheory.nerveEquiv
      ((fundamentalGroupoidNerveUnit X).app _ x)) = _
  rw [fundamentalGroupoidNerveUnit_app_zero,
    Equiv.apply_symm_apply]

/-- Degree-`n` local-coefficient chains before forming the differential. -/
noncomputable abbrev localCoefficientObj
    (L : SSet.LocalSystem R X) (n : ℕ) :
    ModuleCat.{max uR uX} R :=
  nervePullbackCoefficientObj (fundamentalGroupoidNerveUnit X) L n

/-- The local-coefficient map induced by the `i`th face. -/
noncomputable abbrev localCoefficientFace
    (L : SSet.LocalSystem R X) {n : ℕ} (i : Fin (n + 2)) :
    localCoefficientObj L (n + 1) ⟶ localCoefficientObj L n :=
  nervePullbackCoefficientFace (fundamentalGroupoidNerveUnit X) L i

/-- The local-coefficient map induced by the `i`th degeneracy. -/
noncomputable abbrev localCoefficientDegeneracy
    (L : SSet.LocalSystem R X) {n : ℕ} (i : Fin (n + 1)) :
    localCoefficientObj L n ⟶ localCoefficientObj L (n + 1) :=
  nervePullbackCoefficientDegeneracy (fundamentalGroupoidNerveUnit X) L i

/-- The simplicial module associated to a local system on a simplicial set. -/
noncomputable def localCoefficientSimplicial
    (L : SSet.LocalSystem R X) :
    SimplicialObject (ModuleCat.{max uR uX} R) :=
  nervePullbackCoefficientSimplicial (fundamentalGroupoidNerveUnit X) L

/-- Formula for a degree object of the local-coefficient simplicial module. -/
@[simp]
theorem localCoefficientSimplicial_obj
    (L : SSet.LocalSystem R X) (n : ℕ) :
    (localCoefficientSimplicial L).obj
        (op (SimplexCategory.mk n)) =
      localCoefficientObj L n :=
  nervePullbackCoefficientSimplicial_obj
    (fundamentalGroupoidNerveUnit X) L n

/-- Formula for a face of the local-coefficient simplicial module. -/
@[simp]
theorem localCoefficientSimplicial_map_δ
    (L : SSet.LocalSystem R X) {n : ℕ} (i : Fin (n + 2)) :
    (localCoefficientSimplicial L).map
        (SimplexCategory.δ i).op =
      localCoefficientFace L i :=
  nervePullbackCoefficientSimplicial_map_δ
    (fundamentalGroupoidNerveUnit X) L i

/-- Formula for a degeneracy of the local-coefficient simplicial module. -/
@[simp]
theorem localCoefficientSimplicial_map_σ
    (L : SSet.LocalSystem R X) {n : ℕ} (i : Fin (n + 1)) :
    (localCoefficientSimplicial L).map
        (SimplexCategory.σ i).op =
      localCoefficientDegeneracy L i :=
  nervePullbackCoefficientSimplicial_map_σ
    (fundamentalGroupoidNerveUnit X) L i

/-- The unnormalized alternating-face chain complex associated to a local
system on a simplicial set. -/
noncomputable def localCoefficientChainComplex
    (L : SSet.LocalSystem R X) :
    ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
  nervePullbackCoefficientComplex (fundamentalGroupoidNerveUnit X) L

/-- Formula for a degree object of the local-coefficient chain complex. -/
@[simp]
theorem localCoefficientChainComplex_X
    (L : SSet.LocalSystem R X) (n : ℕ) :
    (localCoefficientChainComplex L).X n =
      localCoefficientObj L n :=
  nervePullbackCoefficientComplex_X
    (fundamentalGroupoidNerveUnit X) L n

/-- The differential is the alternating sum of the local-coefficient face
maps. -/
theorem localCoefficientChainComplex_d
    (L : SSet.LocalSystem R X) (n : ℕ) :
    (localCoefficientChainComplex L).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        localCoefficientFace L i :=
  nervePullbackCoefficientComplex_d
    (fundamentalGroupoidNerveUnit X) L n

end Coefficients

end SSet
