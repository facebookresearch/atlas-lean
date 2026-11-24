/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Topology.ContinuousMap.Sigma
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Preservation of coproducts by `TopCat.toSSet`

We show that the singular simplicial set functor `TopCat.toSSet` preserves
arbitrary discrete colimits (coproducts).  The proof uses the explicit
coproduct cofan `TopCat.sigmaCofan` and is pointwise: at a simplex level
`n`, a singular simplex in a disjoint union lands in a unique summand
because the topological standard simplex is connected.

## Main results

* `toSSetObjEquiv_map_sigmaι`: identification of a singular simplex after a
  coproduct leg with postcomposition by `ContinuousMap.sigmaMk`.
* `toSSetMapSigmaCofanIsColimit`: the image of the explicit coproduct cofan
  under `toSSet` is colimiting.
* `PreservesColimit (Discrete.functor X) TopCat.toSSet` and
  `toSSet_preservesColimitsOfShape_discrete`: preservation of discrete
  colimits, per-diagram and shape-wide.
-/

@[expose] public section

universe v w

open CategoryTheory Limits TopCat

namespace TopCat

variable {J : Type v} (X : J → TopCat.{max v w})

/-- A singular simplex after a coproduct inclusion is postcomposition by `sigmaMk`. -/
@[simp]
lemma toSSetObjEquiv_map_sigmaι (j : J) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj (X j)).obj n) :
    (TopCat.toSSetObjEquiv _ n) ((TopCat.toSSet.map (TopCat.sigmaι X j)).app n x) =
      (ContinuousMap.sigmaMk j).comp ((TopCat.toSSetObjEquiv _ n) x) :=
  rfl

/-- The image of the explicit `TopCat` coproduct cofan under `toSSet` is colimiting. -/
noncomputable def toSSetMapSigmaCofanIsColimit :
    IsColimit (TopCat.toSSet.{max v w}.mapCocone (TopCat.sigmaCofan X)) := by
  have hEquiv :=
    isColimitMapCoconeCofanMkEquiv (G := TopCat.toSSet.{max v w}) (f := X) (TopCat.sigmaι X)
  suffices h : IsColimit
      (Cofan.mk (TopCat.toSSet.obj (TopCat.of (Σ i, X i)))
        (fun j => TopCat.toSSet.map (TopCat.sigmaι X j))) from
    hEquiv.symm h
  apply evaluationJointlyReflectsColimits
  intro n
  have hEvalEquiv :=
    Cofan.isColimitMapCoconeEquiv (SSet.evaluation.obj n)
      (fun j => TopCat.toSSet.obj (X j))
      (Cofan.mk (TopCat.toSSet.obj (TopCat.of (Σ i, X i)))
        (fun j => TopCat.toSSet.map (TopCat.sigmaι X j)))
  suffices h : IsColimit
      (Cofan.mk ((TopCat.toSSet.obj (TopCat.of (Σ i, X i))).obj n)
        (fun j => (TopCat.toSSet.map (TopCat.sigmaι X j)).app n)) from
    hEvalEquiv.symm h
  have hBijIff :=
    Cofan.nonempty_isColimit_iff_bijective_fromSigma
      (Cofan.mk ((TopCat.toSSet.obj (TopCat.of (Σ i, X i))).obj n)
        (fun j => (TopCat.toSSet.map (TopCat.sigmaι X j)).app n))
  have hBij : Function.Bijective
      ((Cofan.mk ((TopCat.toSSet.obj (TopCat.of (Σ i, X i))).obj n)
          (fun j => (TopCat.toSSet.map (TopCat.sigmaι X j)).app n)).cofanTypes.fromSigma) := by
    let D := Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))
    have hConn : ConnectedSpace D := inferInstance
    let e₁ : (Σ j, (TopCat.toSSet.obj (X j)).obj n) ≃ (Σ j, C(D, X j)) :=
      Equiv.sigmaCongrRight (fun j => TopCat.toSSetObjEquiv (X j) n)
    let e₂ : (Σ j, C(D, X j)) ≃ C(D, Σ i, X i) :=
      (ContinuousMap.sigmaCodHomeomorph D (fun i => (X i : Type (max v w)))).symm.toEquiv
    let e₃ : C(D, Σ i, X i) ≃ (TopCat.toSSet.obj (TopCat.of (Σ i, X i))).obj n :=
      (TopCat.toSSetObjEquiv (TopCat.of (Σ i, X i)) n).symm
    let e : (Σ j, (TopCat.toSSet.obj (X j)).obj n) ≃
        (TopCat.toSSet.obj (TopCat.of (Σ i, X i))).obj n :=
      e₁.trans (e₂.trans e₃)
    have hEq : (Cofan.mk ((TopCat.toSSet.obj (TopCat.of (Σ i, X i))).obj n)
          (fun j => (TopCat.toSSet.map (TopCat.sigmaι X j)).app n)).cofanTypes.fromSigma = e := by
      funext p
      let j := p.1
      let x := p.2
      let c₀ := Cofan.mk ((TopCat.toSSet.obj (TopCat.of (Σ i, X i))).obj n)
          (fun j => (TopCat.toSSet.map (TopCat.sigmaι X j)).app n)
      let c : CofanTypes _ := c₀.cofanTypes
      have hFrom : (TopCat.toSSetObjEquiv (TopCat.of (Σ i, X i)) n) ((c.fromSigma) p) =
          (ContinuousMap.sigmaMk j).comp ((TopCat.toSSetObjEquiv (X j) n) x) := by
        have : (c.fromSigma) p = (TopCat.toSSet.map (TopCat.sigmaι X j)).app n x := rfl
        rw [this, toSSetObjEquiv_map_sigmaι]
      have hE : (TopCat.toSSetObjEquiv (TopCat.of (Σ i, X i)) n) (e p) =
          (ContinuousMap.sigmaMk j).comp ((TopCat.toSSetObjEquiv (X j) n) x) := by
        have he : e p =
            (TopCat.toSSetObjEquiv (TopCat.of (Σ i, X i)) n).symm
              ((ContinuousMap.sigmaMk j).comp ((TopCat.toSSetObjEquiv (X j) n) x)) := rfl
        rw [he, Equiv.apply_symm_apply]
      exact (TopCat.toSSetObjEquiv (TopCat.of (Σ i, X i)) n).injective
        (hFrom.trans hE.symm)
    rw [hEq]
    exact e.bijective
  exact (hBijIff.mpr hBij).some

/-- `TopCat.toSSet` preserves the colimit of a discrete family `X : J → TopCat`. -/
instance {J : Type v} (X : J → TopCat.{max v w}) :
    PreservesColimit (Discrete.functor X) TopCat.toSSet.{max v w} :=
  preservesColimit_of_preserves_colimit_cocone
    (TopCat.sigmaCofanIsColimit X) (toSSetMapSigmaCofanIsColimit X)

/-- `TopCat.toSSet` preserves all discrete colimits of shape `Discrete J`. -/
instance toSSet_preservesColimitsOfShape_discrete (J : Type v) :
    PreservesColimitsOfShape (Discrete J) TopCat.toSSet.{max v w} :=
  preservesColimitsOfShape_of_discrete _

end TopCat
