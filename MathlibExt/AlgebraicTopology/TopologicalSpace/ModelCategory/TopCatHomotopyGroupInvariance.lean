/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceHomotopyGroupIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidAction
public import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Weak-equivalence invariance of homotopy groups for spaces

A weak homotopy equivalence of spaces induces multiplicative equivalences on
positive homotopy groups.  The forward function is the equality-aware
homotopy-group map; bijectivity goes through the singular comparison.  No
CGWH, pointed, or model-structure statement is made here; the selected
CGWH applications live in `CGWHHomotopyGroupInvariance`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace TopCat

/-- A weak homotopy equivalence of spaces induces a multiplicative
equivalence on positive homotopy groups.  The forward function is the
equality-aware homotopy-group map; bijectivity goes through the singular
comparison. -/
noncomputable def piPositiveMulEquivOfWeakEquivalence
    (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y)
    (hw : TopCat.weakHomotopyEquivalences f) :
    HomotopyGroup.Pi (n + 1) X x ≃*
      HomotopyGroup.Pi (n + 1) Y y := by
  let SX := TopCat.toSSet.obj X
  let SY := TopCat.toSSet.obj Y
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sy := TopCat.toSSetObj₀Equiv.symm y
  let s := TopCat.toSSet.map f
  have hW : SSet.KanComplex.W s :=
    (TopCat.mem_weakHomotopyEquivalences_iff f).mp hw
  letI : SSet.KanComplex SX := SSet.KanComplex.W.kanComplex_source hW
  letI : SSet.KanComplex SY := SSet.KanComplex.W.kanComplex_target hW
  let hs : s.app _ sx = sy := by
    change (TopCat.toSSetObj₀Equiv (X := Y)).symm (f x) =
      (TopCat.toSSetObj₀Equiv (X := Y)).symm y
    exact congrArg (TopCat.toSSetObj₀Equiv (X := Y)).symm h
  let CX := TopCat.homotopyGroupSingularMulEquiv n X x
  let CY := TopCat.homotopyGroupSingularMulEquiv n Y y
  let W := SSet.KanComplex.W.homotopyGroupIso s hW n sx
  let pointEqMulEquiv : ∀ {z z' : SY _⦋0⦌}, z = z' →
      SSet.KanComplex.π (n + 1) SY z ≃*
        SSet.KanComplex.π (n + 1) SY z' :=
    fun {z z'} hz ↦ by
      subst z'
      exact MulEquiv.refl _
  let Ehs := pointEqMulEquiv hs
  have pointEqMulEquiv_homotopyGroupIso
      {z' : SY _⦋0⦌} (hz : s.app _ sx = z')
      (q : SSet.KanComplex.π (n + 1) SX sx) :
      pointEqMulEquiv hz (W q) =
        SSet.KanComplex.π.map s hz (n + 1) q := by
    subst z'
    exact SSet.KanComplex.W.homotopyGroupIso_apply s hW n sx q
  let E := CX.trans (W.trans (Ehs.trans CY.symm))
  refine MulEquiv.ofBijective
    (HomotopyGroup.mapHomOfEq f.hom h n) ?_
  have hfun : (fun a : HomotopyGroup.Pi (n + 1) X x ↦
      HomotopyGroup.mapHomOfEq f.hom h n a) = E := by
    funext a
    apply CY.injective
    rw [TopCat.homotopyGroupSingularMulEquiv_naturality n f h]
    dsimp only [E, CX, CY]
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact (pointEqMulEquiv_homotopyGroupIso hs _).symm
  change Function.Bijective
    (fun a : HomotopyGroup.Pi (n + 1) X x ↦
      HomotopyGroup.mapHomOfEq f.hom h n a)
  rw [hfun]
  exact E.bijective

/-- The forward function of the positive multiplicative equivalence is the
equality-aware homotopy-group map. -/
@[simp]
theorem piPositiveMulEquivOfWeakEquivalence_apply
    (n : ℕ) {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y)
    (hw : TopCat.weakHomotopyEquivalences f)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    piPositiveMulEquivOfWeakEquivalence n f x y h hw a =
      HomotopyGroup.mapHomOfEq f.hom h n a := by
  unfold piPositiveMulEquivOfWeakEquivalence
  rfl

end TopCat

end
