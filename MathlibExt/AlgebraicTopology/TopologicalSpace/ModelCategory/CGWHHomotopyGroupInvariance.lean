/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.ZerothHomotopyWeakHomotopy
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceHomotopyGroupIso
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.TopCatHomotopyGroupInvariance

/-!
# Weak-equivalence invariance of homotopy groups for CGWH spaces

Selected weak equivalences induce equivalences on path components and on
literal-degree pointed homotopy groups, the pointed case as an application of
the general space-level invariance
(`TopCat.piPositiveMulEquivOfWeakEquivalence`).  The forward functions are the
existing functor maps; no inverse continuous map or shifted convention is
introduced.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped CGWH.modelCategory Simplicial Topology

namespace CGWH

/-- A selected weak equivalence of CGWH spaces induces an equivalence on
path components. -/
noncomputable def piZeroEquivOfWeakEquivalence
    {X Y : CGWH.{u, v}} (f : X ⟶ Y)
    (hf : WeakEquivalence f) : piZero X ≃ piZero Y :=
  Equiv.ofBijective (piZeroMap f) (by
    have hCGWH : CGWH.weakHomotopyEquivalences f := hf.mem
    rw [CGWH.weakHomotopyEquivalences_eq_inverseImage,
      MorphismProperty.inverseImage_iff] at hCGWH
    change Function.Bijective
      (TopCat.zerothHomotopyMap (CGWH.cgwhToTop.map f))
    exact hCGWH.bijective_zerothHomotopyMap)

/-- The forward function of `piZeroEquivOfWeakEquivalence` is the existing
map on path components. -/
@[simp]
theorem piZeroEquivOfWeakEquivalence_apply
    {X Y : CGWH.{u, v}} (f : X ⟶ Y)
    (hf : WeakEquivalence f) (a : piZero X) :
    piZeroEquivOfWeakEquivalence f hf a = piZeroMap f a :=
  rfl

end CGWH

namespace PointedCGWH

/-- A selected pointed weak equivalence induces a multiplicative
equivalence in every actual positive degree `k + 1`, as an application of
the general space-level invariance. -/
noncomputable def piNPositiveMulEquivOfWeakEquivalence
    (k : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : WeakEquivalence f) : piN (k + 1) X ≃* piN (k + 1) Y := by
  let g := CGWH.cgwhToTop.map f.right
  let x := underlyingBasepoint X
  let y := underlyingBasepoint Y
  let h : g.hom x = y := underlyingBasepoint_naturality f
  have hfRight : WeakEquivalence f.right :=
    (PointedCGWH.weakEquivalence_iff f).mp hf
  have hCGWH : CGWH.weakHomotopyEquivalences f.right := hfRight.mem
  have hTop : TopCat.weakHomotopyEquivalences g := by
    rw [CGWH.weakHomotopyEquivalences_eq_inverseImage,
      MorphismProperty.inverseImage_iff] at hCGWH
    exact hCGWH
  let E := TopCat.piPositiveMulEquivOfWeakEquivalence k g x y h hTop
  refine MulEquiv.ofBijective (piNPositiveMap k f).hom ?_
  have hfun : (fun a : piN (k + 1) X ↦
      (piNPositiveMap k f).hom a) = E := by
    funext a
    have hTopMap : (piNPositiveMap k f).hom a =
        HomotopyGroup.mapHomOfEq g.hom h k a := by
      rw [piNPositiveMap_apply]
      let P := fun y' => HomotopyGroup.Pi (k + 1)
        (CGWH.cgwhToTop.obj Y.right) y'
      let e : P y ≃ P (g.hom x) :=
        Equiv.cast (congrArg P h.symm)
      apply e.injective
      change Eq.mp (congrArg P h.symm) (piNMap (k + 1) f a) =
        Eq.mp (congrArg P h.symm)
          (HomotopyGroup.mapHomOfEq g.hom h k a)
      rw [piNMap_apply, HomotopyGroup.mapHomOfEq_apply]
      let castBack : ∀ {z z' : CGWH.cgwhToTop.obj Y.right}
          (hz : z = z') (q : P z),
          Eq.mp (congrArg P hz.symm) (hz ▸ q) = q :=
        fun {z z'} hz q ↦ by
          subst z'
          rfl
      exact (castBack h (HomotopyGroup.map g.hom a)).symm
    rw [hTopMap]
    exact (TopCat.piPositiveMulEquivOfWeakEquivalence_apply
      k g x y h hTop a).symm
  change Function.Bijective (fun a : piN (k + 1) X ↦
    (piNPositiveMap k f).hom a)
  rw [hfun]
  exact E.bijective

/-- The forward function of the positive multiplicative equivalence is the
existing positive homotopy-group map. -/
@[simp]
theorem piNPositiveMulEquivOfWeakEquivalence_apply
    (k : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : WeakEquivalence f) (a : piN (k + 1) X) :
    piNPositiveMulEquivOfWeakEquivalence k f hf a =
      (piNPositiveMap k f).hom a :=
  by
    unfold piNPositiveMulEquivOfWeakEquivalence
    rfl

/-- A selected pointed weak equivalence induces an equivalence in every
literal homotopy degree. -/
noncomputable def piNEquivOfWeakEquivalence
    (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : WeakEquivalence f) : piN n X ≃ piN n Y :=
  match n with
  | 0 =>
      (piNZeroEquivPiZero X).trans
        ((CGWH.piZeroEquivOfWeakEquivalence f.right
          ((PointedCGWH.weakEquivalence_iff f).mp hf)).trans
            (piNZeroEquivPiZero Y).symm)
  | k + 1 => (piNPositiveMulEquivOfWeakEquivalence k f hf).toEquiv

/-- The forward function of the all-degree equivalence is the existing
literal-degree homotopy-group map. -/
@[simp]
theorem piNEquivOfWeakEquivalence_apply
    (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : WeakEquivalence f) (a : piN n X) :
    piNEquivOfWeakEquivalence n f hf a = piNMap n f a := by
  cases n with
  | zero =>
      apply (piNZeroEquivPiZero Y).injective
      rw [piNZeroEquivPiZero_naturality]
      simp only [piNEquivOfWeakEquivalence,
        Equiv.trans_apply, Equiv.apply_symm_apply,
        CGWH.piZeroEquivOfWeakEquivalence_apply]
  | succ k =>
      exact (piNPositiveMulEquivOfWeakEquivalence_apply k f hf a).trans
        (piNPositiveMap_apply k f a)

/-- The all-degree equivalence specializes at literal degree zero to the
path-component equivalence. -/
@[simp]
theorem piNEquivOfWeakEquivalence_zero
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : WeakEquivalence f) :
    piNEquivOfWeakEquivalence 0 f hf =
      (piNZeroEquivPiZero X).trans
        ((CGWH.piZeroEquivOfWeakEquivalence f.right
          ((PointedCGWH.weakEquivalence_iff f).mp hf)).trans
            (piNZeroEquivPiZero Y).symm) :=
  rfl

/-- The all-degree equivalence specializes at an actual successor degree to
the positive multiplicative equivalence. -/
@[simp]
theorem piNEquivOfWeakEquivalence_succ
    (k : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : WeakEquivalence f) :
    piNEquivOfWeakEquivalence (k + 1) f hf =
      (piNPositiveMulEquivOfWeakEquivalence k f hf).toEquiv :=
  rfl

end PointedCGWH
