/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.SingularCWType

/-!
# A neutral client for the original singular counit inverse

An arbitrary continuous retract of an open normed space supplies the
inverse and both complete point-relative families through the topology API.
-/

public section

noncomputable section

open CategoryTheory Topology

universe u

example {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    (U : Set E) (hU : IsOpen U) (i : C(M, U)) (r : C(U, M))
    (hri : r.comp i = ContinuousMap.id M) (m : M) :
    let X : TopCat.{u} := TopCat.of M
    let Z : TopCat.{u} := SSet.toTop.obj (TopCat.toSSet.obj X)
    let z0 : Z := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm m)
    ∃ R : X ⟶ Z, R m = z0 ∧
      ∃ HL : ContinuousMap.HomotopyRel (sSetTopAdj.counit.app X ≫ R).hom
          (TopCat.Hom.hom (𝟙 Z)) {z0},
        ∃ HR : ContinuousMap.HomotopyRel (R ≫ sSetTopAdj.counit.app X).hom
            (TopCat.Hom.hom (𝟙 X)) {m},
          (∀ t : unitInterval, HL (t, z0) = z0) ∧
          (∀ t : unitInterval, HR (t, m) = m) ∧
          ∃ A : ContinuousMap.HomotopyEquiv Z X,
            A.toFun = (sSetTopAdj.counit.app X).hom ∧ A.invFun = R.hom := by
  obtain ⟨_, _, R, hR, _, HL, HR, hL, hRight, A, hA, hInv⟩ :=
    TopCat.cwType_of_openNormedRetract U hU i r hri m
  exact ⟨R, hR, HL, HR, hL, hRight, A, hA, hInv⟩
