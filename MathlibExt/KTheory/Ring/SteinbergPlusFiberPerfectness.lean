/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.SteinbergPlusFiberSequence
import MathlibExt.AlgebraicTopology.SingularHomology.IntegralReducedConnectivity
import MathlibExt.Topology.Homotopy.TopCat.HurewiczOne
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Perfectness of the actual plus-fiber fundamental group

The original independent plus inclusion has an acyclic complete ending-path
fiber. Reduced integral H₀ and its original point make that fiber path
connected. Reduced integral H₁ identifies with ordinary singular H₁, which
vanishes. The actual ordinary first Hurewicz isomorphism therefore makes
the abelianization of the fiber fundamental group trivial.

This proves the connectedness and perfect-fundamental-group conclusions
of Weibel, *The K-book*, IV, Lemma 1.3.1, printed page 262 (official PDF
page 270), for the original BGL plus fiber. Its degree-two group-homology
conclusion is supplied by `TopCat.groupHomologyTwo_isZero_of_isAcyclicSpace`,
applied to this same fiber's actual acyclicity and original selected point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace AlgebraicKTheory.StableGL

/-- The complete original ending-path fiber is acyclic by the constructed plus theorem. -/
theorem independentPlusFiber_isAcyclic (R : Type u) [Ring R] :
    TopCat.IsAcyclicSpace (independentPlusFiber R) :=
  (independentBGLCellInclusion_isPlus R).acyclic

/-- Vanishing of the original reduced integral H₀ makes the same fiber path connected. -/
theorem independentPlusFiber_pathConnected (R : Type u) [Ring R] :
    PathConnectedSpace (independentPlusFiber R) :=
  TopCat.pathConnectedSpace_of_isZero_reducedIntegralH0
    (independentPlusFiber R) (independentPlusFiberPoint R)
    (independentPlusFiber_isAcyclic R 0)

/-- The actual ordinary integral singular H₁ of the original fiber vanishes. -/
theorem independentPlusFiber_singularHomologyOne_isZero (R : Type u) [Ring R] :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (independentPlusFiber R)) :=
  (independentPlusFiber_isAcyclic R 1).of_iso
    ((reducedSingularHomologyFunctorIso AddCommGrpCat.{u}
      singularIntegralCoefficients 1 (by decide)).app (independentPlusFiber R)).symm

/-- The total group in the original plus-fiber extension is perfect. -/
theorem independentPlusFiberFundamental_isPerfect (R : Type u) [Ring R] :
    Group.IsPerfect (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) := by
  let X := independentPlusFiber R
  let x := independentPlusFiberPoint R
  let G := FundamentalGroup X x
  let _ : PathConnectedSpace X := independentPlusFiber_pathConnected R
  let E := TopCat.fundamentalGroupAbelianizationHomologyOneIso X x
  have hA : IsZero (AddCommGrpCat.of (Additive (Abelianization G))) :=
    (independentPlusFiber_singularHomologyOne_isZero R).of_iso E
  let _ : Subsingleton (Additive (Abelianization G)) :=
    AddCommGrpCat.subsingleton_of_isZero hA
  let _ : Subsingleton (Abelianization G) := Additive.ofMul.injective.subsingleton
  constructor
  apply top_unique
  intro g _
  have hg : Abelianization.of g = (1 : Abelianization G) := Subsingleton.elim _ _
  have hker : g ∈ (Abelianization.of : G →* Abelianization G).ker :=
    MonoidHom.mem_ker.mpr hg
  simpa only [Abelianization.ker_of] using hker

end AlgebraicKTheory.StableGL

end
