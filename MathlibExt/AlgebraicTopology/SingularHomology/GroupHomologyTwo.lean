/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NativeCoverGroupHomologyTwo
import MathlibExt.AlgebraicTopology.PlusConstruction.Basic
import MathlibExt.AlgebraicTopology.SingularHomology.IntegralReducedConnectivity
import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoidPath
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# The ordinary fundamental group's H2 of an actual acyclic space

Actual reduced integral H2 vanishing gives original ordinary and native
singular H2 vanishing. The canonical singular vertex and the original
fundamental-groupoid equivalence retain the based ordinary group. The
actual native group-H2 theorem and genuine group-homology transport then
prove its integral H2 is zero, with unchanged literal coefficients.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe u

namespace TopCat

/-- Original reduced integral H2 vanishing gives H2 vanishing for the same
space's actual canonical singular simplicial set. -/
theorem nativeSingularHomologyTwo_isZero_of_isAcyclicSpace
    (X : TopCat.{u}) (hX : IsAcyclicSpace X) :
    IsZero ((TopCat.toSSet.obj X).homology
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2) :=
  (hX 2).of_iso
    ((reducedSingularHomologyFunctorIso AddCommGrpCat.{u}
      singularIntegralCoefficients 2 (by decide)).app X).symm

/-- The canonical singular point/group dictionary induces the genuine native
group-homology isomorphism to the original ordinary fundamental group. -/
def singularFundamentalGroupHomologyTwoIso (X : TopCat.{u}) (x : X) :
    groupHomology (Rep.trivial (ULift.{u} ℤ)
      (End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))) (ULift.{u} ℤ)) 2 ≅
        groupHomology (Rep.trivial (ULift.{u} ℤ) (FundamentalGroup X x) (ULift.{u} ℤ)) 2 :=
  groupHomology.mapIso
    (A := Rep.trivial (ULift.{u} ℤ)
      (End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))) (ULift.{u} ℤ))
    (B := Rep.trivial (ULift.{u} ℤ) (FundamentalGroup X x) (ULift.{u} ℤ))
    (TopCat.singularFundamentalGroupoidEndMulEquiv X x)
    (LinearEquiv.refl (ULift.{u} ℤ) (ULift.{u} ℤ)) (fun _ => rfl) 2

/-- The forward transport is the actual group-homology map of the original
fundamental-group equivalence and the unchanged trivial coefficient identity. -/
theorem singularFundamentalGroupHomologyTwoIso_hom (X : TopCat.{u}) (x : X) :
    (singularFundamentalGroupHomologyTwoIso X x).hom =
      groupHomology.map (TopCat.singularFundamentalGroupoidEndMulEquiv X x).toMonoidHom
        (𝟙 (Rep.trivial (ULift.{u} ℤ)
          (End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))) (ULift.{u} ℤ)) :
          Rep.trivial (ULift.{u} ℤ)
              (End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))) (ULift.{u} ℤ) ⟶
            Rep.res (TopCat.singularFundamentalGroupoidEndMulEquiv X x).toMonoidHom
              (Rep.trivial (ULift.{u} ℤ) (FundamentalGroup X x) (ULift.{u} ℤ))) 2 := rfl

/-- For the actual original pointed acyclic space, genuine integral group H2
of its ordinary fundamental group vanishes. -/
theorem groupHomologyTwo_isZero_of_isAcyclicSpace (X : TopCat.{u}) (x : X)
    (hX : IsAcyclicSpace X) :
    IsZero (groupHomology (Rep.trivial (ULift.{u} ℤ)
      (FundamentalGroup X x) (ULift.{u} ℤ)) 2) := by
  let : PathConnectedSpace X := pathConnectedSpace_of_isZero_reducedIntegralH0 X x (hX 0)
  let S := TopCat.toSSet.obj X
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let : SSet.KanComplex S := TopCat.toSSet_obj_kanComplex X
  have hS := nativeSingularHomologyTwo_isZero_of_isAcyclicSpace X hX
  have hG := SSet.KanComplex.nativeCoverGroupHomologyTwo_isZero S sx hS
  exact hG.of_iso (singularFundamentalGroupHomologyTwoIso X x).symm

end TopCat

end
