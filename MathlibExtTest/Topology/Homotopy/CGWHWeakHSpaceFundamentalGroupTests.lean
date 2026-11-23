/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.CGWHWeakHSpaceFundamentalGroup

/-! # Tests for weak-unit native CGWH H-spaces -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory unitInterval

universe u v

namespace MathlibExtTest.Topology.Homotopy
namespace CGWHWeakHSpaceFundamentalGroupTests

section Generic

variable {X : CGWH.{u, v}} (H : X.WeakHSpaceData)

#check CGWH.hspaceLeftUnitPath
#check CGWH.hspaceRightUnitPath
#check CGWH.WeakHSpaceData
#check CGWH.WeakHSpaceData.rawPathMul
#check CGWH.WeakHSpaceData.rawFundamentalMul
#check CGWH.WeakHSpaceData.basepointMulEquiv
#check CGWH.WeakHSpaceData.fundamentalMul
#check CGWH.WeakHSpaceData.fundamentalGroupCommGroup
#check CGWH.WeakHSpaceData.fundamentalGroup_mul_comm

/- These clients retain the arbitrary chosen root path; no reflexivity or
endpoint equality is assumed. -/
example :
    (CGWH.hspaceLeftUnitPath X H.mul H.e H.leftUnit).Homotopic
      H.rootPath :=
  H.leftUnit_root

example :
    (CGWH.hspaceRightUnitPath X H.mul H.e H.rightUnit).Homotopic
      H.rootPath :=
  H.rightUnit_root

/- An explicitly non-strict abstract client: the product point and selected
unit may be unequal, while the chosen root path still supplies transport. -/
example (_hne : H.mulUnit ≠ H.e) : Path H.mulUnit H.e :=
  H.rootPath

example (p q : Path H.e H.e) : Path H.mulUnit H.mulUnit :=
  H.rawPathMul p q

example (p q : FundamentalGroup X H.e) : FundamentalGroup X H.mulUnit :=
  H.rawFundamentalMul p q

example (p q : Path H.e H.e) :
    H.fundamentalMul
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (H.rootPath.symm.trans ((H.rawPathMul p q).trans H.rootPath))) :=
  H.fundamentalMul_mk p q

example (p : FundamentalGroup X H.e) : H.fundamentalMul 1 p = p :=
  H.fundamentalMul_one_left p

example (p : FundamentalGroup X H.e) : H.fundamentalMul p 1 = p :=
  H.fundamentalMul_one_right p

/- The order pins the reversed `FundamentalGroup.mul_def` convention. -/
example (a b c d : FundamentalGroup X H.e) :
    H.fundamentalMul (a * b) (c * d) =
      H.fundamentalMul a c * H.fundamentalMul b d :=
  H.fundamentalMul_interchange a b c d

example (p q : FundamentalGroup X H.e) : p * q = q * p :=
  H.fundamentalGroup_mul_comm p q

noncomputable example : CommGroup (FundamentalGroup X H.e) :=
  H.fundamentalGroupCommGroup

example : True := by
  fail_if_success
    let _ := inferInstanceAs (CommGroup (FundamentalGroup X H.e))
  trivial

end Generic

section RaisedUniverses

variable (X : CGWH.{1, 1}) (H : X.WeakHSpaceData)

example :
    FundamentalGroup X H.mulUnit ≃* FundamentalGroup X H.e :=
  H.basepointMulEquiv

example (p q : FundamentalGroup X H.e) : p * q = q * p :=
  H.fundamentalGroup_mul_comm p q

end RaisedUniverses

#print axioms CGWH.hspaceLeftUnitPath
#print axioms CGWH.hspaceRightUnitPath
#print axioms CGWH.WeakHSpaceData
#print axioms CGWH.WeakHSpaceData.mulUnit
#print axioms CGWH.WeakHSpaceData.pathHom
#print axioms CGWH.WeakHSpaceData.pathPair
#print axioms CGWH.WeakHSpaceData.pathPair_apply
#print axioms CGWH.WeakHSpaceData.rawPathMul
#print axioms CGWH.WeakHSpaceData.rawPathMul_apply
#print axioms CGWH.WeakHSpaceData.pathHomotopyHom
#print axioms CGWH.WeakHSpaceData.pathHomotopyPair
#print axioms CGWH.WeakHSpaceData.pathHomotopyPair_apply
#print axioms CGWH.WeakHSpaceData.rawPathMulHomotopy
#print axioms CGWH.WeakHSpaceData.rawFundamentalMul
#print axioms CGWH.WeakHSpaceData.rawFundamentalMul_mk
#print axioms CGWH.WeakHSpaceData.basepointMulEquiv
#print axioms CGWH.WeakHSpaceData.fundamentalMul
#print axioms CGWH.WeakHSpaceData.fundamentalMul_mk
#print axioms CGWH.WeakHSpaceData.leftUnitMap_unit
#print axioms CGWH.WeakHSpaceData.rightUnitMap_unit
#print axioms CGWH.WeakHSpaceData.leftMappedPath
#print axioms CGWH.WeakHSpaceData.rightMappedPath
#print axioms CGWH.WeakHSpaceData.rawPathMul_refl_left
#print axioms CGWH.WeakHSpaceData.rawPathMul_refl_right
#print axioms CGWH.WeakHSpaceData.rawPathMul_refl_left_trans_leftUnitPath
#print axioms CGWH.WeakHSpaceData.rawPathMul_refl_right_trans_rightUnitPath
#print axioms CGWH.WeakHSpaceData.fundamentalMul_one_left
#print axioms CGWH.WeakHSpaceData.fundamentalMul_one_right
#print axioms CGWH.WeakHSpaceData.rawPathMul_trans
#print axioms CGWH.WeakHSpaceData.rawFundamentalMul_trans
#print axioms CGWH.WeakHSpaceData.rawFundamentalMul_interchange
#print axioms CGWH.WeakHSpaceData.fundamentalMul_interchange
#print axioms CGWH.WeakHSpaceData.fundamentalMul_isUnital
#print axioms CGWH.WeakHSpaceData.fundamentalGroupCommGroup
#print axioms CGWH.WeakHSpaceData.fundamentalGroup_mul_comm

end CGWHWeakHSpaceFundamentalGroupTests
end MathlibExtTest.Topology.Homotopy

end
