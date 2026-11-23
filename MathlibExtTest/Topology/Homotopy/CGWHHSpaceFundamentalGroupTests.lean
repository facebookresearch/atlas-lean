/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.CGWHHSpaceFundamentalGroup

/-! # Tests for native CGWH H-space fundamental groups -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits unitInterval

universe u v

namespace MathlibExtTest.Topology.Homotopy
namespace CGWHHSpaceFundamentalGroupTests

section Generic

variable {X Y Z : CGWH.{u, v}}
variable (H : X.HSpaceData)

#check CGWH.prodPointEquiv
#check CGWH.prodPoint
#check CGWH.prod_lift_apply
#check CGWH.HSpaceData
#check CGWH.HSpaceData.ofStrict
#check CGWH.HSpaceData.pathPair
#check CGWH.HSpaceData.pathMul
#check CGWH.HSpaceData.pathMulHomotopy
#check CGWH.HSpaceData.fundamentalMul
#check CGWH.HSpaceData.fundamentalMul_interchange
#check CGWH.HSpaceData.fundamentalGroupCommGroup
#check CGWH.HSpaceData.fundamentalGroup_mul_comm

example (x : X) (y : Y) :
    CGWH.prodComparisonToTop X Y (CGWH.prodPoint X Y x y) = (x, y) :=
  CGWH.prodComparisonToTop_prodPoint X Y x y

example (f : Z ⟶ X) (g : Z ⟶ Y) (z : Z) :
    Limits.prod.lift f g z = CGWH.prodPoint X Y (f z) (g z) :=
  CGWH.prod_lift_apply f g z

example (p q : Path H.e H.e) (t : unitInterval) :
    H.pathPair p q (ULift.up t) =
      CGWH.prodPoint X X (p t) (q t) :=
  H.pathPair_apply p q t

example (p q : Path H.e H.e) (t : unitInterval) :
    H.pathMul p q t = H.mul (CGWH.prodPoint X X (p t) (q t)) :=
  H.pathMul_apply p q t

example {p₀ p₁ q₀ q₁ : Path H.e H.e}
    (P : Path.Homotopy p₀ p₁) (Q : Path.Homotopy q₀ q₁)
    (st : unitInterval × unitInterval) :
    H.pathHomotopyPair P Q (ULift.up st) =
      CGWH.prodPoint X X (P st) (Q st) :=
  H.pathHomotopyPair_apply P Q st

example (a b c d : FundamentalGroup X H.e) :
    H.fundamentalMul (a * b) (c * d) =
      H.fundamentalMul a c * H.fundamentalMul b d :=
  H.fundamentalMul_interchange a b c d

example (p q : FundamentalGroup X H.e) : p * q = q * p :=
  H.fundamentalGroup_mul_comm p q

noncomputable example : CommGroup (FundamentalGroup X H.e) :=
  H.fundamentalGroupCommGroup

/- The named structure is not installed globally, avoiding a typeclass
diamond with the existing fundamental-group `Group`. -/
example : True := by
  fail_if_success
    let _ := inferInstanceAs (CommGroup (FundamentalGroup X H.e))
  trivial

end Generic

section StrictPoint

abbrev Point : CGWH.{0, 0} := CGWH.of PUnit

noncomputable def pointMul : Point ⨯ Point ⟶ Point :=
  Limits.prod.fst

noncomputable def pointHSpaceData : Point.HSpaceData :=
  CGWH.HSpaceData.ofStrict pointMul PUnit.unit
    (by exact Subsingleton.elim _ _)
    (by
      apply ConcreteCategory.hom_ext
      intro x
      exact Subsingleton.elim _ _)
    (by
      apply ConcreteCategory.hom_ext
      intro x
      exact Subsingleton.elim _ _)

example : pointHSpaceData.mul = pointMul :=
  rfl

example : pointHSpaceData.e = PUnit.unit :=
  rfl

example (p q : FundamentalGroup Point pointHSpaceData.e) : p * q = q * p :=
  pointHSpaceData.fundamentalGroup_mul_comm p q

noncomputable example :
    CommGroup (FundamentalGroup Point pointHSpaceData.e) :=
  pointHSpaceData.fundamentalGroupCommGroup

end StrictPoint

#print axioms CGWH.prodPointEquiv
#print axioms CGWH.prodPoint
#print axioms CGWH.prodPointEquiv_apply
#print axioms CGWH.prodComparisonToTop_prodPoint
#print axioms CGWH.prodPoint_fst
#print axioms CGWH.prodPoint_snd
#print axioms CGWH.prod_lift_apply
#print axioms CGWH.constMap
#print axioms CGWH.constMap_apply
#print axioms CGWH.hspaceLeftUnitMap
#print axioms CGWH.hspaceRightUnitMap
#print axioms CGWH.hspaceLeftUnitMap_apply
#print axioms CGWH.hspaceRightUnitMap_apply
#print axioms CGWH.HSpaceData
#print axioms CGWH.HSpaceData.ofStrict
#print axioms CGWH.HSpaceData.liftedUnitInterval
#print axioms CGWH.HSpaceData.liftedUnitSquare
#print axioms CGWH.HSpaceData.pathHom
#print axioms CGWH.HSpaceData.pathPair
#print axioms CGWH.HSpaceData.pathPair_apply
#print axioms CGWH.HSpaceData.pathMul
#print axioms CGWH.HSpaceData.pathMul_apply
#print axioms CGWH.HSpaceData.pathHomotopyHom
#print axioms CGWH.HSpaceData.pathHomotopyPair
#print axioms CGWH.HSpaceData.pathHomotopyPair_apply
#print axioms CGWH.HSpaceData.pathMulHomotopy
#print axioms CGWH.HSpaceData.fundamentalMul
#print axioms CGWH.HSpaceData.fundamentalMul_mk
#print axioms CGWH.HSpaceData.pathMulReflLeftHomotopy
#print axioms CGWH.HSpaceData.pathMulReflRightHomotopy
#print axioms CGWH.HSpaceData.fundamentalMul_one_left
#print axioms CGWH.HSpaceData.fundamentalMul_one_right
#print axioms CGWH.HSpaceData.pathMul_trans
#print axioms CGWH.HSpaceData.fundamentalMul_trans
#print axioms CGWH.HSpaceData.fundamentalMul_interchange
#print axioms CGWH.HSpaceData.fundamentalMul_isUnital
#print axioms CGWH.HSpaceData.fundamentalGroupCommGroup
#print axioms CGWH.HSpaceData.fundamentalGroup_mul_comm

end CGWHHSpaceFundamentalGroupTests
end MathlibExtTest.Topology.Homotopy

end
