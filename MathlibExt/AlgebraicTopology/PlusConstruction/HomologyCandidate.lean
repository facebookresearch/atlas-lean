/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.PlusConstruction.WeaklyPointed
public import MathlibExt.AlgebraicTopology.SingularHomology.CGWH

/-!
# Integral-homology plus candidates

This file packages the map-level evidence that is available before an
acyclic-map or plus-construction recognition theorem: surjectivity and a
specified kernel on fundamental groups, together with an isomorphism on
ordinary integral singular homology in every degree.

The word `Candidate` is essential.  Ordinary integral homology does not
detect arbitrary local coefficients, so this structure neither supplies nor
coerces to `IsPlusConstructionAlong`.  In particular, it makes no acyclicity,
plus-recognition, existence, uniqueness, or `Q = +` claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w u

namespace CGWH

/-- A CGWH map is an integral homology equivalence when it induces an
isomorphism on ordinary integral singular homology in every nonnegative
degree. -/
def IsIntegralHomologyEquivalence {X Y : CGWH.{w, u}}
    (f : X ⟶ Y) : Prop :=
  ∀ n : ℕ, IsIso ((CGWH.singularIntegralHomologyFunctor n).map f)

/-- Candidate plus-construction data supported by ordinary integral
homology.  The fundamental-group map uses the selected path from the mapped
source point to the target point.

This is deliberately weaker than `CGWH.IsPlusConstructionAlong`: no
acyclicity of the homotopy fiber is included or inferred. -/
structure IsIntegralHomologyPlusCandidateAlong
    {X Y : CGWH.{w, u}} (f : X ⟶ Y)
    (x : X) (y : Y)
    (p : Path ((CGWH.cgwhToTop.map f) x) y)
    (P : Subgroup
      (FundamentalGroup (CGWH.cgwhToTop.obj X) x))
    [P.Normal] [Group.IsPerfect P] : Prop where
  /-- The selected path-based map on fundamental groups is surjective. -/
  fundamental_surjective :
    Function.Surjective
      (basedFundamentalGroupMap
        (CGWH.cgwhToTop.map f).hom p)
  /-- The selected subgroup is exactly the kernel of the path-based map on
  fundamental groups. -/
  kernel_eq :
    MonoidHom.ker
      (basedFundamentalGroupMap
        (CGWH.cgwhToTop.map f).hom p) = P
  /-- The map is an ordinary integral homology equivalence in every degree. -/
  integralHomology : IsIntegralHomologyEquivalence f

end CGWH

end
