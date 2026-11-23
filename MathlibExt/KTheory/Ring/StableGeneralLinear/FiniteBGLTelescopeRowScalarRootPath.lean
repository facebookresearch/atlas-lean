/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeRowScalarZeroRoot
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct

/-!
# Actual path homotopy of the original telescope scalar roots

The categorical zero-root square supplies a genuine nerve composition triangle.
Its standard realization gives a homotopy, with endpoints fixed, from the original
source root path to the component edge followed by the original target root path.
No fundamental-group equality substitutes for this path-homotopy data.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory

universe uR uS

namespace AlgebraicKTheory.StableGL

/-- The original source root path is homotopic to the actual scalar component
edge followed by the original target root path, with both endpoints fixed. -/
public theorem finiteBGLTelescopeRowScalarZeroIso_original_root_path (R : Type uR) (S : Type uS)
    [Ring R] [Ring S] (f : R →+* S) :
    (TopCat.pathEquiv (SSet.realizedEdgePath
      (CategoryTheory.nerve.edgeMk (finiteBGLTelescopeScalarSourceRootZeroIso f).hom))).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk
          ((finiteBGLTelescopeRowScalarZeroIso f).app (finiteBGLTelescopeBaseObject R)).hom))).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (CategoryTheory.nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom)))) := by
  have h :
      ((finiteBGLTelescopeRowScalarZeroIso f).app (finiteBGLTelescopeBaseObject R)).hom ≫
          (finiteBGLTelescopeScalarTargetRootZeroIso f).hom =
        (finiteBGLTelescopeScalarSourceRootZeroIso f).hom :=
    congrArg Iso.hom (finiteBGLTelescopeRowScalarZeroIso_original_root f)
  have hTriangle := (CategoryTheory.nerve.nonempty_compStruct_iff
    ((finiteBGLTelescopeRowScalarZeroIso f).app (finiteBGLTelescopeBaseObject R)).hom
    (finiteBGLTelescopeScalarTargetRootZeroIso f).hom
    (finiteBGLTelescopeScalarSourceRootZeroIso f).hom).2 h
  exact SSet.realizedCompStructHomotopic hTriangle.some

end AlgebraicKTheory.StableGL
