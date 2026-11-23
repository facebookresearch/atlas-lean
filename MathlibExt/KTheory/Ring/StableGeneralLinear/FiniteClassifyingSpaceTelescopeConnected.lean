/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceTelescope
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization

/-!
# Connectedness of the finite-`BGL` telescope

The zeroth-stage object maps to every object of the finite-`BGL` categorical
telescope: use the unique inequality `0 ≤ n` in the indexing category and an
identity transport in the one-object target fiber.  The resulting nerve edge
shows that every vertex lies in the component of the selected base vertex.

Consequently the ordinary realization of the telescope nerve, and hence the
canonical CGWH realization, are path-connected.  This is only the
connectedness input for the group-completion comparison; no homology or plus
property is claimed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe w u

namespace AlgebraicKTheory
namespace StableGL

/-- Canonical morphism from the selected zeroth-stage object to any object of
the finite-`BGL` categorical telescope. -/
noncomputable def finiteBGLTelescopeBaseTo
    (R : Type u) [Semiring R]
    (X : FiniteBGLTelescopeCategory R) :
    finiteBGLTelescopeBaseObject R ⟶ X where
  base := homOfLE (Nat.zero_le X.base)
  fiber := eqToHom (@Quiver.SingleObj.ext
    (Matrix.GeneralLinearGroup (Fin X.base) R)ᵐᵒᵖ _ _)

@[simp]
theorem finiteBGLTelescopeBaseTo_base
    (R : Type u) [Semiring R]
    (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeBaseTo R X).base =
      homOfLE (Nat.zero_le X.base) :=
  rfl

/-- The nerve of the finite-`BGL` categorical telescope. -/
noncomputable abbrev finiteBGLTelescopeNerve
    (R : Type u) [Semiring R] : SSet.{u} :=
  CategoryTheory.nerve (FiniteBGLTelescopeCategory R)

/-- Nerve vertex represented by a telescope object. -/
noncomputable def finiteBGLTelescopeVertex
    (R : Type u) [Semiring R]
    (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeNerve R).obj (op ⦋0⦌) :=
  CategoryTheory.nerveEquiv.symm X

/-- The selected zeroth-stage vertex of the telescope nerve. -/
noncomputable def finiteBGLTelescopeBaseVertex
    (R : Type u) [Semiring R] :
    (finiteBGLTelescopeNerve R).obj (op ⦋0⦌) :=
  finiteBGLTelescopeVertex R (finiteBGLTelescopeBaseObject R)

/-- Nerve edge from the selected base vertex to the vertex represented by a
telescope object. -/
noncomputable def finiteBGLTelescopeBaseEdge
    (R : Type u) [Semiring R]
    (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeNerve R).Edge
      (finiteBGLTelescopeBaseVertex R)
      (finiteBGLTelescopeVertex R X) :=
  CategoryTheory.nerve.edgeMk (finiteBGLTelescopeBaseTo R X)

/-- Canonical base edge with an arbitrary telescope-nerve vertex as its
literal target. -/
noncomputable def finiteBGLTelescopeBaseEdgeToVertex
    (R : Type u) [Semiring R]
    (x : (finiteBGLTelescopeNerve R).obj (op ⦋0⦌)) :
    (finiteBGLTelescopeNerve R).Edge
      (finiteBGLTelescopeBaseVertex R) x :=
  SSet.Edge.ofEq
    (finiteBGLTelescopeBaseEdge R
      (CategoryTheory.nerveEquiv x))
    rfl
    (CategoryTheory.nerveEquiv.left_inv x)

/-- The arbitrary-target base edge as a fundamental-groupoid morphism. -/
noncomputable def finiteBGLTelescopeBaseHomToVertex
    (R : Type u) [Semiring R]
    (x : (finiteBGLTelescopeNerve R).obj (op ⦋0⦌)) :
    SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeBaseVertex R) ⟶
      SSet.FundamentalGroupoid.mk x :=
  SSet.FundamentalGroupoid.homMk
    (finiteBGLTelescopeBaseEdgeToVertex R x)

/-- The arbitrary-target base path as an isomorphism in the fundamental
groupoid. -/
noncomputable def finiteBGLTelescopeBaseIsoToVertex
    (R : Type u) [Semiring R]
    (x : (finiteBGLTelescopeNerve R).obj (op ⦋0⦌)) :
    SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeBaseVertex R) ≅
      SSet.FundamentalGroupoid.mk x :=
  asIso (finiteBGLTelescopeBaseHomToVertex R x)

/-- The nerve of the finite-`BGL` telescope is connected. -/
theorem finiteBGLTelescopeNerve_isConnected
    (R : Type u) [Semiring R] :
    (finiteBGLTelescopeNerve R).IsConnected := by
  have key : ∀ v : (finiteBGLTelescopeNerve R).obj (op ⦋0⦌),
      SSet.π₀.mk (finiteBGLTelescopeBaseVertex R) =
        SSet.π₀.mk v := by
    intro v
    let X : FiniteBGLTelescopeCategory R :=
      CategoryTheory.nerveEquiv v
    have hv : finiteBGLTelescopeVertex R X = v :=
      CategoryTheory.nerveEquiv.left_inv v
    have e : (finiteBGLTelescopeNerve R).Edge
        (finiteBGLTelescopeBaseVertex R) v :=
      SSet.Edge.ofEq (finiteBGLTelescopeBaseEdge R X) rfl hv
    exact SSet.π₀.sound e
  rw [SSet.isConnected_iff]
  constructor
  · refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective b
    exact (key x).symm.trans (key y)
  · exact ⟨finiteBGLTelescopeBaseVertex R⟩

/-- Ordinary realization of the finite-`BGL` telescope nerve. -/
noncomputable abbrev ordinaryFiniteBGLTelescope
    (R : Type u) [Semiring R] : TopCat.{u} :=
  SSet.toTop.obj (finiteBGLTelescopeNerve R)

/-- The ordinary realization of the finite-`BGL` telescope is
path-connected. -/
theorem ordinaryFiniteBGLTelescope_pathConnectedSpace
    (R : Type u) [Semiring R] :
    PathConnectedSpace ↑(ordinaryFiniteBGLTelescope R) := by
  let _ : (finiteBGLTelescopeNerve R).IsConnected :=
    finiteBGLTelescopeNerve_isConnected R
  exact SSet.pathConnectedSpace_realization_of_isConnected
    (finiteBGLTelescopeNerve R)

/-- Forgetting the native CGWH telescope realization recovers its ordinary
realization. -/
noncomputable def finiteBGLTelescopeToOrdinaryTopIso
    (R : Type u) [Semiring R] :
    CGWH.cgwhToTop.obj (finiteBGLTelescope.{w} R) ≅
      ordinaryFiniteBGLTelescope R :=
  CategoryTheory.classifyingSpaceCGWHToTopIso.{w, u, 0}.app
    (Cat.of (FiniteBGLTelescopeCategory R))

/-- The canonical CGWH finite-`BGL` telescope is path-connected. -/
theorem finiteBGLTelescope_pathConnectedSpace
    (R : Type u) [Semiring R] :
    PathConnectedSpace ↑(finiteBGLTelescope.{w} R) := by
  let hOrd : PathConnectedSpace
      ↑(ordinaryFiniteBGLTelescope R) :=
    ordinaryFiniteBGLTelescope_pathConnectedSpace R
  exact @Homeomorph.pathConnectedSpace _ _ _ _ hOrd
    (TopCat.homeoOfIso
      (finiteBGLTelescopeToOrdinaryTopIso.{w} R))

end StableGL
end AlgebraicKTheory

end
