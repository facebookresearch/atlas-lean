/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.PlusConstruction.FundamentalGroup
public import MathlibExt.Topology.Homotopy.LoopComponentsMap

/-!
# Weakly pointed plus-construction data

A map carrying its selected source point to the selected target point only
along a chosen path still induces a based fundamental-group homomorphism.
This file packages plus-construction data using that path and extends the
first-isomorphism comparison to this weakly pointed setting.

Changing the chosen root path does not change the kernel: every root-path
map is the unbased fundamental-group map followed by an injective
change-of-basepoint equivalence.  Consequently equality-pointed and
path-pointed plus data convert in both directions without choosing a
particular equality path.

This file is only a facade for already supplied acyclicity and kernel
evidence.  It constructs no plus target, proves no acyclic-map recognition
theorem, and does not infer acyclicity from ordinary integral homology.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w u

/-- Postcomposing the fundamental-group map with change of basepoint along a
path does not change its kernel. -/
theorem ker_basedFundamentalGroupMap
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) {y : Y} (p : Path (f x) y) :
    MonoidHom.ker (basedFundamentalGroupMap f p) =
      MonoidHom.ker (FundamentalGroup.map f x) := by
  unfold basedFundamentalGroupMap
  exact MonoidHom.ker_comp_of_injective
    (FundamentalGroup.map f x)
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p).injective

/-- The kernel of the equality-pointed fundamental-group map is the kernel
of the underlying unbased map. -/
theorem ker_fundamentalGroup_mapOfEq
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) {y : Y} (hxy : f x = y) :
    MonoidHom.ker (FundamentalGroup.mapOfEq f hxy) =
      MonoidHom.ker (FundamentalGroup.map f x) := by
  unfold FundamentalGroup.mapOfEq
  exact MonoidHom.ker_comp_of_injective
    (FundamentalGroup.map f x)
    (eqToIso (congrArg FundamentalGroupoid.mk hxy)).conj.toMonoidHom
    (eqToIso (congrArg FundamentalGroupoid.mk hxy)).conj.injective

namespace TopCat

/-- Plus-construction data for a map equipped with a path from the mapped
source point to the selected target point. -/
structure IsPlusConstructionAlong {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (p : Path (f x) y)
    (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] : Prop where
  /-- The homotopy fiber over the selected target point is acyclic. -/
  acyclic : IsAcyclicMapAt f y
  /-- The chosen subgroup is the kernel of the path-pointed fundamental
  group map. -/
  kernel_eq :
    MonoidHom.ker (basedFundamentalGroupMap f.hom p) = P

namespace IsPlusConstructionAlong

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {x : X} {y : Y} {p : Path (f x) y}
  {P : Subgroup (FundamentalGroup X x)}
  [P.Normal] [Group.IsPerfect P]

/-- A weakly pointed plus construction has an acyclic homotopy fiber. -/
theorem homotopyFiber_acyclic
    (h : IsPlusConstructionAlong f x y p P) :
    IsAcyclicSpace (TopCat.homotopyFiber f y) :=
  h.acyclic

/-- Recover equality-pointed plus data whenever a literal basepoint equality
is also available.  Kernel independence of the root path is the only
non-definitional step. -/
theorem ofEq (h : IsPlusConstructionAlong f x y p P)
    (hxy : f x = y) : IsPlusConstructionAt f x y hxy P where
  acyclic := h.acyclic
  kernel_eq := by
    rw [ker_fundamentalGroup_mapOfEq f.hom x hxy,
      ← ker_basedFundamentalGroupMap f.hom x p]
    exact h.kernel_eq

/-- A weakly pointed plus-construction target has fundamental group the
source fundamental group modulo the killed subgroup, provided the path-based
map is surjective. -/
noncomputable def fundamentalGroupQuotientMulEquiv
    (h : IsPlusConstructionAlong f x y p P)
    (hsurj : Function.Surjective
      (basedFundamentalGroupMap f.hom p)) :
    FundamentalGroup X x ⧸ P ≃* FundamentalGroup Y y := by
  let phi := basedFundamentalGroupMap f.hom p
  exact (QuotientGroup.quotientMulEquivOfEq h.kernel_eq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective phi hsurj)

/-- The quotient comparison sends a source class to its image under the
path-pointed fundamental-group map. -/
@[simp]
theorem fundamentalGroupQuotientMulEquiv_mk
    (h : IsPlusConstructionAlong f x y p P)
    (hsurj : Function.Surjective
      (basedFundamentalGroupMap f.hom p))
    (q : FundamentalGroup X x) :
    h.fundamentalGroupQuotientMulEquiv hsurj
        (QuotientGroup.mk q) =
      basedFundamentalGroupMap f.hom p q := by
  unfold fundamentalGroupQuotientMulEquiv
  dsimp only [MulEquiv.trans_apply]
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  change QuotientGroup.kerLift
      (basedFundamentalGroupMap f.hom p)
      (QuotientGroup.mk q) = _
  rw [QuotientGroup.kerLift_mk]

/-- Inverse formula for an element represented by a source loop. -/
@[simp]
theorem fundamentalGroupQuotientMulEquiv_symm_map
    (h : IsPlusConstructionAlong f x y p P)
    (hsurj : Function.Surjective
      (basedFundamentalGroupMap f.hom p))
    (q : FundamentalGroup X x) :
    (h.fundamentalGroupQuotientMulEquiv hsurj).symm
        (basedFundamentalGroupMap f.hom p q) =
      QuotientGroup.mk q := by
  apply (h.fundamentalGroupQuotientMulEquiv hsurj).injective
  rw [(h.fundamentalGroupQuotientMulEquiv hsurj).apply_symm_apply,
    fundamentalGroupQuotientMulEquiv_mk]

end IsPlusConstructionAlong

namespace IsPlusConstructionAt

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {x : X} {y : Y} {hxy : f x = y}
  {P : Subgroup (FundamentalGroup X x)}
  [P.Normal] [Group.IsPerfect P]

/-- Equality-pointed plus data gives path-pointed plus data along any chosen
root path with the same endpoints. -/
theorem toAlong (h : IsPlusConstructionAt f x y hxy P)
    (p : Path (f x) y) : IsPlusConstructionAlong f x y p P where
  acyclic := h.acyclic
  kernel_eq := by
    rw [ker_basedFundamentalGroupMap f.hom x p,
      ← ker_fundamentalGroup_mapOfEq f.hom x hxy]
    exact h.kernel_eq

end IsPlusConstructionAt

end TopCat

namespace CGWH

/-- Weakly pointed plus-construction data for a CGWH map, defined through
the underlying topological map. -/
abbrev IsPlusConstructionAlong {X Y : CGWH.{w, u}} (f : X ⟶ Y)
    (x : X) (y : Y)
    (p : Path ((cgwhToTop.map f) x) y)
    (P : Subgroup (FundamentalGroup (cgwhToTop.obj X) x))
    [P.Normal] [Group.IsPerfect P] : Prop :=
  TopCat.IsPlusConstructionAlong (cgwhToTop.map f) x y p P

/-- Forgetting CGWH structure does not change weakly pointed plus data. -/
theorem isPlusConstructionAlong_iff_toTop
    {X Y : CGWH.{w, u}} (f : X ⟶ Y)
    (x : X) (y : Y)
    (p : Path ((cgwhToTop.map f) x) y)
    (P : Subgroup (FundamentalGroup (cgwhToTop.obj X) x))
    [P.Normal] [Group.IsPerfect P] :
    IsPlusConstructionAlong f x y p P ↔
      TopCat.IsPlusConstructionAlong
        (cgwhToTop.map f) x y p P :=
  Iff.rfl

namespace IsPlusConstructionAlong

variable {X Y : CGWH.{w, u}} {f : X ⟶ Y}
  {x : X} {y : Y}
  {p : Path ((cgwhToTop.map f) x) y}
  {P : Subgroup (FundamentalGroup (cgwhToTop.obj X) x)}
  [P.Normal] [Group.IsPerfect P]

/-- Recover equality-pointed CGWH plus data from weakly pointed data. -/
theorem ofEq (h : CGWH.IsPlusConstructionAlong f x y p P)
    (hxy : f x = y) : CGWH.IsPlusConstructionAt f x y hxy P :=
  TopCat.IsPlusConstructionAlong.ofEq h hxy

/-- Fundamental-group quotient comparison for weakly pointed CGWH plus
data. -/
noncomputable def fundamentalGroupQuotientMulEquiv
    (h : CGWH.IsPlusConstructionAlong f x y p P)
    (hsurj : Function.Surjective
      (basedFundamentalGroupMap (cgwhToTop.map f).hom p)) :
    FundamentalGroup (cgwhToTop.obj X) x ⧸ P ≃*
      FundamentalGroup (cgwhToTop.obj Y) y :=
  TopCat.IsPlusConstructionAlong.fundamentalGroupQuotientMulEquiv h hsurj

@[simp]
theorem fundamentalGroupQuotientMulEquiv_mk
    (h : CGWH.IsPlusConstructionAlong f x y p P)
    (hsurj : Function.Surjective
      (basedFundamentalGroupMap (cgwhToTop.map f).hom p))
    (q : FundamentalGroup (cgwhToTop.obj X) x) :
    h.fundamentalGroupQuotientMulEquiv hsurj
        (QuotientGroup.mk q) =
      basedFundamentalGroupMap (cgwhToTop.map f).hom p q :=
  TopCat.IsPlusConstructionAlong.fundamentalGroupQuotientMulEquiv_mk
    h hsurj q

@[simp]
theorem fundamentalGroupQuotientMulEquiv_symm_map
    (h : CGWH.IsPlusConstructionAlong f x y p P)
    (hsurj : Function.Surjective
      (basedFundamentalGroupMap (cgwhToTop.map f).hom p))
    (q : FundamentalGroup (cgwhToTop.obj X) x) :
    (h.fundamentalGroupQuotientMulEquiv hsurj).symm
        (basedFundamentalGroupMap (cgwhToTop.map f).hom p q) =
      QuotientGroup.mk q :=
  TopCat.IsPlusConstructionAlong.fundamentalGroupQuotientMulEquiv_symm_map
    h hsurj q

end IsPlusConstructionAlong

namespace IsPlusConstructionAt

variable {X Y : CGWH.{w, u}} {f : X ⟶ Y}
  {x : X} {y : Y} {hxy : f x = y}
  {P : Subgroup (FundamentalGroup (cgwhToTop.obj X) x)}
  [P.Normal] [Group.IsPerfect P]

/-- Equality-pointed CGWH plus data gives weakly pointed data along any root
path with the same endpoints. -/
theorem toAlong (h : CGWH.IsPlusConstructionAt f x y hxy P)
    (p : Path ((cgwhToTop.map f) x) y) :
    CGWH.IsPlusConstructionAlong f x y p P :=
  TopCat.IsPlusConstructionAt.toAlong h p

end IsPlusConstructionAt

end CGWH

end
