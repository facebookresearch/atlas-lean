/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid
public import Mathlib.CategoryTheory.Conj

/-!
# Singular fundamental-groupoid paths and based endomorphisms

The fully faithful singular fundamental-groupoid comparison identifies the
endomorphism monoid at a canonical singular vertex with the ordinary based
endomorphism monoid.  The object equality is transported explicitly by
conjugation with `eqToIso`.

An ordinary path also determines a canonical morphism in the singular
fundamental groupoid.  This construction preserves reflexivity,
source-first path composition, and maps of topological spaces.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace TopCat

/-- The fully faithful singular comparison identifies based endomorphisms.
The target object is aligned by the proved object formula and an explicit
`eqToIso` conjugation. -/
noncomputable def singularFundamentalGroupoidEndMulEquiv
    (X : TopCat.{u}) (x : X) :
    CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (TopCat.toSSetObj₀Equiv.symm x)) ≃*
      CategoryTheory.End (_root_.FundamentalGroupoid.mk x) := by
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let F := TopCat.singularFundamentalGroupoidFunctor X
  let A := SSet.FundamentalGroupoid.mk sx
  let hObj : F.obj A = _root_.FundamentalGroupoid.mk x :=
    (TopCat.singularFundamentalGroupoidFunctor_obj_mk X sx).trans
      (congrArg _root_.FundamentalGroupoid.mk
        ((TopCat.toSSetObj₀Equiv (X := X)).apply_symm_apply x))
  exact
    ((TopCat.singularFundamentalGroupoidFunctor_fullyFaithful X).mulEquivEnd A).trans
      (CategoryTheory.Iso.conj (eqToIso hObj))

/-- On a singular edge, the based endomorphism equivalence is represented by
the corresponding ordinary path. -/
@[simp]
theorem singularFundamentalGroupoidEndMulEquiv_homMk
    (X : TopCat.{u}) (x : X)
    (e : (TopCat.toSSet.obj X).Edge
      (TopCat.toSSetObj₀Equiv.symm x)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    singularFundamentalGroupoidEndMulEquiv X x
        (End.of (SSet.FundamentalGroupoid.homMk e)) =
      End.of (Path.Homotopic.Quotient.mk
        (TopCat.pathEquiv
          ((TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)) e))) := by
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let F := TopCat.singularFundamentalGroupoidFunctor X
  let A := SSet.FundamentalGroupoid.mk sx
  let hObj : F.obj A = _root_.FundamentalGroupoid.mk x :=
    (TopCat.singularFundamentalGroupoidFunctor_obj_mk X sx).trans
      (congrArg _root_.FundamentalGroupoid.mk
        ((TopCat.toSSetObj₀Equiv (X := X)).apply_symm_apply x))
  let p := TopCat.pathEquiv
    ((TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)) e)
  let q := Path.Homotopic.Quotient.mk p
  apply End.ext
  change ((eqToIso hObj).conj
      (F.mapEnd A (End.of (SSet.FundamentalGroupoid.homMk e)))).asHom = q
  rw [CategoryTheory.Iso.conj_apply_asHom]
  symm
  apply (CategoryTheory.conj_eqToHom_iff_heq
    q (F.map (SSet.FundamentalGroupoid.homMk e))
    hObj.symm hObj.symm).2
  have hp (t) : TopCat.pathEquiv (TopCat.singularEdgePath e) t = p t := by
    dsimp only [p]
    exact congrArg
      (fun r : X.Path x x => TopCat.pathEquiv r t)
      (TopCat.singularEdgePath_of_canonical (x := x) (y := x) e)
  have hMap :=
    TopCat.singularFundamentalGroupoidFunctor_map_homMk X e
  rw [Path.Homotopic.Quotient.mk_cast] at hMap
  have hCast := Path.Homotopic.Quotient.cast_heq
    (TopCat.counit_realizedVertex sx)
    (TopCat.counit_realizedVertex sx)
    (γ := Path.Homotopic.Quotient.mk
      (TopCat.pathEquiv (TopCat.singularEdgePath e)))
  exact ((heq_of_eq hMap).trans
    (hCast.trans (_root_.Path.Homotopic.hpath_hext hp))).symm

/-- The canonical morphism in the singular fundamental groupoid represented
by an ordinary path. -/
noncomputable def singularPathHom
    (X : TopCat.{u}) {x y : X} (p : _root_.Path x y) :
    SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x) ⟶
      SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) :=
  SSet.FundamentalGroupoid.homMk
    ((TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := y)).symm
      ((TopCat.pathEquiv (X := X) (x := x) (y := y)).symm p))

private theorem singularFundamentalGroupoidFunctor_map_singularPathHom_heq
    (X : TopCat.{u}) {x y : X} (p : _root_.Path x y) :
    (TopCat.singularFundamentalGroupoidFunctor X).map
        (singularPathHom X p) ≍
      Path.Homotopic.Quotient.mk p := by
  let e := (TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := y)).symm
    ((TopCat.pathEquiv (X := X) (x := x) (y := y)).symm p)
  have hp (t) : TopCat.pathEquiv (TopCat.singularEdgePath e) t = p t := by
    have he :
        (TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := y)) e =
          (TopCat.pathEquiv (X := X) (x := x) (y := y)).symm p :=
      (TopCat.toSSetObjEdgeEquiv (X := X)
        (x := x) (y := y)).apply_symm_apply _
    have hpCat : TopCat.singularEdgePath e =
        (TopCat.pathEquiv (X := X) (x := x) (y := y)).symm p :=
      (TopCat.singularEdgePath_of_canonical (x := x) (y := y) e).trans he
    calc
      TopCat.pathEquiv (TopCat.singularEdgePath e) t =
          TopCat.pathEquiv
            ((TopCat.pathEquiv (X := X) (x := x) (y := y)).symm p) t :=
        congrArg (fun r : X.Path x y => TopCat.pathEquiv r t) hpCat
      _ = p t := congrArg (fun r : _root_.Path x y => r t)
        ((TopCat.pathEquiv (X := X)
          (x := x) (y := y)).apply_symm_apply p)
  have hMap :=
    TopCat.singularFundamentalGroupoidFunctor_map_homMk X e
  rw [Path.Homotopic.Quotient.mk_cast] at hMap
  have hCast := Path.Homotopic.Quotient.cast_heq
    (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x))
    (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm y))
    (γ := Path.Homotopic.Quotient.mk
      (TopCat.pathEquiv (TopCat.singularEdgePath e)))
  exact (heq_of_eq hMap).trans
    (hCast.trans (_root_.Path.Homotopic.hpath_hext hp))

/-- The reflexive path represents the identity singular morphism. -/
@[simp]
theorem singularPathHom_refl (X : TopCat.{u}) (x : X) :
    singularPathHom X (_root_.Path.refl x) = 𝟙 _ := by
  apply (End.homEquiv (X := SSet.FundamentalGroupoid.mk
    (TopCat.toSSetObj₀Equiv.symm x))).symm.injective
  apply (singularFundamentalGroupoidEndMulEquiv X x).injective
  change singularFundamentalGroupoidEndMulEquiv X x
      (End.of (singularPathHom X (_root_.Path.refl x))) =
    singularFundamentalGroupoidEndMulEquiv X x 1
  rw [singularPathHom,
    singularFundamentalGroupoidEndMulEquiv_homMk,
    (TopCat.toSSetObjEdgeEquiv (X := X)
      (x := x) (y := x)).apply_symm_apply,
    (TopCat.pathEquiv (X := X)
      (x := x) (y := x)).apply_symm_apply,
    Path.Homotopic.Quotient.mk_refl]
  exact (singularFundamentalGroupoidEndMulEquiv X x).map_one.symm

/-- Singular path morphisms preserve source-first path composition. -/
@[simp]
theorem singularPathHom_trans
    (X : TopCat.{u}) {x y z : X}
    (p : _root_.Path x y) (q : _root_.Path y z) :
    singularPathHom X (p.trans q) =
      singularPathHom X p ≫ singularPathHom X q := by
  apply (TopCat.singularFundamentalGroupoidFunctor_fullyFaithful X).map_injective
  rw [Functor.map_comp]
  apply eq_of_heq
  have hLeft :=
    singularFundamentalGroupoidFunctor_map_singularPathHom_heq
      X (p.trans q)
  have hp :=
    singularFundamentalGroupoidFunctor_map_singularPathHom_heq X p
  have hq :=
    singularFundamentalGroupoidFunctor_map_singularPathHom_heq X q
  have hComp :
      (TopCat.singularFundamentalGroupoidFunctor X).map
          (singularPathHom X p) ≫
        (TopCat.singularFundamentalGroupoidFunctor X).map
          (singularPathHom X q) ≍
      Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk p)
        (Path.Homotopic.Quotient.mk q) := by
    let F := TopCat.singularFundamentalGroupoidFunctor X
    let hX : F.obj (SSet.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv.symm x)) =
        _root_.FundamentalGroupoid.mk x :=
      (TopCat.singularFundamentalGroupoidFunctor_obj_mk X
        (TopCat.toSSetObj₀Equiv.symm x)).trans
        (congrArg _root_.FundamentalGroupoid.mk
          ((TopCat.toSSetObj₀Equiv (X := X)).apply_symm_apply x))
    let hY : F.obj (SSet.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv.symm y)) =
        _root_.FundamentalGroupoid.mk y :=
      (TopCat.singularFundamentalGroupoidFunctor_obj_mk X
        (TopCat.toSSetObj₀Equiv.symm y)).trans
        (congrArg _root_.FundamentalGroupoid.mk
          ((TopCat.toSSetObj₀Equiv (X := X)).apply_symm_apply y))
    let hZ : F.obj (SSet.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv.symm z)) =
        _root_.FundamentalGroupoid.mk z :=
      (TopCat.singularFundamentalGroupoidFunctor_obj_mk X
        (TopCat.toSSetObj₀Equiv.symm z)).trans
        (congrArg _root_.FundamentalGroupoid.mk
          ((TopCat.toSSetObj₀Equiv (X := X)).apply_symm_apply z))
    exact CategoryTheory.heq_comp hX hY hZ hp hq
  exact hLeft.trans
    ((heq_of_eq (Path.Homotopic.Quotient.mk_trans p q)).trans hComp.symm)

/-- Singular path morphisms are natural under maps of topological spaces. -/
theorem singularPathHom_map
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {x y : X} (p : _root_.Path x y) :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).map
        (singularPathHom X p) =
      singularPathHom Y (p.map f.hom.continuous) := by
  rw [singularPathHom, singularPathHom,
    SSet.mapFundamentalGroupoid_map_homMk]
  congr 1

end TopCat
