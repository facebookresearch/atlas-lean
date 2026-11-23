/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveEquiv
public import Mathlib.CategoryTheory.Conj

/-!
# Fundamental groupoid of a groupoid nerve

For a small groupoid `G`, this file exposes the counit equivalence

`FundamentalGroupoid (nerve G) ≌ G`.

The underlying counit is already determined by
`SSet.fundamentalGroupoidNerveEquiv`; the inverse sends an object to its nerve
vertex and a morphism to the fundamental-groupoid class of the corresponding
nerve edge. The triangle identities follow from the edge generators and the
composition relations of the simplicial fundamental groupoid.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe v u

namespace SSet

variable (G : Type u) [Groupoid.{v} G]

/-- The canonical counit from the fundamental groupoid of a groupoid nerve
back to the groupoid. -/
noncomputable def fundamentalGroupoidNerveCounit :
    SSet.FundamentalGroupoid (CategoryTheory.nerve G) ⥤ G :=
  SSet.FundamentalGroupoid.desc
    (fun x => CategoryTheory.nerveEquiv x)
    (fun e => CategoryTheory.nerve.homEquiv e)
    (fun h => CategoryTheory.nerve.homEquiv_comp h)

@[simp]
theorem fundamentalGroupoidNerveCounit_obj_mk
    (x : (CategoryTheory.nerve G) _⦋0⦌) :
    (fundamentalGroupoidNerveCounit G).obj
        (SSet.FundamentalGroupoid.mk
          (X := CategoryTheory.nerve G) x) =
      CategoryTheory.nerveEquiv x := by
  rfl

@[simp]
theorem fundamentalGroupoidNerveCounit_map_homMk
    {x y : (CategoryTheory.nerve G) _⦋0⦌}
    (e : (CategoryTheory.nerve G).Edge x y) :
    (fundamentalGroupoidNerveCounit G).map
        (SSet.FundamentalGroupoid.homMk
          (X := CategoryTheory.nerve G) e) =
      CategoryTheory.nerve.homEquiv e := by
  exact SSet.FundamentalGroupoid.desc_map_homMk
    (fun x => CategoryTheory.nerveEquiv x)
    (fun e => CategoryTheory.nerve.homEquiv e)
    (fun h => CategoryTheory.nerve.homEquiv_comp h) e

/-- The canonical section sends objects to nerve vertices and morphisms to
the corresponding edge generators. -/
noncomputable def fundamentalGroupoidNerveSection :
    G ⥤ SSet.FundamentalGroupoid (CategoryTheory.nerve G) where
  obj x := SSet.FundamentalGroupoid.mk
    (X := CategoryTheory.nerve G) (CategoryTheory.nerveEquiv.symm x)
  map {x y} f := SSet.FundamentalGroupoid.homMk
    (X := CategoryTheory.nerve G) (CategoryTheory.nerve.edgeMk f)
  map_id x := by
    rw [CategoryTheory.nerve.edgeMk_id]
    exact SSet.FundamentalGroupoid.homMk_id _
  map_comp {x y z} f g := by
    obtain ⟨h⟩ :=
      (CategoryTheory.nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact h.homMk_comp.symm

@[simp]
theorem fundamentalGroupoidNerveSection_obj (x : G) :
    (fundamentalGroupoidNerveSection G).obj x =
      SSet.FundamentalGroupoid.mk
        (X := CategoryTheory.nerve G)
          (CategoryTheory.nerveEquiv.symm x) :=
  rfl

@[simp]
theorem fundamentalGroupoidNerveSection_map {x y : G} (f : x ⟶ y) :
    (fundamentalGroupoidNerveSection G).map f =
      SSet.FundamentalGroupoid.homMk
        (X := CategoryTheory.nerve G)
          (CategoryTheory.nerve.edgeMk f) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroupoidNerveSection_comp_counit
    (G : Type u) [Groupoid.{v} G] :
    fundamentalGroupoidNerveSection G ⋙
        fundamentalGroupoidNerveCounit G =
      𝟭 G := by
  let hObj : ∀ x : G,
      (fundamentalGroupoidNerveSection G ⋙
        fundamentalGroupoidNerveCounit G).obj x = (𝟭 G).obj x :=
    fun x => CategoryTheory.nerveEquiv.apply_symm_apply x
  refine CategoryTheory.Functor.ext hObj ?_
  intro x y f
  change (fundamentalGroupoidNerveCounit G).map
      (SSet.FundamentalGroupoid.homMk
        (CategoryTheory.nerve.edgeMk f)) =
    eqToHom (hObj x) ≫ f ≫ eqToHom (hObj y).symm
  rw [fundamentalGroupoidNerveCounit_map_homMk,
    CategoryTheory.nerve.homEquiv_edgeMk]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroupoidNerveCounit_comp_section
    (G : Type u) [Groupoid.{v} G] :
    fundamentalGroupoidNerveCounit G ⋙
        fundamentalGroupoidNerveSection G =
      𝟭 (SSet.FundamentalGroupoid (CategoryTheory.nerve G)) := by
  let hObj : ∀ x : (CategoryTheory.nerve G) _⦋0⦌,
      (fundamentalGroupoidNerveCounit G ⋙
        fundamentalGroupoidNerveSection G).obj
          (SSet.FundamentalGroupoid.mk
            (X := CategoryTheory.nerve G) x) =
        (𝟭 (SSet.FundamentalGroupoid
          (CategoryTheory.nerve G))).obj
            (SSet.FundamentalGroupoid.mk
              (X := CategoryTheory.nerve G) x) :=
    fun x => by
      change SSet.FundamentalGroupoid.mk
          (X := CategoryTheory.nerve G)
          (CategoryTheory.nerveEquiv.symm
            (CategoryTheory.nerveEquiv x)) =
        SSet.FundamentalGroupoid.mk
          (X := CategoryTheory.nerve G) x
      rw [CategoryTheory.nerveEquiv.symm_apply_apply]
  refine SSet.FundamentalGroupoid.functor_ext hObj ?_
  intro x y e
  obtain ⟨x, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective y
  obtain ⟨f, rfl⟩ := CategoryTheory.nerve.edgeMk_surjective e
  change (fundamentalGroupoidNerveSection G).map
      ((fundamentalGroupoidNerveCounit G).map
        (SSet.FundamentalGroupoid.homMk
          (X := CategoryTheory.nerve G)
          (CategoryTheory.nerve.edgeMk f))) =
    eqToHom (hObj (CategoryTheory.nerveEquiv.symm x)) ≫
      SSet.FundamentalGroupoid.homMk
        (X := CategoryTheory.nerve G)
          (CategoryTheory.nerve.edgeMk f) ≫
        eqToHom (hObj (CategoryTheory.nerveEquiv.symm y)).symm
  rw [fundamentalGroupoidNerveCounit_map_homMk,
    CategoryTheory.nerve.homEquiv_edgeMk,
    fundamentalGroupoidNerveSection_map]
  cat_disch

/-- The fundamental groupoid of a groupoid nerve is canonically equivalent
to the original groupoid. -/
noncomputable def fundamentalGroupoidNerveIsoCat :
    IsoCat
      (SSet.FundamentalGroupoid (CategoryTheory.nerve G)) G where
  functor := fundamentalGroupoidNerveCounit G
  inverse := fundamentalGroupoidNerveSection G
  unit_eq := (fundamentalGroupoidNerveCounit_comp_section G).symm
  counit_eq := fundamentalGroupoidNerveSection_comp_counit G

/-- The nerve counit is an equivalence of categories. -/
theorem fundamentalGroupoidNerveCounit_isEquivalence :
    (fundamentalGroupoidNerveCounit G).IsEquivalence :=
  (fundamentalGroupoidNerveIsoCat G).toEquivalence.isEquivalence_functor

/-- The based endomorphism-group equivalence induced by the nerve counit. -/
noncomputable def fundamentalGroupoidNerveCounit_endMulEquiv (x : G) :
    CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (X := CategoryTheory.nerve G)
          (CategoryTheory.nerveEquiv.symm x)) ≃*
      CategoryTheory.End x :=
  letI : (fundamentalGroupoidNerveCounit G).IsEquivalence :=
    fundamentalGroupoidNerveCounit_isEquivalence G
  ((Functor.FullyFaithful.ofFullyFaithful
      (fundamentalGroupoidNerveCounit G)).mulEquivEnd _).trans
    (eqToIso (CategoryTheory.nerveEquiv.apply_symm_apply x)).conj

@[simp]
theorem fundamentalGroupoidNerveCounit_endMulEquiv_apply
    (x : G)
    (f : CategoryTheory.End
      (SSet.FundamentalGroupoid.mk
        (X := CategoryTheory.nerve G)
        (CategoryTheory.nerveEquiv.symm x))) :
    fundamentalGroupoidNerveCounit_endMulEquiv G x f =
      (eqToIso
        (CategoryTheory.nerveEquiv.apply_symm_apply x)).conj
          ((fundamentalGroupoidNerveCounit G).mapEnd _ f) :=
  rfl

end SSet

end
