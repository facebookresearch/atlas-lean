/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH3Naturality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictDegreeThreeFunctoriality
public import MathlibExt.RepresentationTheory.Rep.ZModRestrictRes

/-!
# Degree-three corestriction and integral scalar restriction

Canonical finite-index `H³` corestriction commutes with restriction of
scalars from `ZMod n` to `ℤ`.  The comparison is proved first on explicit
three-cocycles and then on cohomology through the representative-preserving
scalar-restriction equivalence.  The statements include `n = 0`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] {H : Subgroup G}

/-- A finite enumeration of a finite-index subgroup's chosen right transversal. -/
noncomputable local instance corestrictionH3ZModRestrictTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Scalar restriction commutes with chosen-transversal transfer on
degree-three cocycles. -/
theorem cocycles₃ZModRestrictIntEquiv_corestrictionCocyclesThree
    (n : ℕ) (A : Rep (ZMod n) G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    cocycles₃ZModRestrictIntEquiv n A
        (corestrictionCocyclesThree A T z) =
      corestrictionCocyclesThree (Rep.zmodRestrictInt n A) T
        (mapCocycles₃ (MonoidHom.id H)
          (zmodRestrictIntResIso n (Subgroup.subtype H) A).hom
          (cocycles₃ZModRestrictIntEquiv n
            (Rep.res (Subgroup.subtype H) A) z)) := by
  apply cocycles₃_ext
  intro g h i
  change zmodRestrictIntCoefficientAddEquiv n A
      (corestrictionCochainThree A T z (g, h, i)) =
    corestrictionCochainThree (Rep.zmodRestrictInt n A) T
      (fun p => (zmodRestrictIntResIso n
        (Subgroup.subtype H) A).hom
          (zmodRestrictIntCoefficientAddEquiv n
            (Rep.res (Subgroup.subtype H) A) (z p))) (g, h, i)
  rw [corestrictionCochainThree_apply,
    corestrictionCochainThree_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rfl

/-- Forward scalar restriction commutes with canonical degree-three
corestriction. -/
theorem H3ZModRestrictIntAddEquiv_corestrictionH3
    (n : ℕ) (A : Rep (ZMod n) G) [H.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype H) A)) :
    H3ZModRestrictIntAddEquiv n A (corestrictionH3 A x) =
      corestrictionH3 (Rep.zmodRestrictInt n A)
        (map (MonoidHom.id H)
          (zmodRestrictIntResIso n (Subgroup.subtype H) A).hom 3
          (H3ZModRestrictIntAddEquiv n
            (Rep.res (Subgroup.subtype H) A) x)) := by
  let T : H.RightTransversal := default
  induction x using H3_induction_on with
  | _ z =>
      rw [corestrictionH3_H3π A T,
        H3ZModRestrictIntAddEquiv_H3π,
        H3ZModRestrictIntAddEquiv_H3π,
        H3π_comp_map_apply,
        corestrictionH3_H3π (Rep.zmodRestrictInt n A) T]
      exact congrArg (H3π (Rep.zmodRestrictInt n A))
        (cocycles₃ZModRestrictIntEquiv_corestrictionCocyclesThree
          n A T z)

end groupCohomology
