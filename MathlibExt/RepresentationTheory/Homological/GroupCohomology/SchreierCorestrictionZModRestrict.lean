/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH1
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictFunctoriality
public import MathlibExt.RepresentationTheory.Rep.ZModRestrictRes

/-!
# Corestriction and restriction of `ZMod` scalars

Restriction of the acting group commutes with restriction of coefficient
scalars from `ZMod n` to `ℤ`.  In degree one, this comparison also
commutes with canonical finite-index corestriction.

The statements include `n = 0`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] {H : Subgroup G}


/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance corestrictionH1ZModRestrictTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Scalar restriction commutes with chosen-transversal transfer on
degree-one cocycles. -/
theorem cocycles₁ZModRestrictIntEquiv_corestrictionCocyclesOne
    (n : ℕ) (A : Rep (ZMod n) G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₁ (Rep.res (Subgroup.subtype H) A)) :
    cocycles₁ZModRestrictIntEquiv n A
        (corestrictionCocyclesOne A T z) =
      corestrictionCocyclesOne (Rep.zmodRestrictInt n A) T
        (mapCocycles₁ (MonoidHom.id H)
          (zmodRestrictIntResIso n (Subgroup.subtype H) A).hom
          (cocycles₁ZModRestrictIntEquiv n
            (Rep.res (Subgroup.subtype H) A) z)) := by
  apply cocycles₁_ext
  intro g
  change zmodRestrictIntCoefficientAddEquiv n A
      (corestrictionCochainOne A T z g) =
    corestrictionCochainOne (Rep.zmodRestrictInt n A) T
      (fun h => (zmodRestrictIntResIso n
        (Subgroup.subtype H) A).hom
          (zmodRestrictIntCoefficientAddEquiv n
            (Rep.res (Subgroup.subtype H) A) (z h))) g
  rw [corestrictionCochainOne_apply,
    corestrictionCochainOne_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rfl

/-- Forward scalar restriction commutes with canonical degree-one
corestriction. -/
theorem H1ZModRestrictIntAddEquiv_corestrictionH1
    (n : ℕ) (A : Rep (ZMod n) G) [H.FiniteIndex]
    (x : H1 (Rep.res (Subgroup.subtype H) A)) :
    H1ZModRestrictIntAddEquiv n A (corestrictionH1 A x) =
      corestrictionH1 (Rep.zmodRestrictInt n A)
        (map (MonoidHom.id H)
          (zmodRestrictIntResIso n (Subgroup.subtype H) A).hom 1
          (H1ZModRestrictIntAddEquiv n
            (Rep.res (Subgroup.subtype H) A) x)) := by
  let T : H.RightTransversal := default
  induction x using H1_induction_on with
  | _ z =>
      rw [corestrictionH1_H1π A T,
        H1ZModRestrictIntAddEquiv_H1π,
        H1ZModRestrictIntAddEquiv_H1π,
        H1π_comp_map_apply,
        corestrictionH1_H1π (Rep.zmodRestrictInt n A) T]
      exact congrArg (H1π (Rep.zmodRestrictInt n A))
        (cocycles₁ZModRestrictIntEquiv_corestrictionCocyclesOne
          n A T z)

end groupCohomology
