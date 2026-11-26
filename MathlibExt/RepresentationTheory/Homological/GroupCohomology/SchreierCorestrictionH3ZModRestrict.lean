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
# Integral scalar restriction and degree-three corestriction

Let `G : Type` be a group, `H ≤ G` a finite-index subgroup, `n : ℕ`, and `A : Rep (ZMod n) G`.
Write `J(A) = Rep.zmodRestrictInt n A` for restriction of scalars along `ℤ → ZMod n`. The
additive equivalences on three-cocycles and degree-three cohomology commute with finite-index
transfer.

The coefficient isomorphism `θ : J(Res A) ≅ Res(J(A))` is inserted on the subgroup side. Thus
`E_A(cor_A³ x) = cor_{J(A)}³(θ_* E_{Res A}(x))`. These statements hold for every `n`,
including `n = 0`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] {H : Subgroup G}

/-- For a group `G : Type`, a finite-index subgroup `H ≤ G`, and a right transversal `T` for `H`,
the subtype of representatives `(T : Set G)` has a finite enumeration. This local `Fintype`
instance enumerates that finite set for the degree-three transfer sum. -/
noncomputable local instance corestrictionH3ZModRestrictTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Let `G : Type` be a group, `H ≤ G` finite index, `n : ℕ`, `A : Rep (ZMod n) G`, and `T` a
right transversal. Write `J(A) = Rep.zmodRestrictInt n A`, `E_A =
cocycles₃ZModRestrictIntEquiv n A`, and `θ = (zmodRestrictIntResIso n (Subgroup.subtype H)
A).hom`. For `z ∈ Z³(H,Res A)`, `E_A(corestrictionCocyclesThree A T z) =
corestrictionCocyclesThree (J(A)) T (mapCocycles₃ (id H) θ (E_{Res A} z))`. The scalar
restriction is along `ℤ → ZMod n` and includes `n = 0`. -/
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

/-- Let `G : Type` be a group, `H ≤ G` finite index, `n : ℕ`, and `A : Rep (ZMod n) G`. Put `J(A)
= Rep.zmodRestrictInt n A`, `E_A = H3ZModRestrictIntAddEquiv n A`, and `θ =
(zmodRestrictIntResIso n (Subgroup.subtype H) A).hom : J(Res A) → Res(J(A))`. For `x ∈
H³(H,Res A)`, `E_A(corestrictionH3 A x) = corestrictionH3 (J(A)) (map (id H) θ 3 (E_{Res A}
x))`. The identity holds for all `n`, including zero. -/
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
