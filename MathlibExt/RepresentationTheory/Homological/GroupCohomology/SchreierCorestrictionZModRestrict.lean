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
# Integral scalar restriction and degree-one corestriction

Let `G : Type` be a group, `H ≤ G` a finite-index subgroup, `n : ℕ`, and `A : Rep (ZMod n) G`.
Restricting coefficient scalars along `ℤ → ZMod n` commutes with the right-transversal
transfer of one-cocycles and with the induced canonical map `H¹(H,Res A) → H¹(G,A)`.

The subgroup coefficient comparison is `J(Res A) ≅ Res(J(A))`, where `J(A) =
Rep.zmodRestrictInt n A`. The scalar-restriction additive equivalences preserve this transfer
square for every `n`, including `n = 0`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G] {H : Subgroup G}


/-- For a group `G : Type`, a finite-index subgroup `H ≤ G`, and a right transversal `T`, the
subtype `(T : Set G)` of representatives has a finite enumeration. This local `Fintype`
instance enumerates the finite set used in the degree-one transfer sum. -/
noncomputable local instance corestrictionH1ZModRestrictTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Let `G : Type` be a group, `H ≤ G` finite index, `n : ℕ`, `A : Rep (ZMod n) G`, and `T` a
right transversal. Put `J(A) = Rep.zmodRestrictInt n A`, `E_A = cocycles₁ZModRestrictIntEquiv
n A`, and `θ = (zmodRestrictIntResIso n (Subgroup.subtype H) A).hom`. For `z ∈ Z¹(H,Res A)`,
`E_A(corestrictionCocyclesOne A T z) = corestrictionCocyclesOne (J(A)) T (mapCocycles₁ (id H)
θ (E_{Res A} z))`. The scalar restriction is along `ℤ → ZMod n` for every `n`, including zero. -/
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

/-- Let `G : Type` be a group, `H ≤ G` finite index, `n : ℕ`, and `A : Rep (ZMod n) G`. Put `J(A)
= Rep.zmodRestrictInt n A`, `E_A = H1ZModRestrictIntAddEquiv n A`, and `θ =
(zmodRestrictIntResIso n (Subgroup.subtype H) A).hom : J(Res A) → Res(J(A))`. For `x ∈
H¹(H,Res A)`, `E_A(corestrictionH1 A x) = corestrictionH1 (J(A)) (map (id H) θ 1 (E_{Res A}
x))`. This identity includes `n = 0`. -/
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
