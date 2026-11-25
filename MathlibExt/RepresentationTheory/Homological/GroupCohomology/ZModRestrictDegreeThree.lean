/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua
-/
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThree
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictLowDegree

/-!
# Degree-three group cohomology under `ZMod n` scalar restriction

Explicit degree-three cochains, cocycles, and coboundaries are unchanged
when a `ZMod n` representation is restricted to an integral
representation.  The resulting H3 comparison is packaged additively and,
after transporting the module structure, `ZMod n`-linearly.

The construction includes `n = 0`.  No continuous or etale comparison is
asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G]

/-- Identity-on-values equivalence of explicit degree-three cochains. -/
noncomputable abbrev cochains₃ZModRestrictIntEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    (G × G × G → A) ≃+ (G × G × G → Rep.zmodRestrictInt n A) where
  toFun f p := zmodRestrictIntCoefficientAddEquiv n A (f p)
  invFun f p := (zmodRestrictIntCoefficientAddEquiv n A).symm (f p)
  left_inv f := by
    funext p
    exact (zmodRestrictIntCoefficientAddEquiv n A).symm_apply_apply (f p)
  right_inv f := by
    funext p
    exact (zmodRestrictIntCoefficientAddEquiv n A).apply_symm_apply (f p)
  map_add' f g := by funext p; exact map_add _ _ _

@[simp]
theorem cochains₃ZModRestrictIntEquiv_apply
    (n : ℕ) (A : Rep (ZMod n) G)
    (f : G × G × G → A) (p : G × G × G) :
    cochains₃ZModRestrictIntEquiv n A f p = f p :=
  rfl

/-- Explicit degree-three cocycles are unchanged by scalar restriction. -/
noncomputable abbrev cocycles₃ZModRestrictIntEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    cocycles₃ A ≃+ cocycles₃ (Rep.zmodRestrictInt n A) where
  toFun z := ⟨fun p => zmodRestrictIntCoefficientAddEquiv n A (z p), by
    rw [mem_cocycles₃_def]
    intro g h i j
    simpa only [map_add, map_sub, map_zero,
      zmodRestrictIntCoefficientAddEquiv_action] using congrArg
        (zmodRestrictIntCoefficientAddEquiv n A)
        ((mem_cocycles₃_def z).mp z.property g h i j)⟩
  invFun z := ⟨fun p =>
      (zmodRestrictIntCoefficientAddEquiv n A).symm (z p), by
    rw [mem_cocycles₃_def]
    intro g h i j
    simpa only [map_add, map_sub, map_zero,
      zmodRestrictIntCoefficientAddEquiv_symm_action] using congrArg
        (zmodRestrictIntCoefficientAddEquiv n A).symm
        ((mem_cocycles₃_def z).mp z.property g h i j)⟩
  left_inv z := by
    apply cocycles₃_ext
    intro g h i
    change (zmodRestrictIntCoefficientAddEquiv n A).symm
      (zmodRestrictIntCoefficientAddEquiv n A (z (g, h, i))) = z (g, h, i)
    exact (zmodRestrictIntCoefficientAddEquiv n A).symm_apply_apply _
  right_inv z := by
    apply cocycles₃_ext
    intro g h i
    change zmodRestrictIntCoefficientAddEquiv n A
      ((zmodRestrictIntCoefficientAddEquiv n A).symm (z (g, h, i))) = z (g, h, i)
    exact (zmodRestrictIntCoefficientAddEquiv n A).apply_symm_apply _
  map_add' x y := by
    apply cocycles₃_ext
    intro g h i
    change zmodRestrictIntCoefficientAddEquiv n A
        (x (g, h, i) + y (g, h, i)) = _
    exact map_add (zmodRestrictIntCoefficientAddEquiv n A) _ _

@[simp]
theorem cocycles₃ZModRestrictIntEquiv_apply
    (n : ℕ) (A : Rep (ZMod n) G) (z : cocycles₃ A)
    (g h i : G) :
    cocycles₃ZModRestrictIntEquiv n A z (g, h, i) = z (g, h, i) :=
  zmodRestrictIntCoefficientAddEquiv_apply n A _

@[simp]
theorem cocycles₃ZModRestrictIntEquiv_symm_apply
    (n : ℕ) (A : Rep (ZMod n) G)
    (z : cocycles₃ (Rep.zmodRestrictInt n A)) (g h i : G) :
    (cocycles₃ZModRestrictIntEquiv n A).symm z (g, h, i) = z (g, h, i) :=
  zmodRestrictIntCoefficientAddEquiv_symm_apply n A _

/-- Degree-three coboundary membership is unchanged by scalar restriction. -/
theorem mem_coboundaries₃_zmodRestrictInt_iff
    (n : ℕ) (A : Rep (ZMod n) G) (f : G × G × G → A) :
    f ∈ coboundaries₃ A ↔
      cochains₃ZModRestrictIntEquiv n A f ∈
        coboundaries₃ (Rep.zmodRestrictInt n A) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun p => zmodRestrictIntCoefficientAddEquiv n A (x p), ?_⟩
    funext p
    have hxp := congrFun hx p
    change A.ρ p.1 (x (p.2.1, p.2.2)) -
        x (p.1 * p.2.1, p.2.2) + x (p.1, p.2.1 * p.2.2) -
        x (p.1, p.2.1) = f p at hxp
    change (Rep.zmodRestrictInt n A).ρ p.1
          (zmodRestrictIntCoefficientAddEquiv n A (x (p.2.1, p.2.2))) -
        zmodRestrictIntCoefficientAddEquiv n A (x (p.1 * p.2.1, p.2.2)) +
        zmodRestrictIntCoefficientAddEquiv n A (x (p.1, p.2.1 * p.2.2)) -
        zmodRestrictIntCoefficientAddEquiv n A (x (p.1, p.2.1)) =
      zmodRestrictIntCoefficientAddEquiv n A (f p)
    rw [← zmodRestrictIntCoefficientAddEquiv_action,
      ← map_sub, ← map_add, ← map_sub, hxp]
  · rintro ⟨x, hx⟩
    refine ⟨fun p => (zmodRestrictIntCoefficientAddEquiv n A).symm (x p), ?_⟩
    funext p
    have hxp := congrFun hx p
    change (Rep.zmodRestrictInt n A).ρ p.1 (x (p.2.1, p.2.2)) -
        x (p.1 * p.2.1, p.2.2) + x (p.1, p.2.1 * p.2.2) -
        x (p.1, p.2.1) =
      zmodRestrictIntCoefficientAddEquiv n A (f p) at hxp
    change A.ρ p.1
          ((zmodRestrictIntCoefficientAddEquiv n A).symm
            (x (p.2.1, p.2.2))) -
        (zmodRestrictIntCoefficientAddEquiv n A).symm
          (x (p.1 * p.2.1, p.2.2)) +
        (zmodRestrictIntCoefficientAddEquiv n A).symm
          (x (p.1, p.2.1 * p.2.2)) -
        (zmodRestrictIntCoefficientAddEquiv n A).symm
          (x (p.1, p.2.1)) = f p
    rw [← zmodRestrictIntCoefficientAddEquiv_symm_action,
      ← map_sub, ← map_add, ← map_sub, hxp]
    exact (zmodRestrictIntCoefficientAddEquiv n A).symm_apply_apply (f p)

/-- Explicit degree-three coboundaries are additively equivalent after
scalar restriction. -/
noncomputable abbrev coboundaries₃ZModRestrictIntEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    coboundaries₃ A ≃+ coboundaries₃ (Rep.zmodRestrictInt n A) where
  toFun b := ⟨fun p => zmodRestrictIntCoefficientAddEquiv n A (b p),
    (mem_coboundaries₃_zmodRestrictInt_iff n A b).mp b.property⟩
  invFun b := ⟨fun p =>
      (zmodRestrictIntCoefficientAddEquiv n A).symm (b p), by
    let f : G × G × G → A := fun p =>
      (zmodRestrictIntCoefficientAddEquiv n A).symm (b p)
    change f ∈ coboundaries₃ A
    apply (mem_coboundaries₃_zmodRestrictInt_iff n A f).mpr
    have heq : cochains₃ZModRestrictIntEquiv n A f = (b : G × G × G → _) := by
      funext p
      exact (zmodRestrictIntCoefficientAddEquiv n A).apply_symm_apply _
    rw [heq]
    exact b.property⟩
  left_inv b := by
    apply coboundaries₃_ext
    intro g h i
    exact (zmodRestrictIntCoefficientAddEquiv n A).symm_apply_apply _
  right_inv b := by
    apply coboundaries₃_ext
    intro g h i
    exact (zmodRestrictIntCoefficientAddEquiv n A).apply_symm_apply _
  map_add' x y := by
    apply coboundaries₃_ext
    intro g h i
    change zmodRestrictIntCoefficientAddEquiv n A
        (x (g, h, i) + y (g, h, i)) = _
    exact map_add (zmodRestrictIntCoefficientAddEquiv n A) _ _

/-! ## Degree-three cohomology -/

/-- Chosen degree-three cocycle representative. -/
noncomputable def H3Representative {k : Type} [CommRing k]
    (A : Rep k G) (x : H3 A) : cocycles₃ A :=
  Function.surjInv
    ((ModuleCat.epi_iff_surjective (H3π A)).mp inferInstance) x

@[simp]
theorem H3Representative_spec {k : Type} [CommRing k]
    (A : Rep k G) (x : H3 A) :
    H3π A (H3Representative A x) = x :=
  Function.rightInverse_surjInv
    ((ModuleCat.epi_iff_surjective (H3π A)).mp inferInstance) x

/-- Underlying degree-three scalar-restriction comparison. -/
noncomputable def H3ZModRestrictIntToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H3 A → H3 (Rep.zmodRestrictInt n A) := fun x =>
  H3π (Rep.zmodRestrictInt n A)
    (cocycles₃ZModRestrictIntEquiv n A (H3Representative A x))

/-- Computation of the degree-three comparison on a presented class. -/
theorem H3ZModRestrictIntToFun_H3π
    (n : ℕ) (A : Rep (ZMod n) G) (z : cocycles₃ A) :
    H3ZModRestrictIntToFun n A (H3π A z) =
      H3π (Rep.zmodRestrictInt n A)
        (cocycles₃ZModRestrictIntEquiv n A z) := by
  unfold H3ZModRestrictIntToFun
  apply (H3π_eq_iff _ _).mpr
  have hsource :
      ((H3Representative A (H3π A z) : G × G × G → A) - z) ∈
        coboundaries₃ A :=
    (H3π_eq_iff _ _).mp (H3Representative_spec A (H3π A z))
  have htarget := (mem_coboundaries₃_zmodRestrictInt_iff n A
    ((H3Representative A (H3π A z) : G × G × G → A) - z)).mp hsource
  have heq : cochains₃ZModRestrictIntEquiv n A
      ((H3Representative A (H3π A z) : G × G × G → A) - z) =
    (fun p => zmodRestrictIntCoefficientAddEquiv n A
      (H3Representative A (H3π A z) p) -
      zmodRestrictIntCoefficientAddEquiv n A (z p)) := by
    funext p
    exact map_sub (zmodRestrictIntCoefficientAddEquiv n A) _ _
  rw [heq] at htarget
  exact htarget

/-- Additive degree-three scalar-restriction comparison. -/
noncomputable def H3ZModRestrictIntAddHom
    (n : ℕ) (A : Rep (ZMod n) G) :
    H3 A →+ H3 (Rep.zmodRestrictInt n A) where
  toFun := H3ZModRestrictIntToFun n A
  map_zero' := by
    simpa only [map_zero] using
      H3ZModRestrictIntToFun_H3π n A (0 : cocycles₃ A)
  map_add' x y := by
    induction x using H3_induction_on with
    | _ zx =>
      induction y using H3_induction_on with
      | _ zy =>
        rw [← map_add, H3ZModRestrictIntToFun_H3π,
          map_add, H3ZModRestrictIntToFun_H3π,
          H3ZModRestrictIntToFun_H3π, map_add]

/-- Underlying inverse degree-three comparison. -/
noncomputable def H3ZModRestrictIntInvToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H3 (Rep.zmodRestrictInt n A) → H3 A := fun x =>
  H3π A ((cocycles₃ZModRestrictIntEquiv n A).symm
    (H3Representative (Rep.zmodRestrictInt n A) x))

/-- Computation of the inverse comparison on a presented class. -/
theorem H3ZModRestrictIntInvToFun_H3π
    (n : ℕ) (A : Rep (ZMod n) G)
    (z : cocycles₃ (Rep.zmodRestrictInt n A)) :
    H3ZModRestrictIntInvToFun n A
        (H3π (Rep.zmodRestrictInt n A) z) =
      H3π A ((cocycles₃ZModRestrictIntEquiv n A).symm z) := by
  unfold H3ZModRestrictIntInvToFun
  apply (H3π_eq_iff _ _).mpr
  have hsource :
      ((H3Representative (Rep.zmodRestrictInt n A)
          (H3π (Rep.zmodRestrictInt n A) z) :
            G × G × G → Rep.zmodRestrictInt n A) - z) ∈
        coboundaries₃ (Rep.zmodRestrictInt n A) :=
    (H3π_eq_iff _ _).mp
      (H3Representative_spec (Rep.zmodRestrictInt n A)
        (H3π (Rep.zmodRestrictInt n A) z))
  let f : G × G × G → A := fun p =>
    (zmodRestrictIntCoefficientAddEquiv n A).symm
      (H3Representative (Rep.zmodRestrictInt n A)
        (H3π (Rep.zmodRestrictInt n A) z) p) -
    (zmodRestrictIntCoefficientAddEquiv n A).symm (z p)
  change f ∈ coboundaries₃ A
  apply (mem_coboundaries₃_zmodRestrictInt_iff n A f).mpr
  change (fun p => zmodRestrictIntCoefficientAddEquiv n A (f p)) ∈
    coboundaries₃ (Rep.zmodRestrictInt n A)
  have heq : (fun p => zmodRestrictIntCoefficientAddEquiv n A (f p)) =
      ((H3Representative (Rep.zmodRestrictInt n A)
          (H3π (Rep.zmodRestrictInt n A) z) :
            G × G × G → Rep.zmodRestrictInt n A) - z) := by
    funext p
    dsimp only [f]
    rw [map_sub]
    change zmodRestrictIntCoefficientAddEquiv n A
          ((zmodRestrictIntCoefficientAddEquiv n A).symm
            (H3Representative (Rep.zmodRestrictInt n A)
              (H3π (Rep.zmodRestrictInt n A) z) p)) -
        zmodRestrictIntCoefficientAddEquiv n A
          ((zmodRestrictIntCoefficientAddEquiv n A).symm (z p)) = _
    rw [(zmodRestrictIntCoefficientAddEquiv n A).apply_symm_apply,
      (zmodRestrictIntCoefficientAddEquiv n A).apply_symm_apply]
    rfl
  rw [heq]
  exact hsource

/-- Additive inverse degree-three comparison. -/
noncomputable def H3ZModRestrictIntInvAddHom
    (n : ℕ) (A : Rep (ZMod n) G) :
    H3 (Rep.zmodRestrictInt n A) →+ H3 A where
  toFun := H3ZModRestrictIntInvToFun n A
  map_zero' := by
    simpa only [map_zero] using H3ZModRestrictIntInvToFun_H3π n A
      (0 : cocycles₃ (Rep.zmodRestrictInt n A))
  map_add' x y := by
    induction x using H3_induction_on with
    | _ zx =>
      induction y using H3_induction_on with
      | _ zy =>
        rw [← map_add, H3ZModRestrictIntInvToFun_H3π,
          map_add, H3ZModRestrictIntInvToFun_H3π,
          H3ZModRestrictIntInvToFun_H3π, map_add]

/-- Additive equivalence on degree-three group cohomology. -/
noncomputable def H3ZModRestrictIntAddEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    H3 A ≃+ H3 (Rep.zmodRestrictInt n A) where
  __ := H3ZModRestrictIntAddHom n A
  invFun := H3ZModRestrictIntInvAddHom n A
  left_inv x := by
    induction x using H3_induction_on with
    | _ z =>
      change H3ZModRestrictIntInvToFun n A
        (H3ZModRestrictIntToFun n A (H3π A z)) = H3π A z
      rw [H3ZModRestrictIntToFun_H3π,
        H3ZModRestrictIntInvToFun_H3π]
      congr 1
  right_inv x := by
    induction x using H3_induction_on with
    | _ z =>
      change H3ZModRestrictIntToFun n A
        (H3ZModRestrictIntInvToFun n A
          (H3π (Rep.zmodRestrictInt n A) z)) =
        H3π (Rep.zmodRestrictInt n A) z
      rw [H3ZModRestrictIntInvToFun_H3π,
        H3ZModRestrictIntToFun_H3π]
      congr 1

@[simp]
theorem H3ZModRestrictIntAddEquiv_H3π
    (n : ℕ) (A : Rep (ZMod n) G) (z : cocycles₃ A) :
    H3ZModRestrictIntAddEquiv n A (H3π A z) =
      H3π (Rep.zmodRestrictInt n A)
        (cocycles₃ZModRestrictIntEquiv n A z) :=
  H3ZModRestrictIntToFun_H3π n A z

/-- Canonical `ZMod n`-module structure on restricted integral H3. -/
@[instance_reducible]
noncomputable def H3ZModRestrictIntModule
    (n : ℕ) (A : Rep (ZMod n) G) :
    Module (ZMod n) (H3 (Rep.zmodRestrictInt n A)) :=
  (H3ZModRestrictIntAddEquiv n A).symm.module (ZMod n)

/-- `ZMod n`-linear degree-three scalar-restriction equivalence. -/
noncomputable def H3ZModRestrictIntLinearEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    let _ : Module (ZMod n) (H3 (Rep.zmodRestrictInt n A)) :=
      H3ZModRestrictIntModule n A
    H3 A ≃ₗ[ZMod n] H3 (Rep.zmodRestrictInt n A) := by
  let _ : Module (ZMod n) (H3 (Rep.zmodRestrictInt n A)) :=
    H3ZModRestrictIntModule n A
  exact ((H3ZModRestrictIntAddEquiv n A).symm.linearEquiv (ZMod n)).symm

@[simp]
theorem H3ZModRestrictIntLinearEquiv_apply
    (n : ℕ) (A : Rep (ZMod n) G) (x : H3 A) :
    H3ZModRestrictIntLinearEquiv n A x =
      H3ZModRestrictIntAddEquiv n A x :=
  rfl

end groupCohomology
