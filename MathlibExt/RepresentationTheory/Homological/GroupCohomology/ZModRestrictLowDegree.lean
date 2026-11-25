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

public import MathlibExt.RepresentationTheory.Rep.ZModRestrict
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Low-degree group cohomology under `ZMod n` scalar restriction

For a `ZMod n` representation, the inhomogeneous cocycle and coboundary
conditions in degrees one and two are unchanged after restricting the
coefficient representation to `ℤ`.  This file uses the explicit low-degree
quotient APIs to identify the resulting `H¹` and `H²` additively, with
representative formulas.

The construction includes `n = 0`.  No continuous or etale comparison is
asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G]

/-- Identity-on-values additive equivalence between a `ZMod n`
representation carrier and its integral scalar restriction. -/
noncomputable def zmodRestrictIntCoefficientAddEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    A ≃+ Rep.zmodRestrictInt n A where
  toFun x := by
    change A
    exact x
  invFun x := by
    change A at x
    exact x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem zmodRestrictIntCoefficientAddEquiv_apply
    (n : ℕ) (A : Rep (ZMod n) G) (x : A) :
    zmodRestrictIntCoefficientAddEquiv n A x = x :=
  rfl

@[simp]
theorem zmodRestrictIntCoefficientAddEquiv_symm_apply
    (n : ℕ) (A : Rep (ZMod n) G)
    (x : Rep.zmodRestrictInt n A) :
    (zmodRestrictIntCoefficientAddEquiv n A).symm x = x :=
  rfl

@[simp]
theorem zmodRestrictIntCoefficientAddEquiv_action
    (n : ℕ) (A : Rep (ZMod n) G) (g : G) (x : A) :
    zmodRestrictIntCoefficientAddEquiv n A (A.ρ g x) =
      (Rep.zmodRestrictInt n A).ρ g
        (zmodRestrictIntCoefficientAddEquiv n A x) :=
  rfl

@[simp]
theorem zmodRestrictIntCoefficientAddEquiv_symm_action
    (n : ℕ) (A : Rep (ZMod n) G) (g : G)
    (x : Rep.zmodRestrictInt n A) :
    (zmodRestrictIntCoefficientAddEquiv n A).symm
        ((Rep.zmodRestrictInt n A).ρ g x) =
      A.ρ g ((zmodRestrictIntCoefficientAddEquiv n A).symm x) :=
  rfl

/-- Degree-one cocycles are unchanged by scalar restriction. -/
noncomputable def cocycles₁ZModRestrictIntEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    cocycles₁ A ≃+ cocycles₁ (Rep.zmodRestrictInt n A) where
  toFun z := ⟨fun g => zmodRestrictIntCoefficientAddEquiv n A (z g), by
    rw [mem_cocycles₁_iff]
    intro g h
    simpa only [map_add, zmodRestrictIntCoefficientAddEquiv_action] using congrArg
      (zmodRestrictIntCoefficientAddEquiv n A)
      ((mem_cocycles₁_iff z).mp z.property g h)⟩
  invFun z := ⟨fun g =>
      (zmodRestrictIntCoefficientAddEquiv n A).symm (z g), by
    rw [mem_cocycles₁_iff]
    intro g h
    simpa only [map_add, zmodRestrictIntCoefficientAddEquiv_symm_action] using congrArg
      (zmodRestrictIntCoefficientAddEquiv n A).symm
      ((mem_cocycles₁_iff z).mp z.property g h)⟩
  left_inv z := by
    apply cocycles₁_ext
    intro g
    change (zmodRestrictIntCoefficientAddEquiv n A).symm
      (zmodRestrictIntCoefficientAddEquiv n A (z g)) = z g
    exact (zmodRestrictIntCoefficientAddEquiv n A).symm_apply_apply (z g)
  right_inv z := by
    apply cocycles₁_ext
    intro g
    change zmodRestrictIntCoefficientAddEquiv n A
      ((zmodRestrictIntCoefficientAddEquiv n A).symm (z g)) = z g
    exact (zmodRestrictIntCoefficientAddEquiv n A).apply_symm_apply (z g)
  map_add' x y := by
    apply cocycles₁_ext
    intro g
    change zmodRestrictIntCoefficientAddEquiv n A ((x + y) g) =
      zmodRestrictIntCoefficientAddEquiv n A (x g) +
        zmodRestrictIntCoefficientAddEquiv n A (y g)
    exact map_add (zmodRestrictIntCoefficientAddEquiv n A) (x g) (y g)

@[simp]
theorem cocycles₁ZModRestrictIntEquiv_apply
    (n : ℕ) (A : Rep (ZMod n) G) (z : cocycles₁ A) (g : G) :
    cocycles₁ZModRestrictIntEquiv n A z g = z g :=
  by rfl

@[simp]
theorem cocycles₁ZModRestrictIntEquiv_symm_apply
    (n : ℕ) (A : Rep (ZMod n) G)
    (z : cocycles₁ (Rep.zmodRestrictInt n A)) (g : G) :
    (cocycles₁ZModRestrictIntEquiv n A).symm z g = z g :=
  by rfl

/-- Degree-two cocycles are unchanged by scalar restriction. -/
noncomputable def cocycles₂ZModRestrictIntEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    cocycles₂ A ≃+ cocycles₂ (Rep.zmodRestrictInt n A) where
  toFun z := ⟨fun gh => zmodRestrictIntCoefficientAddEquiv n A (z gh), by
    rw [mem_cocycles₂_iff]
    intro g h j
    simpa only [map_add, zmodRestrictIntCoefficientAddEquiv_action] using congrArg
      (zmodRestrictIntCoefficientAddEquiv n A)
      ((mem_cocycles₂_iff z).mp z.property g h j)⟩
  invFun z := ⟨fun gh =>
      (zmodRestrictIntCoefficientAddEquiv n A).symm (z gh), by
    rw [mem_cocycles₂_iff]
    intro g h j
    simpa only [map_add, zmodRestrictIntCoefficientAddEquiv_symm_action] using congrArg
      (zmodRestrictIntCoefficientAddEquiv n A).symm
      ((mem_cocycles₂_iff z).mp z.property g h j)⟩
  left_inv z := by
    apply cocycles₂_ext
    intro g h
    change (zmodRestrictIntCoefficientAddEquiv n A).symm
      (zmodRestrictIntCoefficientAddEquiv n A (z (g, h))) = z (g, h)
    exact (zmodRestrictIntCoefficientAddEquiv n A).symm_apply_apply (z (g, h))
  right_inv z := by
    apply cocycles₂_ext
    intro g h
    change zmodRestrictIntCoefficientAddEquiv n A
      ((zmodRestrictIntCoefficientAddEquiv n A).symm (z (g, h))) = z (g, h)
    exact (zmodRestrictIntCoefficientAddEquiv n A).apply_symm_apply (z (g, h))
  map_add' x y := by
    apply cocycles₂_ext
    intro g h
    change zmodRestrictIntCoefficientAddEquiv n A ((x + y) (g, h)) =
      zmodRestrictIntCoefficientAddEquiv n A (x (g, h)) +
        zmodRestrictIntCoefficientAddEquiv n A (y (g, h))
    exact map_add (zmodRestrictIntCoefficientAddEquiv n A) (x (g, h)) (y (g, h))

@[simp]
theorem cocycles₂ZModRestrictIntEquiv_apply
    (n : ℕ) (A : Rep (ZMod n) G) (z : cocycles₂ A) (g h : G) :
    cocycles₂ZModRestrictIntEquiv n A z (g, h) = z (g, h) :=
  by rfl

/-- A degree-one cochain is a coboundary before scalar restriction iff it is
a coboundary afterwards. -/
theorem mem_coboundaries₁_zmodRestrictInt_iff
    (n : ℕ) (A : Rep (ZMod n) G) (f : G → A) :
    f ∈ coboundaries₁ A ↔
      (fun g => zmodRestrictIntCoefficientAddEquiv n A (f g)) ∈
        coboundaries₁ (Rep.zmodRestrictInt n A) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨zmodRestrictIntCoefficientAddEquiv n A x, ?_⟩
    funext g
    have hxg := congrFun hx g
    change A.ρ g x - x = f g at hxg
    change (Rep.zmodRestrictInt n A).ρ g
        (zmodRestrictIntCoefficientAddEquiv n A x) -
      zmodRestrictIntCoefficientAddEquiv n A x =
        zmodRestrictIntCoefficientAddEquiv n A (f g)
    calc
      (Rep.zmodRestrictInt n A).ρ g
            (zmodRestrictIntCoefficientAddEquiv n A x) -
          zmodRestrictIntCoefficientAddEquiv n A x =
        zmodRestrictIntCoefficientAddEquiv n A (A.ρ g x) -
          zmodRestrictIntCoefficientAddEquiv n A x := by
            rw [zmodRestrictIntCoefficientAddEquiv_action]
      _ = zmodRestrictIntCoefficientAddEquiv n A (A.ρ g x - x) :=
        (map_sub (zmodRestrictIntCoefficientAddEquiv n A) _ _).symm
      _ = zmodRestrictIntCoefficientAddEquiv n A (f g) :=
        congrArg (zmodRestrictIntCoefficientAddEquiv n A) hxg
  · rintro ⟨x, hx⟩
    refine ⟨(zmodRestrictIntCoefficientAddEquiv n A).symm x, ?_⟩
    funext g
    have hxg := congrFun hx g
    change (Rep.zmodRestrictInt n A).ρ g x - x =
      zmodRestrictIntCoefficientAddEquiv n A (f g) at hxg
    change A.ρ g ((zmodRestrictIntCoefficientAddEquiv n A).symm x) -
      (zmodRestrictIntCoefficientAddEquiv n A).symm x = f g
    calc
      A.ρ g ((zmodRestrictIntCoefficientAddEquiv n A).symm x) -
          (zmodRestrictIntCoefficientAddEquiv n A).symm x =
        (zmodRestrictIntCoefficientAddEquiv n A).symm
            ((Rep.zmodRestrictInt n A).ρ g x) -
          (zmodRestrictIntCoefficientAddEquiv n A).symm x := by
            rw [zmodRestrictIntCoefficientAddEquiv_symm_action]
      _ = (zmodRestrictIntCoefficientAddEquiv n A).symm
          ((Rep.zmodRestrictInt n A).ρ g x - x) :=
        (map_sub (zmodRestrictIntCoefficientAddEquiv n A).symm _ _).symm
      _ = (zmodRestrictIntCoefficientAddEquiv n A).symm
          (zmodRestrictIntCoefficientAddEquiv n A (f g)) :=
        congrArg (zmodRestrictIntCoefficientAddEquiv n A).symm hxg
      _ = f g :=
        (zmodRestrictIntCoefficientAddEquiv n A).symm_apply_apply (f g)

/-- A degree-two cochain is a coboundary before scalar restriction iff it is
a coboundary afterwards. -/
theorem mem_coboundaries₂_zmodRestrictInt_iff
    (n : ℕ) (A : Rep (ZMod n) G) (f : G × G → A) :
    f ∈ coboundaries₂ A ↔
      (fun gh => zmodRestrictIntCoefficientAddEquiv n A (f gh)) ∈
        coboundaries₂ (Rep.zmodRestrictInt n A) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun g => zmodRestrictIntCoefficientAddEquiv n A (x g), ?_⟩
    funext gh
    have hxgh := congrFun hx gh
    change A.ρ gh.1 (x gh.2) - x (gh.1 * gh.2) + x gh.1 = f gh at hxgh
    change (Rep.zmodRestrictInt n A).ρ gh.1
          (zmodRestrictIntCoefficientAddEquiv n A (x gh.2)) -
        zmodRestrictIntCoefficientAddEquiv n A (x (gh.1 * gh.2)) +
      zmodRestrictIntCoefficientAddEquiv n A (x gh.1) =
        zmodRestrictIntCoefficientAddEquiv n A (f gh)
    calc
      (Rep.zmodRestrictInt n A).ρ gh.1
            (zmodRestrictIntCoefficientAddEquiv n A (x gh.2)) -
          zmodRestrictIntCoefficientAddEquiv n A (x (gh.1 * gh.2)) +
        zmodRestrictIntCoefficientAddEquiv n A (x gh.1) =
        zmodRestrictIntCoefficientAddEquiv n A (A.ρ gh.1 (x gh.2)) -
          zmodRestrictIntCoefficientAddEquiv n A (x (gh.1 * gh.2)) +
            zmodRestrictIntCoefficientAddEquiv n A (x gh.1) := by
              rw [zmodRestrictIntCoefficientAddEquiv_action]
      _ = zmodRestrictIntCoefficientAddEquiv n A
          (A.ρ gh.1 (x gh.2) - x (gh.1 * gh.2) + x gh.1) := by
        rw [map_add, map_sub]
      _ = zmodRestrictIntCoefficientAddEquiv n A (f gh) :=
        congrArg (zmodRestrictIntCoefficientAddEquiv n A) hxgh
  · rintro ⟨x, hx⟩
    refine ⟨fun g =>
      (zmodRestrictIntCoefficientAddEquiv n A).symm (x g), ?_⟩
    funext gh
    have hxgh := congrFun hx gh
    change (Rep.zmodRestrictInt n A).ρ gh.1 (x gh.2) -
      x (gh.1 * gh.2) + x gh.1 =
        zmodRestrictIntCoefficientAddEquiv n A (f gh) at hxgh
    change A.ρ gh.1
          ((zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.2)) -
        (zmodRestrictIntCoefficientAddEquiv n A).symm (x (gh.1 * gh.2)) +
      (zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.1) = f gh
    calc
      A.ρ gh.1
            ((zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.2)) -
          (zmodRestrictIntCoefficientAddEquiv n A).symm (x (gh.1 * gh.2)) +
        (zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.1) =
        (zmodRestrictIntCoefficientAddEquiv n A).symm
            ((Rep.zmodRestrictInt n A).ρ gh.1 (x gh.2)) -
          (zmodRestrictIntCoefficientAddEquiv n A).symm (x (gh.1 * gh.2)) +
            (zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.1) := by
              rw [zmodRestrictIntCoefficientAddEquiv_symm_action]
      _ = (zmodRestrictIntCoefficientAddEquiv n A).symm
          ((Rep.zmodRestrictInt n A).ρ gh.1 (x gh.2) -
            x (gh.1 * gh.2) + x gh.1) := by
        rw [map_add, map_sub]
      _ = (zmodRestrictIntCoefficientAddEquiv n A).symm
          (zmodRestrictIntCoefficientAddEquiv n A (f gh)) :=
        congrArg (zmodRestrictIntCoefficientAddEquiv n A).symm hxgh
      _ = f gh :=
        (zmodRestrictIntCoefficientAddEquiv n A).symm_apply_apply (f gh)

/-! ## Degree-one cohomology -/

/-- A chosen degree-one cocycle representative of a cohomology class. -/
noncomputable def H1Representative {k : Type} [CommRing k]
    (A : Rep k G) (x : H1 A) : cocycles₁ A :=
  Function.surjInv
    ((ModuleCat.epi_iff_surjective (H1π A)).mp inferInstance) x

@[simp]
theorem H1Representative_spec {k : Type} [CommRing k]
    (A : Rep k G) (x : H1 A) :
    H1π A (H1Representative A x) = x :=
  Function.rightInverse_surjInv
    ((ModuleCat.epi_iff_surjective (H1π A)).mp inferInstance) x

/-- Underlying function from `ZMod n`-linear H1 to integral H1 after
coefficient scalar restriction. -/
noncomputable def H1ZModRestrictIntToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H1 A → H1 (Rep.zmodRestrictInt n A) := fun x =>
  H1π (Rep.zmodRestrictInt n A)
    (cocycles₁ZModRestrictIntEquiv n A (H1Representative A x))

/-- Computation of the degree-one comparison on a presented cocycle class. -/
theorem H1ZModRestrictIntToFun_H1π
    (n : ℕ) (A : Rep (ZMod n) G) (z : cocycles₁ A) :
    H1ZModRestrictIntToFun n A (H1π A z) =
      H1π (Rep.zmodRestrictInt n A)
        (cocycles₁ZModRestrictIntEquiv n A z) := by
  unfold H1ZModRestrictIntToFun
  apply (H1π_eq_iff _ _).mpr
  have hsource :
      (⇑(H1Representative A (H1π A z)) - ⇑z) ∈
        coboundaries₁ A :=
    (H1π_eq_iff _ _).mp (H1Representative_spec A (H1π A z))
  have htarget := (mem_coboundaries₁_zmodRestrictInt_iff n A
    (⇑(H1Representative A (H1π A z)) - ⇑z)).mp hsource
  change (fun g => zmodRestrictIntCoefficientAddEquiv n A
      (H1Representative A (H1π A z) g) -
    zmodRestrictIntCoefficientAddEquiv n A (z g)) ∈
      coboundaries₁ (Rep.zmodRestrictInt n A)
  simpa only [Pi.sub_apply, map_sub] using htarget

/-- Additive degree-one comparison from `ZMod n` coefficients to integral
scalar-restricted coefficients. -/
noncomputable def H1ZModRestrictIntAddHom
    (n : ℕ) (A : Rep (ZMod n) G) :
    H1 A →+ H1 (Rep.zmodRestrictInt n A) where
  toFun := H1ZModRestrictIntToFun n A
  map_zero' := by
    simpa using H1ZModRestrictIntToFun_H1π n A (0 : cocycles₁ A)
  map_add' x y := by
    induction x using H1_induction_on with
    | _ zx =>
      induction y using H1_induction_on with
      | _ zy =>
        rw [← map_add, H1ZModRestrictIntToFun_H1π,
          map_add, H1ZModRestrictIntToFun_H1π,
          H1ZModRestrictIntToFun_H1π, map_add]

/-- Underlying inverse degree-one comparison. -/
noncomputable def H1ZModRestrictIntInvToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H1 (Rep.zmodRestrictInt n A) → H1 A := fun x =>
  H1π A ((cocycles₁ZModRestrictIntEquiv n A).symm
    (H1Representative (Rep.zmodRestrictInt n A) x))

/-- Computation of the inverse degree-one comparison on a representative. -/
theorem H1ZModRestrictIntInvToFun_H1π
    (n : ℕ) (A : Rep (ZMod n) G)
    (z : cocycles₁ (Rep.zmodRestrictInt n A)) :
    H1ZModRestrictIntInvToFun n A
        (H1π (Rep.zmodRestrictInt n A) z) =
      H1π A ((cocycles₁ZModRestrictIntEquiv n A).symm z) := by
  unfold H1ZModRestrictIntInvToFun
  apply (H1π_eq_iff _ _).mpr
  have hsource :
      (⇑(H1Representative (Rep.zmodRestrictInt n A)
          (H1π (Rep.zmodRestrictInt n A) z)) - ⇑z) ∈
        coboundaries₁ (Rep.zmodRestrictInt n A) :=
    (H1π_eq_iff _ _).mp
      (H1Representative_spec (Rep.zmodRestrictInt n A)
        (H1π (Rep.zmodRestrictInt n A) z))
  rcases hsource with ⟨x, hx⟩
  refine ⟨(zmodRestrictIntCoefficientAddEquiv n A).symm x, ?_⟩
  funext g
  have hxg := congrFun hx g
  change (Rep.zmodRestrictInt n A).ρ g x - x =
    H1Representative (Rep.zmodRestrictInt n A)
        (H1π (Rep.zmodRestrictInt n A) z) g - z g at hxg
  change A.ρ g ((zmodRestrictIntCoefficientAddEquiv n A).symm x) -
      (zmodRestrictIntCoefficientAddEquiv n A).symm x =
    (zmodRestrictIntCoefficientAddEquiv n A).symm
        (H1Representative (Rep.zmodRestrictInt n A)
          (H1π (Rep.zmodRestrictInt n A) z) g) -
      (zmodRestrictIntCoefficientAddEquiv n A).symm (z g)
  calc
    A.ρ g ((zmodRestrictIntCoefficientAddEquiv n A).symm x) -
        (zmodRestrictIntCoefficientAddEquiv n A).symm x =
      (zmodRestrictIntCoefficientAddEquiv n A).symm
        ((Rep.zmodRestrictInt n A).ρ g x) -
          (zmodRestrictIntCoefficientAddEquiv n A).symm x := by
            rw [zmodRestrictIntCoefficientAddEquiv_symm_action]
    _ = (zmodRestrictIntCoefficientAddEquiv n A).symm
        ((Rep.zmodRestrictInt n A).ρ g x - x) :=
      (map_sub (zmodRestrictIntCoefficientAddEquiv n A).symm _ _).symm
    _ = (zmodRestrictIntCoefficientAddEquiv n A).symm
          (H1Representative (Rep.zmodRestrictInt n A)
            (H1π (Rep.zmodRestrictInt n A) z) g) -
        (zmodRestrictIntCoefficientAddEquiv n A).symm (z g) := by
      rw [hxg, map_sub]

/-- Additive inverse degree-one comparison. -/
noncomputable def H1ZModRestrictIntInvAddHom
    (n : ℕ) (A : Rep (ZMod n) G) :
    H1 (Rep.zmodRestrictInt n A) →+ H1 A where
  toFun := H1ZModRestrictIntInvToFun n A
  map_zero' := by
    simpa using H1ZModRestrictIntInvToFun_H1π n A
      (0 : cocycles₁ (Rep.zmodRestrictInt n A))
  map_add' x y := by
    induction x using H1_induction_on with
    | _ zx =>
      induction y using H1_induction_on with
      | _ zy =>
        rw [← map_add, H1ZModRestrictIntInvToFun_H1π,
          map_add, H1ZModRestrictIntInvToFun_H1π,
          H1ZModRestrictIntInvToFun_H1π, map_add]

/-- Additive equivalence on degree-one group cohomology under scalar
restriction. -/
noncomputable def H1ZModRestrictIntAddEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    H1 A ≃+ H1 (Rep.zmodRestrictInt n A) where
  __ := H1ZModRestrictIntAddHom n A
  invFun := H1ZModRestrictIntInvAddHom n A
  left_inv x := by
    induction x using H1_induction_on with
    | _ z =>
      change H1ZModRestrictIntInvToFun n A
        (H1ZModRestrictIntToFun n A (H1π A z)) = H1π A z
      rw [H1ZModRestrictIntToFun_H1π,
        H1ZModRestrictIntInvToFun_H1π]
      simp
  right_inv x := by
    induction x using H1_induction_on with
    | _ z =>
      change H1ZModRestrictIntToFun n A
        (H1ZModRestrictIntInvToFun n A
          (H1π (Rep.zmodRestrictInt n A) z)) =
        H1π (Rep.zmodRestrictInt n A) z
      rw [H1ZModRestrictIntInvToFun_H1π,
        H1ZModRestrictIntToFun_H1π]
      simp

@[simp]
theorem H1ZModRestrictIntAddEquiv_H1π
    (n : ℕ) (A : Rep (ZMod n) G) (z : cocycles₁ A) :
    H1ZModRestrictIntAddEquiv n A (H1π A z) =
      H1π (Rep.zmodRestrictInt n A)
        (cocycles₁ZModRestrictIntEquiv n A z) :=
  H1ZModRestrictIntToFun_H1π n A z

/-- Canonical `ZMod n`-module structure on integral H1, transported from
the original H1 through the additive comparison. -/
@[instance_reducible]
noncomputable def H1ZModRestrictIntModule
    (n : ℕ) (A : Rep (ZMod n) G) :
    Module (ZMod n) (H1 (Rep.zmodRestrictInt n A)) :=
  (H1ZModRestrictIntAddEquiv n A).symm.module (ZMod n)

/-- `ZMod n`-linear form of the degree-one scalar-restriction comparison. -/
noncomputable def H1ZModRestrictIntLinearEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    let _ : Module (ZMod n) (H1 (Rep.zmodRestrictInt n A)) :=
      H1ZModRestrictIntModule n A
    H1 A ≃ₗ[ZMod n] H1 (Rep.zmodRestrictInt n A) := by
  let _ : Module (ZMod n) (H1 (Rep.zmodRestrictInt n A)) :=
    H1ZModRestrictIntModule n A
  exact ((H1ZModRestrictIntAddEquiv n A).symm.linearEquiv (ZMod n)).symm

@[simp]
theorem H1ZModRestrictIntLinearEquiv_apply
    (n : ℕ) (A : Rep (ZMod n) G) (x : H1 A) :
    H1ZModRestrictIntLinearEquiv n A x =
      H1ZModRestrictIntAddEquiv n A x :=
  rfl

/-! ## Degree-two cohomology -/

/-- A chosen degree-two cocycle representative of a cohomology class. -/
noncomputable def H2Representative {k : Type} [CommRing k]
    (A : Rep k G) (x : H2 A) : cocycles₂ A :=
  Function.surjInv
    ((ModuleCat.epi_iff_surjective (H2π A)).mp inferInstance) x

@[simp]
theorem H2Representative_spec {k : Type} [CommRing k]
    (A : Rep k G) (x : H2 A) :
    H2π A (H2Representative A x) = x :=
  Function.rightInverse_surjInv
    ((ModuleCat.epi_iff_surjective (H2π A)).mp inferInstance) x

/-- Underlying degree-two scalar-restriction comparison. -/
noncomputable def H2ZModRestrictIntToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H2 A → H2 (Rep.zmodRestrictInt n A) := fun x =>
  H2π (Rep.zmodRestrictInt n A)
    (cocycles₂ZModRestrictIntEquiv n A (H2Representative A x))

/-- Computation of the degree-two comparison on a presented cocycle class. -/
theorem H2ZModRestrictIntToFun_H2π
    (n : ℕ) (A : Rep (ZMod n) G) (z : cocycles₂ A) :
    H2ZModRestrictIntToFun n A (H2π A z) =
      H2π (Rep.zmodRestrictInt n A)
        (cocycles₂ZModRestrictIntEquiv n A z) := by
  unfold H2ZModRestrictIntToFun
  apply (H2π_eq_iff _ _).mpr
  have hsource :
      (⇑(H2Representative A (H2π A z)) - ⇑z) ∈
        coboundaries₂ A :=
    (H2π_eq_iff _ _).mp (H2Representative_spec A (H2π A z))
  have htarget := (mem_coboundaries₂_zmodRestrictInt_iff n A
    (⇑(H2Representative A (H2π A z)) - ⇑z)).mp hsource
  change (fun gh => zmodRestrictIntCoefficientAddEquiv n A
      (H2Representative A (H2π A z) gh) -
    zmodRestrictIntCoefficientAddEquiv n A (z gh)) ∈
      coboundaries₂ (Rep.zmodRestrictInt n A)
  simpa only [Pi.sub_apply, map_sub] using htarget

/-- Additive degree-two scalar-restriction comparison. -/
noncomputable def H2ZModRestrictIntAddHom
    (n : ℕ) (A : Rep (ZMod n) G) :
    H2 A →+ H2 (Rep.zmodRestrictInt n A) where
  toFun := H2ZModRestrictIntToFun n A
  map_zero' := by
    simpa using H2ZModRestrictIntToFun_H2π n A (0 : cocycles₂ A)
  map_add' x y := by
    induction x using H2_induction_on with
    | _ zx =>
      induction y using H2_induction_on with
      | _ zy =>
        rw [← map_add, H2ZModRestrictIntToFun_H2π,
          map_add, H2ZModRestrictIntToFun_H2π,
          H2ZModRestrictIntToFun_H2π, map_add]

/-- Underlying inverse degree-two comparison. -/
noncomputable def H2ZModRestrictIntInvToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H2 (Rep.zmodRestrictInt n A) → H2 A := fun x =>
  H2π A ((cocycles₂ZModRestrictIntEquiv n A).symm
    (H2Representative (Rep.zmodRestrictInt n A) x))

/-- Computation of the inverse degree-two comparison on a representative. -/
theorem H2ZModRestrictIntInvToFun_H2π
    (n : ℕ) (A : Rep (ZMod n) G)
    (z : cocycles₂ (Rep.zmodRestrictInt n A)) :
    H2ZModRestrictIntInvToFun n A
        (H2π (Rep.zmodRestrictInt n A) z) =
      H2π A ((cocycles₂ZModRestrictIntEquiv n A).symm z) := by
  unfold H2ZModRestrictIntInvToFun
  apply (H2π_eq_iff _ _).mpr
  have hsource :
      (⇑(H2Representative (Rep.zmodRestrictInt n A)
          (H2π (Rep.zmodRestrictInt n A) z)) - ⇑z) ∈
        coboundaries₂ (Rep.zmodRestrictInt n A) :=
    (H2π_eq_iff _ _).mp
      (H2Representative_spec (Rep.zmodRestrictInt n A)
        (H2π (Rep.zmodRestrictInt n A) z))
  rcases hsource with ⟨x, hx⟩
  refine ⟨fun g =>
    (zmodRestrictIntCoefficientAddEquiv n A).symm (x g), ?_⟩
  funext gh
  have hxgh := congrFun hx gh
  change (Rep.zmodRestrictInt n A).ρ gh.1 (x gh.2) -
      x (gh.1 * gh.2) + x gh.1 =
    H2Representative (Rep.zmodRestrictInt n A)
        (H2π (Rep.zmodRestrictInt n A) z) gh - z gh at hxgh
  change A.ρ gh.1
          ((zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.2)) -
        (zmodRestrictIntCoefficientAddEquiv n A).symm (x (gh.1 * gh.2)) +
      (zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.1) =
    (zmodRestrictIntCoefficientAddEquiv n A).symm
        (H2Representative (Rep.zmodRestrictInt n A)
          (H2π (Rep.zmodRestrictInt n A) z) gh) -
      (zmodRestrictIntCoefficientAddEquiv n A).symm (z gh)
  calc
    A.ρ gh.1 ((zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.2)) -
          (zmodRestrictIntCoefficientAddEquiv n A).symm (x (gh.1 * gh.2)) +
        (zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.1) =
      (zmodRestrictIntCoefficientAddEquiv n A).symm
          ((Rep.zmodRestrictInt n A).ρ gh.1 (x gh.2)) -
        (zmodRestrictIntCoefficientAddEquiv n A).symm (x (gh.1 * gh.2)) +
          (zmodRestrictIntCoefficientAddEquiv n A).symm (x gh.1) := by
            rw [zmodRestrictIntCoefficientAddEquiv_symm_action]
    _ = (zmodRestrictIntCoefficientAddEquiv n A).symm
        ((Rep.zmodRestrictInt n A).ρ gh.1 (x gh.2) -
          x (gh.1 * gh.2) + x gh.1) := by
      rw [map_add, map_sub]
    _ = (zmodRestrictIntCoefficientAddEquiv n A).symm
          (H2Representative (Rep.zmodRestrictInt n A)
            (H2π (Rep.zmodRestrictInt n A) z) gh - z gh) :=
      congrArg (zmodRestrictIntCoefficientAddEquiv n A).symm hxgh
    _ = (zmodRestrictIntCoefficientAddEquiv n A).symm
          (H2Representative (Rep.zmodRestrictInt n A)
            (H2π (Rep.zmodRestrictInt n A) z) gh) -
        (zmodRestrictIntCoefficientAddEquiv n A).symm (z gh) :=
      map_sub (zmodRestrictIntCoefficientAddEquiv n A).symm _ _

/-- Additive inverse degree-two comparison. -/
noncomputable def H2ZModRestrictIntInvAddHom
    (n : ℕ) (A : Rep (ZMod n) G) :
    H2 (Rep.zmodRestrictInt n A) →+ H2 A where
  toFun := H2ZModRestrictIntInvToFun n A
  map_zero' := by
    simpa using H2ZModRestrictIntInvToFun_H2π n A
      (0 : cocycles₂ (Rep.zmodRestrictInt n A))
  map_add' x y := by
    induction x using H2_induction_on with
    | _ zx =>
      induction y using H2_induction_on with
      | _ zy =>
        rw [← map_add, H2ZModRestrictIntInvToFun_H2π,
          map_add, H2ZModRestrictIntInvToFun_H2π,
          H2ZModRestrictIntInvToFun_H2π, map_add]

/-- Additive equivalence on degree-two group cohomology under scalar
restriction. -/
noncomputable def H2ZModRestrictIntAddEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    H2 A ≃+ H2 (Rep.zmodRestrictInt n A) where
  __ := H2ZModRestrictIntAddHom n A
  invFun := H2ZModRestrictIntInvAddHom n A
  left_inv x := by
    induction x using H2_induction_on with
    | _ z =>
      change H2ZModRestrictIntInvToFun n A
        (H2ZModRestrictIntToFun n A (H2π A z)) = H2π A z
      rw [H2ZModRestrictIntToFun_H2π,
        H2ZModRestrictIntInvToFun_H2π]
      simp
  right_inv x := by
    induction x using H2_induction_on with
    | _ z =>
      change H2ZModRestrictIntToFun n A
        (H2ZModRestrictIntInvToFun n A
          (H2π (Rep.zmodRestrictInt n A) z)) =
        H2π (Rep.zmodRestrictInt n A) z
      rw [H2ZModRestrictIntInvToFun_H2π,
        H2ZModRestrictIntToFun_H2π]
      simp

@[simp]
theorem H2ZModRestrictIntAddEquiv_H2π
    (n : ℕ) (A : Rep (ZMod n) G) (z : cocycles₂ A) :
    H2ZModRestrictIntAddEquiv n A (H2π A z) =
      H2π (Rep.zmodRestrictInt n A)
        (cocycles₂ZModRestrictIntEquiv n A z) :=
  H2ZModRestrictIntToFun_H2π n A z

/-- Canonical `ZMod n`-module structure on integral H2, transported from
the original H2 through the additive comparison. -/
@[instance_reducible]
noncomputable def H2ZModRestrictIntModule
    (n : ℕ) (A : Rep (ZMod n) G) :
    Module (ZMod n) (H2 (Rep.zmodRestrictInt n A)) :=
  (H2ZModRestrictIntAddEquiv n A).symm.module (ZMod n)

/-- `ZMod n`-linear form of the degree-two scalar-restriction comparison. -/
noncomputable def H2ZModRestrictIntLinearEquiv
    (n : ℕ) (A : Rep (ZMod n) G) :
    let _ : Module (ZMod n) (H2 (Rep.zmodRestrictInt n A)) :=
      H2ZModRestrictIntModule n A
    H2 A ≃ₗ[ZMod n] H2 (Rep.zmodRestrictInt n A) := by
  let _ : Module (ZMod n) (H2 (Rep.zmodRestrictInt n A)) :=
    H2ZModRestrictIntModule n A
  exact ((H2ZModRestrictIntAddEquiv n A).symm.linearEquiv (ZMod n)).symm

@[simp]
theorem H2ZModRestrictIntLinearEquiv_apply
    (n : ℕ) (A : Rep (ZMod n) G) (x : H2 A) :
    H2ZModRestrictIntLinearEquiv n A x =
      H2ZModRestrictIntAddEquiv n A x :=
  rfl

end groupCohomology
