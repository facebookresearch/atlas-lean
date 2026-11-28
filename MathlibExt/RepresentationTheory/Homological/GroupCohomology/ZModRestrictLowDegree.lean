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
# First and second cohomology under integral scalar restriction

Let n∈ℕ, G be a group and A a ZMod n-representation.
Restriction to ℤ retains the coefficient group and G-action.
The one- and two-cocycle conditions and coboundary subgroups therefore
agree under the pointwise coefficient comparison.

The resulting H¹ and H² comparisons are additive and preserve
cocycle representatives. Their inverses return the same cochains.
Transporting each ZMod n-action to its integral cohomology group
gives linear versions of the comparisons. The case n=0 is included.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G : Type} [Group G]

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The underlying coefficient comparison A≅+Res(A) is the identity
on the additive group. It preserves the values of all G-actions. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The pointwise coefficient map identifies one-cocycles:
Z¹(G,A)≅+Z¹(G,Res(A)). The condition
x(gh)=x(g)+g•x(h) is unchanged. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The pointwise coefficient map identifies two-cocycles:
Z²(G,A)≅+Z²(G,Res(A)), with the same two-cocycle equation
and underlying values. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
A function x:G→A is a one-coboundary exactly when its integral
image is. Both are of the form x(g)=g•a-a for a coefficient a. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
A function z:G²→A is a two-coboundary exactly when its integral
image is. The coboundary formula g•x(h)-x(gh)+x(g) is unchanged. -/
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

/-!
# First cohomology classes

The quotient of one-cocycles by the coboundaries g↦g•a-a is compared
by preserving cocycle coefficient values under integral restriction.
-/

/-- For a commutative ring k, a group G, a k-representation A and
x∈H¹(G,A), this chooses a one-cocycle whose class is x. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The forward H¹ scalar map projects the integral image of a
chosen one-cocycle representative of the input class. -/
noncomputable def H1ZModRestrictIntToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H1 A → H1 (Rep.zmodRestrictInt n A) := fun x =>
  H1π (Rep.zmodRestrictInt n A)
    (cocycles₁ZModRestrictIntEquiv n A (H1Representative A x))

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
For a one-cocycle z, the forward class formula is
χ₁([z])=[χ_Z¹(z)]. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The forward map χ₁:H¹(G,A)→+H¹(G,Res(A)) is additive and
preserves the corresponding one-cocycle classes. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The return H¹ map selects an integral one-cocycle representative,
applies the inverse cocycle comparison, and takes its class over ZMod n. -/
noncomputable def H1ZModRestrictIntInvToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H1 (Rep.zmodRestrictInt n A) → H1 A := fun x =>
  H1π A ((cocycles₁ZModRestrictIntEquiv n A).symm
    (H1Representative (Rep.zmodRestrictInt n A) x))

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
For an integral one-cocycle z, the return class has value
[z]↦[(χ_Z¹)⁻¹(z)]. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The return H¹ map is additive and uses the inverse pointwise
cocycle comparison. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The forward and return maps give
χ₁:H¹(G,A)≅+H¹(G,Res(A)), with the corresponding cocycle-class
formulas in both directions. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The transported ZMod n-action on integral H¹ is
r•y=χ₁(r•χ₁⁻¹(y)). -/
@[instance_reducible]
noncomputable def H1ZModRestrictIntModule
    (n : ℕ) (A : Rep (ZMod n) G) :
    Module (ZMod n) (H1 (Rep.zmodRestrictInt n A)) :=
  (H1ZModRestrictIntAddEquiv n A).symm.module (ZMod n)

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
For the transported target action, χ₁ gives the linear equivalence
H¹(G,A)≅ₗ[ZMod n]H¹(G,Res(A)). -/
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

/-!
# Second cohomology classes

The quotient of two-cocycles by g•x(h)-x(gh)+x(g) is unchanged
additively by restricting coefficient scalars to ℤ.
-/

/-- For a commutative ring k, a group G, a k-representation A and
x∈H²(G,A), this chooses a two-cocycle whose class is x. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The forward H² scalar function takes the integral class of a
chosen two-cocycle representative. -/
noncomputable def H2ZModRestrictIntToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H2 A → H2 (Rep.zmodRestrictInt n A) := fun x =>
  H2π (Rep.zmodRestrictInt n A)
    (cocycles₂ZModRestrictIntEquiv n A (H2Representative A x))

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
For a two-cocycle z, the forward map satisfies
χ₂([z])=[χ_Z²(z)]. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The forward H² comparison H²(G,A)→+H²(G,Res(A)) is additive,
with the pointwise two-cocycle class formula. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The return H² function takes a selected integral two-cocycle,
returns it through the inverse cocycle comparison, and projects
to H²(G,A). -/
noncomputable def H2ZModRestrictIntInvToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H2 (Rep.zmodRestrictInt n A) → H2 A := fun x =>
  H2π A ((cocycles₂ZModRestrictIntEquiv n A).symm
    (H2Representative (Rep.zmodRestrictInt n A) x))

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
For an integral two-cocycle z, the return map sends its class
to [(χ_Z²)⁻¹(z)]. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The return H² map is additive and uses the inverse two-cocycle
comparison on representatives. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The maps give the additive equivalence
χ₂:H²(G,A)≅+H²(G,Res(A)), preserving two-cocycle classes. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The transported target ZMod n-action on integral H² is
r•y=χ₂(r•χ₂⁻¹(y)). -/
@[instance_reducible]
noncomputable def H2ZModRestrictIntModule
    (n : ℕ) (A : Rep (ZMod n) G) :
    Module (ZMod n) (H2 (Rep.zmodRestrictInt n A)) :=
  (H2ZModRestrictIntAddEquiv n A).symm.module (ZMod n)

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
For that transported target action, the additive χ₂ becomes
H²(G,A)≅ₗ[ZMod n]H²(G,Res(A)). -/
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
