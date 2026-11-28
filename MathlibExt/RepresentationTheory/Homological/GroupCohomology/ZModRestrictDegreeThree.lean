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
# Degree-three cohomology under integral scalar restriction

Let n∈ℕ and A be a ZMod n-representation of a group G.
Restriction to ℤ leaves the degree-three cochain values, cocycle
condition and coboundary subgroup unchanged. It therefore gives
the additive comparison H³(G,A)≅H³(G,Res(A)).

The maps have the same values on chosen cocycle representatives.
Transporting the ZMod n-module structure through this additive comparison
makes it a ZMod n-linear equivalence. The case n=0 is included.
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
The degree-three cochain comparison is the additive equivalence
between functions G³→A and G³→Res(A), given pointwise by the
identity on the underlying coefficient group. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The pointwise coefficient comparison restricts to
Z³(G,A)≅Z³(G,Res(A)) as an additive equivalence,
preserving every three-cocycle value. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
A degree-three cochain is a coboundary over ZMod n exactly when
its pointwise integral image is a coboundary over ℤ.
Both coboundary operators use the same G-action and alternating signs. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The coboundary subgroup comparison is the additive equivalence
B³(G,A)≅B³(G,Res(A)), with the same coefficient-valued functions. -/
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

/-!
# Third cohomology and cocycle classes

Third cohomology is the quotient of three-cocycles by three-coboundaries.
The scalar comparison acts on a class by keeping its representative's
coefficient values and changing the scalar interpretation.
-/

/-- For a commutative ring k, a group G, a k-representation A and
x∈H³(G,A), this is a chosen z∈Z³(G,A) whose cohomology class is x.
The selector is not required to be linear. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The forward function on H³ sends x to the integral class of
the scalar-restricted cocycle selected to represent x. -/
noncomputable def H3ZModRestrictIntToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H3 A → H3 (Rep.zmodRestrictInt n A) := fun x =>
  H3π (Rep.zmodRestrictInt n A)
    (cocycles₃ZModRestrictIntEquiv n A (H3Representative A x))

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
On a projected cocycle z, the forward map satisfies
χ₃([z])=[χ_Z³(z)], where χ_Z³ is the additive cocycle comparison. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The forward third-cohomology comparison is additive:
H³(G,A)→+H³(G,Res(A)), with class value [z]↦[χ_Z³(z)]. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The return function H³(G,Res(A))→H³(G,A) takes a chosen integral
three-cocycle representative, returns it through the inverse cocycle
comparison, and projects its ZMod n-cohomology class. -/
noncomputable def H3ZModRestrictIntInvToFun
    (n : ℕ) (A : Rep (ZMod n) G) :
    H3 (Rep.zmodRestrictInt n A) → H3 A := fun x =>
  H3π A ((cocycles₃ZModRestrictIntEquiv n A).symm
    (H3Representative (Rep.zmodRestrictInt n A) x))

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
On an integral cocycle z, the return map has value
[z]↦[(χ_Z³)⁻¹(z)] in H³(G,A). -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The return third-cohomology map is additive and has the
inverse-cocycle representative formula. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The forward and return additive maps give the equivalence
χ₃:H³(G,A)≅+H³(G,Res(A)), preserving the classes of corresponding
cocycle representatives. -/
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

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
The integral H³ group acquires the transported ZMod n-action
r•y=χ₃(r•χ₃⁻¹(y)).
This uses the ZMod n-action on H³(G,A). -/
@[instance_reducible]
noncomputable def H3ZModRestrictIntModule
    (n : ℕ) (A : Rep (ZMod n) G) :
    Module (ZMod n) (H3 (Rep.zmodRestrictInt n A)) :=
  (H3ZModRestrictIntAddEquiv n A).symm.module (ZMod n)

/-- Let n∈ℕ, G be a group, A a ZMod n-representation and Res(A)
its scalar restriction to ℤ. The coefficient group and G-action are
unchanged, including n=0.
With that transported target action, the additive scalar
comparison becomes H³(G,A)≅ₗ[ZMod n]H³(G,Res(A)).
Its underlying map is χ₃. -/
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
