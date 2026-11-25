/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Actions

/-!
# Outer scalar actions on balanced tensor functors

Let `Q` have compatible left `S` and right `R` actions, and let both factors
be modules over the commutative ground ring `k`. The balanced tensor product
of `Q` with a left `R`-module carries an `S`-module structure. Tensoring maps
is functorial and additive.

If `S` is a `k`-algebra and the `k` and `S` actions on `Q` form a scalar
tower, restriction of scalars identifies this functor with the ground-linear
balanced tensor functor. The comparison is the identity on balanced classes.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open MulOpposite

universe u v v' w z

namespace ModuleCat.BalancedTensor.Left

variable (k : Type u) (R : Type v) (S : Type v') (Q : Type w)
  [CommRing k] [Ring R] [Ring S] [Algebra k R]
  [AddCommGroup Q] [Module k Q] [Module Rᵐᵒᵖ Q] [Module S Q]
  [SMulCommClass S k Q] [SMulCommClass S Rᵐᵒᵖ Q]

/-- The original quotient, bundled with its computed outer module. -/
def obj (N : ModuleCat.{z} R) : ModuleCat.{max w z} S :=
  letI : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
  letI : Module S (TensorProduct.Balanced k R Q N.carrier) :=
    TensorProduct.Balanced.leftModule k R S Q N.carrier
  ModuleCat.of S (TensorProduct.Balanced k R Q N.carrier)

/-- Tensoring a morphism in the second factor gives an `S`-linear map on balanced classes. -/
def map {N N' : ModuleCat.{z} R} (g : N ⟶ N') :
    obj k R S Q N ⟶ obj k R S Q N' := by
  letI : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
  letI : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
  let l : N.carrier →ₗ[k] N'.carrier :=
    ((ModuleCat.restrictScalars (algebraMap k R)).map g).hom
  have hg : ∀ (r : R) (n : N.carrier), l (r • n) = r • l n := by
    intro r n
    change g.hom (r • n) = r • g.hom n
    exact g.hom.map_smul r n
  letI : Module S (TensorProduct.Balanced k R Q N.carrier) :=
    TensorProduct.Balanced.leftModule k R S Q N.carrier
  letI : Module S (TensorProduct.Balanced k R Q N'.carrier) :=
    TensorProduct.Balanced.leftModule k R S Q N'.carrier
  exact ModuleCat.ofHom (X := obj k R S Q N) (Y := obj k R S Q N')
    (TensorProduct.Balanced.mapLeft (k := k) (R := R) (S := S)
      (Q := Q) (N := N.carrier) (Q' := Q) (N' := N'.carrier)
      (LinearMap.id : Q →ₗ[k] Q) l (fun _ _ => rfl) hg (fun _ _ => rfl))

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem map_mk {N N' : ModuleCat.{z} R} (g : N ⟶ N') (q : Q) (n : N.carrier) :
    letI : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
    letI : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
    (map k R S Q g).hom (TensorProduct.Balanced.mk k R Q N.carrier q n) =
      TensorProduct.Balanced.mk k R Q N'.carrier q (g.hom n) := by
  let : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
  let : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
  let l : N.carrier →ₗ[k] N'.carrier :=
    ((ModuleCat.restrictScalars (algebraMap k R)).map g).hom
  have hg : ∀ (r : R) (n : N.carrier), l (r • n) = r • l n := by
    intro r n
    change g.hom (r • n) = r • g.hom n
    exact g.hom.map_smul r n
  let : Module S (TensorProduct.Balanced k R Q N.carrier) :=
    TensorProduct.Balanced.leftModule k R S Q N.carrier
  let : Module S (TensorProduct.Balanced k R Q N'.carrier) :=
    TensorProduct.Balanced.leftModule k R S Q N'.carrier
  change TensorProduct.Balanced.mapLeft (k := k) (R := R) (S := S)
    (Q := Q) (N := N.carrier) (Q' := Q) (N' := N'.carrier)
    (LinearMap.id : Q →ₗ[k] Q) l (fun _ _ => rfl) hg (fun _ _ => rfl)
    (TensorProduct.Balanced.mk k R Q N.carrier q n) = _
  change (TensorProduct.balanceRelations k R Q N'.carrier).mkQ
    ((TensorProduct.map (LinearMap.id : Q →ₗ[k] Q) l) (q ⊗ₜ[k] n)) = _
  rfl

/-- The balanced tensor functor with its outer `S`-action. -/
def functor : ModuleCat.{z} R ⥤ ModuleCat.{max w z} S where
  obj := obj k R S Q
  map := map k R S Q
  map_id N := by
    let : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
    let : Module S (TensorProduct.Balanced k R Q N.carrier) :=
      TensorProduct.Balanced.leftModule k R S Q N.carrier
    apply ModuleCat.hom_ext
    change ((map k R S Q (𝟙 N)).hom :
        TensorProduct.Balanced k R Q N.carrier →ₗ[S] TensorProduct.Balanced k R Q N.carrier) =
      LinearMap.id
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext k R Q N.carrier
    intro q n
    change (map k R S Q (𝟙 N)).hom (TensorProduct.Balanced.mk k R Q N.carrier q n) =
      TensorProduct.Balanced.mk k R Q N.carrier q n
    exact (map_mk k R S Q (𝟙 N) q n).trans (by rfl)
  map_comp {N N' N''} g h := by
    let : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
    let : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
    let : Module k N''.carrier := Module.compHom N''.carrier (algebraMap k R)
    let : Module S (TensorProduct.Balanced k R Q N.carrier) :=
      TensorProduct.Balanced.leftModule k R S Q N.carrier
    let : Module S (TensorProduct.Balanced k R Q N'.carrier) :=
      TensorProduct.Balanced.leftModule k R S Q N'.carrier
    let : Module S (TensorProduct.Balanced k R Q N''.carrier) :=
      TensorProduct.Balanced.leftModule k R S Q N''.carrier
    apply ModuleCat.hom_ext
    change ((map k R S Q (g ≫ h)).hom :
        TensorProduct.Balanced k R Q N.carrier →ₗ[S] TensorProduct.Balanced k R Q N''.carrier) =
      (map k R S Q h).hom.comp (map k R S Q g).hom
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext k R Q N.carrier
    intro q n
    change (map k R S Q (g ≫ h)).hom (TensorProduct.Balanced.mk k R Q N.carrier q n) =
      (map k R S Q h).hom ((map k R S Q g).hom
        (TensorProduct.Balanced.mk k R Q N.carrier q n))
    have h₀ : (map k R S Q (g ≫ h)).hom
        (TensorProduct.Balanced.mk k R Q N.carrier q n) =
        TensorProduct.Balanced.mk k R Q N''.carrier q ((g ≫ h).hom n) :=
      map_mk k R S Q (g ≫ h) q n
    have h₁ : TensorProduct.Balanced.mk k R Q N''.carrier q ((g ≫ h).hom n) =
        TensorProduct.Balanced.mk k R Q N''.carrier q (h.hom (g.hom n)) :=
      congrArg (fun y : N''.carrier => TensorProduct.Balanced.mk k R Q N''.carrier q y)
        (ModuleCat.comp_apply (M := N) (N := N') (O := N'') g h n)
    have h₂ : TensorProduct.Balanced.mk k R Q N''.carrier q (h.hom (g.hom n)) =
        (map k R S Q h).hom
          (TensorProduct.Balanced.mk k R Q N'.carrier q (g.hom n)) :=
      (map_mk k R S Q h q (g.hom n)).symm
    have h₃ : (map k R S Q h).hom
        (TensorProduct.Balanced.mk k R Q N'.carrier q (g.hom n)) =
        (map k R S Q h).hom ((map k R S Q g).hom
          (TensorProduct.Balanced.mk k R Q N.carrier q n)) :=
      congrArg (fun y : TensorProduct.Balanced k R Q N'.carrier => (map k R S Q h).hom y)
        (map_mk k R S Q g q n).symm
    exact h₀.trans (h₁.trans (h₂.trans h₃))

/-- Additivity of the actual S-module functor is proved on quotient classes. -/
theorem additive : (functor k R S Q : ModuleCat.{z} R ⥤ ModuleCat.{max w z} S).Additive where
  map_add := by
    intro N N' g h
    let : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
    let : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
    let : Module S (TensorProduct.Balanced k R Q N.carrier) :=
      TensorProduct.Balanced.leftModule k R S Q N.carrier
    let : Module S (TensorProduct.Balanced k R Q N'.carrier) :=
      TensorProduct.Balanced.leftModule k R S Q N'.carrier
    apply ModuleCat.hom_ext
    change ((map k R S Q (g + h)).hom :
        TensorProduct.Balanced k R Q N.carrier →ₗ[S] TensorProduct.Balanced k R Q N'.carrier) =
      (map k R S Q g).hom + (map k R S Q h).hom
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext k R Q N.carrier
    intro q n
    change (map k R S Q (g + h)).hom (TensorProduct.Balanced.mk k R Q N.carrier q n) =
      (map k R S Q g).hom (TensorProduct.Balanced.mk k R Q N.carrier q n) +
        (map k R S Q h).hom (TensorProduct.Balanced.mk k R Q N.carrier q n)
    have h₀ : (map k R S Q (g + h)).hom
        (TensorProduct.Balanced.mk k R Q N.carrier q n) =
        TensorProduct.Balanced.mk k R Q N'.carrier q ((g + h).hom n) :=
      map_mk k R S Q (g + h) q n
    have h₁ : TensorProduct.Balanced.mk k R Q N'.carrier q ((g + h).hom n) =
        TensorProduct.Balanced.mk k R Q N'.carrier q (g.hom n + h.hom n) := rfl
    have h₂ : TensorProduct.Balanced.mk k R Q N'.carrier q (g.hom n + h.hom n) =
        TensorProduct.Balanced.mk k R Q N'.carrier q (g.hom n) +
          TensorProduct.Balanced.mk k R Q N'.carrier q (h.hom n) :=
      (TensorProduct.Balanced.mk k R Q N'.carrier q).map_add (g.hom n) (h.hom n)
    have h₃ : TensorProduct.Balanced.mk k R Q N'.carrier q (g.hom n) +
        TensorProduct.Balanced.mk k R Q N'.carrier q (h.hom n) =
        (map k R S Q g).hom (TensorProduct.Balanced.mk k R Q N.carrier q n) +
          (map k R S Q h).hom (TensorProduct.Balanced.mk k R Q N.carrier q n) :=
      congrArg₂ (fun x y : TensorProduct.Balanced k R Q N'.carrier => x + y)
        (map_mk k R S Q g q n).symm (map_mk k R S Q h q n).symm
    exact h₀.trans (h₁.trans (h₂.trans h₃))

variable [Algebra k S] [hSQ : IsScalarTower k S Q]

include hSQ in
/-- Restriction of the outer scalar action identifies the two functors by the identity on balanced classes. -/
def groundIso :
    functor k R S Q ⋙ ModuleCat.restrictScalars (algebraMap k S) ≅
      ModuleCat.BalancedTensor.functor k R Q := by
  let F : ModuleCat.{z} R ⥤ ModuleCat.{max w z} k :=
    functor k R S Q ⋙ ModuleCat.restrictScalars (algebraMap k S)
  let G : ModuleCat.{z} R ⥤ ModuleCat.{max w z} k :=
    ModuleCat.BalancedTensor.functor k R Q
  refine (show F ≅ G from NatIso.ofComponents (fun N => ?_) ?_)
  · letI : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
    let A : ModuleCat.{max w z} k := F.obj N
    let B : ModuleCat.{max w z} k := G.obj N
    let e : A ≃ₗ[k] B :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro c x
          rw [RingHom.id_apply]
          exact DFunLike.congr_fun
            (TensorProduct.Balanced.leftAction_algebraMap k R S Q N.carrier c)
            (show TensorProduct.Balanced k R Q N.carrier from x) }
    exact (show A ≅ B from e.toModuleIso
      (g₁ := A.isAddCommGroup) (g₂ := B.isAddCommGroup)
      (m₁ := A.isModule) (m₂ := B.isModule))
  · intro N N' g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

@[simp, nolint simpNF] -- stated with Iso.app for rw; Iso.app_hom simplifies LHS
theorem groundIso_hom_apply (N : ModuleCat.{z} R)
    (x : (ModuleCat.restrictScalars (algebraMap k S)).obj (obj k R S Q N)) :
    ((groundIso k R S Q).app N).hom.hom x = x :=
  rfl

end ModuleCat.BalancedTensor.Left
