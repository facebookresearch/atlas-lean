/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced

/-!
# The actual ground-linear balanced tensor functor on left modules

Scalar restriction on the variable left module is native. The quotient and
map are the existing ground-balanced span quotient and native `mapQ`.
Functor laws and additivity are proved on pure balanced representatives.
The acting ring is allowed to be noncommutative; no tensor-additivity,
flatness, or chosen-coequalizer premise is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct
open MulOpposite

universe u v w z

namespace ModuleCat.BalancedTensor

variable (k : Type u) (R : Type v) (M : Type w)
  [CommRing k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]

/-- The variable left module keeps its original acting-ring module and uses
native restriction for the ground module. -/
abbrev obj (N : ModuleCat.{z} R) : ModuleCat.{max w z} k :=
  letI : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
  ModuleCat.of k (TensorProduct.Balanced k R M N.carrier)

/-- The actual quotient map induced by a native left-module morphism. -/
def map {N N' : ModuleCat.{z} R} (g : N ⟶ N') : obj k R M N ⟶ obj k R M N' := by
  letI : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
  letI : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
  let l : N.carrier →ₗ[k] N'.carrier :=
    ((ModuleCat.restrictScalars (algebraMap k R)).map g).hom
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.map (LinearMap.id : M →ₗ[k] M) l
      (fun _ _ => rfl) (by
        intro r n
        change g.hom (r • n) = r • g.hom n
        exact g.hom.map_smul r n))

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem map_mk {N N' : ModuleCat.{z} R} (g : N ⟶ N') (m : M) (n : N.carrier) :
    letI : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
    letI : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
    (map k R M g).hom
        (TensorProduct.Balanced.mk k R M N.carrier m n) =
      TensorProduct.Balanced.mk k R M N'.carrier m (g.hom n) := by
  dsimp only
  let : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
  let : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
  let l : N.carrier →ₗ[k] N'.carrier :=
    ((ModuleCat.restrictScalars (algebraMap k R)).map g).hom
  have hg : ∀ (r : R) (n : N.carrier), l (r • n) = r • l n := by
    intro r n
    change g.hom (r • n) = r • g.hom n
    exact g.hom.map_smul r n
  change TensorProduct.Balanced.map (LinearMap.id : M →ₗ[k] M) l
      (fun _ _ => rfl) hg (TensorProduct.Balanced.mk k R M N.carrier m n) = _
  change (TensorProduct.balanceRelations k R M N'.carrier).mkQ
      ((TensorProduct.map (LinearMap.id : M →ₗ[k] M) l) (m ⊗ₜ[k] n)) = _
  rfl

/-- The actual balanced tensor functor, with both functor laws earned. -/
def functor : ModuleCat.{z} R ⥤ ModuleCat.{max w z} k where
  obj := obj k R M
  map := map k R M
  map_id N := by
    let : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
    apply ModuleCat.hom_ext
    apply TensorProduct.Balanced.hom_ext
    intro m n
    simpa only [ModuleCat.hom_id, LinearMap.id_apply] using map_mk k R M (𝟙 N) m n
  map_comp {N N' N''} g h := by
    let : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
    let : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
    let : Module k N''.carrier := Module.compHom N''.carrier (algebraMap k R)
    apply ModuleCat.hom_ext
    apply TensorProduct.Balanced.hom_ext
    intro m n
    change (map k R M (g ≫ h)).hom
        (TensorProduct.Balanced.mk k R M N.carrier m n) =
      (map k R M h).hom ((map k R M g).hom
        (TensorProduct.Balanced.mk k R M N.carrier m n))
    calc
      _ = TensorProduct.Balanced.mk k R M N''.carrier m ((g ≫ h).hom n) :=
        map_mk k R M (g ≫ h) m n
      _ = TensorProduct.Balanced.mk k R M N''.carrier m (h.hom (g.hom n)) :=
        congrArg (fun y : N''.carrier => TensorProduct.Balanced.mk k R M N''.carrier m y)
          (ModuleCat.comp_apply (M := N) (N := N') (O := N'') g h n)
      _ = (map k R M h).hom
          (TensorProduct.Balanced.mk k R M N'.carrier m (g.hom n)) :=
        (map_mk k R M h m (g.hom n)).symm
      _ = _ := congrArg (fun y => (map k R M h).hom y)
        (map_mk k R M g m n).symm

/-- Additivity is a proof of the actual functor property, not an input premise. -/
theorem additive : (functor k R M : ModuleCat.{z} R ⥤ ModuleCat.{max w z} k).Additive where
  map_add := by
    intro N N' g h
    let : Module k N.carrier := Module.compHom N.carrier (algebraMap k R)
    let : Module k N'.carrier := Module.compHom N'.carrier (algebraMap k R)
    apply ModuleCat.hom_ext
    apply TensorProduct.Balanced.hom_ext
    intro m n
    change (map k R M (g + h)).hom (TensorProduct.Balanced.mk k R M N.carrier m n) =
      ((map k R M g).hom + (map k R M h).hom)
        (TensorProduct.Balanced.mk k R M N.carrier m n)
    rw [map_mk, ModuleCat.hom_add, LinearMap.add_apply, map_add,
      LinearMap.add_apply, map_mk, map_mk]

end ModuleCat.BalancedTensor
