/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic

/-!
# Finite-free complements of finitely generated projective modules

Every finitely generated projective module is a direct summand of a finite free
module.  This file expresses that fact inside `FGProjectiveCat`.

The complement produced here is finitely generated projective, not necessarily
free.  Thus the result does not assert that every finitely generated projective
module is stably free.
-/

@[expose] public section

open CategoryTheory Limits

universe u

variable {R : Type u} [Ring R]

namespace FGProjectiveCat

/-- The standard rank-`n` finite free projective. -/
abbrev standardFree (R : Type u) [Ring R] (n : ℕ) :
    FGProjectiveCat.{u} R :=
  FGProjectiveCat.of (R := R) (Fin n → R)

/-- The regular rank-one projective. -/
abbrev regular (R : Type u) [Ring R] : FGProjectiveCat.{u} R :=
  FGProjectiveCat.of (R := R) R

/-- The carrier of a categorical biproduct of finitely generated projective
modules is linearly equivalent to the product of their carriers. -/
noncomputable def biprodCarrierLinearEquiv (P Q : FGProjectiveCat.{u} R) :
    ((P ⊞ Q : FGProjectiveCat.{u} R) : Type u) ≃ₗ[R] (P × Q) := by
  let F := FGProjectiveCat.toModuleCat (R := R)
  let _ : PreservesBiproduct (pairFunction P Q) F := inferInstance
  let _ : PreservesBinaryBiproduct P Q F :=
    preservesBinaryBiproduct_of_preservesBiproduct F P Q
  exact ((F.mapBiprod P Q).trans
    (ModuleCat.biprodIsoProd P.obj Q.obj)).toLinearEquiv

@[simp]
theorem biprodCarrierLinearEquiv_apply_fst
    (P Q : FGProjectiveCat.{u} R)
    (x : (P ⊞ Q : FGProjectiveCat.{u} R)) :
    (biprodCarrierLinearEquiv P Q x).1 =
      (biprod.fst : P ⊞ Q ⟶ P).hom.hom x := by
  let F := FGProjectiveCat.toModuleCat (R := R)
  let _ : PreservesBiproduct (pairFunction P Q) F := inferInstance
  let _ : PreservesBinaryBiproduct P Q F :=
    preservesBinaryBiproduct_of_preservesBiproduct F P Q
  have hprod :
      (ModuleCat.biprodIsoProd (F.obj P) (F.obj Q)).hom ≫
          ModuleCat.ofHom (LinearMap.fst R (F.obj P) (F.obj Q)) =
        (biprod.fst : F.obj P ⊞ F.obj Q ⟶ F.obj P) := by
    cat_disch
  have hcat :
      (F.mapBiprod P Q).hom ≫
          (ModuleCat.biprodIsoProd (F.obj P) (F.obj Q)).hom ≫
          ModuleCat.ofHom (LinearMap.fst R (F.obj P) (F.obj Q)) =
        F.map (biprod.fst : P ⊞ Q ⟶ P) := by
    dsimp [F]
    dsimp [F] at hprod
    rw [hprod]
    exact biprod.lift_fst _ _
  have hfun := congrArg (fun k => k.hom x) hcat
  change
    (ModuleCat.Hom.hom
      ((F.mapBiprod P Q).hom ≫
        (ModuleCat.biprodIsoProd (F.obj P) (F.obj Q)).hom ≫
        ModuleCat.ofHom (LinearMap.fst R (F.obj P) (F.obj Q)))) x =
      (F.map (biprod.fst : P ⊞ Q ⟶ P)).hom x
  exact hfun

@[simp]
theorem biprodCarrierLinearEquiv_apply_snd
    (P Q : FGProjectiveCat.{u} R)
    (x : (P ⊞ Q : FGProjectiveCat.{u} R)) :
    (biprodCarrierLinearEquiv P Q x).2 =
      (biprod.snd : P ⊞ Q ⟶ Q).hom.hom x := by
  let F := FGProjectiveCat.toModuleCat (R := R)
  let _ : PreservesBiproduct (pairFunction P Q) F := inferInstance
  let _ : PreservesBinaryBiproduct P Q F :=
    preservesBinaryBiproduct_of_preservesBiproduct F P Q
  have hprod :
      (ModuleCat.biprodIsoProd (F.obj P) (F.obj Q)).hom ≫
          ModuleCat.ofHom (LinearMap.snd R (F.obj P) (F.obj Q)) =
        (biprod.snd : F.obj P ⊞ F.obj Q ⟶ F.obj Q) := by
    cat_disch
  have hcat :
      (F.mapBiprod P Q).hom ≫
          (ModuleCat.biprodIsoProd (F.obj P) (F.obj Q)).hom ≫
          ModuleCat.ofHom (LinearMap.snd R (F.obj P) (F.obj Q)) =
        F.map (biprod.snd : P ⊞ Q ⟶ Q) := by
    dsimp [F]
    dsimp [F] at hprod
    rw [hprod]
    exact biprod.lift_snd _ _
  have hfun := congrArg (fun k => k.hom x) hcat
  change
    (ModuleCat.Hom.hom
      ((F.mapBiprod P Q).hom ≫
        (ModuleCat.biprodIsoProd (F.obj P) (F.obj Q)).hom ≫
        ModuleCat.ofHom (LinearMap.snd R (F.obj P) (F.obj Q)))) x =
      (F.map (biprod.snd : P ⊞ Q ⟶ Q)).hom x
  exact hfun

/-- The biproduct carrier equivalence sends a componentwise isomorphism to
the product of the two underlying linear equivalences. -/
theorem biprodCarrierLinearEquiv_mapIso_apply
    {P Q P' Q' : FGProjectiveCat.{u} R}
    (e : P ≅ P') (f : Q ≅ Q')
    (x : (P ⊞ Q : FGProjectiveCat.{u} R)) :
    biprodCarrierLinearEquiv P' Q' ((biprod.mapIso e f).hom x) =
      (isoToLinearEquiv e (biprodCarrierLinearEquiv P Q x).1,
        isoToLinearEquiv f (biprodCarrierLinearEquiv P Q x).2) := by
  apply Prod.ext
  · simp only [biprodCarrierLinearEquiv_apply_fst]
    have hcat := biprod.map_fst e.hom f.hom
    exact congrArg (fun k => k.hom.hom x) hcat
  · simp only [biprodCarrierLinearEquiv_apply_snd]
    have hcat := biprod.map_snd e.hom f.hom
    exact congrArg (fun k => k.hom.hom x) hcat

/-- The biproduct carrier equivalence sends the biproduct braiding to the
swap of product coordinates. -/
theorem biprodCarrierLinearEquiv_braiding_apply
    (P Q : FGProjectiveCat.{u} R)
    (x : (P ⊞ Q : FGProjectiveCat.{u} R)) :
    biprodCarrierLinearEquiv Q P ((biprod.braiding P Q).hom x) =
      ((biprodCarrierLinearEquiv P Q x).2,
        (biprodCarrierLinearEquiv P Q x).1) := by
  apply Prod.ext
  · simp only [biprodCarrierLinearEquiv_apply_fst,
      biprodCarrierLinearEquiv_apply_snd]
    have hcat :
        (biprod.braiding P Q).hom ≫
            (biprod.fst : Q ⊞ P ⟶ Q) =
          (biprod.snd : P ⊞ Q ⟶ Q) := by
      cat_disch
    exact congrArg (fun k => k.hom.hom x) hcat
  · simp only [biprodCarrierLinearEquiv_apply_fst,
      biprodCarrierLinearEquiv_apply_snd]
    have hcat :
        (biprod.braiding P Q).hom ≫
            (biprod.snd : Q ⊞ P ⟶ P) =
          (biprod.fst : P ⊞ Q ⟶ P) := by
      cat_disch
    exact congrArg (fun k => k.hom.hom x) hcat

/-- A linear equivalence between the carriers of two finitely generated
projectives induces an isomorphism in `FGProjectiveCat`. -/
def isoOfLinearEquiv {P Q : FGProjectiveCat.{u} R} (e : P ≃ₗ[R] Q) : P ≅ Q where
  hom := ConcreteCategory.ofHom e.toLinearMap
  inv := ConcreteCategory.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

/-- Automorphisms in `FGProjectiveCat` are the linear automorphisms of the
underlying module. -/
def autCarrierLinearEquiv (P : FGProjectiveCat.{u} R) :
    Aut P ≃* (P ≃ₗ[R] P) where
  toFun e := isoToLinearEquiv e.asIso
  invFun e := .of (isoOfLinearEquiv e)
  left_inv e := by
    apply Aut.ext
    ext x
    rfl
  right_inv e := by
    ext x
    rfl
  map_mul' e f := by
    ext x
    rfl

/-- The automorphism group of the standard rank-`n` finite free object is
the matrix general linear group `GLₙ(R)`. -/
noncomputable def freeAutMulEquivGL (R : Type u) [CommRing R] (n : ℕ) :
    Aut (FGProjectiveCat.of (R := R) (Fin n → R)) ≃*
      Matrix.GeneralLinearGroup (Fin n) R :=
  (autCarrierLinearEquiv (FGProjectiveCat.of (R := R) (Fin n → R))).trans
    (((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := R)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R))).symm)

/-- Split a standard free module indexed by `Fin (n+m)` into the
corresponding categorical biproduct. -/
noncomputable def standardFreeAddIso (R : Type u) [Ring R] (n m : ℕ) :
    standardFree R (n + m) ≅ standardFree R n ⊞ standardFree R m := by
  let sumProd : ((Fin n ⊕ Fin m) → R) ≃ₗ[R]
      (Fin n → R) × (Fin m → R) :=
    { Equiv.sumPiEquivProdPi (fun _ => R) with
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let split : (Fin (n + m) → R) ≃ₗ[R]
      (Fin n → R) × (Fin m → R) :=
    (LinearEquiv.piCongrLeft R (fun _ => R)
      finSumFinEquiv.symm).trans sumProd
  let biprodProduct :
      (((standardFree R n ⊞ standardFree R m :
          FGProjectiveCat.{u} R)) : Type u) ≃ₗ[R]
        (Fin n → R) × (Fin m → R) :=
    biprodCarrierLinearEquiv (standardFree R n) (standardFree R m)
  exact isoOfLinearEquiv (split.trans biprodProduct.symm)

@[simp]
theorem standardFreeAddIso_inv_apply (R : Type u) [Ring R]
    (n m : ℕ)
    (x : (standardFree R n ⊞ standardFree R m :
      FGProjectiveCat.{u} R))
    (i : Fin (n + m)) :
    (standardFreeAddIso R n m).symm.hom.hom x i =
      Sum.elim
        (biprodCarrierLinearEquiv (standardFree R n) (standardFree R m) x).1
        (biprodCarrierLinearEquiv (standardFree R n) (standardFree R m) x).2
        (finSumFinEquiv.symm i) := by
  rfl

theorem standardFreeAddIso_inv_apply_fun (R : Type u) [Ring R]
    (n m : ℕ)
    (x : (standardFree R n ⊞ standardFree R m :
      FGProjectiveCat.{u} R)) :
    (standardFreeAddIso R n m).symm.hom.hom x =
      fun i => Sum.elim
        (biprodCarrierLinearEquiv (standardFree R n) (standardFree R m) x).1
        (biprodCarrierLinearEquiv (standardFree R n) (standardFree R m) x).2
        (finSumFinEquiv.symm i) := by
  funext i
  exact standardFreeAddIso_inv_apply R n m x i

/-- Every finitely generated projective module has a finitely generated
projective complement whose biproduct with it is finite free. -/
theorem exists_biprod_iso_fin_free (P : FGProjectiveCat.{u} R) :
    ∃ (n : ℕ) (Q : FGProjectiveCat.{u} R),
      Nonempty (P ⊞ Q ≅ FGProjectiveCat.of (R := R) (Fin n → R)) := by
  obtain ⟨n, f, g, -, -, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R P
  let K : Submodule R (Fin n → R) := LinearMap.ker f
  let projection : (Fin n → R) →ₗ[R] K :=
    LinearMap.codRestrict K (LinearMap.id - g.comp f) (by
      intro x
      change f (x - g (f x)) = 0
      rw [map_sub, ← LinearMap.comp_apply, hfg, LinearMap.id_apply, sub_self])
  have h_projection_subtype : projection.comp K.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change x.1 - g (f x.1) = x.1
    rw [show f x.1 = 0 from x.2]
    simp
  have h_projection_surjective : Function.Surjective projection := by
    intro x
    refine ⟨x.1, ?_⟩
    apply Subtype.ext
    change x.1 - g (f x.1) = x.1
    rw [show f x.1 = 0 from x.2]
    simp
  let _ : Module.Finite R K :=
    Module.Finite.of_surjective projection h_projection_surjective
  let _ : Module.Projective R K :=
    Module.Projective.of_split K.subtype projection h_projection_subtype
  let Q : FGProjectiveCat.{u} R := FGProjectiveCat.of (R := R) K
  let toFree : P × K →ₗ[R] (Fin n → R) := LinearMap.coprod g K.subtype
  let fromFree : (Fin n → R) →ₗ[R] P × K := LinearMap.prod f projection
  have h_to_from : toFree.comp fromFree = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change g (f x) + (x - g (f x)) = x
    abel
  have h_from_to : fromFree.comp toFree = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change f (g x.1 + x.2.1) = x.1
      rw [map_add, ← LinearMap.comp_apply, hfg, LinearMap.id_apply,
        show f x.2.1 = 0 from x.2.2, add_zero]
    · apply Subtype.ext
      change (g x.1 + x.2.1) - g (f (g x.1 + x.2.1)) = x.2.1
      rw [map_add, ← LinearMap.comp_apply, hfg, LinearMap.id_apply,
        show f x.2.1 = 0 from x.2.2, add_zero]
      abel
  let productEquiv : (P × Q) ≃ₗ[R] (Fin n → R) :=
    LinearEquiv.ofLinearMap toFree fromFree h_to_from h_from_to
  let biprodEquiv :
      ((P ⊞ Q : FGProjectiveCat.{u} R) : Type u) ≃ₗ[R] (Fin n → R) :=
    (biprodCarrierLinearEquiv P Q).trans productEquiv
  exact ⟨n, Q, ⟨isoOfLinearEquiv biprodEquiv⟩⟩

end FGProjectiveCat
