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

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-
Adapted implementation credited to @toskua and Avocado from
AlgebraicGeometry/Sites/RootScalarFlattenMonoidal.lean.
-/

/-!
# Tensor and strong monoidal scalar restriction along a ring equivalence

The original balanced tensor transport identifies the actual restriction-of-scalars
lax tensor and unit maps as isomorphisms. The tensor comparison is natural in
its original coefficient module.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory Functor.LaxMonoidal
open scoped TensorProduct

namespace ModuleCat

universe s u

section TensorTransport

variable {R S : Type s} [CommRing R] [CommRing S] (e : R ≃+* S)

/-- Ring-equivalence tensor transport uses the same two original carriers and balanced relations. -/
def restrictScalarsTensorIsoOfRingEquiv (M N : ModuleCat.{s} S) :
    (ModuleCat.restrictScalars e.toRingHom).obj M ⊗
        (ModuleCat.restrictScalars e.toRingHom).obj N ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (M ⊗ N) := by
  let M₀ : ModuleCat.{s} R := (ModuleCat.restrictScalars e.toRingHom).obj M
  let N₀ : ModuleCat.{s} R := (ModuleCat.restrictScalars e.toRingHom).obj N
  let Z₀ : ModuleCat.{s} R := M₀ ⊗ N₀
  let Z₁ : ModuleCat.{s} R := (ModuleCat.restrictScalars e.toRingHom).obj (M ⊗ N)
  letI : Module R M₀ := M₀.isModule
  letI : Module R N₀ := N₀.isModule
  letI : Module R Z₀ := Z₀.isModule
  letI : Module R Z₁ := Z₁.isModule
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.symm e.toRingHom e.symm.toRingHom
  let f : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) M₀ M :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) N₀ N :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let q := TensorProduct.congr (σ₂₁ := e.symm.toRingHom) f g
  let l : Z₀ ≃ₗ[R] Z₁ :=
    { __ := q.toAddEquiv
      map_smul' := fun r x => by
        change q (r • x) = e r • q x
        exact q.map_smulₛₗ r x }
  exact
    { hom := ConcreteCategory.ofHom (C := ModuleCat.{s} R) (X := Z₀) (Y := Z₁) l.toLinearMap
      inv := ConcreteCategory.ofHom (C := ModuleCat.{s} R) (X := Z₁) (Y := Z₀) l.symm.toLinearMap
      hom_inv_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact l.symm_apply_apply x
      inv_hom_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact l.apply_symm_apply x }

/-- The genuine tensor transport has the literal forward pure-tensor value. -/
theorem restrictScalarsTensorIsoOfRingEquiv_hom_tmul (M N : ModuleCat.{s} S) (m : M) (n : N) :
    (restrictScalarsTensorIsoOfRingEquiv e M N).hom
      ((show (ModuleCat.restrictScalars e.toRingHom).obj M from m) ⊗ₜ[R]
        (show (ModuleCat.restrictScalars e.toRingHom).obj N from n)) =
      m ⊗ₜ[S] n := rfl

/-- The inverse tensor transport also preserves the two original factor values. -/
theorem restrictScalarsTensorIsoOfRingEquiv_inv_tmul (M N : ModuleCat.{s} S) (m : M) (n : N) :
    (restrictScalarsTensorIsoOfRingEquiv e M N).inv (m ⊗ₜ[S] n) =
      (show (ModuleCat.restrictScalars e.toRingHom).obj M from m) ⊗ₜ[R]
        (show (ModuleCat.restrictScalars e.toRingHom).obj N from n) := rfl

/-- The constructed transport is exactly the stock adjunction's lax tensor map. -/
theorem restrictScalarsTensorIsoOfRingEquiv_hom_eq_μ (M N : ModuleCat.{s} S) :
    (restrictScalarsTensorIsoOfRingEquiv e M N).hom =
      Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m n
  exact (restrictScalarsTensorIsoOfRingEquiv_hom_tmul e M N m n).trans
    (ModuleCat.restrictScalars_μ_tmul e.toRingHom M N m n).symm

/-- The actual lax unit is invertible because the given scalar map is a ring equivalence. -/
theorem restrictScalarsUnitIsIsoOfRingEquiv :
    IsIso (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.toRingHom)) := by
  have h : Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.toRingHom) =
      (ModuleCat.restrictScalarsIsoOfEquiv e).inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact (ModuleCat.restrictScalars_η e.toRingHom r).trans
      (ModuleCat.restrictScalarsIsoOfEquiv_inv_apply e r).symm
  rw [h]
  infer_instance

/-- Genuine balanced tensor transport proves invertibility of the original lax tensor map. -/
theorem restrictScalarsTensorIsIsoOfRingEquiv (M N : ModuleCat.{s} S) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) := by
  rw [← restrictScalarsTensorIsoOfRingEquiv_hom_eq_μ e M N]
  infer_instance

/-- Strong scalar transport is constructed from the stock lax maps and the proved isomorphisms. -/
@[instance_reducible]
def restrictScalarsMonoidalOfRingEquiv : (ModuleCat.restrictScalars e.toRingHom).Monoidal := by
  let : IsIso (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.toRingHom)) :=
    restrictScalarsUnitIsIsoOfRingEquiv e
  let : ∀ M N, IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) :=
    restrictScalarsTensorIsIsoOfRingEquiv e
  exact Functor.Monoidal.ofLaxMonoidal (ModuleCat.restrictScalars e.toRingHom)


end TensorTransport

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual tensor comparison is natural in the original derived coefficient. -/
def restrictScalarsTensoringLeftIsoOfRingEquiv
    (e : R ≃+* S) (M : ModuleCat.{u} S) :
    restrictScalars e.toRingHom ⋙
        (tensoringLeft (ModuleCat.{u} R)).obj ((restrictScalars e.toRingHom).obj M) ≅
      (tensoringLeft (ModuleCat.{u} S)).obj M ⋙ restrictScalars e.toRingHom := by
  refine NatIso.ofComponents (fun N => restrictScalarsTensorIsoOfRingEquiv e M N) ?_
  intro N N' f
  change ((restrictScalars e.toRingHom).obj M ◁ (restrictScalars e.toRingHom).map f) ≫
      (restrictScalarsTensorIsoOfRingEquiv e M N').hom =
    (restrictScalarsTensorIsoOfRingEquiv e M N).hom ≫
      (restrictScalars e.toRingHom).map (M ◁ f)
  rw [restrictScalarsTensorIsoOfRingEquiv_hom_eq_μ,
    restrictScalarsTensorIsoOfRingEquiv_hom_eq_μ]
  exact μ_natural_right (restrictScalars e.toRingHom) M f

end ModuleCat
