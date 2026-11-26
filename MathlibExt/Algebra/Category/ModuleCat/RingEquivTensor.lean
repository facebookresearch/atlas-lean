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
# Monoidal restriction of scalars along a ring equivalence

Let `R,S` be commutative rings and `e : R ≃+* S`. For the restriction-of-scalars functor `F :
ModuleCat S → ModuleCat R`, the balanced tensor comparison is an isomorphism `F(M) ⊗_R F(N) ≅
F(M ⊗_S N)`. It sends `m ⊗_R n` to `m ⊗_S n`, and its inverse sends the same pure tensor back.

This comparison is the lax-monoidal tensor map of `F`. The unit map is also invertible, giving
a monoidal structure on `F`. For a fixed left factor `M`, these isomorphisms form a natural
comparison between restriction followed by tensoring with `F(M)` and tensoring with `M`
followed by restriction.
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

/-- Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, and `M,N : ModuleCat.{s} S`. For
`F=ModuleCat.restrictScalars e.toRingHom`, the isomorphism `F(M) ⊗_R F(N) ≅ F(M ⊗_S N)`
identifies the two balanced tensor products using the ring equivalence. Its forward and
inverse maps preserve the two entries of a pure tensor. -/
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

/-- Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, `M,N : ModuleCat.{s} S`, `m∈M`, and
`n∈N`. The forward map of `restrictScalarsTensorIsoOfRingEquiv e M N` sends `m ⊗ₜ[R] n` in the
restricted modules to `m ⊗ₜ[S] n` in the restricted `S`-tensor product. -/
theorem restrictScalarsTensorIsoOfRingEquiv_hom_tmul (M N : ModuleCat.{s} S) (m : M) (n : N) :
    (restrictScalarsTensorIsoOfRingEquiv e M N).hom
      ((show (ModuleCat.restrictScalars e.toRingHom).obj M from m) ⊗ₜ[R]
        (show (ModuleCat.restrictScalars e.toRingHom).obj N from n)) =
      m ⊗ₜ[S] n := rfl

/-- Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, `M,N : ModuleCat.{s} S`, `m∈M`, and
`n∈N`. The inverse map of `restrictScalarsTensorIsoOfRingEquiv e M N` sends `m ⊗ₜ[S] n` to `m
⊗ₜ[R] n` in `F(M) ⊗_R F(N)`, where `F` restricts scalars along `e`. -/
theorem restrictScalarsTensorIsoOfRingEquiv_inv_tmul (M N : ModuleCat.{s} S) (m : M) (n : N) :
    (restrictScalarsTensorIsoOfRingEquiv e M N).inv (m ⊗ₜ[S] n) =
      (show (ModuleCat.restrictScalars e.toRingHom).obj M from m) ⊗ₜ[R]
        (show (ModuleCat.restrictScalars e.toRingHom).obj N from n) := rfl

/-- Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, and `M,N : ModuleCat.{s} S`. For
`F=ModuleCat.restrictScalars e.toRingHom`, `(restrictScalarsTensorIsoOfRingEquiv e M N).hom =
Functor.LaxMonoidal.μ F M N` as maps `F(M) ⊗_R F(N) → F(M ⊗_S N)`. -/
theorem restrictScalarsTensorIsoOfRingEquiv_hom_eq_μ (M N : ModuleCat.{s} S) :
    (restrictScalarsTensorIsoOfRingEquiv e M N).hom =
      Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m n
  exact (restrictScalarsTensorIsoOfRingEquiv_hom_tmul e M N m n).trans
    (ModuleCat.restrictScalars_μ_tmul e.toRingHom M N m n).symm

/-- Let `R,S : Type s` be commutative rings and `e : R ≃+* S`. The lax-monoidal unit morphism
`Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.toRingHom) : R → F(S)` is an isomorphism,
where `R,S` denote the tensor-unit modules and `F` restricts scalars along `e`. -/
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

/-- Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, and `M,N : ModuleCat.{s} S`. The
lax-monoidal comparison `Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N :
F(M) ⊗_R F(N) → F(M ⊗_S N)` is an isomorphism. -/
theorem restrictScalarsTensorIsIsoOfRingEquiv (M N : ModuleCat.{s} S) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) := by
  rw [← restrictScalarsTensorIsoOfRingEquiv_hom_eq_μ e M N]
  infer_instance

/-- For commutative rings `R,S : Type s` and a ring equivalence `e : R ≃+* S`, the
restriction-of-scalars functor `F=ModuleCat.restrictScalars e.toRingHom` is monoidal. The
structure uses its lax unit and tensor maps, with inverses supplied by the ring-equivalence
unit and balanced tensor comparisons. -/
@[instance_reducible]
def restrictScalarsMonoidalOfRingEquiv : (ModuleCat.restrictScalars e.toRingHom).Monoidal := by
  let : IsIso (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.toRingHom)) :=
    restrictScalarsUnitIsIsoOfRingEquiv e
  let : ∀ M N, IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) :=
    restrictScalarsTensorIsIsoOfRingEquiv e
  exact Functor.Monoidal.ofLaxMonoidal (ModuleCat.restrictScalars e.toRingHom)


end TensorTransport

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Let `R,S : Type u` be commutative rings, `e : R ≃+* S`, `M : ModuleCat.{u} S`, and
`F=restrictScalars e.toRingHom`. There is a natural isomorphism `F ⋙ tensorLeft_R(F(M)) ≅
tensorLeft_S(M) ⋙ F`. At `N`, its component is the ring-equivalence tensor comparison `F(M)
⊗_R F(N) ≅ F(M ⊗_S N)`. -/
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
