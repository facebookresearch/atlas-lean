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

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor transport along a ring equivalence

Scalar restriction along a ring equivalence preserves the module carriers.
The semilinear tensor equivalence identifies their balanced tensors over
the two rings. The ring universes and the common module universe are
independent; the resulting module universe contains both rings.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat.RingEquivUniverse

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S)


/-- The actual restriction-of-scalars tensor comparison, built from the
two native semilinear identity carrier equivalences. -/
def tensorIso (M N : ModuleCat.{max u v w} S) :
    ModuleCat.of R (((ModuleCat.restrictScalars.{max u v w} e.toRingHom).obj M) ⊗[R] ((ModuleCat.restrictScalars.{max
      u v w} e.toRingHom).obj N)) ≅
      (ModuleCat.restrictScalars.{max u v w} e.toRingHom).obj (ModuleCat.of S (M ⊗[S] N)) := by
  let M₀ := (ModuleCat.restrictScalars.{max u v w} e.toRingHom).obj M
  let N₀ := (ModuleCat.restrictScalars.{max u v w} e.toRingHom).obj N
  let Z₀ := ModuleCat.of R (M₀ ⊗[R] N₀)
  let Z₁ := (ModuleCat.restrictScalars.{max u v w} e.toRingHom).obj (ModuleCat.of S (M ⊗[S] N))
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.symm e.toRingHom e.symm.toRingHom
  let f : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) M₀ M :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) N₀ N :=
    { toFun := id
      invFun := id
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
  exact l.toModuleIso

theorem tensorIso_hom_tmul (M N : ModuleCat.{max u v w} S)
    (m : (ModuleCat.restrictScalars.{max u v w} e.toRingHom).obj M)
    (n : (ModuleCat.restrictScalars.{max u v w} e.toRingHom).obj N) :
    (tensorIso e M N).hom (m ⊗ₜ[R] n) = m ⊗ₜ[S] n := rfl

theorem tensorIso_inv_tmul (M N : ModuleCat.{max u v w} S) (m : M) (n : N) :
    (tensorIso e M N).inv (m ⊗ₜ[S] n) =
      (show (ModuleCat.restrictScalars.{max u v w} e.toRingHom).obj M from m) ⊗ₜ[R]
        (show (ModuleCat.restrictScalars.{max u v w} e.toRingHom).obj N from n) := rfl

/-- The canonical comparison is natural in both original module maps. -/
@[reassoc]
theorem tensorIso_naturality {M N M' N' : ModuleCat.{max u v w} S}
    (f : M ⟶ M') (g : N ⟶ N') :
    ModuleCat.ofHom (TensorProduct.map ((ModuleCat.restrictScalars.{max u v w} e.toRingHom).map f).hom
      ((ModuleCat.restrictScalars.{max u v w} e.toRingHom).map g).hom) ≫
      (tensorIso e M' N').hom =
    (tensorIso e M N).hom ≫ (ModuleCat.restrictScalars.{max u v w} e.toRingHom).map (ModuleCat.ofHom
      (TensorProduct.map f.hom g.hom)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m n
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, TensorProduct.map_tmul,
    tensorIso_hom_tmul]
  rfl

end ModuleCat.RingEquivUniverse
