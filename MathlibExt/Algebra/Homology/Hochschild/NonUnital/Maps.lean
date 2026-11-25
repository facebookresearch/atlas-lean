/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Basic

/-!
# Maps of the nonunital coefficient Hochschild complex

The degree maps are the native tensor maps. Compatibility with the left and right representations proves every face square, and semisimplicial injection generation supplies full naturality. The chain map is
the map of the alternating complex. No unit-preserving map is used.

The native categorical maps use a common algebra universe and a common
coefficient universe; these remain independent of each other and of the ground
ring. No equality of algebra and coefficient carrier universes is imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable {k : Type u} [CommRing k]
  {A B : Type v} [NonUnitalRing A] [NonUnitalRing B] [Module k A] [Module k B]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [IsScalarTower k B B] [SMulCommClass k B B]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
  (lA : A →ₙₐ[k] Module.End k M) (rA : Aᵐᵒᵖ →ₙₐ[k] Module.End k M)
  (hA : ∀ a b m, lA a (rA b m) = rA b (lA a m))
  (lB : B →ₙₐ[k] Module.End k N) (rB : Bᵐᵒᵖ →ₙₐ[k] Module.End k N)
  (hB : ∀ a b m, lB a (rB b m) = rB b (lB a m))
  (g : A →ₙₐ[k] B) (f : M →ₗ[k] N)
  (hl : ∀ a m, f (lA a m) = lB (g a) (f m))
  (hr : ∀ a m, f (rA (MulOpposite.op a) m) = rB (MulOpposite.op (g a)) (f m))

/-- The native tensor map induced by the coefficient map and the nonunital algebra map. -/
def degreeMap (n : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[k] N ⊗[k] TensorPower k n B :=
  TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => (g : A →ₗ[k] B)))

omit [IsScalarTower k A A] [SMulCommClass k A A] [IsScalarTower k B B]
  [SMulCommClass k B B] in
theorem degreeMap_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    degreeMap g f n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      f m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => g (a i)) := by
  simp only [degreeMap, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  rfl

include hl hr in
theorem degreeMap_face (n : ℕ) (i : Fin (n + 2)) :
    face lA rA hA n i ≫ ModuleCat.ofHom (degreeMap g f n) =
      ModuleCat.ofHom (degreeMap g f (n + 1)) ≫ face lB rB hB n i := by
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun q => ?_) j) i
  · rw [face_first_tprod, degreeMap_tprod, degreeMap_tprod, face_first_tprod, hr]
    rfl
  · simp only [Fin.succ_last]
    rw [face_last_tprod, degreeMap_tprod, degreeMap_tprod, face_last_tprod, hl]
    rfl
  · rw [face_inner_tprod, degreeMap_tprod, degreeMap_tprod, face_inner_tprod]
    congr 2
    funext j
    simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent]
    split_ifs <;> simp only [map_mul]

/-- A morphism of the semisimplicial bars, from the two action squares. -/
def barMap : bar lA rA hA ⟶ bar lB rB hB :=
  SemiSimplicialObject.homMk (fun n => ModuleCat.ofHom (degreeMap g f n))
    (fun n i => degreeMap_face lA rA hA lB rB hB g f hl hr n i)

/-- The chain map induced by the native alternating-face functor. -/
def complexMap : complex lA rA hA ⟶ complex lB rB hB :=
  (AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex _).map
    (barMap lA rA hA lB rB hB g f hl hr)

/-- Its components are the tensor maps, with no coordinate choice. -/
theorem complexMap_f (n : ℕ) :
    (complexMap lA rA hA lB rB hB g f hl hr).f n =
      ModuleCat.ofHom (TensorProduct.map f
        (PiTensorProduct.map (fun _ : Fin n => (g : A →ₗ[k] B)))) := rfl

/-- The map retains the literal coefficient/algebra generator values. -/
theorem complexMap_f_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    ((complexMap lA rA hA lB rB hB g f hl hr).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      f m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => g (a i)) :=
  degreeMap_tprod g f n m a

end ModuleCat.Algebra.Hochschild.NonUnital
