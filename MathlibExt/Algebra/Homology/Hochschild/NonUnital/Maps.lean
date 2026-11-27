/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Basic

/-!
# Algebra and coefficient maps of nonunital Hochschild complexes

Let A and B be nonunital k-algebra rings and M and N coefficient modules with commuting left
and right nonunital actions. A multiplicative k-linear map g : A → B and a k-linear f : M → N
which intertwines both actions define degree maps f ⊗ g^⊗n.

These maps commute with every coefficient Hochschild face and define a morphism of the
semisimplicial bar objects, hence a chain map of their alternating-face complexes. On a pure
tensor, m ⊗ a₁ ⊗ … ⊗ a_n maps to f(m) ⊗ g(a₁) ⊗ … ⊗ g(a_n).

The categorical maps use one carrier universe for A and B and another for M and N; both are
independent of the ground ring's universe.
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

/-- Let k be commutative, A and B nonunital k-algebra rings, M and N k-modules, g : A →ₙₐ[k] B and
f : M →ₗ[k] N. For n : ℕ, degreeMap g f n : M ⊗[k] TensorPower k n A →ₗ[k] N ⊗[k] TensorPower
k n B is TensorProduct.map f (PiTensorProduct.map (fun _ => g)). -/
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

/-- Let k be a commutative ring, A and B nonunital k-algebra rings with k-bilinear multiplication,
and M and N k-modules. Equip M with commuting nonunital actions l_A : A →ₙₐ[k] End_k M and r_A
: Aᵐᵒᵖ →ₙₐ[k] End_k M, and N with commuting actions l_B and r_B. Let g : A →ₙₐ[k] B and f : M
→ₗ[k] N satisfy f(l_A(a)m) = l_B(g(a))f(m) and f(r_A(op a)m) = r_B(op(g(a)))f(m). The degree
maps f ⊗ g^⊗n define barMap from bar(l_A,r_A) to bar(l_B,r_B). Its naturality follows from
commutation with the first right-action face, every inner multiplication face and the last
left-action face. -/
def barMap : bar lA rA hA ⟶ bar lB rB hB :=
  SemiSimplicialObject.homMk (fun n => ModuleCat.ofHom (degreeMap g f n))
    (fun n i => degreeMap_face lA rA hA lB rB hB g f hl hr n i)

/-- Let k be a commutative ring, A and B nonunital k-algebra rings with k-bilinear multiplication,
and M and N k-modules. Equip M with commuting nonunital actions l_A : A →ₙₐ[k] End_k M and r_A
: Aᵐᵒᵖ →ₙₐ[k] End_k M, and N with commuting actions l_B and r_B. Let g : A →ₙₐ[k] B and f : M
→ₗ[k] N satisfy f(l_A(a)m) = l_B(g(a))f(m) and f(r_A(op a)m) = r_B(op(g(a)))f(m). Applying the
semisimplicial alternating-face functor to barMap defines complexMap between the two nonunital
coefficient Hochschild complexes. Its degree-n map is f ⊗ g^⊗n. -/
def complexMap : complex lA rA hA ⟶ complex lB rB hB :=
  (AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex _).map
    (barMap lA rA hA lB rB hB g f hl hr)

/-- Let k be a commutative ring, A and B nonunital k-algebra rings with k-bilinear multiplication,
and M and N k-modules. Equip M with commuting nonunital actions l_A : A →ₙₐ[k] End_k M and r_A
: Aᵐᵒᵖ →ₙₐ[k] End_k M, and N with commuting actions l_B and r_B. Let g : A →ₙₐ[k] B and f : M
→ₗ[k] N satisfy f(l_A(a)m) = l_B(g(a))f(m) and f(r_A(op a)m) = r_B(op(g(a)))f(m). For n : ℕ,
complexMap.f n = ModuleCat.ofHom (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n =>
g))). -/
theorem complexMap_f (n : ℕ) :
    (complexMap lA rA hA lB rB hB g f hl hr).f n =
      ModuleCat.ofHom (TensorProduct.map f
        (PiTensorProduct.map (fun _ : Fin n => (g : A →ₗ[k] B)))) := rfl

/-- Let k be a commutative ring, A and B nonunital k-algebra rings with k-bilinear multiplication,
and M and N k-modules. Equip M with commuting nonunital actions l_A : A →ₙₐ[k] End_k M and r_A
: Aᵐᵒᵖ →ₙₐ[k] End_k M, and N with commuting actions l_B and r_B. Let g : A →ₙₐ[k] B and f : M
→ₗ[k] N satisfy f(l_A(a)m) = l_B(g(a))f(m) and f(r_A(op a)m) = r_B(op(g(a)))f(m). For n : ℕ, m
: M and a : Fin n → A, complexMap.f n sends m ⊗ₜ[k] tprod a to f(m) ⊗ₜ[k] tprod(i ↦ g(a_i)). -/
theorem complexMap_f_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    ((complexMap lA rA hA lB rB hB g f hl hr).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      f m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => g (a i)) :=
  degreeMap_tprod g f n m a

end ModuleCat.Algebra.Hochschild.NonUnital
