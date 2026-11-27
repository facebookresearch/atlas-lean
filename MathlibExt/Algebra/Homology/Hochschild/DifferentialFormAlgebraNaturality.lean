/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormNaturality
public import MathlibExt.Algebra.Homology.Hochschild.Maps
public import MathlibExt.LinearAlgebra.ExteriorPower.Semilinear

/-!
# Algebra naturality of coefficient differential forms

Let k be a commutative ring, g : A → B a unital homomorphism of
commutative k-algebras, and f : M → N a k-linear coefficient map with
f(am) = g(a)f(m). The g-semilinear map of universal differentials sends
da to d(g(a)). Together with f it defines
G_n : M ⊗_A ∧_A^n Ω_{A/k} → N ⊗_B ∧_B^n Ω_{B/k},
m ⊗ (da_1 ∧ ⋯ ∧ da_n) ↦ f(m) ⊗ (d(g(a_1)) ∧ ⋯ ∧ d(g(a_n))).
The map is g-semilinear and is k-linear because g fixes ground scalars.

The underlying tensor maps allow independent ground, algebra and
coefficient universes. For the chain maps, A,B occupy one algebra
universe and M,N one coefficient universe. In their common k-module
category, the lifted G_n define a map of zero-differential form complexes
and satisfy η_B C(g,f) = G η_A for the Hochschild form projections.

Reference: J.-L. Loday, Cyclic Homology, §3.2.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe uk uA uB uM uN

namespace ModuleCat.Algebra.Hochschild.Symmetric

section Raw

variable {k : Type uk} [CommRing k]
  {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [SMulCommClass k A M] [SMulCommClass k B N]
  [IsScalarTower k A M] [IsScalarTower k B N]

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
The map Ω(g) : Ω_{A/k} → Ω_{B/k} is g-semilinear and
sends da to d(g(a)). Its scalar law is Ω(g)(aω) = g(a)Ω(g)(ω). -/
def kaehlerAlgebraMap (g : A →ₐ[k] B) :
    KaehlerDifferential k A →ₛₗ[g.toRingHom] KaehlerDifferential k B := by
  letI : Algebra A B := g.toRingHom.toAlgebra
  letI : IsScalarTower k A B := inferInstance
  let F := KaehlerDifferential.map k k A B
  exact
    { toFun := F
      map_add' := F.map_add
      map_smul' := F.map_smul }

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
For every a ∈ A, the map of Kähler differentials satisfies
Ω(g)(d_A a) = d_B(g(a)). -/
theorem kaehlerAlgebraMap_D (g : A →ₐ[k] B) (a : A) :
    kaehlerAlgebraMap g (KaehlerDifferential.D k A a) =
      KaehlerDifferential.D k B (g a) := by
  let _ : Algebra A B := g.toRingHom.toAlgebra
  let _ : IsScalarTower k A B := inferInstance
  exact KaehlerDifferential.map_D k k A B a

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
The same function f is g-semilinear as a map of the A-module M
to the B-module N: its scalar law is precisely f(am) = g(a)f(m). -/
def algebraCoefficientSemilinearMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) : M →ₛₗ[g.toRingHom] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := hf

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
Writing Ω_A^n = ∧_A^n Ω_{A/k} and Ω_B^n similarly, the map
G_n : M ⊗_A Ω_A^n → N ⊗_B Ω_B^n is g-semilinear.
It sends m ⊗ ω to f(m) ⊗ (∧^n Ω(g))(ω). -/
def coefficientFormAlgebraSemilinearMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    M ⊗[A] (⋀[A]^n (KaehlerDifferential k A)) →ₛₗ[g.toRingHom]
      N ⊗[B] (⋀[B]^n (KaehlerDifferential k B)) :=
  TensorProduct.map (algebraCoefficientSemilinearMap g f hf)
    (exteriorPower.mapSemilinear g.toRingHom (kaehlerAlgebraMap g) n)

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
The g-semilinear form map G_n is also k-linear, with the same
values m ⊗ ω ↦ f(m) ⊗ (∧^n Ω(g))(ω).
Indeed g carries each ground scalar in A to that same scalar in B. -/
def coefficientFormAlgebraLinearMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    M ⊗[A] (⋀[A]^n (KaehlerDifferential k A)) →ₗ[k]
      N ⊗[B] (⋀[B]^n (KaehlerDifferential k B)) where
  toFun := coefficientFormAlgebraSemilinearMap g f hf n
  map_add' := map_add _
  map_smul' c x := by
    rw [← IsScalarTower.algebraMap_smul A c x, map_smulₛₗ]
    have hgc : g.toRingHom (algebraMap k A c) = algebraMap k B c := g.commutes c
    rw [hgc, IsScalarTower.algebraMap_smul B]
    rfl

omit [SMulCommClass k A M] [SMulCommClass k B N] in
/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
For m ∈ M and a : Fin n → A, the coefficient form map sends
m ⊗_A (da_0 ∧ ⋯ ∧ da_{n-1}) to
f(m) ⊗_B (d(g(a_0)) ∧ ⋯ ∧ d(g(a_{n-1}))). -/
theorem coefficientFormAlgebraLinearMap_differentialWord
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (m : M) (a : Fin n → A) :
    coefficientFormAlgebraLinearMap g f hf n
      (m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (a j))) =
        f m ⊗ₜ[B] exteriorPower.ιMulti B n (fun j => KaehlerDifferential.D k B (g (a j))) := by
  change TensorProduct.map (algebraCoefficientSemilinearMap g f hf)
    (exteriorPower.mapSemilinear g.toRingHom (kaehlerAlgebraMap g) n) _ = _
  rw [TensorProduct.map_tmul, exteriorPower.mapSemilinear_ιMulti]
  simp only [kaehlerAlgebraMap_D]
  rfl

end Raw

section Complexes

variable (k : Type uk) [CommRing k]
  {A B : Type uA} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {M N : Type uM} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [SMulCommClass k A M] [SMulCommClass k B N]
  [IsScalarTower k A M] [IsScalarTower k B N]

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
For the categorical chain maps, A,B share universe u_A and M,N
share universe u_M; all objects lie in ModuleCat over k at
max{u_k,u_A,u_M}.
The maps up ∘ G_n ∘ down define a chain map between the
zero-differential coefficient form complexes for (A,M) and (B,N). -/
def coefficientFormAlgebraComplexMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    coefficientDifferentialFormComplex k A M ⟶ coefficientDifferentialFormComplex k B N where
  f n := ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{uk} (N ⊗[B] (⋀[B]^n (KaehlerDifferential k B))) ≃ₗ[k]
      N ⊗[B] (⋀[B]^n (KaehlerDifferential k B))).symm.toLinearMap.comp
        ((coefficientFormAlgebraLinearMap g f hf n).comp
          (ULift.moduleEquiv : ULift.{uk} (M ⊗[A] (⋀[A]^n (KaehlerDifferential k A))) ≃ₗ[k]
            M ⊗[A] (⋀[A]^n (KaehlerDifferential k A))).toLinearMap))
  comm' i j _h := by
    rw [coefficientDifferentialFormComplex_d_eq_zero,
      coefficientDifferentialFormComplex_d_eq_zero]
    exact CategoryTheory.Limits.comp_zero.trans CategoryTheory.Limits.zero_comp.symm

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
For the categorical chain maps, A,B share universe u_A and M,N
share universe u_M; all objects lie in ModuleCat over k at
max{u_k,u_A,u_M}.
The coefficient-first tensor maps
m ⊗ a_1 ⊗ ⋯ ⊗ a_n ↦ f(m) ⊗ g(a_1) ⊗ ⋯ ⊗ g(a_n)
define a Hochschild chain map C_*(A,M) → C_*(B,N). -/
def originalAlgebraCoefficientChainMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) : chainComplex k A M ⟶ chainComplex k B N := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  letI := opModule B N
  letI := actionsComm B N
  letI := kOpComm k B N
  letI := kOpTower k B N
  exact ModuleCat.Algebra.Hochschild.mapInSameUniverse g.toNonUnitalAlgHom f hf
    (by intro a m; exact hf a m)

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
For the categorical chain maps, A,B share universe u_A and M,N
share universe u_M; all objects lie in ModuleCat over k at
max{u_k,u_A,u_M}.
In degree n, the Hochschild map is the k-linear tensor operator
f ⊗_k g^{⊗n} on M ⊗[k] A^{⊗n}. -/
theorem originalAlgebraCoefficientChainMap_f
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    ((originalAlgebraCoefficientChainMap k g f hf).f n).hom =
      ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n := by
  let _ := opModule A M
  let _ := actionsComm A M
  let _ := kOpComm k A M
  let _ := kOpTower k A M
  let _ := opModule B N
  let _ := actionsComm B N
  let _ := kOpComm k B N
  let _ := kOpTower k B N
  have hleft : ∀ a m, f (a • m) = g.toNonUnitalAlgHom a • f m := by
    intro a m
    exact hf a m
  have hright : ∀ a m, f (MulOpposite.op a • m) = MulOpposite.op (g.toNonUnitalAlgHom a) • f m := by
    intro a m
    exact hf a m
  change ((ModuleCat.Algebra.Hochschild.mapInSameUniverse g.toNonUnitalAlgHom f hleft hright).f n).hom = _
  exact ModuleCat.Algebra.Hochschild.mapInSameUniverse_f g.toNonUnitalAlgHom f hleft hright n

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
For the categorical chain maps, A,B share universe u_A and M,N
share universe u_M; all objects lie in ModuleCat over k at
max{u_k,u_A,u_M}.
On an elementary Hochschild tensor, the chain map has value
m ⊗ tprod(a) ↦ f(m) ⊗ tprod(j ↦ g(a_j)). -/
theorem originalAlgebraCoefficientChainMap_tprod
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (m : M) (a : Fin n → A) :
    ((originalAlgebraCoefficientChainMap k g f hf).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        f m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => g (a j)) := by
  have h := originalAlgebraCoefficientChainMap_f k g f hf n
  exact (LinearMap.congr_fun h (m ⊗ₜ[k] PiTensorProduct.tprod k a)).trans
    (ModuleCat.Algebra.Hochschild.linearMap_tprod g.toNonUnitalAlgHom f n m a)

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
For the categorical chain maps, A,B share universe u_A and M,N
share universe u_M; all objects lie in ModuleCat over k at
max{u_k,u_A,u_M}.
The degree-n form-complex map sends
ULift(m ⊗_A (da_0 ∧ ⋯ ∧ da_{n-1})) to
ULift(f(m) ⊗_B (d(g(a_0)) ∧ ⋯ ∧ d(g(a_{n-1})))). -/
theorem coefficientFormAlgebraComplexMap_word
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (m : M) (a : Fin n → A) :
    ((coefficientFormAlgebraComplexMap k g f hf).f n).hom
      (ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (a j)))) =
      ULift.up (f m ⊗ₜ[B] exteriorPower.ιMulti B n
        (fun j => KaehlerDifferential.D k B (g (a j)))) :=
  congrArg ULift.up (coefficientFormAlgebraLinearMap_differentialWord g f hf n m a)

/-- Let k be commutative, A,B commutative unital k-algebras,
and g : A → B a unital k-algebra homomorphism.
Let M,N be compatible modules over A,B and f : M → N k-linear
with f(am) = g(a)f(m) for all a ∈ A and m ∈ M.
For the categorical chain maps, A,B share universe u_A and M,N
share universe u_M; all objects lie in ModuleCat over k at
max{u_k,u_A,u_M}.
Let η_A,η_B be the Hochschild projections to the lifted
zero-differential form complexes. The algebra/coefficient square is
η_B C(g,f) = G η_A. Its degree maps use the unscaled exterior
word of universal differentials. -/
@[reassoc]
theorem coefficientDifferentialFormChainMap_algebra
    (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    originalAlgebraCoefficientChainMap k g f hf ≫ coefficientDifferentialFormChainMap k B N =
      coefficientDifferentialFormChainMap k A M ≫ coefficientFormAlgebraComplexMap k g f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  change ((coefficientDifferentialFormChainMap k B N).f n).hom
    (((originalAlgebraCoefficientChainMap k g f hf).f n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    ((coefficientFormAlgebraComplexMap k g f hf).f n).hom
      (((coefficientDifferentialFormChainMap k A M).f n).hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  rw [originalAlgebraCoefficientChainMap_tprod, coefficientDifferentialFormChainMap_tprod,
    coefficientDifferentialFormChainMap_tprod, coefficientFormAlgebraComplexMap_word]

end Complexes

end ModuleCat.Algebra.Hochschild.Symmetric
