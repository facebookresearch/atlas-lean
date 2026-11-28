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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Basic
public import MathlibExt.Algebra.Homology.HomComplex.LinearFunctor

/-!
# R-linear currying from a tensor coproduct into full Hom products

Let R be a commutative ring and P,Q,I integer R-module cochain complexes in a common carrier
universe. A degree-n cochain f : P⊗Q → I gives a degree-n cochain P → Hom(Q,I) by currying
each tensor summand and assembling all inner Hom coordinates as a product.

Its value on x∈P^p and y∈Q^q is f_{p+q,d}([x,y]), where p+n=b and q+b=d. The construction is
R-linear and uses full products, without support bounds or finiteness assumptions.
-/

@[expose] public section
noncomputable section

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]
  (P Q I : CochainComplex (ModuleCat.{v} R) ℤ)

local instance : HomologicalComplex.HasMapBifunctor P Q
    (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- Let R be a commutative ring and P,Q integer R-module cochain complexes in universe v. For
n,p,q ∈ ℤ with p+n=q, evaluation at the (p,q) coordinate gives an R-linear map C^n(P,Q) →
Hom_R(P^p,Q^q). The cochain object C^n(P,Q) is the full product of all degree-n Hom
coordinates. -/
def productEval (n p q : ℤ) (hpq : p + n = q) :
    Cochain P Q n →ₗ[R] (P.X p ⟶ Q.X q) where
  toFun z := z.v p q hpq
  map_add' z z' := Cochain.add_v z z' p q hpq
  map_smul' r z := Cochain.smul_v r z p q hpq

@[simp]
theorem productEval_apply (n p q : ℤ) (hpq : p + n = q) (z : Cochain P Q n) :
    productEval R P Q n p q hpq z = z.v p q hpq := rfl

/-- For a commutative ring R and integer R-module cochain complexes P,Q,I in universe v, a
degree-n cochain f : P⊗Q → I determines a degree-n cochain P → Hom(Q,I). Its component P^p →
Hom(Q,I)^b, where p+n=b, has inner coordinate at q+b=d given by tensor currying of the summand
map P^p⊗Q^q → I^d. All inner coordinates are assembled by the full product. -/
def curryCochain (n : ℤ) (f : Cochain (complexAt R P Q) I n) :
    Cochain P (linearComplex R Q I) n :=
  Cochain.mk (fun p b hpb => by
    let component : ∀ T : Triplet b,
        P.X p →ₗ[R] (Q.X T.p ⟶ I.X T.q) := fun T =>
      (ModuleCat.homLinearEquiv (R := R) (S := R)
        (M := Q.X T.p) (N := I.X T.q)).symm.toLinearMap.comp
          (TensorProduct.curry
            ((HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R)
              (.up ℤ) p T.p (p + T.p) rfl ≫
                f.v (p + T.p) T.q (by have := T.hpq; omega)).hom))
    exact ModuleCat.ofHom (LinearMap.pi component))

/-- Let R be a commutative ring, P,Q,I integer cochain complexes in ModuleCat.{v} R, and f a
degree-n cochain P⊗Q → I. For p+n=b and q+b=d, the curried cochain satisfies
(curry(f)_{p,b}(x))_{q,d}(y)=f_{p+q,d}([x,y]), where [x,y] is the canonical tensor-total
summand representative. No extra sign occurs in this cochain evaluation formula. -/
theorem curryCochain_v (n : ℤ) (f : Cochain (complexAt R P Q) I n)
    (p b : ℤ) (hpb : p + n = b) (q d : ℤ) (hqd : q + b = d)
    (x : P.X p) (y : Q.X q) :
    ((((curryCochain R P Q I n f).v p b hpb).hom x).v q d hqd).hom y =
      (f.v (p + q) d (by omega)).hom (mkAt R P Q p q (p + q) rfl x y) := rfl

/-- For a commutative ring R and integer R-module cochain complexes P,Q,I in a common universe v,
the operation curryCochain defines an R-linear map C^n(P⊗Q,I) → C^n(P,Hom(Q,I)) for every n ∈
ℤ. Its value is the summandwise tensor currying into the full Hom product, with no boundedness
condition. -/
def curryLinear (n : ℤ) :
    Cochain (complexAt R P Q) I n →ₗ[R] Cochain P (linearComplex R Q I) n where
  toFun := curryCochain R P Q I n
  map_add' f g := by
    apply Cochain.ext
    intro p b hpb
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Cochain.ext
    intro q d hqd
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply, curryCochain_v]
    rfl
  map_smul' r f := by
    apply Cochain.ext
    intro p b hpb
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Cochain.ext
    intro q d hqd
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [RingHom.id_apply, Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply,
      curryCochain_v]
    rfl

end CochainComplex.ModuleTensor
