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
# Actual R-linear currying from the sum tensor into full native Hom products

The cochains and scalar structures are the existing native linear Hom complexes.
Each component is the native tensor curry of the original summand and original
cochain component. No new product, differential or comparison model is used.
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

/-- Evaluation on the original full Hom product is R-linear. -/
def productEval (n p q : ℤ) (hpq : p + n = q) :
    Cochain P Q n →ₗ[R] (P.X p ⟶ Q.X q) where
  toFun z := z.v p q hpq
  map_add' z z' := Cochain.add_v z z' p q hpq
  map_smul' r z := Cochain.smul_v r z p q hpq

@[simp]
theorem productEval_apply (n p q : ℤ) (hpq : p + n = q) (z : Cochain P Q n) :
    productEval R P Q n p q hpq z = z.v p q hpq := rfl

/-- The actual degree-n curry map, retaining both original factor values. -/
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

/-- Every product component has the original pure tensor value, in every integer degree. -/
theorem curryCochain_v (n : ℤ) (f : Cochain (complexAt R P Q) I n)
    (p b : ℤ) (hpb : p + n = b) (q d : ℤ) (hqd : q + b = d)
    (x : P.X p) (y : Q.X q) :
    ((((curryCochain R P Q I n f).v p b hpb).hom x).v q d hqd).hom y =
      (f.v (p + q) d (by omega)).hom (mkAt R P Q p q (p + q) rfl x y) := rfl

/-- The actual sum-to-product curry is bundled with its earned R-linearity. -/
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
