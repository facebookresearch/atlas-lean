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

public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor
public import MathlibExt.Algebra.Homology.ChainComplex.ModuleHomCochainComplex
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.GroupAdjunction

/-!
# Actual signed currying on the full tensor-total Hom cochains

All cochains are the native products. Currying is the existing balanced
tensor–Hom map, applied to each original tensor summand. The inner total
degree supplies the actual triangular sign required by the source convention.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ChainComplex.BalancedTensor

universe u v

variable (R : Type u) [Ring R]
  (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
  (Q : ChainComplex (ModuleCat.{v} R) ℤ)
  (I : CochainComplex AddCommGrpCat.{v} ℤ)

local notation "HI" => moduleHomCochainComplex R Q I

/-- The original sum-to-product currying map, with the required inner-degree sign. -/
def curryCochain (n : ℤ) (f : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (complex R P Q)) I n) :
    CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P) HI n :=
  CochainComplex.HomComplex.Cochain.mk (fun a b hab => by
    let homModules : ∀ T : CochainComplex.HomComplex.Triplet b,
        Module Rᵐᵒᵖ ((ChainComplex.moduleHomDomainCochain R Q).X T.p ⟶ I.X T.q) := fun T =>
      homGroupModule R (Q.X (-T.p)) (I.X T.q)
    letI := homModules
    letI := homCochainModule R Q I b
    let component : ∀ T : CochainComplex.HomComplex.Triplet b,
        P.X (-a) →ₗ[Rᵐᵒᵖ] ((ChainComplex.moduleHomDomainCochain R Q).X T.p ⟶ I.X T.q) := fun T =>
      Int.triangularSign b • ModuleCat.BalancedTensor.groupCurry R
        (P.X (-a)) (Q.X (-T.p)) (I.X T.q)
        (HomologicalComplex.ιMapBifunctor P Q
          (ModuleCat.BalancedTensor.groupBifunctor R) (ComplexShape.down ℤ)
          (-a) (-T.p) (-(a + T.p))
            (by change -a + -T.p = -(a + T.p); omega) ≫
          f.v (a + T.p) T.q (by have := T.hpq; omega))
    exact ModuleCat.ofHom (LinearMap.pi component))

/-- Every native product component has the original pure-tensor value and the actual sign. -/
theorem curryCochain_v (n : ℤ) (f : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (complex R P Q)) I n)
    (a b : ℤ) (hab : a + n = b) (c d : ℤ) (hcd : c + b = d)
    (x : P.X (-a)) (y : Q.X (-c)) :
    ((((curryCochain R P Q I n f).v a b hab).hom x).v c d hcd).hom y =
      Int.triangularSign b • (f.v (a + c) d (by omega)).hom
        (mk R P Q (-a) (-c) (-(a + c)) (by omega) x y) := by
  let := homCochainModule R Q I b
  let := homGroupModule R (Q.X (-c)) (I.X d)
  change (Int.triangularSign b • ModuleCat.BalancedTensor.groupCurry R
    (P.X (-a)) (Q.X (-c)) (I.X d)
      (HomologicalComplex.ιMapBifunctor P Q
        (ModuleCat.BalancedTensor.groupBifunctor R) (ComplexShape.down ℤ)
          (-a) (-c) (-(a + c))
            (by change -a + -c = -(a + c); omega) ≫
        f.v (a + c) d (by omega)) x).hom y = _
  simp only [Units.smul_def, AddCommGrpCat.hom_zsmul,
    AddMonoidHom.zsmul_apply]
  rw [ModuleCat.BalancedTensor.groupCurry_mk]
  rfl

end ChainComplex.BalancedTensor
