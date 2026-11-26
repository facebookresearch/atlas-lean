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
# Signed currying of full integer tensor–Hom cochains

Let `P` and `Q` be integer chain complexes of right and left `R`-modules, and let `I` be a
cochain complex of additive groups. Write chain degree `p` as cochain degree `-p`. The inner
Hom consists of additive maps from `Q` to `I`, with right `R`-action by domain precomposition;
the outer Hom consists of right `R`-linear maps from `P`. The tensor-total and iterated Hom
cochains use full products over integer degrees.

For a degree-`n` cochain `f`, put `b = a + n` and `d = c + b`. Its curried coordinate on `x ∈
P_(-a)` and `y ∈ Q_(-c)` is `θ(b) • f_(a+c,d)([x ⊗ y])`, where `θ(b) = Int.triangularSign b =
(-1)^(b*(b+1)/2)`. This inner-degree sign is defined for every integer `b`.
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

/-- Signed currying in each integer total-Hom degree.

For a degree-`n` Hom cochain from the negative-index cochain view of `P ⊗_R Q` to `I`, curry
each tensor summand and multiply the inner Hom component of degree `b` by `Int.triangularSign
b`. The result is a degree-`n` cochain from the cochain view of `P` to
`moduleHomCochainComplex R Q I`. -/
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

/-- Evaluation formula for signed tensor–Hom currying.

Let `a + n = b` and `c + b = d`. For `x : P.X (-a)` and `y : Q.X (-c)`, the curried cochain
evaluated in outer coordinate `(a, b)` and inner coordinate `(c, d)` equals
`Int.triangularSign b` times `f.v (a + c) d` evaluated on the total class `[x ⊗ y]` in chain
degree `-(a + c)`. -/
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
