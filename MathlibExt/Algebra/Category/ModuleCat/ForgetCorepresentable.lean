/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Yoneda

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace ModuleCat

/-- Evaluation at one identifies maps from the regular module with elements,
linearly over every commuting scalar action. -/
def regularHomEquiv (R : Type u) [Ring R] (S : Type w) [Semiring S]
    (M : ModuleCat.{u} R) [Module S M] [SMulCommClass R S M] :
    (ModuleCat.of R R ⟶ M) ≃ₗ[S] M :=
  ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R S M)

@[simp]
theorem regularHomEquiv_apply (R : Type u) [Ring R] (S : Type w) [Semiring S]
    (M : ModuleCat.{u} R) [Module S M] [SMulCommClass R S M]
    (f : ModuleCat.of R R ⟶ M) :
    regularHomEquiv R S M f = f 1 := rfl

@[simp]
theorem regularHomEquiv_symm_apply_apply (R : Type u) [Ring R]
    (S : Type w) [Semiring S] (M : ModuleCat.{u} R)
    [Module S M] [SMulCommClass R S M] (x : M) (r : R) :
    ((regularHomEquiv R S M).symm x : ModuleCat.of R R ⟶ M) r = r • x := rfl

/-- The regular module corepresents the underlying-type functor. -/
noncomputable def coyonedaObjIsoForget (R : Type u) [Ring R] :
    coyoneda.obj (op (ModuleCat.of R R)) ≅ forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun M => (regularHomEquiv R ℕ M).toEquiv.toIso)
    (fun {M N} f => by ext g; rfl)

instance forget_isCorepresentable (R : Type u) [Ring R] :
    (forget (ModuleCat.{u} R)).IsCorepresentable :=
  Functor.IsCorepresentable.mk' (coyonedaObjIsoForget R)

theorem isSeparator_regular (R : Type u) [Ring R] :
    IsSeparator (ModuleCat.of R R) := by
  rw [isSeparator_iff_faithful_coyoneda_obj]
  exact Functor.Faithful.of_iso (coyonedaObjIsoForget R).symm

noncomputable instance isFinitelyPresentable_regular
    (R : Type u) [Ring R] [UnivLE.{w, u}] :
    IsFinitelyPresentable.{w} (ModuleCat.of R R) := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  let _ : PreservesFilteredColimitsOfSize.{w, w}
      (forget (ModuleCat.{u} R)) :=
    preservesFilteredColimitsOfSize_of_univLE (forget (ModuleCat.{u} R))
  constructor
  intro J
  exact preservesColimitsOfShape_of_natIso (J := J)
    (coyonedaObjIsoForget R).symm

end ModuleCat
