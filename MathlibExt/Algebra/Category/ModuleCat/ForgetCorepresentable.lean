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

/-!
# Regular modules as corepresenting objects

For a ring R in universe u and an R-module M in the same carrier universe, evaluation at 1
identifies Hom_R(R,M) with M. The inverse sends x to the map r ↦ r·x. This equivalence is
linear over any semiring S whose action on M commutes with the R-action, with S in its
separately stated universe.

The equivalences are natural in M, so the regular module R corepresents the forgetful functor
to types and is a separator. At an indexing universe w with UnivLE w u, the regular module is
finitely presentable.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace ModuleCat

/-- Evaluation at one for maps from the regular module.

For a ring R, an R-module M and a commuting semiring S-action on M, the map f ↦ f(1) is an
S-linear equivalence Hom_R(R,M) ≃ M. -/
def regularHomEquiv (R : Type u) [Ring R] (S : Type w) [Semiring S]
    (M : ModuleCat.{u} R) [Module S M] [SMulCommClass R S M] :
    (ModuleCat.of R R ⟶ M) ≃ₗ[S] M :=
  ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R S M)

/-- The forward regular-module evaluation formula.

The regular Hom equivalence sends an R-linear morphism f : R → M to f(1). -/
@[simp]
theorem regularHomEquiv_apply (R : Type u) [Ring R] (S : Type w) [Semiring S]
    (M : ModuleCat.{u} R) [Module S M] [SMulCommClass R S M]
    (f : ModuleCat.of R R ⟶ M) :
    regularHomEquiv R S M f = f 1 := rfl

/-- The inverse regular-module evaluation formula.

The inverse equivalence sends x ∈ M to the R-linear map r ↦ r·x. -/
@[simp]
theorem regularHomEquiv_symm_apply_apply (R : Type u) [Ring R]
    (S : Type w) [Semiring S] (M : ModuleCat.{u} R)
    [Module S M] [SMulCommClass R S M] (x : M) (r : R) :
    ((regularHomEquiv R S M).symm x : ModuleCat.of R R ⟶ M) r = r • x := rfl

/-- The regular module corepresents the underlying-type functor.

The covariant Hom functor Hom_R(R,−) is naturally isomorphic to the forgetful functor from
ModuleCat R to types, through evaluation at 1. -/
noncomputable def coyonedaObjIsoForget (R : Type u) [Ring R] :
    coyoneda.obj (op (ModuleCat.of R R)) ≅ forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun M => (regularHomEquiv R ℕ M).toEquiv.toIso)
    (fun {M N} f => by ext g; rfl)

/-- Corepresentability of forgetting module structure.

The underlying-type functor on ModuleCat R is corepresentable by the regular module R. -/
instance forget_isCorepresentable (R : Type u) [Ring R] :
    (forget (ModuleCat.{u} R)).IsCorepresentable :=
  Functor.IsCorepresentable.mk' (coyonedaObjIsoForget R)

/-- The regular module is a separator.

Maps from R distinguish morphisms of R-modules: evaluation of such maps at 1 gives every
coefficient element. -/
theorem isSeparator_regular (R : Type u) [Ring R] :
    IsSeparator (ModuleCat.of R R) := by
  rw [isSeparator_iff_faithful_coyoneda_obj]
  exact Functor.Faithful.of_iso (coyonedaObjIsoForget R).symm

/-- Finite presentability of the regular module.

For indexing universe w with UnivLE w u, the regular module over a ring R in universe u is
finitely presentable at size w, since its Hom functor is the filtered-colimit-preserving
underlying-type functor. -/
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
