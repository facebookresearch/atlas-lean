/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import MathlibExt.Algebra.Category.ModuleCat.MonoidAction
public import MathlibExt.Algebra.Homology.SpectralObject.Functor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Integral monoid actions on actual spectral objects

A representation by endomorphisms of an abelian-group-valued spectral object
gives categorical monoid actions on its original interval groups. Applying
`Action.monoidAlgebraModuleFunctor` to these actions and their equivariant maps
supplies the integral monoid-algebra scalar actions and the actual linear
interval and connecting maps. Their exactness is reflected by the
underlying-group functor.
-/

public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ComposableArrows

universe v u w t

namespace CategoryTheory.Abelian.SpectralObject

variable {ι : Type t} [Category.{v} ι] {M : Type w} [Monoid M]
  (E : SpectralObject AddCommGrpCat.{u} ι) (ρ : M →* End E)

/-- The categorical monoid action on one original interval homology group. -/
@[expose]
def intervalAction (n : ℤ) (I : ComposableArrows ι 1) :
    Action AddCommGrpCat.{u} M where
  V := (E.H n).obj I
  ρ :=
    { toFun := fun a => .of (((ρ a).asHom.hom n).app I)
      map_one' := by
        rw [ρ.map_one]
        rfl
      map_mul' a b := by
        rw [ρ.map_mul, End.mul_asHom]
        rfl }

/-- The canonical integral representation of the original interval action. -/
@[expose]
def intervalRepresentation (n : ℤ) (I : ComposableArrows ι 1) :
    Representation ℤ M ((E.H n).obj I) :=
  Action.intRepresentation M (E.intervalAction ρ n I)

/-- The constructed integral monoid-algebra module on the original carrier. -/
@[expose]
def monoidModuleInterval (n : ℤ) (I : ComposableArrows ι 1) :
    ModuleCat.{u} (MonoidAlgebra ℤ M) :=
  (Action.monoidAlgebraModuleFunctor M).obj (E.intervalAction ρ n I)

/-- The additive comparison with the exact original interval group is the
canonical identity comparison of the representation type synonym. -/
def monoidModuleIntervalForgetIso (n : ℤ) (I : ComposableArrows ι 1) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat).obj
        (E.monoidModuleInterval ρ n I) ≅ (E.H n).obj I :=
  (Action.monoidAlgebraModuleForgetIso M).app (E.intervalAction ρ n I)

/-- The interval forget comparison sends each element by the canonical
representation equivalence on the original carrier. -/
theorem monoidModuleIntervalForgetIso_hom_apply
    (n : ℤ) (I : ComposableArrows ι 1)
    (x : E.monoidModuleInterval ρ n I) :
    (E.monoidModuleIntervalForgetIso ρ n I).hom x =
      (E.intervalRepresentation ρ n I).asModuleEquiv x := by
  exact Action.monoidAlgebraModuleForgetIso_hom_apply M (E.intervalAction ρ n I) x

/-- A monoid-algebra generator acts by the original spectral endomorphism. -/
theorem monoidModuleInterval_generator_apply (n : ℤ) (I : ComposableArrows ι 1)
    (a : M) (x : E.monoidModuleInterval ρ n I) :
    (E.intervalRepresentation ρ n I).asModuleEquiv
        (MonoidAlgebra.single a (1 : ℤ) • x) = ((ρ a).asHom.hom n).app I x := by
  have h : (E.intervalRepresentation ρ n I).asModuleEquiv
      (MonoidAlgebra.single a (1 : ℤ) • x) = (1 : ℤ) • ((ρ a).asHom.hom n).app I x :=
    Action.monoidAlgebraModuleForgetIso_single_smul M (E.intervalAction ρ n I) a 1 x
  simpa only [one_smul] using h

/-- An integral multiple of a monoid-algebra generator acts by that multiple
of the original spectral endomorphism. -/
theorem monoidModuleInterval_single_apply (n : ℤ) (I : ComposableArrows ι 1)
    (a : M) (z : ℤ) (x : E.monoidModuleInterval ρ n I) :
    (E.intervalRepresentation ρ n I).asModuleEquiv
        (MonoidAlgebra.single a z • x) = z • ((ρ a).asHom.hom n).app I x := by
  exact Action.monoidAlgebraModuleForgetIso_single_smul M
    (E.intervalAction ρ n I) a z x

/-- An original group map commuting with the spectral action induces an actual
integral monoid-algebra linear map. -/
@[expose]
def monoidModuleMap {n m : ℤ} {I J : ComposableArrows ι 1}
    (f : (E.H n).obj I ⟶ (E.H m).obj J)
    (hf : ∀ a : M, ((ρ a).asHom.hom n).app I ≫ f =
      f ≫ ((ρ a).asHom.hom m).app J) :
    E.monoidModuleInterval ρ n I ⟶ E.monoidModuleInterval ρ m J :=
  (Action.monoidAlgebraModuleFunctor M).map
    (show E.intervalAction ρ n I ⟶ E.intervalAction ρ m J from
      { hom := f, comm := hf })

private lemma reflectsExact {X Y Z : ModuleCat.{u} (MonoidAlgebra ℤ M)}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : (mk₂ ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat).map f)
      ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat).map g)).Exact) :
    (mk₂ f g).Exact := by
  let U := forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat
  have hz : f ≫ g = 0 := U.map_injective (by
    rw [U.map_comp, U.map_zero]
    exact h.zero 0)
  apply ComposableArrows.exact₂_mk _ hz
  apply ((ShortComplex.mk f g hz).exact_map_iff_of_faithful U).mp
  exact h.exact 0

/-- The interval functor with its constructed monoid-algebra scalar actions. -/
@[expose]
def monoidModuleH (n : ℤ) :
    ComposableArrows ι 1 ⥤ ModuleCat.{u} (MonoidAlgebra ℤ M) where
  obj := E.monoidModuleInterval ρ n
  map f := E.monoidModuleMap ρ ((E.H n).map f)
    (fun a => ((ρ a).asHom.hom n).naturality f |>.symm)
  map_id I := by
    apply ModuleCat.hom_ext
    ext x
    exact ConcreteCategory.congr_hom ((E.H n).map_id I) x
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    exact ConcreteCategory.congr_hom ((E.H n).map_comp f g) x

/-- The original connecting transformation with its derived scalar linearity. -/
@[expose]
def monoidModuleδ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    functorArrows ι 1 2 2 ⋙ E.monoidModuleH ρ n₀ ⟶
      functorArrows ι 0 1 2 ⋙ E.monoidModuleH ρ n₁ where
  app D := E.monoidModuleMap ρ ((E.δ' n₀ n₁ h).app D) (by
    obtain ⟨_, _, _, f, g, rfl⟩ := mk₂_surjective D
    intro a
    exact ((ρ a).asHom.comm n₀ n₁ h f g).symm)
  naturality D D' f := by
    apply ModuleCat.hom_ext
    ext x
    exact ConcreteCategory.congr_hom ((E.δ' n₀ n₁ h).naturality f) x

/-- The actual integral-monoid-algebra-valued spectral object. Its interval
groups and all underlying interval and connecting maps are the original ones. -/
@[expose]
def monoidModule : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) ι where
  H := E.monoidModuleH ρ
  δ' := E.monoidModuleδ ρ
  exact₁' n₀ n₁ h D := by exact reflectsExact _ _ (E.exact₁' n₀ n₁ h D)
  exact₂' n D := by exact reflectsExact _ _ (E.exact₂' n D)
  exact₃' n₀ n₁ h D := by exact reflectsExact _ _ (E.exact₃' n₀ n₁ h D)

/-- The constructed spectral object has the exact original interval carrier
equipped with the extended scalar action. -/
theorem monoidModule_H_obj (n : ℤ) (I : ComposableArrows ι 1) :
    ((E.monoidModule ρ).H n).obj I = E.monoidModuleInterval ρ n I := rfl

/-- Its interval maps have the exact original underlying functions. -/
@[simp]
theorem monoidModule_H_map_apply (n : ℤ) {I J : ComposableArrows ι 1} (f : I ⟶ J)
    (x : E.monoidModuleInterval ρ n I) :
    (((E.monoidModule ρ).H n).map f :
      E.monoidModuleInterval ρ n I ⟶ E.monoidModuleInterval ρ n J) x =
        (E.H n).map f x := rfl

/-- Its connecting maps have the exact original underlying functions. -/
@[simp]
theorem monoidModule_δ_apply {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (x : E.monoidModuleInterval ρ n₀ (mk₁ g)) :
    ((E.monoidModule ρ).δ f g n₀ n₁ h :
      E.monoidModuleInterval ρ n₀ (mk₁ g) ⟶
        E.monoidModuleInterval ρ n₁ (mk₁ f)) x = E.δ f g n₀ n₁ h x := rfl

/-- Forget the integral monoid-algebra scalars on every interval and connecting
map of a module-valued spectral object. -/
@[expose]
def forgetMonoidModule (X : SpectralObject
    (ModuleCat.{u} (MonoidAlgebra ℤ M)) ι) : SpectralObject AddCommGrpCat.{u} ι := by
  letI : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  exact (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObject X

/-- Forgetting the constructed scalars recovers the full original spectral
object, including its interval functors and connecting transformations. -/
theorem forgetMonoidModule_monoidModule :
    forgetMonoidModule (E.monoidModule ρ) = E := by
  cases E
  rfl

/-- The exact forgetful spectral comparison with the original object. -/
def monoidModuleForgetIso : forgetMonoidModule (E.monoidModule ρ) ≅ E :=
  eqToIso (E.forgetMonoidModule_monoidModule ρ)

end CategoryTheory.Abelian.SpectralObject

end
