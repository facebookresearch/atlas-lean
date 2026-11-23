/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarFunctoriality
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Additivity and scalar linearity of the actual coefficient bar

The coefficient category needs only preadditivity and sized coproducts.
Degreewise additivity follows from the native colimit/constant adjunction,
using a local additive structure on the constant functor. The actual
simplicial bar inherits that additivity componentwise.

The scalar-linearity proof and its existing public instance are moved from
`CoefficientLinear`, with its historical author credit retained. They require
only a linear coefficient category; normalized complexes and homology retain
their separate Abelian hypotheses in that consumer module.
-/

public section

noncomputable section

open CategoryTheory Limits

universe wS uJ vJ uV vV

namespace CategoryTheory.CategoryHomology

section Additivity

variable {J : Type uJ} [Category.{vJ} J]
  {V : Type uV} [Category.{vV} V] [Preadditive V]
  [HasCoproducts.{max uJ vJ} V]
  {M N : J ⥤ V}

/-- The actual degreewise coefficient-bar map preserves addition. -/
theorem coefficientBarMap_add (α β : M ⟶ N) (n : ℕ) :
    coefficientBarMap (α + β) n = coefficientBarMap α n + coefficientBarMap β n := by
  let η (γ : M ⟶ N) : Discrete.functor (coefficientBarFamily M n) ⟶
      Discrete.functor (coefficientBarFamily N n) :=
    Discrete.natTrans fun F ↦ γ.app F.as.left
  let : (Functor.const (Discrete (ComposableArrows J n)) :
      V ⥤ Discrete (ComposableArrows J n) ⥤ V).Additive :=
    { map_add := by
        intro X Y f g
        apply NatTrans.ext
        funext F
        rfl }
  let : (colim (J := Discrete (ComposableArrows J n)) (C := V)).Additive :=
    (colimConstAdj (J := Discrete (ComposableArrows J n)) (C := V)).left_adjoint_additive
  have hη : η (α + β) = η α + η β := by
    apply NatTrans.ext
    funext F
    rfl
  change (colim (J := Discrete (ComposableArrows J n)) (C := V)).map (η (α + β)) =
    (colim (J := Discrete (ComposableArrows J n)) (C := V)).map (η α) +
      (colim (J := Discrete (ComposableArrows J n)) (C := V)).map (η β)
  rw [hη, Functor.map_add]

/-- Additivity of the actual simplicial coefficient-bar functor. -/
instance coefficientBarSimplicialFunctor_additive :
    (coefficientBarSimplicialFunctor (C := J) (A := V)).Additive where
  map_add {M N α β} := by
    apply NatTrans.ext
    funext Δ
    change coefficientBarMap (α + β) Δ.unop.len =
      coefficientBarMap α Δ.unop.len + coefficientBarMap β Δ.unop.len
    exact coefficientBarMap_add α β Δ.unop.len

end Additivity

section Scalars

variable {S : Type wS} [Semiring S]
  {J : Type uJ} [Category.{vJ} J]
  {V : Type uV} [Category.{vV} V] [Preadditive V] [CategoryTheory.Linear S V]
  [HasCoproducts.{max uJ vJ} V]

private theorem bar_scalar_id (M : J ⥤ V) (s : S) (n : ℕ) :
    CategoryHomology.coefficientBarMap (s • 𝟙 M) n =
      s • 𝟙 (CategoryHomology.coefficientBarObj M n) := by
  apply CategoryHomology.coefficientBar_hom_ext M
  intro F
  rw [CategoryHomology.coefficientBarι_map]
  change (s • 𝟙 (M.obj F.left)) ≫ CategoryHomology.coefficientBarι M F =
    CategoryHomology.coefficientBarι M F ≫ (s • 𝟙 _)
  simp

private theorem bar_simplicial_scalar_id (M : J ⥤ V) (s : S) :
    CategoryHomology.coefficientBarSimplicialMap (s • 𝟙 M) =
      s • 𝟙 (CategoryHomology.coefficientBarSimplicial M) := by
  apply NatTrans.ext
  funext n
  change CategoryHomology.coefficientBarMap (s • 𝟙 M) n.unop.len =
    s • 𝟙 (CategoryHomology.coefficientBarObj M n.unop.len)
  exact bar_scalar_id M s n.unop.len

/-- Linearity for every actual coefficient simplicial-bar morphism.
`linear_iff` turns the proved identity-scalar formula into the arbitrary-map
formula using `(s • id) >> f = s • f` and functorial composition. -/
instance coefficientBarSimplicialFunctor_linear :
    Functor.Linear S (CategoryHomology.coefficientBarSimplicialFunctor
      (C := J) (A := V)) := by
  apply (Functor.linear_iff S _).2
  intro M s
  exact bar_simplicial_scalar_id M s

end Scalars

end CategoryTheory.CategoryHomology

end
