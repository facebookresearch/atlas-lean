/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreBifunctor
import MathlibExt.AlgebraicTopology.Quasicategory.CoreFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FunctionRestriction
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Actual spaces of functor extensions with prescribed core families

The chosen object is the original pullback of full functor-core restriction.
Its two projections retain the actual functor and coefficient family. Arbitrary
prism coefficients retain the full condition that curry lands in the same core;
no standard simplex or original source is inferred Kan. Empty fibres are allowed.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FunctorCore.Extension

variable {A₀ A Q K : SSet.{u}}

/-- The same full source restriction of the original functor-core bifunctor. -/
def restriction (i : A₀ ⟶ A) (Q : SSet.{u}) :
    (FunctorCore.functor A).obj Q ⟶ (FunctorCore.functor A₀).obj Q :=
  (FunctorCore.sourceMap i).app Q

/-- The original chosen pullback fixes the entire supplied coefficient family. -/
abbrev object (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) : SSet.{u} :=
  pullback (restriction i Q) α

/-- The actual original full functor coordinate of the extension space. -/
abbrev functorProjection (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    object i α ⟶ (FunctorCore.functor A).obj Q := pullback.fst _ _

/-- The actual prescribed coefficient coordinate of the extension space. -/
abbrev coefficientProjection (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    object i α ⟶ K := pullback.snd _ _

/-- Both full original coordinates obey the original restriction-family square. -/
@[reassoc]
theorem projection_square (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    functorProjection i α ≫ restriction i Q = coefficientProjection i α ≫ α :=
  pullback.condition

/-- The existing categorical restriction and core-fibration theorems provide its Kan fibration. -/
instance restriction_fibration (i : A₀ ⟶ A) [Mono i] (Q : SSet.{u}) [Quasicategory Q] :
    HomotopicalAlgebra.Fibration (restriction i Q) := by
  let p := (MonoidalClosed.pre i).app Q
  have h := (categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p).mp
    (categoricalFibrations_pre_app_of_mono i Q)
  let _ : InnerFibration p := h.1
  let _ : HasStrictEquivalenceLifting p := h.2
  change HomotopicalAlgebra.Fibration (core.map p)
  exact fibration_core_map_of_hasStrictEquivalenceLifting p

/-- The same original coefficient projection is a fibration for every prescribed family. -/
instance coefficientProjection_fibration (i : A₀ ⟶ A) [Mono i]
    [Quasicategory Q] (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    HomotopicalAlgebra.Fibration (coefficientProjection i α) := by
  change HomotopicalAlgebra.Fibration (pullback.snd (restriction i Q) α)
  infer_instance

/-- The actual extension space is Kan for a Kan coefficient; its fibre may be empty. -/
theorem object_isKan (i : A₀ ⟶ A) [Mono i] [Quasicategory Q] [KanComplex K]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) : KanComplex (object i α) :=
  HomotopicalAlgebra.isFibrant_of_fibration (coefficientProjection i α)

/-- Every map into the extension space retains its original uncurried whole functor prism. -/
def prism {L : SSet.{u}} (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (f : L ⟶ object i α) : A ⊗ L ⟶ Q :=
  uncurry (f ≫ functorProjection i α ≫ (core ((ihom A).obj Q)).ι)

/-- Curry of the original prism factors through the same full functor core. -/
theorem prism_curry {L : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (f : L ⟶ object i α) :
    curry (prism i α f) = f ≫ functorProjection i α ≫ (core ((ihom A).obj Q)).ι :=
  curry_uncurry _

/-- The complete original prism has the prescribed whole boundary-family prism. -/
theorem prism_restriction {L : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (f : L ⟶ object i α) :
    i ▷ L ≫ prism i α f =
      uncurry (f ≫ coefficientProjection i α ≫ α ≫ (core ((ihom A₀).obj Q)).ι) := by
  rw [prism, ← uncurry_pre_app]
  congr 1
  simp only [Category.assoc]
  rw [← FunctorCore.sourceMap_inclusion i Q]
  change f ≫ functorProjection i α ≫ restriction i Q ≫ _ = _
  rw [projection_square_assoc]

/-- A full original prism is admissible exactly with its core range and actual boundary equation. -/
def Admissible {L : SSet.{u}} (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (p : (A ⊗ L ⟶ Q) × (L ⟶ K)) : Prop :=
  Subcomplex.range (curry p.1) ≤ core ((ihom A).obj Q) ∧
    i ▷ L ≫ p.1 = uncurry (p.2 ≫ α ≫ (core ((ihom A₀).obj Q)).ι)

/-- The original prism and coefficient maps give the actual marked pair of an extension. -/
def toPrism {L : SSet.{u}} (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (f : L ⟶ object i α) : {p : (A ⊗ L ⟶ Q) × (L ⟶ K) // Admissible i α p} :=
  ⟨(prism i α f, f ≫ coefficientProjection i α), by
    constructor
    · rw [prism_curry]
      intro n x hx
      obtain ⟨y, rfl⟩ := hx
      exact ((functorProjection i α).app n (f.app n y)).property
    · exact prism_restriction i α f⟩

/-- An admissible original prism gives its actual core factor and chosen pullback lift. -/
def fromPrism {L : SSet.{u}} (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (p : {p : (A ⊗ L ⟶ Q) × (L ⟶ K) // Admissible i α p}) : L ⟶ object i α := by
  let d : L ⟶ (FunctorCore.functor A).obj Q := Subcomplex.lift (curry p.1.1) p.2.1
  refine pullback.lift d p.1.2 ?_
  apply (cancel_mono (core ((ihom A₀).obj Q)).ι).mp
  rw [Category.assoc]
  change d ≫ (FunctorCore.sourceMap i).app Q ≫ _ = _
  rw [FunctorCore.sourceMap_inclusion, ← Category.assoc, Subcomplex.lift_ι,
    curry_pre_app, p.2.2, curry_uncurry, Category.assoc]

/-- The actual inverse retains its same original core lift as the full functor coordinate. -/
theorem fromPrism_fst {L : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (p : {p : (A ⊗ L ⟶ Q) × (L ⟶ K) // Admissible i α p}) :
    fromPrism i α p ≫ functorProjection i α = Subcomplex.lift (curry p.1.1) p.2.1 := by
  unfold fromPrism functorProjection
  exact pullback.lift_fst _ _ _

/-- The actual inverse retains the same prescribed coefficient coordinate. -/
theorem fromPrism_snd {L : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (p : {p : (A ⊗ L ⟶ Q) × (L ⟶ K) // Admissible i α p}) :
    fromPrism i α p ≫ coefficientProjection i α = p.1.2 := by
  unfold fromPrism coefficientProjection
  exact pullback.lift_snd _ _ _

/-- The native core-prism dictionary is a genuine bijection for every coefficient object. -/
def prismEquiv (L : SSet.{u}) (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    (L ⟶ object i α) ≃ {p : (A ⊗ L ⟶ Q) × (L ⟶ K) // Admissible i α p} where
  toFun := toPrism i α
  invFun := fromPrism i α
  left_inv f := by
    apply pullback.hom_ext
    · apply (cancel_mono (core ((ihom A).obj Q)).ι).mp
      change (fromPrism i α (toPrism i α f) ≫ functorProjection i α) ≫ _ = _
      rw [fromPrism_fst, Subcomplex.lift_ι]
      change curry (prism i α f) = (f ≫ functorProjection i α) ≫ _
      exact (prism_curry i α f).trans
        (Category.assoc f (functorProjection i α) (core ((ihom A).obj Q)).ι).symm
    · exact fromPrism_snd i α (toPrism i α f)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change prism i α (fromPrism i α p) = p.1.1
      rw [prism, ← Category.assoc, fromPrism_fst, Subcomplex.lift_ι, uncurry_curry]
    · change fromPrism i α p ≫ coefficientProjection i α = p.1.2
      exact fromPrism_snd i α p

/-- Every actual simplex retains its full marked prism dictionary without a Kan-simplex assumption. -/
def simplexEquiv (n : ℕ) (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    object i α _⦋n⦌ ≃
      {p : (A ⊗ (Δ[n] : SSet.{u}) ⟶ Q) × ((Δ[n] : SSet.{u}) ⟶ K) // Admissible i α p} :=
  yonedaEquiv.symm.trans (prismEquiv (Δ[n] : SSet.{u}) i α)

end SSet.FunctorCore.Extension
