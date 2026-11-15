/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The actual trait, fibres and mapping property of a p-adic Néron model

The base is `Spec ℤ_p`, with its actual fraction-field inclusion and
residue-field quotient. Generic and special fibres are scheme pullbacks.
A Néron model is a smooth separated finite-type scheme with the universal
extension property for every smooth scheme over this trait.

The normalized Hom equivalence and reduction of integral points below are
complete constructions from these characterized model data. Existence of
models of abelian varieties remains a Wanted request.

Reference: Bosch–Lütkebohmert–Raynaud, *Néron Models*, §§1.1–1.3.
https://doi.org/10.1007/978-3-642-51438-8
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PadicNeronModels

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- The actual complete discrete valuation trait. -/
abbrev trait : Scheme.{0} := Spec (CommRingCat.of.{0} (PadicInt p))

/-- Its fraction-field point. -/
abbrev genericBase : Scheme.{0} := Spec (CommRingCat.of.{0} (Padic p))

/-- Its residue-field point. -/
abbrev specialBase : Scheme.{0} := Spec (CommRingCat.of.{0} (ZMod p))

/-- The actual inclusion of the fraction field. -/
def genericInclusion : genericBase p ⟶ trait p :=
  Spec.map (CommRingCat.ofHom (algebraMap (PadicInt p) (Padic p)))

/-- The actual quotient to the residue field. -/
def specialInclusion : specialBase p ⟶ trait p :=
  Spec.map (CommRingCat.ofHom (PadicInt.toZMod))

/-- The scheme-theoretic generic-fibre functor. -/
abbrev genericFunctor : Over (trait p) ⥤ Over (genericBase p) :=
  Over.pullback (genericInclusion p)

/-- The scheme-theoretic special-fibre functor. -/
abbrev specialFunctor : Over (trait p) ⥤ Over (specialBase p) :=
  Over.pullback (specialInclusion p)

/-- A characterized Néron model on the actual p-adic trait. The model
contains no group, component or point-set oracle. -/
structure NeronModel (A : Over (genericBase p)) where
  /-- The integral model as an actual scheme over the trait. -/
  model : Over (trait p)
  /-- Smoothness over the trait. -/
  [smooth : Smooth model.hom]
  /-- Separatedness over the trait. -/
  [separated : IsSeparated model.hom]
  /-- Local finite type over the trait. -/
  [finiteType : LocallyOfFiniteType model.hom]
  /-- Quasi-compactness, so this is a finite-type Néron model. -/
  [quasiCompact : QuasiCompact model.hom]
  /-- The actual generic fibre is identified over `ℚ_p` with `A`. -/
  genericIso : (genericFunctor p).obj model ≅ A
  /-- Every generic map from a smooth test scheme has a unique extension. -/
  mappingProperty : ∀ (Y : Over (trait p)) [Smooth Y.hom]
    (f : (genericFunctor p).obj Y ⟶ A),
    ∃! e : Y ⟶ model, (genericFunctor p).map e ≫ genericIso.hom = f

attribute [instance] NeronModel.smooth NeronModel.separated
  NeronModel.finiteType NeronModel.quasiCompact

namespace NeronModel

variable {p} {A : Over (genericBase p)} (N : NeronModel p A)

/-- The extension operator is exactly inverse to restriction to the
identified generic fibre. No independent extension map is selected. -/
def homEquiv (Y : Over (trait p)) [Smooth Y.hom] :
    (Y ⟶ N.model) ≃ ((genericFunctor p).obj Y ⟶ A) where
  toFun e := (genericFunctor p).map e ≫ N.genericIso.hom
  invFun f := Classical.choose (N.mappingProperty Y f)
  left_inv e :=
    ((Classical.choose_spec (N.mappingProperty Y
      ((genericFunctor p).map e ≫ N.genericIso.hom))).2 e rfl).symm
  right_inv f := (Classical.choose_spec (N.mappingProperty Y f)).1

/-- The extension's defining comparison commutes with generic restriction. -/
theorem extend_generic (Y : Over (trait p)) [Smooth Y.hom]
    (f : (genericFunctor p).obj Y ⟶ A) :
    (genericFunctor p).map ((N.homEquiv Y).symm f) ≫ N.genericIso.hom = f :=
  (N.homEquiv Y).apply_symm_apply f

variable {B C : Over (genericBase p)}

/-- Every generic morphism extends between the specified Néron models. -/
def map (M : NeronModel p A) (N : NeronModel p B) (f : A ⟶ B) :
    M.model ⟶ N.model :=
  (N.homEquiv M.model).symm (M.genericIso.hom ≫ f)

/-- The extended morphism restricts to the given generic morphism. -/
theorem map_generic (M : NeronModel p A) (N : NeronModel p B) (f : A ⟶ B) :
    (genericFunctor p).map (map M N f) ≫ N.genericIso.hom =
      M.genericIso.hom ≫ f :=
  (N.homEquiv M.model).apply_symm_apply _

/-- Extension preserves the actual identity map. -/
theorem map_id (M : NeronModel p A) : map M M (𝟙 A) = 𝟙 M.model := by
  apply (M.homEquiv M.model).injective
  change (genericFunctor p).map (map M M (𝟙 A)) ≫ M.genericIso.hom =
    (genericFunctor p).map (𝟙 M.model) ≫ M.genericIso.hom
  rw [map_generic, (genericFunctor p).map_id]
  simp

/-- Extension preserves composition, including compositions of isogenies. -/
theorem map_comp (M : NeronModel p A) (N : NeronModel p B)
    (O : NeronModel p C) (f : A ⟶ B) (g : B ⟶ C) :
    map M O (f ≫ g) = map M N f ≫ map N O g := by
  apply (O.homEquiv M.model).injective
  change (genericFunctor p).map (map M O (f ≫ g)) ≫ O.genericIso.hom =
    (genericFunctor p).map (map M N f ≫ map N O g) ≫ O.genericIso.hom
  rw [map_generic, CategoryTheory.Functor.map_comp, Category.assoc, map_generic]
  simpa only [Category.assoc] using
    (congrArg (fun u => u ≫ g) (map_generic M N f)).symm

end NeronModel

/-- Integral scheme-valued points over `ℤ_p`. -/
abbrev IntegralPoint (N : Over (trait p)) :=
  {q : trait p ⟶ N.left // q ≫ N.hom = 𝟙 _}

/-- Points of the actual special fibre over the residue field. -/
abbrev SpecialPoint (N : Over (trait p)) :=
  {q : specialBase p ⟶ ((specialFunctor p).obj N).left //
    q ≫ ((specialFunctor p).obj N).hom = 𝟙 _}

/-- Reduction is induced by the actual residue quotient and pullback square. -/
def reducePoint (N : Over (trait p)) (q : IntegralPoint p N) :
    SpecialPoint p N :=
  ⟨pullback.lift (specialInclusion p ≫ q.1) (𝟙 _) (by
      simp [Category.assoc, q.2]),
    pullback.lift_snd _ _ _⟩

end MathlibExt.AlgebraicGeometry.PadicNeronModels
