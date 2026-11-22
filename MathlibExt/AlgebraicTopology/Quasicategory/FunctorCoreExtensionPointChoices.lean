/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreExtensionTrivialFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber

/-!
# Canonical point fibres of genuinely trivial extension moduli

Every point choice is the existing strict fibre of the original coefficient
projection. Its actual map to Δ[0] is trivial, and a genuine fibre vertex is
derived from lifting. Compatible actions use the existing mapFiber; their weak
class follows from the two actual terminal weak maps of the choice spaces.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FunctorCore.Extension

variable {A₀ A Q K : SSet.{u}}

/-- The point-choice object is the existing original strict fibre. -/
abbrev pointChoice (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) : SSet.{u} := (Subcomplex.fiber (coefficientProjection i α) k : SSet.{u})

/-- The original point fibre retains its whole extension-space inclusion. -/
abbrev pointChoiceInclusion (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) : pointChoice i α k ⟶ object i α :=
  (Subcomplex.fiber (coefficientProjection i α) k).ι

/-- The actual terminal projection of the same point-choice fibre. -/
def pointProjection (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) : pointChoice i α k ⟶ (Δ[0] : SSet.{u}) :=
  stdSimplex.isTerminalObj₀.from _

/-- The point choice retains the same actual coefficient vertex in all degrees. -/
@[reassoc]
theorem pointChoice_coefficient (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) : pointChoiceInclusion i α k ≫ coefficientProjection i α = const k :=
  Subcomplex.fiber_ι_comp _ _

/-- The actual point-fibre projection is trivial from the proven original extension projection. -/
theorem pointProjection_mem_trivialFibrations (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    trivialFibrations SSet.{u} (pointProjection i α k) :=
  MorphismProperty.of_isPullback (Subcomplex.fiber_isPullback (coefficientProjection i α) k)
    (coefficientProjection_mem_trivialFibrations i hi α)

/-- Point fibres are genuinely Kan with an arbitrary original coefficient object. -/
theorem pointChoice_isKan (i : A₀ ⟶ A) [Mono i] [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    KanComplex (pointChoice i α k) := by
  infer_instance

/-- Weak contractibility is the original point-fibre projection in the structural Kan weak class. -/
theorem pointProjection_mem_W (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    KanComplex.W (pointProjection i α k) := by
  let _ : KanComplex (pointChoice i α k) := pointChoice_isKan i α k
  let _ : KanComplex (Δ[0] : SSet.{u}) := by
    apply KanComplex.iff.mpr
    intro n j f hf
    exact ⟨stdSimplex.isTerminalObj₀.from _, fun _ _ => stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (pointProjection_mem_trivialFibrations i hi α k).2

/-- The specified coefficient point has an actual extension-fibre vertex, derived from lifting. -/
theorem pointChoice_nonempty (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    Nonempty (pointChoice i α k _⦋0⦌) := by
  obtain ⟨x, hx⟩ := exists_vertex_lift_of_rlp_I (coefficientProjection_rlp_I i hi α) k
  exact ⟨Subcomplex.fiber.basePoint x hx⟩

/-- An actual coefficient vertex supplies an actual vertex of the original extension space. -/
theorem extension_vertex_exists (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌) :
    ∃ x : object i α _⦋0⦌, (coefficientProjection i α).app (op ⦋0⦌) x = k :=
  exists_vertex_lift_of_rlp_I (coefficientProjection_rlp_I i hi α) k

/-- The same point-fibre map retains its original complete marked prism. -/
def pointPrism {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (f : T ⟶ pointChoice i α k) : A ⊗ T ⟶ Q :=
  prism i α (f ≫ pointChoiceInclusion i α k)

/-- The original point prism retains the full actual source boundary at its specified coefficient point. -/
theorem pointPrism_boundary {T : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (k : K _⦋0⦌)
    (f : T ⟶ pointChoice i α k) :
    i ▷ T ≫ pointPrism i α k f =
      uncurry (const (X := T) k ≫ α ≫ (core ((ihom A₀).obj Q)).ι) := by
  rw [pointPrism, prism_restriction]
  congr 1
  calc
    _ = f ≫ (pointChoiceInclusion i α k ≫ coefficientProjection i α) ≫
        α ≫ (core ((ihom A₀).obj Q)).ι := by simp only [Category.assoc]
    _ = _ := by rw [pointChoice_coefficient, ← Category.assoc, comp_const]

variable {B₀ B Q' L : SSet.{u}}

/-- The compatible original whole action uses the canonical strict-fibre map. -/
def pointMap (i : A₀ ⟶ A) (j : B₀ ⟶ B) (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B)
    (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l) :
    pointChoice j α k ⟶ pointChoice i β l :=
  Subcomplex.mapFiber (map i j u₀ u₁ g h α β c hc) c (map_snd i j u₀ u₁ g h α β c hc) hl

/-- The canonical point action keeps the original full extension-map inclusion square. -/
@[reassoc]
theorem pointMap_inclusion (i : A₀ ⟶ A) (j : B₀ ⟶ B) (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B)
    (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l) :
    pointMap i j u₀ u₁ g h α β c hc k l hl ≫ pointChoiceInclusion i β l =
      pointChoiceInclusion j α k ≫ map i j u₀ u₁ g h α β c hc :=
  Subcomplex.mapFiber_ι _ _ _ _

/-- Compatible actions preserve the actual terminal projection of the point-choice objects. -/
theorem pointMap_projection (i : A₀ ⟶ A) (j : B₀ ⟶ B) (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B)
    (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l) :
    pointMap i j u₀ u₁ g h α β c hc k l hl ≫ pointProjection i β l = pointProjection j α k :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Identity on every original parameter is the identity on the same point fibre. -/
theorem pointMap_id (i : A₀ ⟶ A) (α : K ⟶ (FunctorCore.functor A₀).obj Q)
    (k : K _⦋0⦌) :
    pointMap i i (𝟙 A₀) (𝟙 A) (𝟙 Q) (by simp) α α (𝟙 K)
      (by rw [FunctorCore.mapBoth_id, Category.comp_id, Category.id_comp]) k k rfl =
        𝟙 (pointChoice i α k) := by
  apply (cancel_mono (pointChoiceInclusion i α k)).mp
  rw [pointMap_inclusion, map_id, Category.comp_id, Category.id_comp]

/-- Actual compatible actions compose in the same contravariant source and covariant target order. -/
theorem pointMap_comp {C₀ C Q'' M : SSet.{u}}
    (i : A₀ ⟶ A) (j : B₀ ⟶ B) (k : C₀ ⟶ C)
    (u₀ : B₀ ⟶ C₀) (u₁ : B ⟶ C) (hu : j ≫ u₁ = u₀ ≫ k)
    (v₀ : A₀ ⟶ B₀) (v₁ : A ⟶ B) (hv : i ≫ v₁ = v₀ ≫ j)
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'')
    (α : K ⟶ (FunctorCore.functor C₀).obj Q)
    (β : L ⟶ (FunctorCore.functor B₀).obj Q')
    (γ : M ⟶ (FunctorCore.functor A₀).obj Q'') (c : K ⟶ L) (d : L ⟶ M)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (hd : β ≫ FunctorCore.mapBoth v₀ g' = d ≫ γ)
    (x : K _⦋0⦌) (y : L _⦋0⦌) (z : M _⦋0⦌)
    (hx : c.app (op ⦋0⦌) x = y) (hy : d.app (op ⦋0⦌) y = z) :
    pointMap j k u₀ u₁ g hu α β c hc x y hx ≫
        pointMap i j v₀ v₁ g' hv β γ d hd y z hy =
      pointMap i k (v₀ ≫ u₀) (v₁ ≫ u₁) (g ≫ g')
        (square_comp i j k u₀ u₁ hu v₀ v₁ hv) α γ (c ≫ d)
        (family_comp u₀ v₀ g g' α β γ c d hc hd) x z (by simpa [hx] using hy) := by
  apply (cancel_mono (pointChoiceInclusion i γ z)).mp
  rw [Category.assoc, pointMap_inclusion, ← Category.assoc, pointMap_inclusion,
    Category.assoc, map_comp, pointMap_inclusion]

/-- The original whole point-prism action retains source precomposition and target postcomposition. -/
theorem pointPrism_map {T : SSet.{u}} (i : A₀ ⟶ A) (j : B₀ ⟶ B)
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l)
    (f : T ⟶ pointChoice j α k) :
    pointPrism i β l (f ≫ pointMap i j u₀ u₁ g h α β c hc k l hl) =
      u₁ ▷ T ≫ pointPrism j α k f ≫ g := by
  rw [pointPrism, pointPrism, Category.assoc, pointMap_inclusion,
    ← Category.assoc, prism_map]

/-- Any compatible original point action between these genuinely contractible choices is weak. -/
theorem pointMap_realizationWeak (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) (j : B₀ ⟶ B) [Mono j]
    (hj : categoricalEquivalences j) [Quasicategory Q] [Quasicategory Q']
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l) :
    realizationWeakEquivalences (pointMap i j u₀ u₁ g h α β c hc k l hl) := by
  have ht : realizationWeakEquivalences (pointProjection i β l) :=
    (pointProjection_mem_trivialFibrations i hi β l).2
  have hs : realizationWeakEquivalences (pointProjection j α k) :=
    (pointProjection_mem_trivialFibrations j hj α k).2
  apply realizationWeakEquivalences.of_postcomp _ _ ht
  rw [pointMap_projection]
  exact hs

/-- The same actual point action is a structural Kan weak map without weak-map premises on its parameters. -/
theorem pointMap_mem_W (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) (j : B₀ ⟶ B) [Mono j]
    (hj : categoricalEquivalences j) [Quasicategory Q] [Quasicategory Q']
    (u₀ : A₀ ⟶ B₀) (u₁ : A ⟶ B) (g : Q ⟶ Q') (h : i ≫ u₁ = u₀ ≫ j)
    (α : K ⟶ (FunctorCore.functor B₀).obj Q)
    (β : L ⟶ (FunctorCore.functor A₀).obj Q') (c : K ⟶ L)
    (hc : α ≫ FunctorCore.mapBoth u₀ g = c ≫ β)
    (k : K _⦋0⦌) (l : L _⦋0⦌) (hl : c.app (op ⦋0⦌) k = l) :
    KanComplex.W (pointMap i j u₀ u₁ g h α β c hc k l hl) := by
  let _ : KanComplex (pointChoice j α k) := pointChoice_isKan j α k
  let _ : KanComplex (pointChoice i β l) := pointChoice_isKan i β l
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (pointMap_realizationWeak i hi j hj u₀ u₁ g h α β c hc k l hl)

end SSet.FunctorCore.Extension
