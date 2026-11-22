/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original coverage-to-all-target fibre application.
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibreComparisonPiZeroTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ComponentUnionProducts
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PullbackFibreWeakDetection
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Fibre detection over component-covering base maps

For two fibrations over a common base, a map covering all base components lets image-fibre realization weak equivalences extend to every point fibre and implies weakness of the total-space comparison. The connected-component quotient also preserves chosen `Fin n` products, and component surjectivity of every factor map gives component surjectivity of the full product map, including the empty product.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-- Actual coverage of base components extends the same original fibre comparison
from image vertices to all target vertices. No fibration of c is assumed. -/
theorem sameBasePullbackComparison_weak_at_all_vertices_of_component_coverage
    {A E D B : SSet.{u}} (a : A ⟶ B)
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    [Fibration s] [Fibration t]
    (ha : Function.Surjective (SSet.mapπ₀ a))
    (himage : ∀ x : A _⦋0⦌, SSet.realizationWeakEquivalences
      (sameBasePullbackComparison c s t h
        (SSet.yonedaEquiv.symm (a.app (op ⦋0⦌) x)))) :
    ∀ y : B _⦋0⦌, SSet.realizationWeakEquivalences
      (sameBasePullbackComparison c s t h (SSet.yonedaEquiv.symm y)) := by
  intro y
  obtain ⟨q, hq⟩ := ha (SSet.π₀.mk y)
  obtain ⟨x, hx⟩ := SSet.π₀.mk_surjective q
  have hxy : SSet.π₀.mk (a.app (op ⦋0⦌) x) = SSet.π₀.mk y := by
    rw [← hx, SSet.mapπ₀_mk] at hq
    exact hq
  exact (sameBasePullbackComparison_weak_iff_of_piZero_eq c s t h
    (a.app (op ⦋0⦌) x) y hxy).mp (himage x)

/-- The arbitrary comparison is globally weak as soon as component coverage and
the original image-fibre weaknesses have been derived. The base need not be Kan. -/
theorem realizationWeakEquivalence_of_image_fibres_component_coverage
    {A E D B : SSet.{u}} (a : A ⟶ B)
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    [Fibration s] [Fibration t]
    (ha : Function.Surjective (SSet.mapπ₀ a))
    (himage : ∀ x : A _⦋0⦌, SSet.realizationWeakEquivalences
      (sameBasePullbackComparison c s t h
        (SSet.yonedaEquiv.symm (a.app (op ⦋0⦌) x)))) :
    SSet.realizationWeakEquivalences c := by
  apply (SSet.realizationWeakEquivalence_iff_pullbackFibrewise_of_base_fibrations
    c s t h).mpr
  intro b
  let y : B _⦋0⦌ := SSet.yonedaEquiv b
  have point : SSet.yonedaEquiv.symm y = b := SSet.yonedaEquiv.symm_apply_apply b
  have all_vertices := sameBasePullbackComparison_weak_at_all_vertices_of_component_coverage
    a c s t h ha himage y
  change SSet.realizationWeakEquivalences (sameBasePullbackComparison c s t h b)
  have transport (b0 : (Δ[0] : SSet.{u}) ⟶ B) (hb0 : b0 = b)
      (hc0 : SSet.realizationWeakEquivalences (sameBasePullbackComparison c s t h b0)) :
      SSet.realizationWeakEquivalences (sameBasePullbackComparison c s t h b) := by
    subst b0
    exact hc0
  exact transport _ point all_vertices

/-- The actual finite product of original component classes, including Fin 0. -/
def piZeroFiniteProductEquiv (n : ℕ) (X : Fin n → SSet.{u}) :
    SSet.π₀ (∏ᶜ X) ≃ (∀ i : Fin n, SSet.π₀ (X i)) :=
  ((PreservesProduct.iso (SSet.π₀Functor : SSet.{u} ⥤ Type u) X) ≪≫
    Types.productIso (fun i : Fin n => SSet.π₀ (X i))).toEquiv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Every coordinate is the actual π₀ map of the original chosen projection. -/
theorem piZeroFiniteProductEquiv_apply (n : ℕ) (X : Fin n → SSet.{u})
    (q : SSet.π₀ (∏ᶜ X)) (i : Fin n) :
    piZeroFiniteProductEquiv n X q i = SSet.mapπ₀ (Pi.π X i) q := by
  have coordinate :
      (PreservesProduct.iso (SSet.π₀Functor : SSet.{u} ⥤ Type u) X).hom ≫
        (Types.productIso (fun j : Fin n => SSet.π₀ (X j))).hom ≫
          (↾fun f => f i) = SSet.π₀Functor.map (Pi.π X i) := by
    rw [Types.productIso_hom_comp_eval, PreservesProduct.iso_hom]
    exact piComparison_comp_π (SSet.π₀Functor : SSet.{u} ⥤ Type u) X i
  exact congrArg (fun f => f q) coordinate

/-- Naturality retains all Fin n projections, with no nonempty-arity restriction. -/
theorem piZeroFiniteProductEquiv_map (n : ℕ)
    {X Y : Fin n → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (q : SSet.π₀ (∏ᶜ X)) (i : Fin n) :
    piZeroFiniteProductEquiv n Y (SSet.mapπ₀ (CategoryTheory.Limits.Pi.map f) q) i =
      SSet.mapπ₀ (f i) (piZeroFiniteProductEquiv n X q i) := by
  rw [piZeroFiniteProductEquiv_apply, ← SSet.mapπ₀_comp_apply,
    CategoryTheory.Limits.Pi.map_π, SSet.mapπ₀_comp_apply, piZeroFiniteProductEquiv_apply]

/-- The SAME chosen finite product map covers target components if its actual
factor maps do. For Fin 0 this is the terminal product, not an invented vertex. -/
theorem mapPiZero_surjective_finite_Pi_map (n : ℕ)
    {X Y : Fin n → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, Function.Surjective (SSet.mapπ₀ (f i))) :
    Function.Surjective (SSet.mapπ₀ (CategoryTheory.Limits.Pi.map f)) := by
  intro q
  choose a ha using fun i => hf i (piZeroFiniteProductEquiv n Y q i)
  refine ⟨(piZeroFiniteProductEquiv n X).symm a, ?_⟩
  apply (piZeroFiniteProductEquiv n Y).injective
  funext i
  rw [piZeroFiniteProductEquiv_map,
    show piZeroFiniteProductEquiv n X ((piZeroFiniteProductEquiv n X).symm a) = a
      from (piZeroFiniteProductEquiv n X).apply_symm_apply a]
  exact ha i

/-- Image-tuple fibre weakness extends to every target tuple component for the
literal Fin n base map, preserving c and both original fibration projections. -/
theorem sameBasePullbackComparison_all_finite_tuples_of_factor_component_coverage
    (n : ℕ) {X Y : Fin n → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    {E D : SSet.{u}} (c : E ⟶ D)
    (s : E ⟶ ∏ᶜ Y) (t : D ⟶ ∏ᶜ Y) (h : c ≫ t = s)
    [Fibration s] [Fibration t]
    (hf : ∀ i, Function.Surjective (SSet.mapπ₀ (f i)))
    (himage : ∀ x : (∏ᶜ X) _⦋0⦌, SSet.realizationWeakEquivalences
      (sameBasePullbackComparison c s t h
        (SSet.yonedaEquiv.symm ((CategoryTheory.Limits.Pi.map f).app (op ⦋0⦌) x)))) :
    ∀ y : (∏ᶜ Y) _⦋0⦌, SSet.realizationWeakEquivalences
      (sameBasePullbackComparison c s t h (SSet.yonedaEquiv.symm y)) :=
  sameBasePullbackComparison_weak_at_all_vertices_of_component_coverage
    (CategoryTheory.Limits.Pi.map f) c s t h (mapPiZero_surjective_finite_Pi_map n f hf) himage

end SSet
