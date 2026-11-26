/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentIntervalHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNerveProducts
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Coherent Hom cubes

The nerve of strict interior subsets is identified with the 
product of scalar intervals. Coordinates retain precisely the membership
of each supplied interior vertex. The construction uses 
inverse functors and the nerve/product comparison, including an
empty coordinate family. It supplies no horn-filler or enriched-model
conclusion as a hypothesis.

## References

- Emily Riehl, *Homotopy coherent structures*, Example II.1.4 (the
  finite-ordinal mapping cubes),
  https://emilyriehl.github.io/files/coherent-structures.pdf.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingCube
variable {I : Type u}

/-- The strict interior Boolean coordinate family. -/
abbrev Coordinates (I : Type u) := I → ULift.{u} (Fin 2)

private instance (x y : Coordinates I) : Subsingleton (x ⟶ y) where
  allEq f g := funext (fun i => Subsingleton.elim (f i) (g i))

/-- Membership of an interior vertex is the zero-or-one cube coordinate. -/
def characteristic (S : Set I) (i : I) : ULift.{u} (Fin 2) := by
  classical
  exact if i ∈ S then ULift.up 1 else ULift.up 0

/-- The coordinate family gives exactly the subset of interior vertices at one. -/
def coordinateSet (p : Coordinates I) : Set I := {i | p i = ULift.up 1}

/-- This coordinate equals one precisely at the supplied subset members. -/
theorem characteristic_one (S : Set I) (i : I) : characteristic S i = ULift.up 1 ↔ i ∈ S := by
  classical
  by_cases h : i ∈ S <;> simp [characteristic, h]

/-- The membership coordinate is monotone under subset inclusion. -/
theorem characteristic_le {S T : Set I} (h : S ⊆ T) (i : I) :
    characteristic S i ≤ characteristic T i := by
  classical
  by_cases hs : i ∈ S
  · have ht := h hs
    simp only [characteristic, ite_eq_left hs, ite_eq_left ht]
    exact le_rfl
  · by_cases ht : i ∈ T
    · simp only [characteristic, ite_eq_right hs, ite_eq_left ht]
      decide
    · simp only [characteristic, ite_eq_right hs, ite_eq_right ht]
      exact le_rfl

/-- Every supplied subset is recovered from its Boolean membership coordinates. -/
theorem coordinateSet_characteristic (S : Set I) : coordinateSet (characteristic S) = S := by
  ext i
  exact characteristic_one S i

/-- The Boolean coordinate family is recovered from its member subset. -/
theorem characteristic_coordinateSet (p : Coordinates I) : characteristic (coordinateSet p)
  = p := by
  classical
  funext i
  have h : (p i).down = (0 : Fin 2) ∨ (p i).down = (1 : Fin 2) := by omega
  rcases h with h | h
  · have hp : p i = ULift.up (0 : Fin 2) := ULift.ext h
    simp [characteristic, coordinateSet, hp]
  · have hp : p i = ULift.up (1 : Fin 2) := ULift.ext h
    simp [characteristic, coordinateSet, hp]

/-- The subset-to-coordinate map as a categorical product functor. -/
def characteristicFunctor : Set I ⥤ Coordinates I where
  obj := characteristic
  map f i := homOfLE (characteristic_le f.down.down i)
  map_id S := by funext i; exact Subsingleton.elim _ _
  map_comp f g := by funext i; exact Subsingleton.elim _ _

/-- The inverse functor reads the coordinate-one subset. -/
def coordinateFunctor : Coordinates I ⥤ Set I where
  obj := coordinateSet
  map {S T} f := homOfLE (by
    intro i hi
    have h : S i ≤ T i := leOfHom (f i)
    change S i = ULift.up (1 : Fin 2) at hi
    rw [hi] at h
    change (1 : Fin 2) ≤ (T i).down at h
    change T i = ULift.up (1 : Fin 2)
    exact ULift.ext (le_antisymm (Fin.le_last _) h))

/-- These coordinate functors are inverses on the subset category. -/
theorem characteristic_coordinate_functor :
    characteristicFunctor (I := I) ⋙ coordinateFunctor = 𝟭 (Set I) := by
  refine CategoryTheory.Functor.ext (fun S => coordinateSet_characteristic S) ?_
  intro S T f
  exact Subsingleton.elim _ _

/-- They are also inverses on the Boolean coordinate category. -/
theorem coordinate_characteristic_functor :
    coordinateFunctor (I := I) ⋙ characteristicFunctor = 𝟭 (Coordinates I) := by
  refine CategoryTheory.Functor.ext (fun p => characteristic_coordinateSet p) ?_
  intro p q f
  exact Subsingleton.elim _ _

/-- The subset nerve is the nerve of the Boolean coordinate product
category. -/
def coordinateNerveIso : nerve (Set I) ≅ nerve (Coordinates I) where
  hom := nerveMap characteristicFunctor
  inv := nerveMap coordinateFunctor
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    change (p ⋙ characteristicFunctor) ⋙ coordinateFunctor = p
    refine CategoryTheory.Functor.ext (fun k => coordinateSet_characteristic (p.obj k)) ?_
    intro x y f
    exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    change (p ⋙ coordinateFunctor) ⋙ characteristicFunctor = p
    refine CategoryTheory.Functor.ext (fun k => characteristic_coordinateSet (p.obj k)) ?_
    intro x y f
    exact Subsingleton.elim _ _

/-- The product of scalar intervals with the supplied coordinate labels. -/
abbrev cube (I : Type u) : SSet.{u} := ∏ᶜ fun _ : I => (Δ[1] : SSet.{u})

/-- The subset-nerve/interval-product isomorphism. -/
def subsetCubeIso (I : Type u) : nerve (Set I) ≅ cube I :=
  coordinateNerveIso ≪≫ NerveProducts.nervePiIso (fun _ : I => ULift.{u} (Fin 2)) ≪≫
    Limits.Pi.mapIso (fun _ : I => (SSet.stdSimplex.isoNerve.{u} 1).symm)

/-- The coherent Hom nerve is the scalar cube on its strict interior labels. -/
def intervalCubeIso {J : Type u} [LinearOrder J] {i j : J} (hij : i ≤ j) :
    nerve (SimplicialThickening.Path i j) ≅ cube (IntervalHom.Interior i j) :=
  IntervalHom.intervalNerveIso hij ≪≫ subsetCubeIso _

end CategoryTheory.CoherentRealization.MappingCube
