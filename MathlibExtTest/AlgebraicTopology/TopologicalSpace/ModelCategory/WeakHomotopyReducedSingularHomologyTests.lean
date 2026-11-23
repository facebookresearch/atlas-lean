/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopyReducedSingularHomology

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Data.Matrix.Mul
import MathlibExt.AlgebraicTopology.SingularHomology.ReducedCoefficientFunctor
import MathlibExt.AlgebraicTopology.SingularHomology.Sphere.Zero
import MathlibExt.Topology.Category.TopCat.ZerothHomotopy

/-!
# Reduced singular-homology invariance tests

These clients exercise degree zero, positive degrees, empty, point, and
disconnected spaces, arbitrary noncommutative-ring coefficients, coefficient
naturality, independent universes, and the exact weak-equivalence premise.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicTopology CategoryTheory HomologicalComplex Limits
open CategoryTheory.MorphismProperty

universe w v u

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
namespace WeakHomotopyReducedSingularHomologyTests

section PublicContract

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]
variable {X Y : TopCat.{w}} {f : X ⟶ Y} (A : C)

example (hf : TopCat.weakHomotopyEquivalences f) (n : ℕ) :
    IsIso ((reducedSingularHomologyFunctor C A n).map f) :=
  hf.isIso_reducedSingularHomologyFunctor_map A n

/-- Degree zero uses the same augmentation-kernel theorem and has no
connectedness or nonemptiness premise. -/
example (hf : TopCat.weakHomotopyEquivalences f) :
    IsIso ((reducedSingularHomologyFunctor C A 0).map f) :=
  hf.isIso_reducedSingularHomologyFunctor_map A 0

example (hf : TopCat.weakHomotopyEquivalences f) (n : ℕ) :
    IsIso ((reducedSingularHomologyFunctor C A (n + 1)).map f) :=
  hf.isIso_reducedSingularHomologyFunctor_map A (n + 1)

end PublicContract

section BasicSpaces

private noncomputable abbrev emptySpace : TopCat.{w} :=
  TopCat.of (ULift.{w} Empty)

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C] (A : C)

example : IsIso
    ((reducedSingularHomologyFunctor C A 0).map
      (𝟙 emptySpace.{w})) :=
  TopCat.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map
      (TopCat.weakHomotopyEquivalences.id_mem _) A 0

example : IsIso
    ((reducedSingularHomologyFunctor C A 0).map
      (𝟙 (TopCat.of PUnit.{w + 1}))) :=
  TopCat.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map
      (TopCat.weakHomotopyEquivalences.id_mem _) A 0

end BasicSpaces

section ZeroSphere

private abbrev IntModule := ModuleCat.of ℤ ℤ

example : IsIso
    ((reducedSingularHomologyFunctor (ModuleCat ℤ) IntModule 0).map
      (sphereAntipodalMap 0)) := by
  let _ : IsIso (sphereAntipodalMap 0) := by
    change IsIso (TopCat.isoOfHomeo (sphereAntipodalHomeo 0)).hom
    infer_instance
  exact
    TopCat.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map
      (MorphismProperty.of_isIso _ (sphereAntipodalMap 0)) IntModule 0

/-- The disconnected degree-zero example is nonzero: reduced `H₀(S⁰; ℤ)`
is canonically the coefficient module. -/
example : ¬ IsZero
    (reducedSingularHomology (ModuleCat ℤ) IntModule 0
      (TopCat.sphere.{0} 0)) := by
  intro h
  have hZ : IsZero IntModule :=
    h.of_iso (sphereZeroReducedH0Iso (C := ModuleCat ℤ) IntModule).symm
  exact not_subsingleton ℤ (ModuleCat.subsingleton_of_isZero hZ)

example :
    (sphereZeroReducedH0Iso (C := ModuleCat ℤ) IntModule).inv ≫
        (reducedSingularHomologyFunctor (ModuleCat ℤ) IntModule 0).map
          (sphereAntipodalMap 0) ≫
        (sphereZeroReducedH0Iso (C := ModuleCat ℤ) IntModule).hom =
      -𝟙 IntModule :=
  sphereZeroReducedH0Iso_inv_comp_reducedAntipodal_comp_hom IntModule

end ZeroSphere

section PremiseGates

private noncomputable def emptyToPoint :
    TopCat.of (ULift.{0} Empty) ⟶ TopCat.of PUnit :=
  TopCat.isTerminalPUnit.from _

private noncomputable def sphereZeroFold :
    TopCat.sphere.{0} 0 ⟶ TopCat.of PUnit :=
  TopCat.isTerminalPUnit.from _

private theorem bijective_zerothHomotopyMap_of_weak
    {X Y : TopCat.{w}} {f : X ⟶ Y}
    (hf : TopCat.weakHomotopyEquivalences f) :
    Function.Bijective (TopCat.zerothHomotopyMap f) := by
  have hπ : Function.Bijective (SSet.mapπ₀ (TopCat.toSSet.map f)) :=
    hf.bijective_mapπ₀
  constructor
  · intro x y hxy
    apply TopCat.zerothHomotopyEquiv.injective
    apply hπ.injective
    simpa only [TopCat.zerothHomotopyEquiv_naturality] using
      congrArg TopCat.zerothHomotopyEquiv hxy
  · intro y
    obtain ⟨q, hq⟩ := hπ.surjective (TopCat.zerothHomotopyEquiv y)
    refine ⟨TopCat.zerothHomotopyEquiv.symm q, ?_⟩
    apply TopCat.zerothHomotopyEquiv.injective
    rw [TopCat.zerothHomotopyEquiv_naturality]
    simpa only [Equiv.apply_symm_apply] using hq

private theorem emptyToPoint_not_weak :
    ¬ TopCat.weakHomotopyEquivalences emptyToPoint := by
  intro hf
  have hs := (bijective_zerothHomotopyMap_of_weak hf).surjective
  obtain ⟨q, _⟩ := hs (ZerothHomotopy.mk PUnit.unit)
  obtain ⟨x, _⟩ := ZerothHomotopy.mk_surjective q
  exact x.down.elim

private theorem sphereZeroFold_map_not_injective :
    ¬ Function.Injective (TopCat.zerothHomotopyMap sphereZeroFold) := by
  intro h
  let x := sphereZeroPi0Equiv.symm true
  let y := sphereZeroPi0Equiv.symm false
  have hxy : x ≠ y := by
    intro hxy
    have := congrArg sphereZeroPi0Equiv hxy
    simp [x, y] at this
  apply hxy
  apply h
  exact Subsingleton.elim _ _

private theorem sphereZeroFold_not_weak :
    ¬ TopCat.weakHomotopyEquivalences sphereZeroFold := by
  intro hf
  exact sphereZeroFold_map_not_injective
    (bijective_zerothHomotopyMap_of_weak hf).injective

example : ¬ TopCat.weakHomotopyEquivalences emptyToPoint :=
  emptyToPoint_not_weak

example : ¬ TopCat.weakHomotopyEquivalences sphereZeroFold :=
  sphereZeroFold_not_weak

end PremiseGates

section Coefficients

variable {R : Type u} [Ring R]

/-- Zero coefficients still require the weak-equivalence premise and yield
no converse. -/
example (X : TopCat.{u}) (n : ℕ) : IsIso
    ((reducedSingularHomologyFunctor (ModuleCat.{u} R)
      (⊥_ (ModuleCat.{u} R)) n).map (𝟙 X)) :=
  TopCat.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map
      (TopCat.weakHomotopyEquivalences.id_mem _) _ n

private abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

example : True := by
  fail_if_success let _ : CommRing MatrixRing := inferInstance
  trivial

example (n : ℕ) : IsIso
    ((reducedSingularHomologyFunctor (ModuleCat MatrixRing)
      (ModuleCat.of MatrixRing MatrixRing) n).map
        (𝟙 (TopCat.of PUnit))) :=
  TopCat.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map
      (TopCat.weakHomotopyEquivalences.id_mem _)
      (ModuleCat.of MatrixRing MatrixRing) n

end Coefficients

section CoefficientNaturality

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]
variable {A B : C} (a : A ⟶ B) {X Y : TopCat.{w}} (f : X ⟶ Y)
  (n : ℕ)

example :
    (reducedSingularHomologyFunctor C A n).map f ≫
        ((reducedSingularHomologyCoefficientFunctor C n).map a).app Y =
      ((reducedSingularHomologyCoefficientFunctor C n).map a).app X ≫
        (reducedSingularHomologyFunctor C B n).map f :=
  ((reducedSingularHomologyCoefficientFunctor C n).map a).naturality f

end CoefficientNaturality

section ExplicitUniverses

example {R : Type 1} [Ring R] (A : ModuleCat.{1} R)
    {X Y : TopCat.{1}} {f : X ⟶ Y}
    (hf : TopCat.weakHomotopyEquivalences f) (n : ℕ) :
    IsIso ((reducedSingularHomologyFunctor (ModuleCat.{1} R) A n).map f) :=
  hf.isIso_reducedSingularHomologyFunctor_map A n

example {R : Type} [Ring R] (A : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f : X ⟶ Y}
    (hf : TopCat.weakHomotopyEquivalences f) :
    IsIso ((reducedSingularHomologyFunctor (ModuleCat.{0} R) A 0).map f) :=
  hf.isIso_reducedSingularHomologyFunctor_map A 0

end ExplicitUniverses

section NegativeAPI

#guard_msgs (error, substring := true) in
#check TopCat.weakHomotopyEquivalences.of_isIso_reducedSingularHomologyFunctor_map

#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.isIso_reducedSingularHomologyFunctor_map

#guard_msgs (error, substring := true) in
#check SSet.reducedSingularHomologyFunctor

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.reducedSingularChainComplex

#guard_msgs (error, substring := true) in
#check TopCat.weakHomotopyEquivalences.isIso_relativeSingularHomologyFunctor_map

#guard_msgs (error, substring := true) in
#check TopCat.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map_crossRing

end NegativeAPI

#check TopCat.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map

#print axioms TopCat.weakHomotopyEquivalences.isIso_reducedSingularHomologyFunctor_map

end WeakHomotopyReducedSingularHomologyTests
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
