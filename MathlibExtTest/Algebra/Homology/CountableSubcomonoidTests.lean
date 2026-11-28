/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.CountableSubcomonoid
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Tactic.NormNum

/-!
# Finite and infinite closure with a nonzero subcomonoid

A finite successor operation on `Fin 3` reaches the whole finite carrier. Successor on the
natural numbers generates every natural number from zero, so a countable closure can be
infinite even when its seed is a singleton.

The tensor unit in rational integer cochain complexes has its canonical comonoid structure.
Closing its degree-zero unit generator gives a nonzero subcomonoid with a countable homogeneous
basis. Its inclusion and counit detect one and three, and the restricted comultiplication
recovers the ambient map through the actual tensor-square inclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex

namespace CountableSubcomonoidTests

private def finiteNext (_ : Fin 3) : Finset (Fin 3) := Finset.univ

private theorem finiteClosure_eq_univ :
    Set.finiteClosure finiteNext ({0} : Set (Fin 3)) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _
  have hz : (0 : Fin 3) ∈ Set.finiteClosure finiteNext ({0} : Set (Fin 3)) :=
    Set.subset_finiteClosure _ _ (by simp)
  exact Set.finiteClosure_closed _ _ hz (by simp [finiteNext])

example : (Set.finiteClosure finiteNext ({0} : Set (Fin 3))).Finite := by
  rw [finiteClosure_eq_univ]
  exact Set.toFinite _

private def successorNext (n : ℕ) : Finset ℕ := {n + 1}

private theorem successorClosure_mem (n : ℕ) :
    n ∈ Set.finiteClosure successorNext ({0} : Set ℕ) := by
  induction n with
  | zero => exact Set.subset_finiteClosure _ _ (by simp)
  | succ n ih =>
    exact Set.finiteClosure_closed _ _ ih (by simp [successorNext])

private theorem successorClosure_eq_univ :
    Set.finiteClosure successorNext ({0} : Set ℕ) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  exact fun n _ => successorClosure_mem n

example : (Set.finiteClosure successorNext ({0} : Set ℕ)).Countable :=
  (Set.countable_singleton 0).finiteClosure successorNext

example : (Set.finiteClosure successorNext ({0} : Set ℕ)).Infinite := by
  rw [successorClosure_eq_univ]
  exact Set.infinite_univ

private abbrev C := CochainComplex (ModuleCat.{0} ℚ) ℤ

private abbrev unitComplex : C := 𝟙_ C

private instance : ComonObj unitComplex := ComonObj.instTensorUnit C

private def unitCoordinate : unitComplex.X 0 ≅ ModuleCat.of ℚ ℚ :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℚ ℚ)

private def generator : unitComplex.X 0 := unitCoordinate.inv.hom 1

private def seed : Set (HomogeneousElement unitComplex) := {⟨0, generator⟩}

private theorem seed_countable : seed.Countable := Set.countable_singleton _

private theorem generator_mem :
    (⟨0, generator⟩ : HomogeneousElement unitComplex) ∈
      dgCoalgebraClosure unitComplex ComonObj.comul seed :=
  subset_dgCoalgebraClosure unitComplex ComonObj.comul seed (by simp [seed])

private abbrev D := coalgebraClosureCarrier unitComplex seed

private instance : ComonObj D := coalgebraClosureComonObj unitComplex seed

private abbrev inclusion : D ⟶ unitComplex := coalgebraClosureInclusion unitComplex seed

private instance : IsComonHom inclusion :=
  coalgebraClosureInclusion_isComonHom unitComplex seed

private def oneElement : D.X 0 := ⟨generator, Submodule.subset_span generator_mem⟩

private theorem inclusion_one : (inclusion.f 0).hom oneElement = generator := rfl

private theorem coefficient_one : unitCoordinate.hom.hom generator = 1 :=
  ModuleCat.hom_inv_apply unitCoordinate 1

private theorem inclusion_one_value :
    unitCoordinate.hom.hom ((inclusion.f 0).hom oneElement) = 1 := by
  rw [inclusion_one]
  exact coefficient_one

private theorem counit_zero_degree : (ComonObj.counit (X := D)).f 0 = inclusion.f 0 := by
  have h := IsComonHom.hom_counit inclusion
  have hf := congrArg (fun f : D ⟶ unitComplex => f.f 0) h
  change (inclusion.f 0 ≫ (𝟙 unitComplex).f 0) = (ComonObj.counit (X := D)).f 0 at hf
  simpa only [HomologicalComplex.id_f, Category.comp_id] using hf.symm

example : oneElement ≠ 0 := by
  intro hzero
  have h := congrArg (fun x : D.X 0 => unitCoordinate.hom.hom ((inclusion.f 0).hom x)) hzero
  rw [inclusion_one_value] at h
  exact one_ne_zero (by simpa only [map_zero] using h)

example : unitCoordinate.hom.hom ((inclusion.f 0).hom ((3 : ℚ) • oneElement)) = 3 := by
  rw [map_smul, map_smul, inclusion_one_value]
  norm_num

example : unitCoordinate.hom.hom (((ComonObj.counit (X := D)).f 0).hom oneElement) = 1 := by
  rw [counit_zero_degree]
  exact inclusion_one_value

example :
    unitCoordinate.hom.hom (((ComonObj.counit (X := D)).f 0).hom ((3 : ℚ) • oneElement)) = 3 := by
  rw [counit_zero_degree, map_smul, map_smul, inclusion_one_value]
  norm_num

example :
    (dgCoalgebraClosure unitComplex ComonObj.comul seed).Countable :=
  dgCoalgebraClosure_countable unitComplex ComonObj.comul seed_countable

example :
    (dgCoalgebraDegreeGenerators unitComplex ComonObj.comul seed 0).Countable :=
  dgCoalgebraDegreeGenerators_countable unitComplex ComonObj.comul seed_countable 0

example : Countable (Σ n : ℤ, (countableCoalgebraBasis unitComplex seed seed_countable).index n) :=
  (countableCoalgebraBasis unitComplex seed seed_countable).countable

example : IsComonHom inclusion :=
  coalgebraClosureInclusion_isComonHom unitComplex seed

example : Mono (coalgebraClosureTensorInclusion unitComplex seed) := inferInstance

example :
    coalgebraClosureComul unitComplex seed ≫ coalgebraClosureTensorInclusion unitComplex seed =
      inclusion ≫ ComonObj.comul := coalgebraClosureComul_fac unitComplex seed

example :
    (ComonObj.counit (X := D)).f 0 ≫ unitCoordinate.hom =
      inclusion.f 0 ≫ unitCoordinate.hom := by
  rw [counit_zero_degree]

end CountableSubcomonoidTests
