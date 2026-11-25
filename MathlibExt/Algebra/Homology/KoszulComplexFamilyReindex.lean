/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.KoszulComplexFamily
public import MathlibExt.Algebra.Homology.FiniteLengthEuler
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Length
import Mathlib.Tactic.FinCases

/-!
# Reindexing finite-family Koszul complexes

An equivalence of finite index types reindexes the free coefficient module
and induces an isomorphism of the corresponding Koszul complexes. Its
homology isomorphisms preserve module length in every degree.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace KoszulComplex

universe u v

variable (R : Type u) [CommRing R]
variable {I J : Type v} [Fintype I] [Fintype J]

/-- Reindex a finite free coefficient module along an equivalence of its
index type. -/
noncomputable def familyReindexLinearEquiv (e : I ≃ J) :
    (I → R) ≃ₗ[R] (J → R) :=
  LinearEquiv.piCongrLeft R (fun _ : J => R) e

omit [Fintype I] [Fintype J] in
@[simp]
theorem familyReindexLinearEquiv_apply
    (e : I ≃ J) (x : I → R) (j : J) :
    familyReindexLinearEquiv R e x j = x (e.symm j) :=
  by
    change (Equiv.piCongrLeft (fun _ : J => R) e) x j = _
    simpa using
      (Equiv.piCongrLeft_apply (P := fun _ : J => R) (e := e) x j)

/-- The reindexed family functional composed with coordinate reindexing is
the original family functional. -/
theorem familyFunctional_comp_reindex
    (a : I → R) (e : I ≃ J) :
    (familyFunctional R (fun j => a (e.symm j))).comp
        (familyReindexLinearEquiv R e).toLinearMap =
      familyFunctional R a := by
  apply LinearMap.ext
  intro x
  classical
  simp only [LinearMap.comp_apply, familyFunctional,
    Fintype.linearCombination_apply]
  simpa using
    (Equiv.sum_comp e
      (fun j => x (e.symm j) * a (e.symm j))).symm

omit [CommRing R] [Fintype I] [Fintype J] in
/-- Reindexing a family along an equivalence does not change its range. -/
theorem familyReindex_range (a : I → R) (e : I ≃ J) :
    Set.range (fun j => a (e.symm j)) = Set.range a := by
  change Set.range (a ∘ e.symm) = Set.range a
  exact e.symm.surjective.range_comp a

/-- Reindexing a finite coefficient family induces an isomorphism of its
Koszul chain complex. -/
noncomputable def familyComplexReindexIso
    (a : I → R) (e : I ≃ J) :
    familyComplex R a ≅
      familyComplex R (fun j => a (e.symm j)) :=
  mapIso R (I → R)
    (familyFunctional R a)
    (familyFunctional R (fun j => a (e.symm j)))
    (familyReindexLinearEquiv R e)
    (familyFunctional_comp_reindex R a e)

/-- Reindexing induces an isomorphism on Koszul homology in every degree. -/
noncomputable def familyComplexReindexHomologyIso
    (a : I → R) (e : I ≃ J) (n : ℕ) :
    (familyComplex R a).homology n ≅
      (familyComplex R (fun j => a (e.symm j))).homology n :=
  (HomologicalComplex.homologyFunctor
    (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (familyComplexReindexIso R a e)

/-- Reindexing preserves the length of every Koszul homology module. -/
theorem familyComplexReindex_homology_length_eq
    (a : I → R) (e : I ≃ J) (n : ℕ) :
    Module.length R ((familyComplex R a).homology n) =
      Module.length R
        ((familyComplex R (fun j => a (e.symm j))).homology n) :=
  (familyComplexReindexHomologyIso R a e n).toLinearEquiv.length_eq

/-- Ordered two-element coefficient family. -/
def pairFamily (f g : R) : Fin 2 → R :=
  Fin.cases f (fun _ => g)

omit [CommRing R] in
@[simp]
theorem pairFamily_zero (f g : R) : pairFamily R f g 0 = f :=
  rfl

omit [CommRing R] in
@[simp]
theorem pairFamily_one (f g : R) : pairFamily R f g 1 = g :=
  rfl

omit [CommRing R] in
/-- The range of the ordered two-element family is the unordered pair of its
coefficients. -/
theorem pairFamily_range (f g : R) :
    Set.range (pairFamily R f g) = {f, g} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with
      h | h
    · exact ⟨0, (pairFamily_zero R f g).trans h.symm⟩
    · exact ⟨1, (pairFamily_one R f g).trans h.symm⟩

omit [CommRing R] in
/-- Reindexing the two-element family by the transposition swaps its two
coefficients. -/
theorem pairFamily_reindex_swap (f g : R) :
    (fun j => pairFamily R f g
      ((Equiv.swap (0 : Fin 2) 1).symm j)) =
      pairFamily R g f := by
  funext j
  fin_cases j
  · exact pairFamily_one R f g
  · exact (pairFamily_one R g f).symm

/-- Swapping two generators gives an isomorphism of their Koszul
complexes. -/
noncomputable def pairComplexSwapIso (f g : R) :
    familyComplex R (pairFamily R f g) ≅
      familyComplex R (pairFamily R g f) :=
  familyComplexReindexIso R (pairFamily R f g)
      (Equiv.swap (0 : Fin 2) 1) ≪≫
    eqToIso (congrArg (familyComplex R)
      (pairFamily_reindex_swap R f g))

/-- Swapping two generators preserves every Koszul homology length. -/
theorem pairComplexSwap_homology_length_eq (f g : R) (n : ℕ) :
    Module.length R
        ((familyComplex R (pairFamily R f g)).homology n) =
      Module.length R
        ((familyComplex R (pairFamily R g f)).homology n) :=
  ((HomologicalComplex.homologyFunctor
    (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (pairComplexSwapIso R f g)).toLinearEquiv.length_eq

/-- Transport explicit finite-length Koszul homology data through a family
reindexing. -/
noncomputable def familyComplexReindexFiniteLengthData
    (a : I → R) (e : I ≃ J)
    (h : HomologicalComplex.FiniteLengthHomologyData R
      (familyComplex R a)) :
    HomologicalComplex.FiniteLengthHomologyData R
      (familyComplex R (fun j => a (e.symm j))) :=
  h.mapIso R (familyComplexReindexIso R a e)

/-- The finite-length Koszul Euler characteristic is invariant under family
reindexing. -/
theorem familyComplexReindex_eulerCharacteristic
    (a : I → R) (e : I ≃ J)
    (h : HomologicalComplex.FiniteLengthHomologyData R
      (familyComplex R a)) :
    HomologicalComplex.finiteLengthEulerCharacteristic R h =
      HomologicalComplex.finiteLengthEulerCharacteristic R
        (familyComplexReindexFiniteLengthData R a e h) :=
  HomologicalComplex.finiteLengthEulerCharacteristic_mapIso R h
    (familyComplexReindexIso R a e)

/-- The finite-length two-generator Koszul Euler characteristic is
invariant under swapping the two generators. -/
theorem pairComplexSwap_eulerCharacteristic
    (f g : R)
    (h : HomologicalComplex.FiniteLengthHomologyData R
      (familyComplex R (pairFamily R f g))) :
    HomologicalComplex.finiteLengthEulerCharacteristic R h =
      HomologicalComplex.finiteLengthEulerCharacteristic R
        (h.mapIso R (pairComplexSwapIso R f g)) :=
  HomologicalComplex.finiteLengthEulerCharacteristic_mapIso R h
    (pairComplexSwapIso R f g)

end KoszulComplex
