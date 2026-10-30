/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCube

/-!
# Consumer tests for the Finset-indexed Fourier API

These examples exercise the `Finset`-indexed Fourier transform
(`fourierChar`/`fourierCoeff`), its bridges to the canonical `Fin n` API, and
the inversion and Plancherel laws on empty and nonempty finite sets.
-/

open Finset BooleanCube

namespace BooleanCubeFinsetTests

/-- The character at overlapping singletons is `-1`. -/
example : fourierChar ({0} : Finset (Fin 2)) {0, 1} = -1 := by
  simp [fourierChar]

/-- The character at disjoint sets is `1`. -/
example : fourierChar ({0} : Finset (Fin 2)) {1} = 1 := by
  simp [fourierChar]

/-- On the empty index set the only Fourier coefficient is the value itself. -/
example (f : Finset (Fin 2) → ℝ) : fourierCoeff ∅ f ∅ = f ∅ := by
  simp [fourierCoeff, fourierChar]

/-- The constant-`1` function on a singleton cube has coefficients `1, 0`. -/
example : fourierCoeff ({0} : Finset (Fin 2)) (fun _ => 1) ∅ = 1 := by
  simp [fourierCoeff, fourierChar]

example : fourierCoeff ({0} : Finset (Fin 2)) (fun _ => 1) {0} = 0 := by
  unfold fourierCoeff fourierChar
  rw [show ({0} : Finset (Fin 2)).powerset = {∅, {0}} by decide]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- Fourier inversion on the empty index set. -/
example (f : Finset (Fin 2) → ℝ) :
    f ∅ = ∑ S ∈ (∅ : Finset (Fin 2)).powerset, fourierCoeff ∅ f S * fourierChar S ∅ :=
  fourier_inversion ∅ f ∅ (by simp)

/-- Fourier inversion on a nonempty index set. -/
example (f : Finset (Fin 2) → ℝ) :
    f {0} = ∑ S ∈ ({0, 1} : Finset (Fin 2)).powerset,
      fourierCoeff {0, 1} f S * fourierChar S {0} :=
  fourier_inversion {0, 1} f {0} (by decide)

/-- Plancherel on the empty index set. -/
example (f : Finset (Fin 2) → ℝ) :
    (∑ T ∈ (∅ : Finset (Fin 2)).powerset, f T ^ 2) / 2 ^ (∅ : Finset (Fin 2)).card
      = ∑ S ∈ (∅ : Finset (Fin 2)).powerset, fourierCoeff ∅ f S ^ 2 :=
  fourier_plancherel ∅ f

/-- Plancherel on a nonempty index set. -/
example (f : Finset (Fin 2) → ℝ) :
    (∑ T ∈ ({0, 1} : Finset (Fin 2)).powerset, f T ^ 2) / 2 ^ ({0, 1} : Finset (Fin 2)).card
      = ∑ S ∈ ({0, 1} : Finset (Fin 2)).powerset, fourierCoeff {0, 1} f S ^ 2 :=
  fourier_plancherel {0, 1} f

/-- The bridge identifying `fourierChar` with the canonical `cubeChi`. -/
example :
    fourierChar ({0} : Finset (Fin 2)) {0, 1}
      = cubeChi ({0, 1} : Finset (Fin 2)).card
          (reindexFinset {0, 1} {0} (by decide))
          (powersetEquivBoolCube {0, 1} ⟨{0, 1}, by decide⟩) :=
  fourierChar_eq_cubeChi {0, 1} {0} {0, 1} (by decide) (by decide)

/-- The bridge identifying `fourierCoeff` with `boolFourierCoeff`. -/
example (f : Finset (Fin 2) → ℝ) :
    fourierCoeff ({0, 1} : Finset (Fin 2)) f {0}
      = boolFourierCoeff ({0, 1} : Finset (Fin 2)).card (fun x => f (decodeBoolCube {0, 1} x))
          (reindexFinset {0, 1} {0} (by decide)) :=
  fourierCoeff_eq_boolFourierCoeff {0, 1} f {0} (by decide)

/-- The powerset/cube equivalence round-trips. -/
example (S : ↥({0, 1} : Finset (Fin 2)).powerset) :
    (powersetEquivBoolCube {0, 1}).symm (powersetEquivBoolCube {0, 1} S) = S :=
  Equiv.symm_apply_apply _ _

end BooleanCubeFinsetTests
