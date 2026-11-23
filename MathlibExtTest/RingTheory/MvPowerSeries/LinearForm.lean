/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.LinearForm

@[expose] public section

open MvPowerSeries

private def finCoeffs : Fin 2 → ℤ := fun i => if i = 0 then 2 else -3

example : constantCoeff (linearForm finCoeffs) = 0 := by simp

example : coeff (Finsupp.single (0 : Fin 2) 1) (linearForm finCoeffs) = 2 := by
  norm_num [finCoeffs]

example : coeff (Finsupp.single (1 : Fin 2) 1) (linearForm finCoeffs) = -3 := by
  norm_num [finCoeffs]

example : coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
    (linearForm finCoeffs) = 0 := by
  rw [coeff_linearForm, map_add, Finsupp.degree_single]
  norm_num

example : pderiv (0 : Fin 2) (linearForm finCoeffs) = C 2 := by
  norm_num [finCoeffs]

example : pderiv (1 : Fin 2) (linearForm finCoeffs) = C (-3) := by
  norm_num [finCoeffs]

-- Addition and scalar multiplication use the canonical linear-map interface.
example :
    linearForm ((3 : ℤ) • finCoeffs + fun _ => 1) =
      3 • linearForm finCoeffs + linearForm (fun _ : Fin 2 => (1 : ℤ)) := by
  rw [map_add, map_smul]
  rfl

example :
    coeff (Finsupp.single (0 : Fin 2) 1)
        (linearForm ((3 : ℤ) • finCoeffs + fun _ => 1)) = 7 := by
  norm_num [finCoeffs]

private def natCoeffs (i : ℕ) : ℤ := i + 1

-- No finite-variable or finite-support condition is imposed on the family.
example (i : ℕ) :
    coeff (Finsupp.single i 1) (linearForm natCoeffs) = i + 1 := by
  simp [natCoeffs]

example (i : ℕ) : pderiv i (linearForm natCoeffs) = C (natCoeffs i) := by
  simp [natCoeffs]

-- The empty variable type produces the zero series.
example (b : Empty → ℤ) : linearForm b = (0 : MvPowerSeries Empty ℤ) := by
  ext d
  have hd : d = 0 := Subsingleton.elim _ _
  subst d
  simp

-- Coefficient-ring maps commute with the construction, here from `ℤ` to `ℚ`.
example :
    map (Int.castRingHom ℚ) (linearForm finCoeffs) =
      linearForm (fun i => (finCoeffs i : ℚ)) := by
  exact map_linearForm (Int.castRingHom ℚ) finCoeffs

-- Exact specialization of the source constructor in its original ring context.
example {σ A : Type*} [CommRing A] (b : σ → A) :
    ((fun d : σ →₀ ℕ =>
      if d.degree = 1 then ∑ i ∈ d.support, b i else 0) : MvPowerSeries σ A) =
      linearForm b := rfl

example {σ A : Type*} [CommRing A]
    (b : σ → A) (w : MvPowerSeries σ A) :
    (∀ d, coeff d w = if d.degree = 1 then ∑ i ∈ d.support, b i else 0) ↔
      w = linearForm b := by
  constructor
  · intro h
    ext d
    exact h d
  · rintro rfl d
    exact coeff_linearForm b d

-- The source derivative statement specializes directly to the canonical constructor.
example {σ A : Type*} [CommRing A] (b : σ → A) (i : σ) :
    pderiv i
        ((fun d : σ →₀ ℕ =>
          if d.degree = 1 then ∑ j ∈ d.support, b j else 0) : MvPowerSeries σ A) =
      C (b i) := by
  exact pderiv_linearForm b i

#print axioms MvPowerSeries.linearForm
#print axioms MvPowerSeries.coeff_linearForm
#print axioms MvPowerSeries.coeff_linearForm_single
#print axioms MvPowerSeries.constantCoeff_linearForm
#print axioms MvPowerSeries.pderiv_linearForm
#print axioms MvPowerSeries.map_linearForm
