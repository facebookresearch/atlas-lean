/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.InformationTheory.LinearGaussianJointLaw
import PhyslibExt.Mechanics.TrussObservationInference

/-!
# Truss observation inference checks

## i. Overview

Elaboration and non-vacuity checks for
`PhyslibExt.Mechanics.TrussObservationInference`: the two public shapes
with the observation matrix spelled out, a zero-dimensional instance of
the sensor-reading identity whose premises are actually discharged, and
the positive-definite-noise case of the innovation invertibility
premise through the existing output-covariance producer. These are
checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Public shapes
- B. Zero-dimensional sensor-reading instance
- C. Positive-definite sensor noise

## iv. References

- `PhyslibExt.Mechanics.TrussObservationInference`
- `MathlibExt.InformationTheory.LinearGaussianJointLaw`
-/

open Matrix MeasureTheory ProbabilityTheory

/-! ## A. Public shapes -/

/-- Public shape of the sensor-reading identity. -/
example {J M : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [DecidableEq M] {nf np nm : ℕ} (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) (Fin nf) ℝ) (k : M → ℝ)
    (hPD : ((Mechanics.TrussCompatibility.axialCompatibility r a b * S)ᵀ *
        Matrix.diagonal k
        * (Mechanics.TrussCompatibility.axialCompatibility r a b * S)).PosDef)
    (Cmat : Matrix (Fin nm) (Fin nf) ℝ)
    (Bload : Matrix (Fin nf) (Fin np) ℝ) (f0 : Fin nf → ℝ)
    {u : Fin nf → ℝ} {θ : EuclideanSpace ℝ (Fin np)}
    (hu : ((Mechanics.TrussCompatibility.axialCompatibility r a b * S)ᵀ *
        Matrix.diagonal k
        * (Mechanics.TrussCompatibility.axialCompatibility r a b * S)) *ᵥ u
          = f0 + Bload *ᵥ WithLp.ofLp θ) :
    WithLp.toLp 2 (Cmat *ᵥ u)
      = Matrix.toEuclideanLin
          (Mechanics.TrussCompatibility.loadObservationMatrix r a b S k
            Cmat Bload) θ
        + WithLp.toLp 2
          (Cmat *ᵥ (((Mechanics.TrussCompatibility.axialCompatibility r a b
              * S)ᵀ * Matrix.diagonal k
            * (Mechanics.TrussCompatibility.axialCompatibility r a b
              * S))⁻¹ *ᵥ f0)) :=
  Mechanics.TrussCompatibility.toLp_sensor_eq_toEuclideanLin_add_offset
    r a b S k hPD Cmat Bload f0 hu

/-- Public shape of the load-parameter posterior. -/
example {J M : Type*} [Fintype J] [DecidableEq J] [Fintype M]
    [DecidableEq M] {nf np nm : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (r : J → (Fin 2 → ℝ))
    (a b : M → J) (S : Matrix (J × Fin 2) (Fin nf) ℝ) (k : M → ℝ)
    (hPD : ((Mechanics.TrussCompatibility.axialCompatibility r a b * S)ᵀ *
        Matrix.diagonal k
        * (Mechanics.TrussCompatibility.axialCompatibility r a b * S)).PosDef)
    (Cmat : Matrix (Fin nm) (Fin nf) ℝ)
    (Bload : Matrix (Fin nf) (Fin np) ℝ) (f0 : Fin nf → ℝ)
    {θ : Ω → EuclideanSpace ℝ (Fin np)}
    {v : Ω → EuclideanSpace ℝ (Fin nm)} {u : Ω → Fin nf → ℝ}
    (hu : ∀ ω, ((Mechanics.TrussCompatibility.axialCompatibility r a b
        * S)ᵀ * Matrix.diagonal k
        * (Mechanics.TrussCompatibility.axialCompatibility r a b * S)) *ᵥ
          u ω = f0 + Bload *ᵥ WithLp.ofLp (θ ω))
    (hθ : Measurable θ) (hv : Measurable v) (hind : IndepFun θ v P)
    {m : EuclideanSpace ℝ (Fin np)} {Sθ : Matrix (Fin np) (Fin np) ℝ}
    {R : Matrix (Fin nm) (Fin nm) ℝ} (hS : Sθ.PosSemidef)
    (hR : R.PosSemidef) (hθl : P.map θ = multivariateGaussian m Sθ)
    (hvl : P.map v = multivariateGaussian 0 R)
    (hinv : IsUnit (Mechanics.TrussCompatibility.loadObservationMatrix r a b
        S k Cmat Bload * Sθ
        * (Mechanics.TrussCompatibility.loadObservationMatrix r a b S k
          Cmat Bload)ᵀ + R).det) :
    ∀ᵐ y ∂P.map (fun ω => WithLp.toLp 2 (Cmat *ᵥ u ω) + v ω
        - WithLp.toLp 2
          (Cmat *ᵥ (((Mechanics.TrussCompatibility.axialCompatibility r a b
              * S)ᵀ * Matrix.diagonal k
            * (Mechanics.TrussCompatibility.axialCompatibility r a b
              * S))⁻¹ *ᵥ f0))),
      condDistrib θ (fun ω => WithLp.toLp 2 (Cmat *ᵥ u ω) + v ω
          - WithLp.toLp 2
            (Cmat *ᵥ (((Mechanics.TrussCompatibility.axialCompatibility r a b
                * S)ᵀ * Matrix.diagonal k
              * (Mechanics.TrussCompatibility.axialCompatibility r a b
                * S))⁻¹ *ᵥ f0))) P y =
        multivariateGaussian
          (m + toEuclideanLin
              (Sθ * (Mechanics.TrussCompatibility.loadObservationMatrix r a b
                  S k Cmat Bload)ᵀ
                * (Mechanics.TrussCompatibility.loadObservationMatrix r a b
                    S k Cmat Bload * Sθ
                  * (Mechanics.TrussCompatibility.loadObservationMatrix r a b
                      S k Cmat Bload)ᵀ + R)⁻¹)
              (y - toEuclideanLin
                (Mechanics.TrussCompatibility.loadObservationMatrix r a b S k
                  Cmat Bload) m))
          (Sθ - Sθ * (Mechanics.TrussCompatibility.loadObservationMatrix r a b
                S k Cmat Bload)ᵀ
              * (Mechanics.TrussCompatibility.loadObservationMatrix r a b S k
                  Cmat Bload * Sθ
                * (Mechanics.TrussCompatibility.loadObservationMatrix r a b S
                    k Cmat Bload)ᵀ + R)⁻¹
              * (Mechanics.TrussCompatibility.loadObservationMatrix r a b S k
                  Cmat Bload * Sθ)) :=
  Mechanics.TrussCompatibility.condDistrib_loadParameter_correctedReading
    r a b S k hPD Cmat Bload f0 hu hθ hv hind hS hR hθl hvl hinv

/-! ## B. Zero-dimensional sensor-reading instance -/

/-- At zero free, parameter, and sensor dimensions (one joint, no
members), the supported stiffness is the empty matrix, which is
positive definite, and the sensor-reading identity holds with its
premises discharged. -/
example :
    WithLp.toLp 2 ((0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ (0 : Fin 0 → ℝ)) = 0 := by
  have hPD : ((Mechanics.TrussCompatibility.axialCompatibility
        (fun _ => 0) (fun e : Fin 0 => e.elim0) (fun e : Fin 0 => e.elim0)
        * (0 : Matrix (Fin 1 × Fin 2) (Fin 0) ℝ))ᵀ
      * Matrix.diagonal (fun e : Fin 0 => e.elim0)
      * (Mechanics.TrussCompatibility.axialCompatibility
        (fun _ => 0) (fun e : Fin 0 => e.elim0) (fun e : Fin 0 => e.elim0)
        * (0 : Matrix (Fin 1 × Fin 2) (Fin 0) ℝ))).PosDef := by
    refine ⟨?_, ?_⟩
    · ext i j
      exact i.elim0
    · intro x hx
      exact absurd (Subsingleton.elim x 0) hx
  have key := Mechanics.TrussCompatibility.toLp_sensor_eq_toEuclideanLin_add_offset
    (J := Fin 1) (M := Fin 0) (nf := 0) (np := 0) (nm := 0)
    (fun _ => 0) (fun e : Fin 0 => e.elim0) (fun e : Fin 0 => e.elim0) 0
    (fun e : Fin 0 => e.elim0) hPD 0 0 0 (u := 0) (θ := 0)
    (by funext i; exact i.elim0)
  rw [key]
  exact Subsingleton.elim _ _

/-! ## C. Positive-definite sensor noise -/

/-- Positive definite sensor noise supplies the invertible-innovation
premise of the posterior for every observation matrix and every
positive semidefinite prior covariance, through the existing
output-covariance producer. -/
example {np nm : ℕ} (H : Matrix (Fin nm) (Fin np) ℝ)
    {Sθ : Matrix (Fin np) (Fin np) ℝ} (hS : Sθ.PosSemidef)
    {R : Matrix (Fin nm) (Fin nm) ℝ} (hR : R.PosDef) :
    IsUnit (H * Sθ * Hᵀ + R).det :=
  isUnit_iff_ne_zero.mpr
    (MathlibExt.InformationTheory.LinearGaussianJointLaw.posDef_output_covariance
      H hS hR).det_pos.ne'
