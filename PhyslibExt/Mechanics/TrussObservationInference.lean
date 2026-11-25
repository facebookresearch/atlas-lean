/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.TrussCompatibility
public import MathlibExt.Probability.Distributions.GaussianConditioning
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Gaussian inference of truss load parameters from sensor readings

## i. Overview

Joints `J` sit at reference positions `r : J → (Fin 2 → ℝ)`; member
`e : M` joins joint `a e` to joint `b e`. With the supported-coordinate
matrix `S` and member weights `k`, the supported stiffness is
`K = (axialCompatibility r a b * S)ᵀ * Matrix.diagonal k *
(axialCompatibility r a b * S)`, and the results below keep it fixed,
known and positive definite: the stiffness is never an unknown, and no
unknown-stiffness inverse problem is stated.

Load parameters `θ : Ω → EuclideanSpace ℝ (Fin np)` act through a fixed
load basis `Bload` on top of a known fixed supported load `f0`. The
supported displacement solves
`K *ᵥ u ω = f0 + Bload *ᵥ WithLp.ofLp (θ ω)`; sensors `Cmat` read it and
add noise `v ~ N(0, R)`. Subtracting the deterministic offset of `f0`
gives the corrected reading. Parameter and sensor vectors live in
`EuclideanSpace`, the coordinate space of the Gaussian conditioning
interface, while structural matrices act on plain functions; the two are
related only by `WithLp.ofLp` and `WithLp.toLp 2`, and the observation
matrix `H = loadObservationMatrix r a b S k Cmat Bload` acts on
parameters through `Matrix.toEuclideanLin`.

Under the proper Gaussian prior `θ ~ N(m, Sθ)` with `Sθ` positive
semidefinite, independent noise and an invertible innovation covariance
`H Sθ Hᵀ + R`, the conditional law of `θ` given the corrected reading is
the linear-Gaussian posterior with gain `Sθ Hᵀ (H Sθ Hᵀ + R)⁻¹`. No
identifiability hypothesis is made: a proper prior gives a well-defined
posterior even when the load parameters are not identifiable from the
readings. Positive definite sensor noise supplies the invertibility
premise for every `H`, checked as an instance in the test module. Units:
`θ` in load-parameter units, `Cmat · K⁻¹ · Bload` lands in sensor units,
`Sθ` in load-parameter units squared, `R` in sensor units squared.

## ii. Key results

- `Mechanics.TrussCompatibility.toLp_sensor_eq_toEuclideanLin_add_offset`:
  the sensor reading in Gaussian-interface coordinates is the observation
  matrix applied to `θ` plus the deterministic offset of `f0`.
- `Mechanics.TrussCompatibility.condDistrib_loadParameter_correctedReading`:
  the Gaussian posterior of the load parameters given the corrected
  reading.

## iii. Table of contents

- A. Sensor reading in Gaussian-interface coordinates
- B. Gaussian posterior of the load parameters

## iv. References

- `PhyslibExt.Mechanics.TrussCompatibility` for the supported-stiffness
  model, `axialCompatibility` and `loadObservationMatrix`.
- `MathlibExt.Probability.Distributions.GaussianConditioning` for the
  linear-Gaussian conditioning theorem.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

namespace Mechanics.TrussCompatibility

/-! ## A. Sensor reading in Gaussian-interface coordinates -/

/-- Sensor reading in Gaussian-interface coordinates: at
positive-definite fixed supported stiffness, a supported displacement
`u` solving the supported system at load `f0 + Bload *ᵥ ofLp θ` is
read by the sensors, as a Euclidean vector, as the observation matrix
applied to `θ` plus the deterministic offset of the known load `f0`.
Uses the supported inverse characterization
`supported_mulVec_eq_iff_inv_mulVec`. -/
lemma toLp_sensor_eq_toEuclideanLin_add_offset {J M : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    {nf np nm : ℕ}
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) (Fin nf) ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef)
    (Cmat : Matrix (Fin nm) (Fin nf) ℝ)
    (Bload : Matrix (Fin nf) (Fin np) ℝ) (f0 : Fin nf → ℝ)
    {u : Fin nf → ℝ} {θ : EuclideanSpace ℝ (Fin np)}
    (hu : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u
          = f0 + Bload *ᵥ WithLp.ofLp θ) :
    WithLp.toLp 2 (Cmat *ᵥ u)
      = Matrix.toEuclideanLin
          (loadObservationMatrix r a b S k Cmat Bload) θ
        + WithLp.toLp 2
          (Cmat *ᵥ (((axialCompatibility r a b * S)ᵀ
            * Matrix.diagonal k
            * (axialCompatibility r a b * S))⁻¹ *ᵥ f0)) := by
  have hu_eq : u = ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S))⁻¹ *ᵥ
          (f0 + Bload *ᵥ WithLp.ofLp θ) :=
    (supported_mulVec_eq_iff_inv_mulVec r a b S k hPD).mp hu
  rw [hu_eq, Matrix.mulVec_add, Matrix.mulVec_add, WithLp.toLp_add]
  rw [add_comm]
  congr 1
  unfold loadObservationMatrix
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rfl

/-! ## B. Gaussian posterior of the load parameters -/

/-- Gaussian posterior of the load parameters given the corrected
sensor reading: at positive-definite fixed supported stiffness `K`,
with the displacement `u ω` solving `K *ᵥ u ω = f0 + Bload *ᵥ θ ω`
at every outcome `ω`, measurable `θ` and `v`, a Gaussian prior
`θ ~ N(m, Sθ)` and independent Gaussian sensor noise `v ~ N(0, R)`
(`Sθ` and `R` positive semidefinite) and an invertible innovation
covariance, the conditional law of `θ` given the corrected
reading `toLp (Cmat *ᵥ u) + v - toLp (Cmat *ᵥ (K⁻¹ *ᵥ f0))` is, for
almost every reading `y`, Gaussian with mean
`m + Sθ Hᵀ (H Sθ Hᵀ + R)⁻¹ (y - H m)` and covariance
`Sθ - Sθ Hᵀ (H Sθ Hᵀ + R)⁻¹ H Sθ`, with `H` the load observation
matrix. No identifiability hypothesis is made. Uses the supported
inverse characterization `supported_mulVec_eq_iff_inv_mulVec` and the
linear-Gaussian conditioning theorem
`MetaMathlibExt.condDistrib_linear_add_of_indepFun`. -/
theorem condDistrib_loadParameter_correctedReading {J M : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    {nf np nm : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) (Fin nf) ℝ) (k : M → ℝ)
    (hPD : ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)).PosDef)
    (Cmat : Matrix (Fin nm) (Fin nf) ℝ)
    (Bload : Matrix (Fin nf) (Fin np) ℝ) (f0 : Fin nf → ℝ)
    {θ : Ω → EuclideanSpace ℝ (Fin np)}
    {v : Ω → EuclideanSpace ℝ (Fin nm)} {u : Ω → Fin nf → ℝ}
    (hu : ∀ ω, ((axialCompatibility r a b * S)ᵀ * Matrix.diagonal k
        * (axialCompatibility r a b * S)) *ᵥ u ω
          = f0 + Bload *ᵥ WithLp.ofLp (θ ω))
    (hθ : Measurable θ) (hv : Measurable v) (hind : IndepFun θ v P)
    {m : EuclideanSpace ℝ (Fin np)} {Sθ : Matrix (Fin np) (Fin np) ℝ}
    {R : Matrix (Fin nm) (Fin nm) ℝ} (hS : Sθ.PosSemidef)
    (hR : R.PosSemidef) (hθl : P.map θ = multivariateGaussian m Sθ)
    (hvl : P.map v = multivariateGaussian 0 R)
    (hinv : IsUnit (loadObservationMatrix r a b S k Cmat Bload * Sθ
        * (loadObservationMatrix r a b S k Cmat Bload)ᵀ + R).det) :
    ∀ᵐ y ∂P.map (fun ω => WithLp.toLp 2 (Cmat *ᵥ u ω) + v ω
        - WithLp.toLp 2
          (Cmat *ᵥ (((axialCompatibility r a b * S)ᵀ
            * Matrix.diagonal k
            * (axialCompatibility r a b * S))⁻¹ *ᵥ f0))),
      condDistrib θ (fun ω => WithLp.toLp 2 (Cmat *ᵥ u ω) + v ω
          - WithLp.toLp 2
            (Cmat *ᵥ (((axialCompatibility r a b * S)ᵀ
              * Matrix.diagonal k
              * (axialCompatibility r a b * S))⁻¹ *ᵥ f0))) P y =
        multivariateGaussian
          (m + toEuclideanLin
              (Sθ * (loadObservationMatrix r a b S k Cmat Bload)ᵀ
                * (loadObservationMatrix r a b S k Cmat Bload * Sθ
                  * (loadObservationMatrix r a b S k Cmat Bload)ᵀ
                  + R)⁻¹)
              (y - toEuclideanLin
                (loadObservationMatrix r a b S k Cmat Bload) m))
          (Sθ - Sθ * (loadObservationMatrix r a b S k Cmat Bload)ᵀ
              * (loadObservationMatrix r a b S k Cmat Bload * Sθ
                * (loadObservationMatrix r a b S k Cmat Bload)ᵀ
                + R)⁻¹
              * (loadObservationMatrix r a b S k Cmat Bload * Sθ)) := by
  have h_obs : (fun ω => WithLp.toLp 2 (Cmat *ᵥ u ω) + v ω
        - WithLp.toLp 2
          (Cmat *ᵥ (((axialCompatibility r a b * S)ᵀ
            * Matrix.diagonal k
            * (axialCompatibility r a b * S))⁻¹ *ᵥ f0)))
      = (fun ω => toEuclideanLin
          (loadObservationMatrix r a b S k Cmat Bload) (θ ω) + v ω) := by
    funext ω
    have h1 := toLp_sensor_eq_toEuclideanLin_add_offset r a b S k hPD
      Cmat Bload f0 (hu ω)
    rw [h1]
    abel
  rw [h_obs]
  exact MetaMathlibExt.condDistrib_linear_add_of_indepFun hθ hv hind hS hR hθl hvl
    (loadObservationMatrix r a b S k Cmat Bload) hinv
end Mechanics.TrussCompatibility
