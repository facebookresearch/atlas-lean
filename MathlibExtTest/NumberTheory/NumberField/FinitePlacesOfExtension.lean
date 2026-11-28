/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NumberField.FinitePlacesOfExtension

open IsDedekindDomain NumberField Real

-- The identity at one place, for an arbitrary extension of number fields.
example (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 L)) (_ : w.asIdeal.LiesOver v.asIdeal),
        log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      Module.finrank K L * log (max 1 (HeightOneSpectrum.adicAbv K v x)) :=
  sum_log_max_one_adicAbv_liesOver K L v x

-- The identity over all places.
example (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L] (x : K) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 L),
        log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      Module.finrank K L *
        ∑ᶠ v : HeightOneSpectrum (𝓞 K), log (max 1 (HeightOneSpectrum.adicAbv K v x)) :=
  finsum_log_max_one_adicAbv K L x

-- The trivial extension `ℚ/ℚ`: degree one.
example (x : ℚ) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 ℚ),
        log (max 1 (HeightOneSpectrum.adicAbv ℚ w (algebraMap ℚ ℚ x))) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 ℚ), log (max 1 (HeightOneSpectrum.adicAbv ℚ v x)) := by
  rw [finsum_log_max_one_adicAbv ℚ ℚ x, Module.finrank_self, Nat.cast_one, one_mul]

-- At one place above another: `log max(1, ‖x‖_w) = e f log max(1, ‖x‖_v)`.
example (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (x : K) :
    log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) : ℕ) *
        log (max 1 (HeightOneSpectrum.adicAbv K v x)) :=
  log_max_one_adicAbv_algebraMap_liesOver K L v w x

-- `x = 1`: every term is `log 1 = 0`.
example (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 L)) (_ : w.asIdeal.LiesOver v.asIdeal),
        log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L 1))) = 0 := by
  rw [sum_log_max_one_adicAbv_liesOver K L v 1, map_one, max_self, log_one, mul_zero]
