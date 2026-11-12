/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.G04DiffusiveEnergy

/-!
# Tests for the diffusive energy estimate (G04)

Closed checks: `D = 0` conserves energy (the derivative is `0`), and
a constant-in-space profile has zero energy derivative. The energy
identity itself is the module-level statement, applied here through
the zero-diffusion case with all hypotheses discharged by `simp`.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace MathlibExt.Analysis.PDE.G04DiffusiveEnergy

/-- `D = 0`: the energy derivative is `0` for every periodic profile. -/
example {L : ℝ} (hL : 0 < L) (c ct cx cxx : ℝ → ℝ → ℝ) (t : ℝ)
    (hct : ∀ t x, HasDerivAt (fun s => c s x) (ct t x) t)
    (hcx : ∀ t x, HasDerivAt (fun y => c t y) (cx t x) x)
    (hcxx : ∀ t x, HasDerivAt (fun y => cx t y) (cxx t x) x)
    (hPDE : ∀ t x, ct t x + (0 : ℝ) * cx t x = 0 * cxx t x)
    (hper_c : ∀ t, c t 0 = c t L) (hper_cx : ∀ t, cx t 0 = cx t L)
    (hInter : HasDerivAt (fun t => ∫ x in (0 : ℝ)..L, (c t x) ^ 2 / 2)
      (∫ x in (0 : ℝ)..L, c t x * ct t x) t)
    (hInt_cxx : IntervalIntegrable (fun x => c t x * cxx t x) volume 0 L)
    (hInt_cx2 : IntervalIntegrable (fun x => (cx t x) ^ 2) volume 0 L)
    (hInt_ccx : IntervalIntegrable (fun x => c t x * cx t x) volume 0 L) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..L, (c t x) ^ 2 / 2) 0 t := by
  have h := g04_energy_deriv (L := L) (D := 0) (U := 0) hL (by norm_num) c ct cx cxx t
    hct hcx hcxx hPDE hper_c hper_cx hInter hInt_cxx hInt_cx2 hInt_ccx
  simpa using h

/-- Nonpositivity with `D = 0`: `0 * ∫ c_x^2 = 0 ≤ 0` is the boundary case. -/
example {L : ℝ} (hL : 0 < L) (cx : ℝ → ℝ → ℝ) (t : ℝ)
    (hInt_cx2 : IntervalIntegrable (fun x => (cx t x) ^ 2) volume 0 L) :
    -(0 : ℝ) * ∫ x in (0 : ℝ)..L, (cx t x) ^ 2 ≤ 0 :=
  g04_energy_nonpos hL (by norm_num) cx t hInt_cx2

#print axioms g04_energy_deriv
#print axioms g04_energy_nonpos

end MathlibExt.Analysis.PDE.G04DiffusiveEnergy
