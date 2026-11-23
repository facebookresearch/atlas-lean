/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Shallow-water hydrostatic reconstruction: wet-bed face balance

The first-order hydrostatic reconstruction of Audusse, Bouchut,
Bristeau, Klein and Perthame, restricted to one strictly wet face of a
lake at rest. For every numerical flux consistent on wet states, the
corrected momentum flux used by each side of the face is that side's
hydrostatic momentum flux.

## i. Overview

One face between a left cell (depth `hL`, velocity `uL`, bed `zL`) and
a right cell (`hR`, `uR`, `zR`), ordered towards increasing `x`. Bed
elevations are measured upward from one fixed horizontal datum; only
bed differences enter, so the datum is arbitrary. The free-surface
elevation is `η = h + z`, not the surface perturbation of the linear
shallow-water module.

The face bed is `max zL zR`. The reconstructed depth is
`max 0 (h + z - max zL zR)`, and the reconstructed conserved state
carries the cell velocity unchanged as `(h', h' * u)`. An arbitrary
numerical flux for the homogeneous problem is evaluated at the two
reconstructed states. The corrected left and right fluxes add
`(0, g * hL ^ 2 / 2 - g * hL' ^ 2 / 2)` and
`(0, g * hR ^ 2 / 2 - g * hR' ^ 2 / 2)`, respectively. This is the
`(h, q = h * u, g)` convention of
`EarthScience.shallow_water_conservative_iff_primitive`: pairs are
(mass, momentum), the physical flux pair is
`(h * u, h * u ^ 2 + g * h ^ 2 / 2)`, and fluxes are positive towards
increasing `x`, as in
`MathlibExt.Analysis.ODE.ContinuumBalances.discreteBalance`.

The numerical flux is assumed consistent only on wet states. The lake
at rest has one free-surface elevation `η`, strict wetness
`max zL zR < η`, and zero discharge in each cell. The physical domain
also has `0 < g`; the balance identities themselves hold for every
real `g`, while the strict one-sided step inequality uses `0 < g`.
Quantities are in any consistent unit system.

Only this one face and its corrected fluxes are treated. There is no
cell update, boundary-face rule, time stepping, positivity, entropy or
convergence claim, and no dry or partially dry state in the balance.
The only division is by the literal `2`; `max` is total and exact.

## ii. Key results

- `EarthScience.HydrostaticReconstruction.faceState_eq_of_lake_at_rest`:
  both reconstructed states at a strictly wet lake at rest equal
  `(η - max zL zR, 0)`.
- `EarthScience.HydrostaticReconstruction.hydrostatic_face_balance`:
  each corrected momentum flux equals the hydrostatic momentum flux of
  the cell on its side.
- `EarthScience.HydrostaticReconstruction.interfaceFlux_snd_of_step`:
  on a step, the uncorrected interface momentum is the higher cell's
  hydrostatic flux and is strictly below the lower cell's.
- `EarthScience.HydrostaticReconstruction.exists_dry_left_face_imbalance`:
  strict wetness cannot be relaxed for fluxes assumed consistent only
  on wet states.

## iii. Table of contents

- A. Reconstruction and corrected fluxes
- B. Wet lake-at-rest balance
- C. Step and dry-endpoint controls

## iv. References

- E. Audusse, F. Bouchut, M.-O. Bristeau, R. Klein, B. Perthame,
  *A fast and stable well-balanced scheme with hydrostatic
  reconstruction for shallow water flows*, SIAM J. Sci. Comput. 25(6)
  (2004), 2050-2065. Section 2.1 gives
  the semidiscrete first-order scheme: equation (1.1) and the flux
  `F(U)` (p. 2050), the lake at rest (2.3) (p. 2052), equations
  (2.9) and (2.11)-(2.16) (p. 2053), and Theorem 2.1 (ii) with (2.18)
  (p. 2054). Equation numbers are those of the published article.
- `EarthScience.shallow_water_conservative_iff_primitive`.
- `MathlibExt.Analysis.ODE.ContinuumBalances.discreteBalance`.

## A. Reconstruction and corrected fluxes
-/

@[expose] public section

namespace EarthScience.HydrostaticReconstruction

/-- **Reconstructed depth** at a face, source (2.13): for a cell of
depth `h` on bed elevation `z`, at a face of bed elevation `zF`, the
height `max 0 (h + z - zF)` of the cell's free surface above the face
bed, truncated at zero. The scheme takes `zF = max zL zR`, source
(2.9). -/
noncomputable def faceDepth (h z zF : ℝ) : ℝ :=
  max 0 (h + z - zF)

/-- **Reconstructed face state**, source (2.12): the conserved pair
`(h', h' * u)` with `h' = faceDepth h z zF`; the cell velocity `u` is
carried unchanged. -/
noncomputable def faceState (h u z zF : ℝ) : ℝ × ℝ :=
  (faceDepth h z zF, faceDepth h z zF * u)

/-- **Interface flux** `F_{i+1/2}`, source (2.11): the numerical flux
evaluated at the reconstructed states of the face between a left cell
`(hL, uL)` on bed `zL` and a right cell `(hR, uR)` on bed `zR`, with
face bed `max zL zR`. -/
noncomputable def interfaceFlux (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hL uL hR uR zL zR : ℝ) : ℝ × ℝ :=
  numFlux (faceState hL uL zL (max zL zR)) (faceState hR uR zR (max zL zR))

/-- **Left numerical flux** `𝓕_l`, source (2.15): the interface flux
plus the left hydrostatic correction `(0, g hL² / 2 - g h'² / 2)`, where
`h'` is the left reconstructed depth. The left cell uses it at its
right face. -/
noncomputable def leftFlux (g : ℝ) (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hL uL hR uR zL zR : ℝ) : ℝ × ℝ :=
  interfaceFlux numFlux hL uL hR uR zL zR +
    (0, g * hL ^ 2 / 2 - g * faceDepth hL zL (max zL zR) ^ 2 / 2)

/-- **Right numerical flux** `𝓕_r`, source (2.16): the interface flux
plus the right hydrostatic correction `(0, g hR² / 2 - g h'² / 2)`,
where `h'` is the right reconstructed depth. The right cell uses it at
its left face. -/
noncomputable def rightFlux (g : ℝ) (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hL uL hR uR zL zR : ℝ) : ℝ × ℝ :=
  interfaceFlux numFlux hL uL hR uR zL zR +
    (0, g * hR ^ 2 / 2 - g * faceDepth hR zR (max zL zR) ^ 2 / 2)

/-! ## B. Wet lake-at-rest balance -/

/-- **Reconstruction at a wet lake at rest.** If the free surface
`η = hL + zL = hR + zR` lies strictly above both bed elevations and
both cells carry zero discharge, then both reconstructed states at the
face equal the wet rest state `(η - max zL zR, 0)`: the reconstructed
depths agree and the velocities vanish. This is the first step of the
source's proof of Theorem 2.1 (ii). -/
lemma faceState_eq_of_lake_at_rest {η hL uL hR uR zL zR : ℝ}
    (hηL : hL + zL = η) (hηR : hR + zR = η) (hwet : max zL zR < η)
    (hqL : hL * uL = 0) (hqR : hR * uR = 0) :
    faceState hL uL zL (max zL zR) = (η - max zL zR, 0) ∧
      faceState hR uR zR (max zL zR) = (η - max zL zR, 0) := by
  have hpos : 0 < η - max zL zR := sub_pos.mpr hwet
  have hdepthL : faceDepth hL zL (max zL zR) = η - max zL zR := by
    show max 0 (hL + zL - max zL zR) = η - max zL zR
    rw [hηL]
    exact max_eq_right (le_of_lt hpos)
  have hdepthR : faceDepth hR zR (max zL zR) = η - max zL zR := by
    show max 0 (hR + zR - max zL zR) = η - max zL zR
    rw [hηR]
    exact max_eq_right (le_of_lt hpos)
  have hzL : zL < η := lt_of_le_of_lt (le_max_left _ _) hwet
  have hzR : zR < η := lt_of_le_of_lt (le_max_right _ _) hwet
  have hL_eq : hL = η - zL := by rw [← hηL, add_sub_cancel_right]
  have hR_eq : hR = η - zR := by rw [← hηR, add_sub_cancel_right]
  have hLpos : 0 < hL := by rw [hL_eq]; exact sub_pos.mpr hzL
  have hRpos : 0 < hR := by rw [hR_eq]; exact sub_pos.mpr hzR
  have huL : uL = 0 := by
    rw [mul_eq_zero] at hqL
    cases hqL with
    | inl h => exact absurd h (ne_of_gt hLpos)
    | inr h => exact h
  have huR : uR = 0 := by
    rw [mul_eq_zero] at hqR
    cases hqR with
    | inl h => exact absurd h (ne_of_gt hRpos)
    | inr h => exact h
  have hleft : faceState hL uL zL (max zL zR) = (η - max zL zR, 0) := by
    show (faceDepth hL zL (max zL zR), faceDepth hL zL (max zL zR) * uL) = _
    rw [hdepthL, huL, mul_zero]
  have hright : faceState hR uR zR (max zL zR) = (η - max zL zR, 0) := by
    show (faceDepth hR zR (max zL zR), faceDepth hR zR (max zL zR) * uR) = _
    rw [hdepthR, huR, mul_zero]
  exact ⟨hleft, hright⟩

/-- **Wet-bed reconstructed face balance.** At a face between two wet
cells of a lake at rest (free surface `η` strictly above both beds, zero
discharge), and for any numerical flux consistent on wet states, each
corrected momentum flux of source (2.15)–(2.16) equals the hydrostatic momentum
flux of the cell on its side: `g * hL ^ 2 / 2` for the left flux, used by
the left cell, and `g * hR ^ 2 / 2` for the right flux, used by the right
cell. This is the momentum part of the source's identities
`𝓕_l = F(U_i)`, `𝓕_r = F(U_{i+1})` (Theorem 2.1 (ii)), on the strictly
wet domain only. -/
theorem hydrostatic_face_balance {g η hL uL hR uR zL zR : ℝ}
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    (hηL : hL + zL = η) (hηR : hR + zR = η) (hwet : max zL zR < η)
    (hqL : hL * uL = 0) (hqR : hR * uR = 0) :
    (leftFlux g numFlux hL uL hR uR zL zR).2 = g * hL ^ 2 / 2 ∧
      (rightFlux g numFlux hL uL hR uR zL zR).2 = g * hR ^ 2 / 2 := by
  have hface := faceState_eq_of_lake_at_rest hηL hηR hwet hqL hqR
  have hpos : 0 < η - max zL zR := sub_pos.mpr hwet
  have hinter : interfaceFlux numFlux hL uL hR uR zL zR
      = ((η - max zL zR) * 0, (η - max zL zR) * 0 ^ 2 + g * (η - max zL zR) ^ 2 / 2) := by
    show numFlux (faceState hL uL zL (max zL zR)) (faceState hR uR zR (max zL zR)) = _
    rw [hface.1, hface.2]
    have hc := hcons (η - max zL zR) 0 hpos
    simp only [mul_zero] at hc ⊢
    exact hc
  have hsnd : (interfaceFlux numFlux hL uL hR uR zL zR).2
      = (η - max zL zR) * 0 ^ 2 + g * (η - max zL zR) ^ 2 / 2 :=
    congrArg Prod.snd hinter
  have hdepthL : faceDepth hL zL (max zL zR) = η - max zL zR :=
    congrArg Prod.fst hface.1
  have hdepthR : faceDepth hR zR (max zL zR) = η - max zL zR :=
    congrArg Prod.fst hface.2
  have hA : (η - max zL zR) * 0 ^ 2 = 0 := by simp only [pow_two, mul_zero]
  have hleft : (leftFlux g numFlux hL uL hR uR zL zR).2 = g * hL ^ 2 / 2 := by
    show (interfaceFlux numFlux hL uL hR uR zL zR).2
      + (g * hL ^ 2 / 2 - g * faceDepth hL zL (max zL zR) ^ 2 / 2) = _
    rw [hsnd, hdepthL, hA, zero_add]
    exact add_sub_cancel _ _
  have hright : (rightFlux g numFlux hL uL hR uR zL zR).2 = g * hR ^ 2 / 2 := by
    show (interfaceFlux numFlux hL uL hR uR zL zR).2
      + (g * hR ^ 2 / 2 - g * faceDepth hR zR (max zL zR) ^ 2 / 2) = _
    rw [hsnd, hdepthR, hA, zero_add]
    exact add_sub_cancel _ _
  exact ⟨hleft, hright⟩

/-! ## C. Step and dry-endpoint controls -/

/-- **One-sided correction on a step.** For a wet lake at rest over a
step whose left bed is lower, `zL < zR`, with `0 < g` and a numerical
flux consistent on wet states, the uncorrected interface momentum flux
equals the right (higher) cell's hydrostatic flux `g * hR ^ 2 / 2` and is
strictly below the left (lower) cell's `g * hL ^ 2 / 2`. With the face
balance, only the lower side's correction is nonzero; without it the
left cell would see a spurious momentum imbalance at this face. -/
lemma interfaceFlux_snd_of_step {g η hL uL hR uR zL zR : ℝ}
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    (hg : 0 < g) (hstep : zL < zR)
    (hηL : hL + zL = η) (hηR : hR + zR = η) (hwet : max zL zR < η)
    (hqL : hL * uL = 0) (hqR : hR * uR = 0) :
    (interfaceFlux numFlux hL uL hR uR zL zR).2 < g * hL ^ 2 / 2 ∧
      (interfaceFlux numFlux hL uL hR uR zL zR).2 = g * hR ^ 2 / 2 := by
  have hmax : max zL zR = zR := max_eq_right (le_of_lt hstep)
  have hface := faceState_eq_of_lake_at_rest hηL hηR hwet hqL hqR
  have hpos : 0 < η - max zL zR := sub_pos.mpr hwet
  have hinter : interfaceFlux numFlux hL uL hR uR zL zR
      = ((η - max zL zR) * 0, (η - max zL zR) * 0 ^ 2 + g * (η - max zL zR) ^ 2 / 2) := by
    show numFlux (faceState hL uL zL (max zL zR)) (faceState hR uR zR (max zL zR)) = _
    rw [hface.1, hface.2]
    have hc := hcons (η - max zL zR) 0 hpos
    simp only [mul_zero] at hc ⊢
    exact hc
  have hif2 : (interfaceFlux numFlux hL uL hR uR zL zR).2
      = (η - max zL zR) * 0 ^ 2 + g * (η - max zL zR) ^ 2 / 2 :=
    congrArg Prod.snd hinter
  have hR_eq : hR = η - zR := by rw [← hηR, add_sub_cancel_right]
  have hL_eq : hL = η - zL := by rw [← hηL, add_sub_cancel_right]
  have hheq : η - max zL zR = hR := by rw [hmax]; exact hR_eq.symm
  have hA : hR * 0 ^ 2 = 0 := by simp only [pow_two, mul_zero]
  have heq : (interfaceFlux numFlux hL uL hR uR zL zR).2 = g * hR ^ 2 / 2 := by
    rw [hif2, hheq, hA, zero_add]
  have hzL : zL < η := lt_of_le_of_lt (le_max_left _ _) hwet
  have hzR : zR < η := lt_of_le_of_lt (le_max_right _ _) hwet
  have hLpos : 0 < hL := by rw [hL_eq]; exact sub_pos.mpr hzL
  have hRpos : 0 < hR := by rw [hR_eq]; exact sub_pos.mpr hzR
  have hlt : hR < hL := by
    rw [hR_eq, hL_eq]
    exact sub_lt_sub_left hstep η
  have hsq : hR ^ 2 < hL ^ 2 := by
    rw [pow_two, pow_two]
    exact lt_trans (mul_lt_mul_of_pos_left hlt hRpos) (mul_lt_mul_of_pos_right hlt hLpos)
  have hg2 : 0 < g / 2 := div_pos hg zero_lt_two
  have hmul := mul_lt_mul_of_pos_left hsq hg2
  constructor
  · rw [heq, ← div_mul_eq_mul_div g 2 (hR ^ 2), ← div_mul_eq_mul_div g 2 (hL ^ 2)]
    exact hmul
  · exact heq

/-- **Dry state excluded.** Strict wetness cannot be relaxed to a free
surface that touches the higher bed, for numerical fluxes assumed
consistent only on wet states. For every `g` and every step
`zL < zR`, take the lake at rest with `η = zR`: a wet left cell of depth
`zR - zL` at rest beside a dry right cell. Some numerical flux that is
consistent on every wet state gives a corrected left momentum flux
different from `g * (zR - zL) ^ 2 / 2`, because both reconstructed
states are the dry state `(0, 0)`, about which consistency on wet states
says nothing. A flux consistent also at the dry state, as in the
source's Theorem 2.1, balances at this endpoint. -/
lemma exists_dry_left_face_imbalance (g zL zR : ℝ) (hstep : zL < zR) :
    ∃ numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ,
      (∀ h u : ℝ, 0 < h →
        numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2)) ∧
      (leftFlux g numFlux (zR - zL) 0 0 0 zL zR).2 ≠ g * (zR - zL) ^ 2 / 2 := by
  refine ⟨fun p _ => (p.2, p.2 ^ 2 / p.1 + g * p.1 ^ 2 / 2 + (1 - p.1 / p.1)), ?_, ?_⟩
  · intro h u hh
    show (h * u, (h * u) ^ 2 / h + g * h ^ 2 / 2 + (1 - h / h))
      = (h * u, h * u ^ 2 + g * h ^ 2 / 2)
    have hne : h ≠ 0 := ne_of_gt hh
    have hdiv : (h * u) ^ 2 / h = h * u ^ 2 := by
      rw [div_eq_iff hne, mul_pow, mul_assoc, mul_comm (u ^ 2) h, ← mul_assoc, ← pow_two]
    rw [hdiv, div_self hne, sub_self, add_zero]
  · have hmax : max zL zR = zR := max_eq_right (le_of_lt hstep)
    have harg : (zR - zL) + zL - zR = 0 := by rw [sub_add_cancel, sub_self]
    have hdL : faceDepth (zR - zL) zL (max zL zR) = 0 := by
      show max 0 ((zR - zL) + zL - max zL zR) = 0
      rw [hmax, harg]
      exact max_self 0
    have hA1 : (faceState (zR - zL) 0 zL (max zL zR)).1 = 0 := hdL
    have hA2 : (faceState (zR - zL) 0 zL (max zL zR)).2 = 0 := by
      show faceDepth (zR - zL) zL (max zL zR) * 0 = 0
      rw [hdL, mul_zero]
    have hif2 : (interfaceFlux (fun p _ =>
        (p.2, p.2 ^ 2 / p.1 + g * p.1 ^ 2 / 2 + (1 - p.1 / p.1)))
        (zR - zL) 0 0 0 zL zR).2 = 1 := by
      show (faceState (zR - zL) 0 zL (max zL zR)).2 ^ 2
          / (faceState (zR - zL) 0 zL (max zL zR)).1
          + g * (faceState (zR - zL) 0 zL (max zL zR)).1 ^ 2 / 2
          + (1 - (faceState (zR - zL) 0 zL (max zL zR)).1
              / (faceState (zR - zL) 0 zL (max zL zR)).1) = 1
      rw [hA1, hA2]
      simp only [pow_two, mul_zero, div_zero, zero_div, sub_zero, zero_add]
    show (interfaceFlux (fun p _ =>
          (p.2, p.2 ^ 2 / p.1 + g * p.1 ^ 2 / 2 + (1 - p.1 / p.1)))
          (zR - zL) 0 0 0 zL zR).2
        + (g * (zR - zL) ^ 2 / 2 - g * faceDepth (zR - zL) zL (max zL zR) ^ 2 / 2)
        ≠ g * (zR - zL) ^ 2 / 2
    rw [hif2, hdL]
    have h0 : g * (0 : ℝ) ^ 2 / 2 = 0 := by simp only [pow_two, mul_zero, zero_div]
    rw [h0, sub_zero]
    intro hcon
    have h1 : (1 : ℝ) + g * (zR - zL) ^ 2 / 2 - g * (zR - zL) ^ 2 / 2 = 0 := by
      rw [hcon, sub_self]
    have h2 : (1 : ℝ) + g * (zR - zL) ^ 2 / 2 - g * (zR - zL) ^ 2 / 2 = 1 :=
      add_sub_cancel_right 1 _
    rw [h2] at h1
    exact one_ne_zero h1

end EarthScience.HydrostaticReconstruction
