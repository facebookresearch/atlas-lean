/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.ShallowWaterHydrostaticReconstruction
public import MathlibExt.Analysis.ODE.ContinuumBalances

/-!
# Shallow-water hydrostatic reconstruction: lake-at-rest cell update

The fully discrete hydrostatic-reconstruction update on a wall-bounded
chain preserves every strictly wet lake-at-rest cell exactly.

## i. Overview

This module extends the one-face balance in
`PhyslibExt.EarthScience.ShallowWaterHydrostaticReconstruction` to one
explicit update step on a chain of `n + 1` cells indexed by
`Fin (n + 1)` towards increasing `x`. Cell `i` has depth `h i`,
velocity `u i`, bed elevation `z i` and positive width `Δx i`. States
passed to the numerical flux are conserved pairs `(h, h * u)`; pairs are
(mass, momentum), and fluxes are positive towards increasing `x`.

At an interior face, the left cell uses `leftFlux` and the right cell
uses `rightFlux`, as in source (2.15). The update is source (2.28):
the old conserved state minus `(Δt / Δx i)` times the difference of the
right-face and left-face corrected fluxes. The numerical flux is
arbitrary apart from consistency on wet states. A lake at rest has one
free-surface elevation `η = h i + z i`, strict wetness `z i < η`, and
zero discharge `h i * u i = 0` in every cell. The physical domain also
has `0 < g` and `0 ≤ Δt`; the invariance identities themselves are exact
real equalities for arbitrary `g` and `Δt`.

The article states no boundary-face rule. This module declares one as a
modeling convention, not a source equation: both ends of the chain are
solid walls with a reflective ghost cell. The ghost beside a boundary
cell of depth `h`, velocity `u` and bed `z` has depth `h`, velocity
`-u` and bed `z`. The first cell uses `rightFlux` at its left wall and
the last cell uses `leftFlux` at its right wall. At rest the ghost state
equals the cell state. This ghost rule makes the wall impermeable only
for fluxes with the usual reflection symmetry; no off-rest wall claim is
made.

The momentum flux at an unequal-bed face is two-sided: the two adjacent
cells use different corrected momentum values. The mass component is
single-valued at each face, and `cellUpdate_fst_eq_discreteBalance`
identifies it with `MathlibExt.Analysis.ODE.ContinuumBalances.discreteBalance`.
Only one explicit step at a strictly wet lake at rest is treated. There
is no generic finite-volume library, approximate well-balancing claim,
positivity, entropy, CFL or convergence claim, other boundary condition,
or dry state in the invariance. Division by a cell width uses the
bundled positivity of `Δx i`; the dry control uses totalized real
division only through the flux values it constructs.

## ii. Key results

- `EarthScience.HydrostaticReconstruction.corrected_fluxes_eq_of_lake_at_rest`:
  the full corrected flux vectors at one wet lake-at-rest face.
- `EarthScience.HydrostaticReconstruction.wall_fluxes_eq_of_rest`:
  both declared wall fluxes at a wet rest cell.
- `EarthScience.HydrostaticReconstruction.cellUpdate_eq_of_lake_at_rest`:
  every cell of a wall-bounded chain is preserved by one update step.
- `EarthScience.HydrostaticReconstruction.cellUpdate_fst_eq_discreteBalance`:
  the mass update is the canonical discrete-balance step.
- `EarthScience.HydrostaticReconstruction.cellUpdate_fst_ne_of_uniform_flow`
  and `exists_cellUpdate_ne_of_dry`: nonzero discharge and the dry
  endpoint are outside the invariant.

## iii. Table of contents

- A. Wall faces, cell faces and the update
- B. Lake-at-rest invariance and controls

## iv. References

- E. Audusse, F. Bouchut, M.-O. Bristeau, R. Klein, B. Perthame,
  *A fast and stable well-balanced scheme with hydrostatic
  reconstruction for shallow water flows*, SIAM J. Sci. Comput. 25(6)
  (2004), 2050-2065. The lake at rest is (2.3) (p. 2052); the face bed,
  interface flux, reconstructed states and corrected fluxes are (2.9)
  and (2.11)-(2.16) (p. 2053), with cell orientation in (2.15);
  Theorem 2.1 (ii) with (2.18) is on p. 2054; the fully discrete scheme
  is Section 2.2, equation (2.28) (p. 2056). Equation numbers are those
  of the published article.
- `EarthScience.shallow_water_conservative_iff_primitive`.
- `PhyslibExt.EarthScience.ShallowWaterHydrostaticReconstruction`.
- `MathlibExt.Analysis.ODE.ContinuumBalances.discreteBalance`.
-/

@[expose] public section

namespace EarthScience.HydrostaticReconstruction

open MathlibExt.Analysis.ODE.ContinuumBalances (discreteBalance)

/-! ## A. Wall faces, cell faces and the update -/

/-- **Left wall flux** (declared convention): the flux `𝓕_r` that the
first cell, of depth `h`, velocity `u` and bed `z`, uses at the left
wall, whose ghost cell has depth `h`, velocity `-u` and bed `z`. -/
noncomputable def leftWallFlux (g : ℝ) (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (h u z : ℝ) : ℝ × ℝ :=
  rightFlux g numFlux h (-u) h u z z

/-- **Right wall flux** (declared convention): the flux `𝓕_l` that the
last cell, of depth `h`, velocity `u` and bed `z`, uses at the right
wall, whose ghost cell has depth `h`, velocity `-u` and bed `z`. -/
noncomputable def rightWallFlux (g : ℝ) (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (h u z : ℝ) : ℝ × ℝ :=
  leftFlux g numFlux h u h (-u) z z

/-- **Flux at the left face of cell `i`**, source (2.15): the cell is
the right cell of that face, so it uses `𝓕_r` of the face with the
previous cell, or the left wall flux for the first cell. -/
noncomputable def leftFaceFlux {n : ℕ} (g : ℝ)
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ × ℝ :=
  Fin.cases (leftWallFlux g numFlux (h 0) (u 0) (z 0))
    (fun j => rightFlux g numFlux (h j.castSucc) (u j.castSucc) (h j.succ)
      (u j.succ) (z j.castSucc) (z j.succ)) i

/-- **Flux at the right face of cell `i`**, source (2.15): the cell is
the left cell of that face, so it uses `𝓕_l` of the face with the next
cell, or the right wall flux for the last cell. -/
noncomputable def rightFaceFlux {n : ℕ} (g : ℝ)
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ × ℝ :=
  Fin.lastCases
    (rightWallFlux g numFlux (h (Fin.last n)) (u (Fin.last n)) (z (Fin.last n)))
    (fun j => leftFlux g numFlux (h j.castSucc) (u j.castSucc) (h j.succ)
      (u j.succ) (z j.castSucc) (z j.succ)) i

/-- **Explicit cell update**, source (2.28): the new conserved state of
cell `i` after one step `Δt`,
`(h i, h i * u i) - (Δt / Δx i) • (rightFaceFlux - leftFaceFlux)`. -/
noncomputable def cellUpdate {n : ℕ} (g Δt : ℝ)
    (Δx : Fin (n + 1) → {x : ℝ // 0 < x})
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ × ℝ :=
  (h i, h i * u i) - (Δt / (Δx i : ℝ)) •
    (rightFaceFlux g numFlux h u z i - leftFaceFlux g numFlux h u z i)

/-- **Face mass flux** of the chain, positive towards increasing `x`:
face `0` is the left wall and face `j.succ` is the right face of cell
`j`. -/
noncomputable def faceMassFlux {n : ℕ} (g : ℝ)
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (h u z : Fin (n + 1) → ℝ)
    (j : Fin (n + 2)) : ℝ :=
  Fin.cases (leftFaceFlux g numFlux h u z 0).1
    (fun k => (rightFaceFlux g numFlux h u z k).1) j

/-! ## B. Lake-at-rest invariance and controls -/

/-- **Corrected fluxes at a wet lake at rest.** At a face between two
cells of a lake at rest whose free surface `η` lies strictly above both
beds, every numerical flux consistent on wet states gives corrected
fluxes equal to the rest fluxes of the cells on their sides:
`𝓕_l = (0, g * hL ^ 2 / 2)` and `𝓕_r = (0, g * hR ^ 2 / 2)`, the
source's `𝓕_l = F(U_i)`, `𝓕_r = F(U_{i+1})`, mass components included. -/
lemma corrected_fluxes_eq_of_lake_at_rest {g η hL uL hR uR zL zR : ℝ}
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    (hηL : hL + zL = η) (hηR : hR + zR = η) (hwet : max zL zR < η)
    (hqL : hL * uL = 0) (hqR : hR * uR = 0) :
    leftFlux g numFlux hL uL hR uR zL zR = (0, g * hL ^ 2 / 2) ∧
      rightFlux g numFlux hL uL hR uR zL zR = (0, g * hR ^ 2 / 2) := by
  have hface := faceState_eq_of_lake_at_rest hηL hηR hwet hqL hqR
  have hHpos : 0 < η - max zL zR := sub_pos.mpr hwet
  have hDepthL : faceDepth hL zL (max zL zR) = η - max zL zR :=
    congrArg Prod.fst hface.1
  have hDepthR : faceDepth hR zR (max zL zR) = η - max zL zR :=
    congrArg Prod.fst hface.2
  have hStateL : faceState hL uL zL (max zL zR) =
      (η - max zL zR, (η - max zL zR) * 0) := by
    rw [hface.1, mul_zero]
  have hStateR : faceState hR uR zR (max zL zR) =
      (η - max zL zR, (η - max zL zR) * 0) := by
    rw [hface.2, mul_zero]
  have hIF : interfaceFlux numFlux hL uL hR uR zL zR =
      (0, g * (η - max zL zR) ^ 2 / 2) := by
    unfold interfaceFlux
    rw [hStateL, hStateR, hcons _ _ hHpos]
    simp
  constructor
  · unfold leftFlux
    rw [hIF, hDepthL]
    apply Prod.ext <;> simp
  · unfold rightFlux
    rw [hIF, hDepthR]
    apply Prod.ext <;> simp

/-- **Boundary lake state.** For a wet boundary cell at rest, `0 < h`
and `h * u = 0`, both wall fluxes of the declared reflective convention
equal the cell's rest flux `(0, g * h ^ 2 / 2)`, for every numerical
flux consistent on wet states and every bed elevation. -/
lemma wall_fluxes_eq_of_rest {g h u z : ℝ}
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    (hh : 0 < h) (hq : h * u = 0) :
    leftWallFlux g numFlux h u z = (0, g * h ^ 2 / 2) ∧
      rightWallFlux g numFlux h u z = (0, g * h ^ 2 / 2) := by
  have hqNeg : h * (-u) = 0 := by
    rw [mul_neg, hq, neg_zero]
  have h1 : h + z - z = h := add_sub_cancel_right h z
  have h2 : 0 < h + z - z := by
    rw [h1]
    exact hh
  have hz : z < h + z := sub_pos.mp h2
  have hwet : max z z < h + z := max_lt hz hz
  have hLeft := (corrected_fluxes_eq_of_lake_at_rest numFlux hcons
    (rfl : h + z = h + z) (rfl : h + z = h + z) hwet hqNeg hq).2
  have hRight := (corrected_fluxes_eq_of_lake_at_rest numFlux hcons
    (rfl : h + z = h + z) (rfl : h + z = h + z) hwet hq hqNeg).1
  constructor
  · unfold leftWallFlux
    exact hLeft
  · unfold rightWallFlux
    exact hRight

/-- **Lake-at-rest invariance of the cell update.** On a wall-bounded
chain of cells of arbitrary positive widths, with one free surface `η`
strictly above every bed and zero discharge in every cell, one explicit
step of the scheme with any time step and any numerical flux consistent
on wet states leaves every cell's conserved state unchanged. -/
theorem cellUpdate_eq_of_lake_at_rest {n : ℕ} {g η Δt : ℝ}
    (Δx : Fin (n + 1) → {x : ℝ // 0 < x})
    (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    {h u z : Fin (n + 1) → ℝ}
    (hη : ∀ i, h i + z i = η) (hwet : ∀ i, z i < η)
    (hq : ∀ i, h i * u i = 0) (i : Fin (n + 1)) :
    cellUpdate g Δt Δx numFlux h u z i = (h i, h i * u i) := by
  have hL : leftFaceFlux g numFlux h u z i = (0, g * (h i) ^ 2 / 2) := by
    refine Fin.cases ?_ ?_ i
    · unfold leftFaceFlux
      rw [Fin.cases_zero]
      have hEq : h 0 = η - z 0 := by
        have h1 : h 0 + z 0 - z 0 = η - z 0 := by rw [hη 0]
        rwa [add_sub_cancel_right] at h1
      have hpos : 0 < h 0 := by
        rw [hEq]
        exact sub_pos.mpr (hwet 0)
      exact (wall_fluxes_eq_of_rest numFlux hcons hpos (hq 0)).1
    · intro j
      unfold leftFaceFlux
      rw [Fin.cases_succ]
      exact (corrected_fluxes_eq_of_lake_at_rest numFlux hcons (hη j.castSucc)
        (hη j.succ) (max_lt (hwet j.castSucc) (hwet j.succ))
        (hq j.castSucc) (hq j.succ)).2
  have hR : rightFaceFlux g numFlux h u z i = (0, g * (h i) ^ 2 / 2) := by
    refine Fin.lastCases ?_ ?_ i
    · unfold rightFaceFlux
      rw [Fin.lastCases_last]
      have hEq : h (Fin.last n) = η - z (Fin.last n) := by
        have h1 : h (Fin.last n) + z (Fin.last n) - z (Fin.last n) =
            η - z (Fin.last n) := by rw [hη (Fin.last n)]
        rwa [add_sub_cancel_right] at h1
      have hpos : 0 < h (Fin.last n) := by
        rw [hEq]
        exact sub_pos.mpr (hwet (Fin.last n))
      exact (wall_fluxes_eq_of_rest numFlux hcons hpos
        (hq (Fin.last n))).2
    · intro j
      unfold rightFaceFlux
      rw [Fin.lastCases_castSucc]
      exact (corrected_fluxes_eq_of_lake_at_rest numFlux hcons (hη j.castSucc)
        (hη j.succ) (max_lt (hwet j.castSucc) (hwet j.succ))
        (hq j.castSucc) (hq j.succ)).1
  unfold cellUpdate
  rw [hL, hR]
  apply Prod.ext <;> simp

/-- **Conservative mass update.** On cells of a common width `Δx`, the
mass component of the update is the finite-volume step
`h i + Δt * discreteBalance Δx (faceMassFlux …) i` with one mass flux
per face, for every state and every numerical flux. -/
lemma cellUpdate_fst_eq_discreteBalance {n : ℕ} (g Δt : ℝ)
    (Δx : {x : ℝ // 0 < x}) (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (h u z : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (cellUpdate g Δt (fun _ => Δx) numFlux h u z i).1 =
      h i + Δt * discreteBalance Δx (faceMassFlux g numFlux h u z) i := by
  have hMass : ∀ hL uL hR uR zL zR,
      (leftFlux g numFlux hL uL hR uR zL zR).1 =
      (rightFlux g numFlux hL uL hR uR zL zR).1 := by
    intro hL uL hR uR zL zR
    simp [leftFlux, rightFlux]
  have hSucc : faceMassFlux g numFlux h u z i.succ =
      (rightFaceFlux g numFlux h u z i).1 := by
    simp [faceMassFlux]
  have hCast : faceMassFlux g numFlux h u z i.castSucc =
      (leftFaceFlux g numFlux h u z i).1 := by
    refine Fin.cases ?_ ?_ i
    · have hZero : (0 : Fin (n + 1)).castSucc = 0 := Fin.castSucc_zero
      rw [hZero]
      simp [faceMassFlux, leftFaceFlux]
    · intro j
      have hEq : (j.succ).castSucc = j.castSucc.succ := Fin.castSucc_succ j
      rw [hEq]
      simp only [faceMassFlux, leftFaceFlux, rightFaceFlux, Fin.cases_succ,
        Fin.lastCases_castSucc]
      exact hMass _ _ _ _ _ _
  have hCell : (cellUpdate g Δt (fun _ => Δx) numFlux h u z i).1 =
      h i - (Δt / (Δx : ℝ)) *
        ((rightFaceFlux g numFlux h u z i).1 -
          (leftFaceFlux g numFlux h u z i).1) := by
    simp [cellUpdate]
  have hDisc : discreteBalance Δx (faceMassFlux g numFlux h u z) i =
      -((rightFaceFlux g numFlux h u z i).1 -
          (leftFaceFlux g numFlux h u z i).1) / (Δx : ℝ) := by
    simp [discreteBalance, hSucc, hCast]
  have hAlg : ∀ (hh t c d : ℝ), hh - (t / d) * c = hh + t * (-c / d) := by
    intro hh t c d
    rw [div_eq_mul_inv, div_eq_mul_inv, sub_eq_add_neg]
    have hComm : d⁻¹ * c = c * d⁻¹ := mul_comm _ _
    have hStep1 : (-d⁻¹) * c = (-c) * d⁻¹ := by
      rw [neg_mul, neg_mul, hComm]
    have hA : -((t * d⁻¹) * c) = t * ((-d⁻¹) * c) := by
      have e1 : -((t * d⁻¹) * c) = (-(t * d⁻¹)) * c := (neg_mul _ _).symm
      have e2 : (-(t * d⁻¹)) = t * (-d⁻¹) := (mul_neg _ _).symm
      rw [e1, e2, mul_assoc]
    have h1 : -((t * d⁻¹) * c) = t * ((-c) * d⁻¹) := by
      rw [hA, hStep1]
    rw [h1]
  rw [hCell, hDisc]
  exact hAlg _ _ _ _

/-- **Nonzero discharge is outside the invariant.** Three cells on a
strictly rising bed under one free surface `η` above every bed, all
moving with one velocity `u ≠ 0`: for every numerical flux consistent
on wet states and every nonzero time step, the depth of the middle cell
changes. -/
lemma cellUpdate_fst_ne_of_uniform_flow {g η Δt u : ℝ}
    (Δx : Fin 3 → {x : ℝ // 0 < x}) (numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcons : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2))
    {z : Fin 3 → ℝ} (h01 : z 0 < z 1) (h12 : z 1 < z 2) (hwet : z 2 < η)
    (hu : u ≠ 0) (hΔt : Δt ≠ 0) :
    (cellUpdate g Δt Δx numFlux (fun i => η - z i) (fun _ => u) z 1).1 ≠
      η - z 1 := by
  have hMax01 : max (z 0) (z 1) = z 1 := max_eq_right (le_of_lt h01)
  have hMax12 : max (z 1) (z 2) = z 2 := max_eq_right (le_of_lt h12)
  have h1lt : z 1 < η := lt_trans h12 hwet
  have hH1pos : 0 < η - z 1 := sub_pos.mpr h1lt
  have hH2pos : 0 < η - z 2 := sub_pos.mpr hwet
  have hArg0 : (η - z 0) + z 0 - z 1 = η - z 1 := by
    rw [sub_add_cancel]
  have hArg1a : (η - z 1) + z 1 - z 1 = η - z 1 := by
    rw [sub_add_cancel]
  have hArg1b : (η - z 1) + z 1 - z 2 = η - z 2 := by
    rw [sub_add_cancel]
  have hArg2 : (η - z 2) + z 2 - z 2 = η - z 2 := by
    rw [sub_add_cancel]
  have hDepth01L : faceDepth (η - z 0) (z 0) (max (z 0) (z 1)) = η - z 1 := by
    rw [hMax01]
    unfold faceDepth
    rw [hArg0]
    exact max_eq_right (le_of_lt hH1pos)
  have hDepth01R : faceDepth (η - z 1) (z 1) (max (z 0) (z 1)) = η - z 1 := by
    rw [hMax01]
    unfold faceDepth
    rw [hArg1a]
    exact max_eq_right (le_of_lt hH1pos)
  have hDepth12L : faceDepth (η - z 1) (z 1) (max (z 1) (z 2)) = η - z 2 := by
    rw [hMax12]
    unfold faceDepth
    rw [hArg1b]
    exact max_eq_right (le_of_lt hH2pos)
  have hDepth12R : faceDepth (η - z 2) (z 2) (max (z 1) (z 2)) = η - z 2 := by
    rw [hMax12]
    unfold faceDepth
    rw [hArg2]
    exact max_eq_right (le_of_lt hH2pos)
  have hIF01 : interfaceFlux numFlux (η - z 0) u (η - z 1) u (z 0) (z 1) =
      ((η - z 1) * u, (η - z 1) * u ^ 2 + g * (η - z 1) ^ 2 / 2) := by
    unfold interfaceFlux
    have hsL : faceState (η - z 0) u (z 0) (max (z 0) (z 1)) =
        (η - z 1, (η - z 1) * u) := by
      unfold faceState
      rw [hDepth01L]
    have hsR : faceState (η - z 1) u (z 1) (max (z 0) (z 1)) =
        (η - z 1, (η - z 1) * u) := by
      unfold faceState
      rw [hDepth01R]
    rw [hsL, hsR, hcons _ _ hH1pos]
  have hIF12 : interfaceFlux numFlux (η - z 1) u (η - z 2) u (z 1) (z 2) =
      ((η - z 2) * u, (η - z 2) * u ^ 2 + g * (η - z 2) ^ 2 / 2) := by
    unfold interfaceFlux
    have hsL : faceState (η - z 1) u (z 1) (max (z 1) (z 2)) =
        (η - z 2, (η - z 2) * u) := by
      unfold faceState
      rw [hDepth12L]
    have hsR : faceState (η - z 2) u (z 2) (max (z 1) (z 2)) =
        (η - z 2, (η - z 2) * u) := by
      unfold faceState
      rw [hDepth12R]
    rw [hsL, hsR, hcons _ _ hH2pos]
  have hMass01R : (rightFlux g numFlux (η - z 0) u (η - z 1) u (z 0) (z 1)).1 =
      (η - z 1) * u := by
    unfold rightFlux
    rw [hIF01]
    simp
  have hMass12L : (leftFlux g numFlux (η - z 1) u (η - z 2) u (z 1) (z 2)).1 =
      (η - z 2) * u := by
    unfold leftFlux
    rw [hIF12]
    simp
  have h1L : (1 : Fin 3) = (0 : Fin 2).succ := rfl
  have h1R : (1 : Fin 3) = (1 : Fin 2).castSucc := rfl
  have h0c : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
  have h0s : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
  have h1c : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
  have h1s : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
  have hLeftEq : leftFaceFlux g numFlux (fun i => η - z i) (fun _ => u) z 1 =
      rightFlux g numFlux (η - z 0) u (η - z 1) u (z 0) (z 1) := by
    rw [h1L]
    unfold leftFaceFlux
    rw [Fin.cases_succ]
    simp only [h0c, h0s]
  have hRightEq : rightFaceFlux g numFlux (fun i => η - z i) (fun _ => u) z 1 =
      leftFlux g numFlux (η - z 1) u (η - z 2) u (z 1) (z 2) := by
    rw [h1R]
    unfold rightFaceFlux
    rw [Fin.lastCases_castSucc]
    simp only [h1c, h1s]
  have hCell : (cellUpdate g Δt Δx numFlux (fun i => η - z i) (fun _ => u) z 1).1 =
      (η - z 1) - (Δt / (Δx 1 : ℝ)) * ((η - z 2) * u - (η - z 1) * u) := by
    simp [cellUpdate, hLeftEq, hRightEq, hMass01R, hMass12L]
  have hdne : (Δx 1 : ℝ) ≠ 0 := ne_of_gt (Δx 1).2
  have hDiv : Δt / (Δx 1 : ℝ) ≠ 0 := div_ne_zero hΔt hdne
  have hHlt : η - z 2 < η - z 1 := sub_lt_sub_left h12 η
  have hHne : η - z 2 ≠ η - z 1 := ne_of_lt hHlt
  have hSub : (η - z 2) - (η - z 1) ≠ 0 := sub_ne_zero.mpr hHne
  have hMul : ((η - z 2) - (η - z 1)) * u ≠ 0 := mul_ne_zero hSub hu
  have hEq : (η - z 2) * u - (η - z 1) * u = ((η - z 2) - (η - z 1)) * u :=
    (sub_mul _ _ _).symm
  have hDiff : (η - z 2) * u - (η - z 1) * u ≠ 0 := by
    rw [hEq]
    exact hMul
  have hX : (Δt / (Δx 1 : ℝ)) * ((η - z 2) * u - (η - z 1) * u) ≠ 0 :=
    mul_ne_zero hDiv hDiff
  rw [hCell]
  intro hCon
  have h1 : (η - z 1) + (-((Δt / (Δx 1 : ℝ)) *
      ((η - z 2) * u - (η - z 1) * u))) = (η - z 1) + 0 := by
    rw [add_zero]
    rwa [sub_eq_add_neg] at hCon
  have h3 : -((Δt / (Δx 1 : ℝ)) * ((η - z 2) * u - (η - z 1) * u)) = 0 :=
    add_left_cancel h1
  have h4 : (Δt / (Δx 1 : ℝ)) * ((η - z 2) * u - (η - z 1) * u) = 0 :=
    neg_eq_zero.mp h3
  exact hX h4

/-- **Dry cell excluded.** Strict wetness cannot be relaxed to a free
surface equal to the highest bed. For two cells with beds `z 0 < z 1`
and `η = z 1`, a wet first cell at rest beside a dry second cell, some
numerical flux consistent on every wet state moves the first cell in one
step with any nonzero time step. -/
lemma exists_cellUpdate_ne_of_dry (g Δt : ℝ) (hΔt : Δt ≠ 0)
    (Δx : Fin 2 → {x : ℝ // 0 < x}) {z : Fin 2 → ℝ} (h01 : z 0 < z 1) :
    ∃ numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ,
      (∀ h u : ℝ, 0 < h →
        numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2)) ∧
      cellUpdate g Δt Δx numFlux (fun i => z 1 - z i) (fun _ => 0) z 0 ≠
        (z 1 - z 0, 0) := by
  let numFlux : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ :=
    fun p q => (p.2 + (1 - p.1 / p.1) * (1 - q.1 / q.1),
      p.2 ^ 2 / p.1 + g * p.1 ^ 2 / 2)
  have hcons' : ∀ h u : ℝ, 0 < h →
      numFlux (h, h * u) (h, h * u) = (h * u, h * u ^ 2 + g * h ^ 2 / 2) := by
    intro h u hh
    have hne : h ≠ 0 := ne_of_gt hh
    have hDiv : h / h = 1 := div_self hne
    have hFst : (h * u) + (1 - h / h) * (1 - h / h) = h * u := by
      simp [hDiv]
    have hPow : (h * u) ^ 2 / h = h * u ^ 2 := by
      have hEq : (h * u) ^ 2 = (h * u ^ 2) * h := by
        rw [mul_pow, pow_two h, pow_two u]
        exact (mul_right_comm _ _ _).symm
      rw [hEq]
      exact mul_div_cancel_right₀ _ hne
    have hSnd : (h * u) ^ 2 / h + g * h ^ 2 / 2 = h * u ^ 2 + g * h ^ 2 / 2 := by
      rw [hPow]
    change ((h * u) + (1 - h / h) * (1 - h / h),
      (h * u) ^ 2 / h + g * h ^ 2 / 2) = (h * u, h * u ^ 2 + g * h ^ 2 / 2)
    apply Prod.ext
    · exact hFst
    · exact hSnd
  refine ⟨numFlux, hcons', ?_⟩
  have hMax : max (z 0) (z 1) = z 1 := max_eq_right (le_of_lt h01)
  have hH0pos : 0 < z 1 - z 0 := sub_pos.mpr h01
  have hArg0 : (z 1 - z 0) + z 0 - z 1 = 0 := by
    rw [sub_add_cancel, sub_self]
  have hArg1 : (z 1 - z 1) + z 1 - z 1 = 0 := by
    rw [sub_self, zero_add, sub_self]
  have hDepth0 : faceDepth (z 1 - z 0) (z 0) (max (z 0) (z 1)) = 0 := by
    rw [hMax]
    unfold faceDepth
    rw [hArg0]
    exact max_self 0
  have hDepth1 : faceDepth (z 1 - z 1) (z 1) (max (z 0) (z 1)) = 0 := by
    rw [hMax]
    unfold faceDepth
    rw [hArg1]
    exact max_self 0
  have hArgW : (z 1 - z 0) + z 0 - z 0 = z 1 - z 0 := by
    rw [sub_add_cancel]
  have hDepthW : faceDepth (z 1 - z 0) (z 0) (z 0) = z 1 - z 0 := by
    unfold faceDepth
    rw [hArgW]
    exact max_eq_right (le_of_lt hH0pos)
  have hMaxWW : max (z 0) (z 0) = z 0 := max_self (z 0)
  have hsW0 : faceState (z 1 - z 0) (-0) (z 0) (max (z 0) (z 0)) =
      (z 1 - z 0, (z 1 - z 0) * 0) := by
    rw [hMaxWW]
    unfold faceState
    rw [hDepthW, neg_zero]
  have hsW1 : faceState (z 1 - z 0) 0 (z 0) (max (z 0) (z 0)) =
      (z 1 - z 0, (z 1 - z 0) * 0) := by
    rw [hMaxWW]
    unfold faceState
    rw [hDepthW]
  have hIFW : interfaceFlux numFlux (z 1 - z 0) (-0) (z 1 - z 0) 0 (z 0) (z 0) =
      ((z 1 - z 0) * 0, (z 1 - z 0) * 0 ^ 2 + g * (z 1 - z 0) ^ 2 / 2) := by
    unfold interfaceFlux
    rw [hsW0, hsW1, hcons' _ _ hH0pos]
  have hMassW : (rightFlux g numFlux (z 1 - z 0) (-0) (z 1 - z 0) 0
      (z 0) (z 0)).1 = 0 := by
    unfold rightFlux
    rw [hIFW]
    simp
  have hsD0 : faceState (z 1 - z 0) 0 (z 0) (max (z 0) (z 1)) = (0, 0) := by
    simp [faceState, hDepth0]
  have hsD1 : faceState (z 1 - z 1) 0 (z 1) (max (z 0) (z 1)) = (0, 0) := by
    unfold faceState
    rw [hDepth1]
    simp
  have hDryFst : (0 : ℝ) + (1 - 0 / 0) * (1 - 0 / 0) = 1 := by simp
  have hDrySnd : (0 : ℝ) ^ 2 / 0 + g * (0 : ℝ) ^ 2 / 2 = 0 := by simp
  have hDryNF : numFlux (0, 0) (0, 0) = (1, 0) := by
    change ((0 : ℝ) + (1 - 0 / 0) * (1 - 0 / 0),
      (0 : ℝ) ^ 2 / 0 + g * (0 : ℝ) ^ 2 / 2) = (1, 0)
    apply Prod.ext
    · exact hDryFst
    · exact hDrySnd
  have hIFD : interfaceFlux numFlux (z 1 - z 0) 0 (z 1 - z 1) 0 (z 0) (z 1) =
      (1, 0) := by
    unfold interfaceFlux
    rw [hsD0, hsD1, hDryNF]
  have hMassD : (leftFlux g numFlux (z 1 - z 0) 0 (z 1 - z 1) 0
      (z 0) (z 1)).1 = 1 := by
    unfold leftFlux
    rw [hIFD]
    simp
  have hLW : leftFaceFlux g numFlux (fun i => z 1 - z i) (fun _ => 0) z 0 =
      leftWallFlux g numFlux (z 1 - z 0) 0 (z 0) := by
    simp [leftFaceFlux]
  have hWallUnfold : leftWallFlux g numFlux (z 1 - z 0) 0 (z 0) =
      rightFlux g numFlux (z 1 - z 0) (-0) (z 1 - z 0) 0 (z 0) (z 0) := rfl
  have hLeftMass0 : (leftFaceFlux g numFlux (fun i => z 1 - z i)
      (fun _ => 0) z 0).1 = 0 := by
    rw [hLW, hWallUnfold]
    exact hMassW
  have h0eq : (0 : Fin 2) = (0 : Fin 1).castSucc := rfl
  have h0c : ((0 : Fin 1).castSucc : Fin 2) = 0 := rfl
  have h0s : ((0 : Fin 1).succ : Fin 2) = 1 := rfl
  have hRightEq : rightFaceFlux g numFlux (fun i => z 1 - z i) (fun _ => 0) z 0 =
      leftFlux g numFlux (z 1 - z 0) 0 (z 1 - z 1) 0 (z 0) (z 1) := by
    rw [h0eq]
    unfold rightFaceFlux
    rw [Fin.lastCases_castSucc]
    simp only [h0c, h0s]
  have hCell : (cellUpdate g Δt Δx numFlux (fun i => z 1 - z i)
      (fun _ => 0) z 0).1 =
      (z 1 - z 0) - (Δt / (Δx 0 : ℝ)) * (1 - 0) := by
    have hC0 : (cellUpdate g Δt Δx numFlux (fun i => z 1 - z i)
        (fun _ => 0) z 0).1 = (z 1 - z 0) - (Δt / (Δx 0 : ℝ)) *
        ((rightFaceFlux g numFlux (fun i => z 1 - z i) (fun _ => 0) z 0).1 -
          (leftFaceFlux g numFlux (fun i => z 1 - z i) (fun _ => 0) z 0).1) := by
      simp [cellUpdate]
    rw [hC0, hRightEq, hLeftMass0, hMassD]
  have hdne : (Δx 0 : ℝ) ≠ 0 := ne_of_gt (Δx 0).2
  have hDiv : Δt / (Δx 0 : ℝ) ≠ 0 := div_ne_zero hΔt hdne
  have h10 : (1 : ℝ) - 0 = 1 := sub_zero 1
  have hMul1 : (Δt / (Δx 0 : ℝ)) * 1 = Δt / (Δx 0 : ℝ) := mul_one _
  have hX : (Δt / (Δx 0 : ℝ)) * (1 - 0) ≠ 0 := by
    rw [h10, hMul1]
    exact hDiv
  have hFstNe : (cellUpdate g Δt Δx numFlux (fun i => z 1 - z i)
      (fun _ => 0) z 0).1 ≠ z 1 - z 0 := by
    rw [hCell]
    intro hCon
    have h1 : (z 1 - z 0) + (-((Δt / (Δx 0 : ℝ)) * (1 - 0))) =
        (z 1 - z 0) + 0 := by
      rw [add_zero]
      rwa [sub_eq_add_neg] at hCon
    have h3 : -((Δt / (Δx 0 : ℝ)) * (1 - 0)) = 0 := add_left_cancel h1
    have h4 : (Δt / (Δx 0 : ℝ)) * (1 - 0) = 0 := neg_eq_zero.mp h3
    exact hX h4
  intro hCon
  have hF := congrArg Prod.fst hCon
  exact hFstNe hF


end EarthScience.HydrostaticReconstruction
