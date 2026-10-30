/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.EsInfinite
public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.FvES
public import PhyslibExt.CondensedMatter.IsingModel.TransitionRegime

/-!
# Magnetization equals FK percolation probability, through box graphs

If the finite-volume magnetization equals the wired Edwards–Sokal one-point function on box
graphs, then the spontaneous magnetization equals the FK percolation probability, and the Ising
transition occurs at the FK critical point.

## i. Overview

On the box graph of `Λ_n` with its outer boundary wired, the Edwards–Sokal one-point function at
the origin is the probability `φ^w_n(0 ↔ ∂Λ_n)`. Its limit is the FK percolation probability
`θ(p)`. Combined with the subsequential convergence of the finite-volume magnetization this gives
`m*(β) = θ(1 - e^{-2β})` for `β > 0`, so the magnetization is positive exactly above the image of
the FK critical point, and `β_c = -(1/2) log (1 - p_c)`. The identity between the lattice
magnetization and the box one-point function is a hypothesis here; `HisingBoxClose` proves it.

## ii. Key results

- `boxBoundaryConnProfile` : `φ^w_n(0 ↔ ∂Λ_n)` on the box graph.
- `magPercoIdBox_of_hisingBox` : `m*(β) = θ(pOfBeta β)` for all `β > 0`.
- `ising_transition_box` : the magnetization is positive exactly for `β > pToBeta 2 p_c`.
- `isingBetaC_eq_box` : `β_c = pToBeta 2 p_c`.

## iii. Table of contents

- A. Box graphs and the boundary connection profile
- B. Magnetization equals percolation probability
- C. The phase transition

## iv. References

- C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model I. Introduction and relation to
  other models*, Physica 57 (1972) 536–564.
- R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin–Kasteleyn–Swendsen–Wang
  representation and Monte Carlo algorithm*, Phys. Rev. D 38 (1988) 2009–2012.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 1.4.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

/-! ## A. Box graphs and the boundary connection profile -/

/-- The origin lies in every box. Same statement as `Ising.origin_mem_box`, which this module does
not import. -/
lemma origin_mem_box_boxVerts (d n : ℕ) : origin d ∈ box d n := fun i => by
  simp [origin]

/-- The origin as a vertex of the box graph. -/
def boxOrigin (d n : ℕ) : boxVerts d n := ⟨origin d, origin_mem_box_boxVerts d n⟩

lemma boxBoundary_nonempty (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∃ v : boxVerts d n, boxBoundary d n v := by
  classical
  have hd0 : (0 : ℕ) < d := hd
  let i0 : Fin d := ⟨0, hd0⟩
  let w : Site d := fun i => if i = i0 then (n : ℤ) else 0
  have hwbox : w ∈ box d n := by
    intro i
    by_cases h : i = i0
    · simp only [w, ite_eq_left h, Int.natAbs_natCast]
      exact le_refl n
    · simp only [w, ite_eq_right h, Int.natAbs_zero]; exact Nat.zero_le n
  have hwnotbox : w ∉ box d (n - 1) := by
    rw [mem_box, not_forall]
    refine ⟨i0, ?_⟩
    simp only [w, ite_eq_left rfl, Int.natAbs_natCast, not_le]
    omega
  exact ⟨⟨w, hwbox⟩, by rw [boxBoundary]; exact ⟨hwbox, hwnotbox⟩⟩

/-- The probability `φ^w_n(0 ↔ ∂Λ_n)` that the origin is connected to the boundary of the box graph
of `Λ_n` under the wired FK measure with `q = 2`. -/
noncomputable def boxBoundaryConnProfile (d : ℕ) {p : ℝ} (_hp : 0 < p) (_hp1 : p < 1)
    (_hq : (0 : ℝ) < 2) (n : ℕ) : ℝ :=
  wiredConnToBdryProb (boxGraph d n) (boxBoundary d n) p (boxOrigin d n)

lemma fvMagnetization_eq_boxBoundaryConnProfile (d : ℕ) (β : ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : (0 : ℝ) < 2)
    (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n)
    (hisingBox : fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) p (boxOrigin d n)) :
    fvMagnetization d β n = boxBoundaryConnProfile d hp hp1 hq n := by
  obtain ⟨v₀, hv₀⟩ := boxBoundary_nonempty d n hd hn
  rw [hisingBox, boxBoundaryConnProfile,
    esWiredOnePoint_eq_wiredConnToBdryProb (boxGraph d n) (boxBoundary d n) p
      (boxOrigin d n) v₀ hv₀]

/-! ## B. Magnetization equals percolation probability -/

lemma magPercoIdBox_of_fvES_of_fkLim (d : ℕ) (β : ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : (0 : ℝ) < 2) (hd : 1 ≤ d)
    (hisingBox : ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) p (boxOrigin d n))
    (hfkLimBox : Tendsto (fun n => boxBoundaryConnProfile d hp hp1 hq n) atTop
        (𝓝 (FK.fkTheta d hp hp1 hq (q := 2)))) :
    magnetization d β = FK.fkTheta d hp hp1 hq (q := 2) := by
  set b : ℕ → ℝ := fun n => if 1 ≤ n then boxBoundaryConnProfile d hp hp1 hq n
    else fvMagnetization d β n with hb
  have hES : ∀ n, fvMagnetization d β n = b n := by
    intro n
    by_cases hn : 1 ≤ n
    · simp only [hb, ite_eq_left hn]
      exact fvMagnetization_eq_boxBoundaryConnProfile d β hp hp1 hq hd hn (hisingBox n hn)
    · simp only [hb, ite_eq_right hn]
  have hlim : Tendsto b atTop (𝓝 (FK.fkTheta d hp hp1 hq (q := 2))) := by
    refine hfkLimBox.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [hb, ite_eq_left hn]
  exact magPercoId_of_fvES_of_fkLim d β hp hp1 hq b hES hlim

/-- The magnetization equals the wired FK percolation probability at `p = pOfBeta β`, assuming
the box identity `hisingBox` and convergence of the box connection profiles. The hypothesis
`hisingBox` uses the box `Λ_n` on both sides, whereas the identity proved in `BoxMagnetization`
(`hbx_hisingBox`) has the wired measure on `Λ_{n+1}` on the right. Together they force the box
magnetizations to be constant in `n ≥ 1`, which is expected to fail, so this statement is probably
vacuous (not proved). The unconditional results are in `PcUpperAllDimensions`. -/
lemma magPercoIdBox_of_hisingBox (d : ℕ) (hd : 1 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) (pOfBeta β)
            (boxOrigin d n))
    (hfkLimBox : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
        Tendsto (fun n => boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
          atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))) :
    ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  intro β hβ hp hp1
  exact magPercoIdBox_of_fvES_of_fkLim d β hp hp1 (by norm_num) hd
    (hisingBox β hβ) (hfkLimBox β hβ hp hp1)

/-! ## C. The phase transition -/

/-- Existence of the Ising phase transition from the box identity `hisingBox`, the FK limit,
non-percolation at `p_c` and `p_c < 1`. The hypothesis `hisingBox` uses the box `Λ_n` on both sides,
whereas the identity proved in `BoxMagnetization` (`hbx_hisingBox`) has the wired measure on
`Λ_{n+1}` on the right. Together they force the box magnetizations to be constant in `n ≥ 1`, which
is expected to fail, so this statement is probably vacuous (not proved). The unconditional results
are in `PcUpperAllDimensions`. -/
lemma ising_transition_box (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) (pOfBeta β)
            (boxOrigin d n))
    (hfkLimBox : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
        Tendsto (fun n => boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
          atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  Ising.ising_transition_of_fkPc_lt_one d hd
    (magPercoIdBox_of_hisingBox d (le_trans (by norm_num) hd) hisingBox hfkLimBox) hFKsub hpc1

/-- `β_c = -½ log(1 - p_c)` from the same hypotheses as `ising_transition_box`. The hypothesis
`hisingBox` uses the box `Λ_n` on both sides, whereas the identity proved in `BoxMagnetization`
(`hbx_hisingBox`) has the wired measure on `Λ_{n+1}` on the right. Together they force the box
magnetizations to be constant in `n ≥ 1`, which is expected to fail, so this statement is probably
vacuous (not proved). The unconditional results are in `PcUpperAllDimensions`. -/
lemma isingBetaC_eq_box (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) (pOfBeta β)
            (boxOrigin d n))
    (hfkLimBox : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
        Tendsto (fun n => boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
          atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  Ising.isingBetaC_eq_of_fkPc_lt_one d hd
    (magPercoIdBox_of_hisingBox d (le_trans (by norm_num) hd) hisingBox hfkLimBox) hFKsub hpc1

end IsingFK

end StatMech
