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
- `magPercoIdBox_of_fvES_of_fkLim` : `m*(β) = θ(p)` from the box Edwards–Sokal identity
  and convergence of the box connection profiles.

## iii. Table of contents

- A. Box graphs and the boundary connection profile
- B. Magnetization equals percolation probability

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

end IsingFK

end StatMech
