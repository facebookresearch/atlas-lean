/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.ConvexDerivLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.SuperMultiplicative
public import PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromFreeEnergy

/-!
# Derivative of the `q = 2` random-cluster free energy in the tilt variable

The finite-volume free energy per edge in the tilt variable `t` (with `p = logistic(t)`) is
differentiable with derivative the average edge density; at points where the limiting free energy
is differentiable its derivative is the limit of average densities, and identifying the one-sided
derivatives with the infinite-volume densities yields countable-exception uniqueness.

## i. Overview

For a finite graph `G`, `t ↦ |E|^{-1} log Z_G(logistic(t), 2) + log(1 + e^t)` has derivative
`|E|^{-1} E[#open edges]` (`fpd_tiltFreeEnergy_deriv_eq_avgDensity`). For a sequence of graphs whose
free energies converge to a convex `g`, the derivatives converge to `g'(t)` wherever `g` is
differentiable (`fpd_deriv_interchange_of_differentiable`). If the average densities collapse to the
free infinite-volume density (`fpd_AvgDensityCollapse`), the free density equals `g'(t)` at such
points. The predicate `fpd_IVDensityIsOneSidedDeriv` (wired and free densities are the right and
left derivatives of `g`) is equivalent to `fuc_HomogeneousFreeEnergyData` and gives uniqueness off
a countable set.

## ii. Key results

- `fpd_tiltFreeEnergy_deriv_eq_avgDensity` : the finite-volume derivative is the average density.
- `fpd_ivPressureDeriv_eq_avgDensity_limit` : the limiting derivative is the limit of average
  densities at differentiability points.
- `fpd_freeDensity_at_diff_of_collapse` : under density collapse, the free density is `g'(t)`.
- `fpd_fk_uniqueness` : countable-exception uniqueness from `fpd_IVDensityIsOneSidedDeriv`.

## iii. Table of contents

- A. Convexity of the limiting free energy
- B. Finite-volume derivatives
- C. Interchanging limit and derivative
- D. Densities as one-sided derivatives

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorems 4.58 and 4.63.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}

/-! ## A. Convexity of the limiting free energy -/

lemma fpd_exists_convex_ivPressure
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : ℕ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (hjux : ∀ m n, Gn (m + n) ≃g Gn m ⊕g Gn n)
    (hbdd : ∀ t, BddBelow (Set.range fun n =>
      (-Real.log (fkZ (Gn n) (fsc_logistic t) 2)) / n))
    (c : ℝ → ℝ) (hc : ∀ t, c t ≠ 0)
    (he : ∀ t, Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 (c t))) :
    ∃ g : ℝ → ℝ,
      (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
        ∧ ConvexOn ℝ univ g :=
  fsm_fekete_limit Gn 2 (by norm_num) hE hjux hbdd c hc he

lemma fpd_ivPressure_convexDeriv_facts
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : ℕ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (hconv : ∀ n, ConvexOn ℝ univ (ivp2_tiltFreeEnergy (Gn n) 2))
    (g : ℝ → ℝ)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t))) :
    ConvexOn ℝ univ g
      ∧ (∀ t, HasDerivWithinAt g (pressureRightDeriv g t) (Ioi t) t)
      ∧ (∀ t, HasDerivWithinAt g (pressureLeftDeriv g t) (Iio t) t)
      ∧ (∀ t, Tendsto (slope g t) (𝓝[>] t) (𝓝 (pressureRightDeriv g t)))
      ∧ (∀ t, Tendsto (slope g t) (𝓝[<] t) (𝓝 (pressureLeftDeriv g t)))
      ∧ (∀ a b, Tendsto (fun n => slope (ivp2_tiltFreeEnergy (Gn n) 2) a b) atTop
          (𝓝 (slope g a b)))
      ∧ (∀ t, pressureLeftDeriv g t ≤ pressureRightDeriv g t)
      ∧ Monotone (pressureRightDeriv g)
      ∧ Monotone (pressureLeftDeriv g)
      ∧ {t : ℝ | pressureLeftDeriv g t ≠ pressureRightDeriv g t}.Countable :=
  cdl_convexDerivLimit (fun n => ivp2_tiltFreeEnergy (Gn n) 2) g hconv hlim

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. Finite-volume derivatives -/

lemma fpd_tiltFreeEnergy_deriv_eq_avgDensity (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    HasDerivAt (ivp2_tiltFreeEnergy G 2)
      ((1 / (G.edgeFinset.card : ℝ)) * fkExpect G (fsc_logistic t) 2
        (fun ω => (openCount G ω : ℝ))) t := by
  have hbase := ivp2_tiltFreeEnergy_hasDerivAt G 2 (by norm_num) hE t
  rwa [← ivp2_cgfMean_eq_openCount_expect G 2 (by norm_num) t] at hbase

/-- The average edge density `|E|^{-1} E_{φ_{G,p,2}}[#open edges]` at `p = logistic(t)`. -/
noncomputable def fpd_avgDensity (t : ℝ) : ℝ :=
  (1 / (G.edgeFinset.card : ℝ)) * fkExpect G (fsc_logistic t) 2 (fun ω => (openCount G ω : ℝ))

/-! ## C. Interchanging limit and derivative -/

lemma fpd_deriv_interchange_of_differentiable {κ : Type*} {l : Filter κ} [l.NeBot]
    (gn : κ → ℝ → ℝ) (g : ℝ → ℝ) (dn : κ → ℝ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ univ (gn i))
    (hderiv : ∀ i t, HasDerivAt (gn i) (dn i t) t)
    (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x)))
    (t : ℝ) (hg : ConvexOn ℝ univ g)
    (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
    Tendsto (fun i => dn i t) l (𝓝 (pressureRightDeriv g t)) := by
  set L := pressureRightDeriv g t with hL
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hr := cdl_rightDeriv_tendsto_slope hg t
  have hlft := cdl_leftDeriv_tendsto_slope hg t
  rw [hdiff] at hlft
  rw [Metric.tendsto_nhdsWithin_nhds] at hr hlft
  obtain ⟨δr, hδr, hrr⟩ := hr (ε/2) (by linarith)
  obtain ⟨δl, hδl, hll⟩ := hlft (ε/2) (by linarith)
  set y := t + δr/2 with hy
  set z := t - δl/2 with hz
  have hyt : t < y := by rw [hy]; linarith
  have hzt : z < t := by rw [hz]; linarith
  have hsy : slope g t y < L + ε/2 := by
    have hyd : dist y t < δr := by
      rw [Real.dist_eq, hy, show t + δr/2 - t = δr/2 by ring, abs_of_pos (by linarith)]; linarith
    have h2 := hrr (x := y) (by rw [hy]; exact mem_Ioi.mpr (by linarith)) hyd
    rw [Real.dist_eq] at h2
    have := (abs_lt.mp h2).2; linarith
  have hsz : L - ε/2 < slope g z t := by
    have hzd : dist z t < δl := by
      rw [Real.dist_eq, hz, show t - δl/2 - t = -(δl/2) by ring, abs_of_neg (by linarith)]
      linarith
    have h2 := hll (x := z) (by rw [hz]; exact mem_Iio.mpr (by linarith)) hzd
    rw [Real.dist_eq, slope_comm] at h2
    have := (abs_lt.mp h2).1; linarith
  have hslz := cdl_slope_tendsto gn g hlim z t
  have hsly := cdl_slope_tendsto gn g hlim t y
  have hmemz : slope g z t ∈ Ioi (L - ε) := mem_Ioi.mpr (by linarith)
  have hmemy : slope g t y ∈ Iio (L + ε) := mem_Iio.mpr (by linarith)
  have hez : ∀ᶠ i in l, L - ε < slope (gn i) z t := by
    filter_upwards [hslz.eventually (isOpen_Ioi.mem_nhds hmemz)] with i hi; exact hi
  have hey : ∀ᶠ i in l, slope (gn i) t y < L + ε := by
    filter_upwards [hsly.eventually (isOpen_Iio.mem_nhds hmemy)] with i hi; exact hi
  filter_upwards [hez, hey] with i hiz hiy
  have hmem : t ∈ interior (univ : Set ℝ) := by rw [interior_univ]; trivial
  have hr' : derivWithin (gn i) (Ioi t) t = dn i t :=
    ((hderiv i t).hasDerivWithinAt (s := Ioi t)).derivWithin (uniqueDiffWithinAt_Ioi t)
  have hl' : derivWithin (gn i) (Iio t) t = dn i t :=
    ((hderiv i t).hasDerivWithinAt (s := Iio t)).derivWithin (uniqueDiffWithinAt_Iio t)
  have hle1 : slope (gn i) z t ≤ dn i t := by
    have h3 := (hconv i).slope_le_leftDeriv_of_mem_interior (mem_univ z) hmem hzt
    rwa [hl'] at h3
  have hle2 : dn i t ≤ slope (gn i) t y := by
    have h3 := (hconv i).rightDeriv_le_slope_of_mem_interior hmem (mem_univ y) hyt
    rwa [hr'] at h3
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

lemma fpd_ivPressureDeriv_eq_avgDensity_limit
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : ℕ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (t : ℝ) (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
    Tendsto (fun n => fpd_avgDensity (Gn n) t) atTop (𝓝 (pressureRightDeriv g t)) :=
  fpd_deriv_interchange_of_differentiable
    (fun n => ivp2_tiltFreeEnergy (Gn n) 2) g
    (fun n => fpd_avgDensity (Gn n))
    (fun n => ivp2_tiltFreeEnergy_convexOn (Gn n) 2 (by norm_num) (hE n))
    (fun n s => fpd_tiltFreeEnergy_deriv_eq_avgDensity (Gn n) (hE n) s)
    hlim t hg hdiff

/-! ## D. Densities as one-sided derivatives -/

/-- The average edge densities of the graphs `Gn n` converge to the free infinite-volume `q = 2`
density of every edge of `Λ_N`, at every `t`.
-/
def fpd_AvgDensityCollapse (d N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj] : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    Tendsto (fun n => fpd_avgDensity (Gn n) t) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))

lemma fpd_freeDensity_at_diff_of_collapse (d N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t := by
  have hderiv := fpd_ivPressureDeriv_eq_avgDensity_limit Gn hE g hg hlim t hdiff
  rw [hdiff]
  exact tendsto_nhds_unique (hcol e' t) hderiv

/-- The wired and free `q = 2` infinite-volume densities of every edge of `Λ_N` at `p =
logistic(t)`
are the right and left derivatives of `g` at `t`.
-/
def fpd_IVDensityIsOneSidedDeriv (d N : ℕ) (g : ℝ → ℝ) : Prop :=
  (∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
      wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv g t)
    ∧ (∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
        freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t)

lemma fpd_homogeneousFreeEnergyData_of_densityDeriv (d N : ℕ) {g : ℝ → ℝ}
    (hg : ConvexOn ℝ univ g) (hres : fpd_IVDensityIsOneSidedDeriv d N g) :
    fuc_HomogeneousFreeEnergyData d N :=
  ⟨g, hg, hres.1, hres.2⟩

lemma fpd_fk_uniqueness (d N : ℕ) (eb : Sym2 (boxVerts d N)) {g : ℝ → ℝ}
    (hg : ConvexOn ℝ univ g) (hres : fpd_IVDensityIsOneSidedDeriv d N g) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fuc_fk_uniqueness d N eb (fpd_homogeneousFreeEnergyData_of_densityDeriv d N hg hres)

lemma fpd_densityDeriv_imp_fsc (d N : ℕ) {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hres : fpd_IVDensityIsOneSidedDeriv d N g) (e' : Sym2 (boxVerts d N)) :
    fsc_FreeEnergyData d N e' :=
  ⟨g, hg, fun t => hres.1 e' t, fun t => hres.2 e' t⟩

lemma fpd_homogeneousFreeEnergyData_iff (d N : ℕ) :
    fuc_HomogeneousFreeEnergyData d N
      ↔ ∃ g : ℝ → ℝ, ConvexOn ℝ univ g ∧ fpd_IVDensityIsOneSidedDeriv d N g := by
  constructor
  · rintro ⟨g, hg, hw, hf⟩; exact ⟨g, hg, hw, hf⟩
  · rintro ⟨g, hg, hres⟩
    exact fpd_homogeneousFreeEnergyData_of_densityDeriv d N hg hres

end FK

end StatMech
