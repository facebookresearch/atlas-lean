/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Basic objects of the chordal Loewner equation

Definitions for the chordal Loewner equation `∂_t g_t(z) = 2 / (g_t(z) - W_t)`, `g_0(z) = z`, in the
upper half-plane `ℍ = {z : 0 < Im z}` (Mathlib's `UpperHalfPlane.upperHalfPlaneSet`), driven by a
real function `W`, together with compact `ℍ`-hulls, half-plane capacity, and the defining properties
of chordal SLE`_κ` (driving function `√κ B_t` for a standard Brownian motion `B`). This file
contains definitions and immediate facts only; existence of solutions is in
`MathlibExt.Analysis.Complex.Loewner.LoewnerExistence` and
`MathlibExt.Analysis.Complex.Loewner.LoewnerMaximal`.

## Main definitions

* `StatMech.SLE.closedUpperHalfPlane`, `StatMech.SLE.realLine`.
* `StatMech.SLE.IsCompactHull`: a compact `ℍ`-hull.
* `StatMech.SLE.HasHalfPlaneCapacity`: `g(z) = z + a/z + o(1/z)` at infinity.
* `StatMech.SLE.loewnerField`: the vector field `2 / (w - W_t)`.
* `StatMech.SLE.IsLoewnerSolutionAt`, `StatMech.SLE.IsLoewnerSolutionOn`,
  `StatMech.SLE.SatisfiesLoewnerEquation`, `StatMech.SLE.SatisfiesMaximalLoewnerEquation`.
* `StatMech.SLE.IsStandardBrownianMotion`, `StatMech.SLE.sleDriving`, `StatMech.SLE.IsChordalSLE`.

## References

* G. F. Lawler, *Conformally Invariant Processes in the Plane*, Mathematical Surveys and Monographs
  114, Amer. Math. Soc., 2005, Chapter 4.
-/

@[expose] public section

open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology

open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)

namespace StatMech.SLE

@[simp] lemma mem_upperHalfPlane {z : ℂ} : z ∈ upperHalfPlaneSet ↔ 0 < z.im := Iff.rfl

/-- The closed upper half-plane `{z : 0 ≤ Im z}`. -/
def closedUpperHalfPlane : Set ℂ := {z : ℂ | 0 ≤ z.im}

@[simp] lemma mem_closedUpperHalfPlane {z : ℂ} : z ∈ closedUpperHalfPlane ↔ 0 ≤ z.im := Iff.rfl

lemma isClosed_closedUpperHalfPlane : IsClosed closedUpperHalfPlane := by
  simpa only [closedUpperHalfPlane] using (isClosed_le continuous_const Complex.continuous_im)

lemma upperHalfPlane_subset_closed : upperHalfPlaneSet ⊆ closedUpperHalfPlane :=
  fun _ hz => le_of_lt (mem_upperHalfPlane.mp hz)

/-- The real axis `{z : Im z = 0}` in `ℂ`. -/
def realLine : Set ℂ := {z : ℂ | z.im = 0}

@[simp] lemma mem_realLine {z : ℂ} : z ∈ realLine ↔ z.im = 0 := Iff.rfl

lemma ofReal_mem_realLine (x : ℝ) : (x : ℂ) ∈ realLine := by simp [realLine]

/-- A compact `ℍ`-hull: a bounded subset `K` of `ℍ`, relatively closed in `ℍ`, whose complement
`ℍ \ K` is open and simply connected. -/
structure IsCompactHull (K : Set ℂ) : Prop where
  subset : K ⊆ upperHalfPlaneSet
  bounded : Bornology.IsBounded K
  relClosed : ∃ C : Set ℂ, IsClosed C ∧ K = C ∩ upperHalfPlaneSet
  complement_open : IsOpen (upperHalfPlaneSet \ K)
  complement_simplyConnected : IsSimplyConnected (upperHalfPlaneSet \ K)

/-- The complement of a compact `ℍ`-hull is connected. -/
lemma IsCompactHull.complement_connected {K : Set ℂ} (hK : IsCompactHull K) :
    IsConnected (upperHalfPlaneSet \ K) :=
  hK.complement_simplyConnected.isPathConnected.isConnected

/-- The complex upper half-plane is simply connected. -/
lemma isSimplyConnected_upperHalfPlane : IsSimplyConnected upperHalfPlaneSet := by
  let e : UpperHalfPlane ≃ₜ upperHalfPlaneSet :=
    UpperHalfPlane.isEmbedding_coe.toHomeomorph.trans
      (Homeomorph.setCongr UpperHalfPlane.range_coe)
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

lemma isCompactHull_empty : IsCompactHull (∅ : Set ℂ) where
  subset := Set.empty_subset _
  bounded := Bornology.isBounded_empty
  relClosed := ⟨∅, isClosed_empty, by simp⟩
  complement_open := by simpa using isOpen_upperHalfPlaneSet
  complement_simplyConnected := by
    simpa only [Set.sdiff_empty] using isSimplyConnected_upperHalfPlane

/-- `g` is hydrodynamically normalized at infinity with half-plane capacity `a`: `g(z) - z → 0`
and `z (g(z) - z) → a` as `z → ∞`, i.e. `g(z) = z + a/z + o(1/z)`. -/
def HasHalfPlaneCapacity (g : ℂ → ℂ) (a : ℝ) : Prop :=
  Tendsto (fun z => g z - z) (cocompact ℂ) (𝓝 0) ∧
    Tendsto (fun z => z * (g z - z)) (cocompact ℂ) (𝓝 (a : ℂ))

lemma hasHalfPlaneCapacity_id : HasHalfPlaneCapacity id 0 := by
  refine ⟨?_, ?_⟩
  · have : (fun z : ℂ => id z - z) = fun _ => (0 : ℂ) := by funext z; simp
    rw [this]; exact tendsto_const_nhds
  · have : (fun z : ℂ => z * (id z - z)) = fun _ => (0 : ℂ) := by funext z; simp
    rw [this, Complex.ofReal_zero]; exact tendsto_const_nhds

lemma HasHalfPlaneCapacity.unique {g : ℂ → ℂ} {a b : ℝ}
    (ha : HasHalfPlaneCapacity g a) (hb : HasHalfPlaneCapacity g b) : a = b := by
  have hne : (Filter.cocompact ℂ).NeBot := inferInstance
  have := tendsto_nhds_unique ha.2 hb.2
  exact_mod_cast this

/-- The chordal Loewner vector field `w ↦ 2 / (w - W_t)` at time `t`. -/
noncomputable def loewnerField (W : ℝ → ℝ) (t : ℝ) (w : ℂ) : ℂ := 2 / (w - (W t : ℂ))

@[simp] lemma loewnerField_apply (W : ℝ → ℝ) (t : ℝ) (w : ℂ) :
    loewnerField W t w = 2 / (w - (W t : ℂ)) := rfl

/-- `t ↦ g_t(z)` satisfies the Loewner equation `∂_t g_t(z) = 2 / (g_t(z) - W_t)` at time `t`. -/
def IsLoewnerSolutionAt (W : ℝ → ℝ) (g : ℝ → ℂ → ℂ) (z : ℂ) (t : ℝ) : Prop :=
  HasDerivAt (fun s => g s z) (loewnerField W t (g t z)) t

/-- `t ↦ g_t(z)` satisfies the Loewner equation on `s` (derivatives within `s`). -/
def IsLoewnerSolutionOn (W : ℝ → ℝ) (g : ℝ → ℂ → ℂ) (z : ℂ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt (fun u => g u z) (loewnerField W t (g t z)) s t

/-- The Loewner trajectory from `z` extends in `ℍ` beyond time `t`. This is the intrinsic
maximal-lifetime condition used to determine the unswallowed domain. -/
def HasLoewnerForwardExtension (W : ℝ → ℝ) (z : ℂ) (t : ℝ) : Prop :=
  z ∈ upperHalfPlaneSet ∧ ∃ T, t < T ∧ ∃ γ : ℝ → ℂ,
    γ 0 = z ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt γ (loewnerField W s (γ s)) (Set.Icc (0 : ℝ) T) s) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, γ s ∈ upperHalfPlaneSet

/-- `g_0 = id` and `t ↦ g_t(z)` solves the Loewner equation for every `z ∈ ℂ` and every `t ≥ 0`,
with no domain restriction (compare `SatisfiesMaximalLoewnerEquation`, where `z` ranges over the
unswallowed domain `D_t`). -/
def SatisfiesLoewnerEquation (W : ℝ → ℝ) (g : ℝ → ℂ → ℂ) : Prop :=
  (∀ z, g 0 z = z) ∧ ∀ z, ∀ t ∈ Set.Ici (0 : ℝ), IsLoewnerSolutionAt W g z t

/-- The maximal chordal Loewner evolution with domains `D_t`. The domains are exactly the points
whose trajectories extend beyond `t`, and `g_t : D_t → ℍ` is a conformal bijection. -/
def SatisfiesMaximalLoewnerEquation
    (W : ℝ → ℝ) (D : ℝ → Set ℂ) (g : ℝ → ℂ → ℂ) : Prop :=
  D 0 = upperHalfPlaneSet ∧
    (∀ z ∈ D 0, g 0 z = z) ∧
    (∀ z ∈ D 0, HasDerivWithinAt (fun t => g t z)
      (loewnerField W 0 (g 0 z)) (Set.Ici (0 : ℝ)) 0) ∧
    (∀ t, 0 < t → ∀ z ∈ D t, IsLoewnerSolutionAt W g z t) ∧
    Continuous W ∧
    (∀ t, 0 ≤ t → D t = {z | HasLoewnerForwardExtension W z t}) ∧
    (∀ t, 0 ≤ t → Set.BijOn (g t) (D t) upperHalfPlaneSet) ∧
    ∀ t, 0 ≤ t → ∀ z ∈ D t, ConformalAt (g t) z

namespace SatisfiesMaximalLoewnerEquation
variable {W : ℝ → ℝ} {D : ℝ → Set ℂ} {g : ℝ → ℂ → ℂ}
lemma domain_zero (h : SatisfiesMaximalLoewnerEquation W D g) :
    D 0 = upperHalfPlaneSet := h.1

lemma maps_zero (h : SatisfiesMaximalLoewnerEquation W D g) {z : ℂ} (hz : z ∈ D 0) :
    g 0 z = z := h.2.1 z hz

lemma hasDerivWithinAt_zero (h : SatisfiesMaximalLoewnerEquation W D g)
    {z : ℂ} (hz : z ∈ D 0) :
    HasDerivWithinAt (fun t => g t z) (loewnerField W 0 (g 0 z)) (Set.Ici 0) 0 :=
  h.2.2.1 z hz

lemma isLoewnerSolutionAt (h : SatisfiesMaximalLoewnerEquation W D g)
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ D t) : IsLoewnerSolutionAt W g z t :=
  h.2.2.2.1 t ht z hz

lemma continuous_driving (h : SatisfiesMaximalLoewnerEquation W D g) : Continuous W :=
  h.2.2.2.2.1

lemma domain_eq (h : SatisfiesMaximalLoewnerEquation W D g) {t : ℝ} (ht : 0 ≤ t) :
    D t = {z | HasLoewnerForwardExtension W z t} := h.2.2.2.2.2.1 t ht

lemma bijOn (h : SatisfiesMaximalLoewnerEquation W D g) {t : ℝ} (ht : 0 ≤ t) :
    Set.BijOn (g t) (D t) upperHalfPlaneSet := h.2.2.2.2.2.2.1 t ht

lemma conformalAt (h : SatisfiesMaximalLoewnerEquation W D g)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ D t) : ConformalAt (g t) z :=
  h.2.2.2.2.2.2.2 t ht z hz

end SatisfiesMaximalLoewnerEquation

/-- A standard real Brownian motion indexed by `ℝ` (used for `t ≥ 0`): `B_0 = 0` a.s., continuous
paths a.s., Gaussian, with independent increments `B_t - B_s ~ N(0, t - s)`.

See also Mathlib's `ProbabilityTheory.IsPreBrownianReal` (time `ℝ≥0`, finite-dimensional laws). -/
structure IsStandardBrownianMotion {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ → Ω → ℝ) (P : Measure Ω) : Prop where
  start : ∀ᵐ ω ∂P, B 0 ω = 0
  continuous_paths : ∀ᵐ ω ∂P, Continuous fun t => B t ω
  measurable : ∀ t, Measurable (B t)
  gaussian : IsGaussianProcess (fun t ω => B t ω) P
  increment_law : ∀ s t : ℝ, s ≤ t →
    HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t - s).toNNReal) P
  indep_increments : ∀ s t u v : ℝ, s ≤ t → t ≤ u → u ≤ v →
    IndepFun (fun ω => B t ω - B s ω) (fun ω => B v ω - B u ω) P

/-- The SLE`_κ` driving function `W_t = √κ B_t(ω)`. -/
noncomputable def sleDriving {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun t => Real.sqrt κ * B t ω

@[simp] lemma sleDriving_apply {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω) (t : ℝ) :
    sleDriving κ B ω t = Real.sqrt κ * B t ω := rfl

/-- `(D, g)` is chordal SLE`_κ` in `ℍ` from `0` to `∞`: `κ ≥ 0`, `B` is a standard Brownian
motion and almost surely `g` solves the maximal Loewner equation with driving function `√κ B`.
This is a definition only; existence of SLE is not proved. -/
structure IsChordalSLE {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (B : ℝ → Ω → ℝ) (P : Measure Ω)
    (D : Ω → ℝ → Set ℂ) (g : Ω → ℝ → ℂ → ℂ) : Prop where
  kappa_nonneg : 0 ≤ κ
  isBrownian : IsStandardBrownianMotion B P
  loewner : ∀ᵐ ω ∂P, SatisfiesMaximalLoewnerEquation
    (sleDriving κ B ω) (D ω) (g ω)

lemma sleDriving_zero {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω) :
    sleDriving κ B ω 0 = Real.sqrt κ * B 0 ω := rfl

lemma sleDriving_kappa_zero {Ω : Type*} (B : ℝ → Ω → ℝ) (ω : Ω) (t : ℝ) :
    sleDriving 0 B ω t = 0 := by simp

end StatMech.SLE
