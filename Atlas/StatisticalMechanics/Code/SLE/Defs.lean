/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































import Mathlib

open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology

namespace StatMech.SLE






def upperHalfPlane : Set ℂ := {z : ℂ | 0 < z.im}

@[simp] lemma mem_upperHalfPlane {z : ℂ} : z ∈ upperHalfPlane ↔ 0 < z.im := Iff.rfl


lemma isOpen_upperHalfPlane : IsOpen upperHalfPlane := by
  simpa only [upperHalfPlane] using (isOpen_lt continuous_const Complex.continuous_im)


def closedUpperHalfPlane : Set ℂ := {z : ℂ | 0 ≤ z.im}

@[simp] lemma mem_closedUpperHalfPlane {z : ℂ} : z ∈ closedUpperHalfPlane ↔ 0 ≤ z.im := Iff.rfl


lemma isClosed_closedUpperHalfPlane : IsClosed closedUpperHalfPlane := by
  simpa only [closedUpperHalfPlane] using (isClosed_le continuous_const Complex.continuous_im)


lemma upperHalfPlane_subset_closed : upperHalfPlane ⊆ closedUpperHalfPlane :=
  fun _ hz => le_of_lt (mem_upperHalfPlane.mp hz)



def realLine : Set ℂ := {z : ℂ | z.im = 0}

@[simp] lemma mem_realLine {z : ℂ} : z ∈ realLine ↔ z.im = 0 := Iff.rfl


lemma ofReal_mem_realLine (x : ℝ) : (x : ℂ) ∈ realLine := by simp [realLine]















structure IsCompactHull (K : Set ℂ) : Prop where
  
  subset : K ⊆ upperHalfPlane
  
  bounded : Bornology.IsBounded K
  
  relClosed : ∃ C : Set ℂ, IsClosed C ∧ K = C ∩ upperHalfPlane
  
  complement_open : IsOpen (upperHalfPlane \ K)
  
  complement_connected : IsConnected (upperHalfPlane \ K)



lemma isCompactHull_empty : IsCompactHull (∅ : Set ℂ) where
  subset := Set.empty_subset _
  bounded := Bornology.isBounded_empty
  relClosed := ⟨∅, isClosed_empty, by simp⟩
  complement_open := by simpa using isOpen_upperHalfPlane
  complement_connected := by
    have h : upperHalfPlane = {c : ℂ | (0 : ℝ) < c.im} := rfl
    simp only [Set.diff_empty, h]
    exact (convex_halfSpace_im_gt 0).isConnected ⟨(0 + 1) * Complex.I, by simp⟩




















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












noncomputable def loewnerField (W : ℝ → ℝ) (t : ℝ) (w : ℂ) : ℂ := 2 / (w - (W t : ℂ))

@[simp] lemma loewnerField_apply (W : ℝ → ℝ) (t : ℝ) (w : ℂ) :
    loewnerField W t w = 2 / (w - (W t : ℂ)) := rfl




def IsLoewnerSolutionAt (W : ℝ → ℝ) (g : ℝ → ℂ → ℂ) (z : ℂ) (t : ℝ) : Prop :=
  HasDerivAt (fun s => g s z) (loewnerField W t (g t z)) t




def IsLoewnerSolutionOn (W : ℝ → ℝ) (g : ℝ → ℂ → ℂ) (z : ℂ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt (fun u => g u z) (loewnerField W t (g t z)) s t






def SatisfiesLoewnerEquation (W : ℝ → ℝ) (g : ℝ → ℂ → ℂ) : Prop :=
  (∀ z, g 0 z = z) ∧ ∀ z, ∀ t ∈ Set.Ici (0 : ℝ), IsLoewnerSolutionAt W g z t





def SatisfiesMaximalLoewnerEquation
    (W : ℝ → ℝ) (D : ℝ → Set ℂ) (g : ℝ → ℂ → ℂ) : Prop :=
  D 0 = upperHalfPlane ∧
    (∀ z ∈ D 0, g 0 z = z) ∧
    (∀ z ∈ D 0, HasDerivWithinAt (fun t => g t z)
      (loewnerField W 0 (g 0 z)) (Set.Ici (0 : ℝ)) 0) ∧
    ∀ t, 0 < t → ∀ z ∈ D t, IsLoewnerSolutionAt W g z t












structure LoewnerChain where
  
  driving : ℝ → ℝ
  
  driving_continuous : Continuous driving
  
  maps : ℝ → ℂ → ℂ
  

  loewner : SatisfiesLoewnerEquation driving maps


lemma LoewnerChain.continuous_driving (c : LoewnerChain) : Continuous c.driving :=
  c.driving_continuous


lemma LoewnerChain.maps_zero (c : LoewnerChain) (z : ℂ) : c.maps 0 z = z :=
  c.loewner.1 z


















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













noncomputable def sleDriving {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun t => Real.sqrt κ * B t ω

@[simp] lemma sleDriving_apply {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω) (t : ℝ) :
    sleDriving κ B ω t = Real.sqrt κ * B t ω := rfl





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
