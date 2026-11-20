/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Code.SLE.LoewnerCapacity
import Code.SLE.LoewnerExistence

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace StatMech.SLE




















structure IsCapacityParametrized (c : LoewnerChain) (a₁ : ℝ → ℝ) : Prop where
  

  normalized : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (c.maps t) (a₁ t)
  
  rate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t




lemma IsCapacityParametrized.coeff_zero {c : LoewnerChain} {a₁ : ℝ → ℝ}
    (h : IsCapacityParametrized c a₁) : a₁ 0 = 0 := by
  have hid : HasHalfPlaneCapacity (c.maps 0) 0 :=
    hasHalfPlaneCapacity_zero_of_eq_id (fun z => c.maps_zero z)
  exact (h.normalized 0 Set.self_mem_Ici).unique hid














structure CapacityParametrizedChain where
  
  chain : LoewnerChain
  
  hull : ℝ → Set ℂ
  
  coeff : ℝ → ℝ
  
  hull_isHull : ∀ t, IsCompactHull (hull t)
  
  hull_monotone : Monotone hull
  
  capacity : IsCapacityParametrized chain coeff














theorem chordalSLE_capacity_parametrized (c : CapacityParametrizedChain) :
    ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (c.chain.maps t) (2 * t) :=
  loewner_capacity_eq_of_loewnerChain c.chain c.capacity.normalized c.capacity.rate






theorem loewnerChain_hulls_increasing (c : CapacityParametrizedChain) :
    MonotoneHullFamily c.hull :=
  ⟨c.hull_isHull, c.hull_monotone⟩





theorem chordalSLE_hull_subset (c : CapacityParametrizedChain) {s t : ℝ}
    (hst : s ≤ t) : c.hull s ⊆ c.hull t :=
  subset_of_monotoneHull (loewnerChain_hulls_increasing c) hst




theorem chordalSLE_complement_antitone (c : CapacityParametrizedChain) :
    Antitone (fun t => upperHalfPlane \ c.hull t) :=
  complement_antitone_of_monotoneHull (loewnerChain_hulls_increasing c)



theorem chordalSLE_hcap_eq (c : CapacityParametrizedChain) :
    ∀ t ∈ Ici (0 : ℝ), c.coeff t = 2 * t :=
  loewner_capacity_coeff_eq c.capacity.coeff_zero c.capacity.rate







theorem chordalSLE_normalized_map_unique (c : CapacityParametrizedChain)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) {b : ℝ}
    (hb : HasHalfPlaneCapacity (c.chain.maps t) b) : b = 2 * t :=
  hb.unique (chordalSLE_capacity_parametrized c t ht)




theorem chordalSLE_hcap_zero (c : CapacityParametrizedChain) :
    HasHalfPlaneCapacity (c.chain.maps 0) 0 := by
  have := chordalSLE_capacity_parametrized c 0 Set.self_mem_Ici
  rwa [mul_zero] at this














lemma continuous_sleDriving {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω)
    (hcont : Continuous fun t => B t ω) : Continuous (sleDriving κ B ω) := by
  unfold sleDriving
  exact continuous_const.mul hcont







noncomputable def loewnerChain_of_sle_realization {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) : LoewnerChain where
  driving := sleDriving κ B ω
  driving_continuous := continuous_sleDriving κ B ω hcont
  maps := g
  loewner := hloe

@[simp] lemma loewnerChain_of_sle_realization_maps {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) :
    (loewnerChain_of_sle_realization κ B ω g hcont hloe).maps = g := rfl

@[simp] lemma loewnerChain_of_sle_realization_driving {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) :
    (loewnerChain_of_sle_realization κ B ω g hcont hloe).driving = sleDriving κ B ω := rfl







theorem chordalSLE_realization_capacity_parametrized {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) {a₁ : ℝ → ℝ}
    (hnorm : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
    ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (2 * t) :=
  loewner_capacity_eq_of_loewnerChain
    (loewnerChain_of_sle_realization κ B ω g hcont hloe) hnorm hrate













noncomputable def capacityParametrizedChain_of_sle_realization {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) {a₁ : ℝ → ℝ}
    (K : ℝ → Set ℂ) (hKhull : ∀ t, IsCompactHull (K t)) (hKmono : Monotone K)
    (hnorm : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
    CapacityParametrizedChain where
  chain := loewnerChain_of_sle_realization κ B ω g hcont hloe
  hull := K
  coeff := a₁
  hull_isHull := hKhull
  hull_monotone := hKmono
  capacity := ⟨hnorm, hrate⟩

end StatMech.SLE
