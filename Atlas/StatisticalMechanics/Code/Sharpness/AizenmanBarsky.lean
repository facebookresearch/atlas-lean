/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib

open Set Real Filter Topology

set_option linter.unusedSectionVars false

namespace StatMech

namespace Sharpness


















def AizenmanBarskyInequality (M : ℝ → ℝ → ℝ) (J : ℝ) : Prop :=
  ∀ β h, deriv (fun β => M β h) β ≤ J * (M β h * deriv (fun h => M β h) h)





def AizenmanBarskyPDI (M : ℝ → ℝ → ℝ) : Prop :=
  ∀ β h, M β h ≤
      h * deriv (fun h => M β h) h + (M β h) ^ 2 + β * (M β h * deriv (fun β => M β h) β)
























theorem ab_inequality_implies_eq12 (M : ℝ → ℝ → ℝ) (J : ℝ)
    (hAB : AizenmanBarskyInequality M J) (β h : ℝ) (hβ : 0 ≤ β)
    (heq6 : 1 - M β h ≤ β * deriv (fun β => M β h) β) :
    1 - M β h ≤ (β * J) * (M β h * deriv (fun h => M β h) h) := by
  
  have hmul : β * deriv (fun β => M β h) β
      ≤ β * (J * (M β h * deriv (fun h => M β h) h)) :=
    mul_le_mul_of_nonneg_left (hAB β h) hβ
  calc 1 - M β h ≤ β * deriv (fun β => M β h) β := heq6
    _ ≤ β * (J * (M β h * deriv (fun h => M β h) h)) := hmul
    _ = (β * J) * (M β h * deriv (fun h => M β h) h) := by ring
























theorem ab_field_sq_lower_bound (K : ℝ) (hK : 0 < K) (m : ℝ → ℝ)
    (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ m h)
    (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv m h)
    (hm0 : m 0 = 0)
    (heq12 : ∀ h ∈ Ici (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h))
    (h₀ : ℝ) (hh₀ : 0 < h₀) (hle : m h₀ ≤ 1 / 2) :
    h₀ / K ≤ (m h₀) ^ 2 := by
  
  have hMono : MonotoneOn m (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun h hh => (hdiff h hh).continuousAt.continuousWithinAt
    · intro h hh
      rw [interior_Ici] at hh
      exact (hdiff h (mem_Ici.mpr (le_of_lt hh))).differentiableWithinAt
    · intro h hh
      rw [interior_Ici] at hh
      exact hmono h (mem_Ici.mpr (le_of_lt hh))
  
  have hbound : ∀ h ∈ Icc (0 : ℝ) h₀, m h ≤ 1 / 2 := by
    intro h hh
    calc m h ≤ m h₀ := hMono (mem_Ici.mpr hh.1) (mem_Ici.mpr (le_of_lt hh₀)) hh.2
      _ ≤ 1 / 2 := hle
  
  set g : ℝ → ℝ := fun h => (m h) ^ 2 - h / K with hg
  
  have hgderiv : ∀ h ∈ Ioo (0 : ℝ) h₀, deriv g h = 2 * m h * deriv m h - 1 / K := by
    intro h hh
    have hhI : h ∈ Ici (0 : ℝ) := mem_Ici.mpr (le_of_lt hh.1)
    have hd : HasDerivAt g (2 * m h * deriv m h - 1 / K) h := by
      have h1 : HasDerivAt (fun h => (m h) ^ 2) (2 * m h * deriv m h) h := by
        have hh2 := ((hdiff h hhI).hasDerivAt).pow 2
        simpa [pow_one, mul_comm] using hh2
      have h2 : HasDerivAt (fun h : ℝ => h / K) (1 / K) h := by
        simpa using (hasDerivAt_id h).div_const K
      simpa using h1.sub h2
    exact hd.deriv
  
  have hgnn : ∀ h ∈ Ioo (0 : ℝ) h₀, 0 ≤ deriv g h := by
    intro h hh
    rw [hgderiv h hh]
    have hhI : h ∈ Ici (0 : ℝ) := mem_Ici.mpr (le_of_lt hh.1)
    have hAB' := heq12 h hhI
    have hmle : m h ≤ 1 / 2 := hbound h ⟨le_of_lt hh.1, le_of_lt hh.2⟩
    
    have hhalf : (1 : ℝ) / 2 ≤ K * (m h * deriv m h) := by linarith
    rw [sub_nonneg, div_le_iff₀ hK]
    nlinarith [hhalf]
  
  have hgMono : MonotoneOn g (Icc (0 : ℝ) h₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 h₀)
    · apply ContinuousOn.sub
      · apply ContinuousOn.pow
        intro h hh
        exact (hdiff h (Icc_subset_Ici_self hh)).continuousAt.continuousWithinAt
      · exact continuousOn_id.div_const K
    · intro h hh
      rw [interior_Icc] at hh
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.sub
      · exact (hdiff h (mem_Ici.mpr (le_of_lt hh.1))).pow 2
      · exact differentiableAt_id.div_const K
    · rw [interior_Icc]; exact hgnn
  
  have hg0 : g 0 = 0 := by simp [hg, hm0]
  have hfin := hgMono ⟨le_rfl, le_of_lt hh₀⟩ ⟨le_of_lt hh₀, le_rfl⟩ (le_of_lt hh₀)
  rw [hg0] at hfin
  simp only [hg] at hfin
  linarith [hfin]














theorem ab_field_sqrt_lower_bound (K : ℝ) (hK : 0 < K) (m : ℝ → ℝ)
    (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ m h)
    (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv m h)
    (hmnn : ∀ h, 0 ≤ m h)
    (hm0 : m 0 = 0)
    (heq12 : ∀ h ∈ Ici (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h))
    (h : ℝ) (hh : h ∈ Ioc (0 : ℝ) (K / 4)) :
    Real.sqrt (h / K) ≤ m h := by
  by_cases hcase : m h ≤ 1 / 2
  · 
    have hsq := ab_field_sq_lower_bound K hK m hdiff hmono hm0 heq12 h hh.1 hcase
    calc Real.sqrt (h / K) ≤ Real.sqrt ((m h) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = m h := Real.sqrt_sq (hmnn h)
  · 
    have hcase' : 1 / 2 < m h := lt_of_not_ge hcase
    have hle : h / K ≤ 1 / 4 := by
      rw [div_le_iff₀ hK]; linarith [hh.2]
    have hroot : Real.sqrt (h / K) ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hle
    have hq : Real.sqrt (1 / 4) = 1 / 2 := by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hq] at hroot
    linarith












theorem ab_field_meanfield_bound (K : ℝ) (hK : 0 < K) (m : ℝ → ℝ)
    (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ m h)
    (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv m h)
    (hmnn : ∀ h, 0 ≤ m h)
    (hm0 : m 0 = 0)
    (heq12 : ∀ h ∈ Ici (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h)) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (K / 4), c * Real.sqrt h ≤ m h := by
  refine ⟨1 / Real.sqrt K, by positivity, ?_⟩
  intro h hh
  have hbound := ab_field_sqrt_lower_bound K hK m hdiff hmono hmnn hm0 heq12 h hh
  
  have hsplit : Real.sqrt (h / K) = 1 / Real.sqrt K * Real.sqrt h := by
    rw [Real.sqrt_div (le_of_lt hh.1)]; ring
  rw [hsplit] at hbound
  exact hbound































theorem ab_perco_meanfield_sqrt (M : ℝ → ℝ → ℝ) (J : ℝ) (βc : ℝ)
    (hβc : 0 < βc) (hJ : 0 < J)
    (hAB : AizenmanBarskyInequality M J)
    (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun h => M βc h) h)
    (hmono : ∀ h ∈ Ici (0 : ℝ), 0 ≤ deriv (fun h => M βc h) h)
    (hmnn : ∀ h, 0 ≤ M βc h)
    (hm0 : M βc 0 = 0)
    (heq6 : ∀ h ∈ Ici (0 : ℝ),
      1 - M βc h ≤ βc * deriv (fun β => M β h) βc) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (βc * J / 4),
      c * Real.sqrt h ≤ M βc h := by
  set K : ℝ := βc * J with hKdef
  have hK : 0 < K := mul_pos hβc hJ
  
  have heq12 : ∀ h ∈ Ici (0 : ℝ),
      1 - M βc h ≤ K * (M βc h * deriv (fun h => M βc h) h) := by
    intro h hh
    have h6 := heq6 h hh
    exact ab_inequality_implies_eq12 M J hAB βc h (le_of_lt hβc) h6
  
  have := ab_field_meanfield_bound K hK (fun h => M βc h) hdiff hmono hmnn hm0 heq12
  simpa [hKdef] using this











theorem ab_field_sq_lower_bound_pos (K : ℝ) (hK : 0 < K) (m : ℝ → ℝ)
    (hdiff : ∀ h ∈ Ioi (0 : ℝ), DifferentiableAt ℝ m h)
    (hmono : ∀ h ∈ Ioi (0 : ℝ), 0 ≤ deriv m h)
    (hcont0 : ContinuousWithinAt m (Ici (0 : ℝ)) 0)
    (hm0 : m 0 = 0)
    (heq12 : ∀ h ∈ Ioi (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h))
    (h₀ : ℝ) (hh₀ : 0 < h₀) (hle : m h₀ ≤ 1 / 2) :
    h₀ / K ≤ (m h₀) ^ 2 := by
  have hmcont : ContinuousOn m (Ici (0 : ℝ)) := by
    intro h hh
    have hh' : 0 ≤ h := hh
    rcases eq_or_lt_of_le hh' with rfl | hh
    · exact hcont0
    · exact (hdiff h hh).continuousAt.continuousWithinAt
  have hMono : MonotoneOn m (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hmcont
    · intro h hh
      rw [interior_Ici] at hh
      exact (hdiff h hh).differentiableWithinAt
    · intro h hh
      rw [interior_Ici] at hh
      exact hmono h hh
  have hbound : ∀ h ∈ Icc (0 : ℝ) h₀, m h ≤ 1 / 2 := by
    intro h hh
    calc
      m h ≤ m h₀ := hMono (mem_Ici.mpr hh.1)
        (mem_Ici.mpr hh₀.le) hh.2
      _ ≤ 1 / 2 := hle
  let g : ℝ → ℝ := fun h => (m h) ^ 2 - h / K
  have hgderiv : ∀ h ∈ Ioo (0 : ℝ) h₀,
      deriv g h = 2 * m h * deriv m h - 1 / K := by
    intro h hh
    have hd : HasDerivAt g (2 * m h * deriv m h - 1 / K) h := by
      have h1 : HasDerivAt (fun t => (m t) ^ 2)
          (2 * m h * deriv m h) h := by
        have hh2 := ((hdiff h hh.1).hasDerivAt).pow 2
        simpa [pow_one, mul_comm] using hh2
      have h2 : HasDerivAt (fun t : ℝ => t / K) (1 / K) h := by
        simpa using (hasDerivAt_id h).div_const K
      simpa [g] using h1.sub h2
    exact hd.deriv
  have hgnn : ∀ h ∈ Ioo (0 : ℝ) h₀, 0 ≤ deriv g h := by
    intro h hh
    rw [hgderiv h hh]
    have hab := heq12 h hh.1
    have hmle : m h ≤ 1 / 2 := hbound h ⟨hh.1.le, hh.2.le⟩
    have hhalf : (1 : ℝ) / 2 ≤ K * (m h * deriv m h) := by linarith
    rw [sub_nonneg, div_le_iff₀ hK]
    nlinarith [hhalf]
  have hgMono : MonotoneOn g (Icc (0 : ℝ) h₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 h₀)
    · exact ((hmcont.mono Icc_subset_Ici_self).pow 2).sub
        (continuousOn_id.div_const K)
    · intro h hh
      rw [interior_Icc] at hh
      exact ((hdiff h hh.1).pow 2).sub
        (differentiableAt_id.div_const K) |>.differentiableWithinAt
    · rw [interior_Icc]
      exact hgnn
  have hg0 : g 0 = 0 := by simp [g, hm0]
  have hfin := hgMono ⟨le_rfl, hh₀.le⟩ ⟨hh₀.le, le_rfl⟩ hh₀.le
  rw [hg0] at hfin
  simp only [g] at hfin
  linarith



theorem ab_field_sqrt_lower_bound_pos (K : ℝ) (hK : 0 < K) (m : ℝ → ℝ)
    (hdiff : ∀ h ∈ Ioi (0 : ℝ), DifferentiableAt ℝ m h)
    (hmono : ∀ h ∈ Ioi (0 : ℝ), 0 ≤ deriv m h)
    (hcont0 : ContinuousWithinAt m (Ici (0 : ℝ)) 0)
    (hmnn : ∀ h, 0 ≤ m h) (hm0 : m 0 = 0)
    (heq12 : ∀ h ∈ Ioi (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h))
    (h : ℝ) (hh : h ∈ Ioc (0 : ℝ) (K / 4)) :
    Real.sqrt (h / K) ≤ m h := by
  by_cases hcase : m h ≤ 1 / 2
  · have hsq := ab_field_sq_lower_bound_pos K hK m hdiff hmono hcont0
      hm0 heq12 h hh.1 hcase
    calc
      Real.sqrt (h / K) ≤ Real.sqrt ((m h) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = m h := Real.sqrt_sq (hmnn h)
  · have hcase' : 1 / 2 < m h := lt_of_not_ge hcase
    have hle : h / K ≤ 1 / 4 := by
      rw [div_le_iff₀ hK]
      linarith [hh.2]
    have hroot : Real.sqrt (h / K) ≤ Real.sqrt (1 / 4) :=
      Real.sqrt_le_sqrt hle
    have hq : Real.sqrt (1 / 4) = 1 / 2 := by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [hq] at hroot
    linarith


theorem ab_field_meanfield_bound_pos (K : ℝ) (hK : 0 < K) (m : ℝ → ℝ)
    (hdiff : ∀ h ∈ Ioi (0 : ℝ), DifferentiableAt ℝ m h)
    (hmono : ∀ h ∈ Ioi (0 : ℝ), 0 ≤ deriv m h)
    (hcont0 : ContinuousWithinAt m (Ici (0 : ℝ)) 0)
    (hmnn : ∀ h, 0 ≤ m h) (hm0 : m 0 = 0)
    (heq12 : ∀ h ∈ Ioi (0 : ℝ), 1 - m h ≤ K * (m h * deriv m h)) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (K / 4), c * Real.sqrt h ≤ m h := by
  refine ⟨1 / Real.sqrt K, by positivity, ?_⟩
  intro h hh
  have hbound := ab_field_sqrt_lower_bound_pos K hK m hdiff hmono
    hcont0 hmnn hm0 heq12 h hh
  have hsplit : Real.sqrt (h / K) = 1 / Real.sqrt K * Real.sqrt h := by
    rw [Real.sqrt_div hh.1.le]
    ring
  rwa [hsplit] at hbound


def AizenmanBarskyInequalityPhysical (M : ℝ → ℝ → ℝ) (J : ℝ) : Prop :=
  ∀ β, 0 ≤ β → ∀ h, 0 < h →
    deriv (fun b => M b h) β ≤
      J * (M β h * deriv (fun t => M β t) h)




theorem ab_perco_meanfield_sqrt_physical (M : ℝ → ℝ → ℝ) (J βc : ℝ)
    (hβc : 0 < βc) (hJ : 0 < J)
    (hAB : AizenmanBarskyInequalityPhysical M J)
    (hdiff : ∀ h ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun t => M βc t) h)
    (hmono : ∀ h ∈ Ioi (0 : ℝ),
      0 ≤ deriv (fun t => M βc t) h)
    (hcont0 : ContinuousWithinAt (fun t => M βc t) (Ici (0 : ℝ)) 0)
    (hmnn : ∀ h, 0 ≤ M βc h) (hm0 : M βc 0 = 0)
    (heq6 : ∀ h ∈ Ioi (0 : ℝ),
      1 - M βc h ≤ βc * deriv (fun b => M b h) βc) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (βc * J / 4),
      c * Real.sqrt h ≤ M βc h := by
  let K := βc * J
  have hK : 0 < K := mul_pos hβc hJ
  have heq12 : ∀ h ∈ Ioi (0 : ℝ),
      1 - M βc h ≤ K * (M βc h * deriv (fun t => M βc t) h) := by
    intro h hh
    calc
      1 - M βc h ≤ βc * deriv (fun b => M b h) βc := heq6 h hh
      _ ≤ βc * (J * (M βc h * deriv (fun t => M βc t) h)) :=
        mul_le_mul_of_nonneg_left (hAB βc hβc.le h hh) hβc.le
      _ = K * (M βc h * deriv (fun t => M βc t) h) := by
        dsimp [K]
        ring
  simpa [K] using ab_field_meanfield_bound_pos K hK (fun h => M βc h)
    hdiff hmono hcont0 hmnn hm0 heq12

end Sharpness

end StatMech
