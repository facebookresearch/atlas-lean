/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Universality.HexVertex

namespace StatMech.Universality

open Complex Filter Topology
open scoped Topology Real BigOperators










noncomputable def hexBdryCl : ℝ := Real.cos (3 * Real.pi / 8)


noncomputable def hexBdryCt : ℝ := Real.cos (Real.pi / 4)


lemma hexBdryCl_pos : 0 < hexBdryCl := by
  unfold hexBdryCl
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]


lemma hexBdryCt_pos : 0 < hexBdryCt := by
  unfold hexBdryCt; rw [Real.cos_pi_div_four]; positivity




lemma hexBdryCl_eq : hexBdryCl = Real.cos (3 * Real.pi / 8) := rfl



lemma hexBdryCt_eq : hexBdryCt = Real.cos (Real.pi / 4) := rfl























structure HexIncidence (V : Type*) where
  
  vtx : V
  
  edge : Fin 3
  deriving DecidableEq













structure HexDomain (V : Type*) where
  
  interiorVertices : Finset V
  
  pos : V → ℂ
  
  mid : V → Fin 3 → ℂ
  
  obs : ℂ → ℂ
  

  relation : ∀ v ∈ interiorVertices,
    ∑ j : Fin 3, (mid v j - pos v) * obs (mid v j) = 0

namespace HexDomain

variable {V : Type*} [DecidableEq V] (D : HexDomain V)




noncomputable def incTerm (e : HexIncidence V) : ℂ :=
  (D.mid e.vtx e.edge - D.pos e.vtx) * D.obs (D.mid e.vtx e.edge)



noncomputable def incidences : Finset (HexIncidence V) :=
  D.interiorVertices ×ˢ (Finset.univ : Finset (Fin 3))
    |>.image (fun p => ⟨p.1, p.2⟩)




noncomputable def globalSum : ℂ :=
  ∑ v ∈ D.interiorVertices, ∑ j : Fin 3, D.incTerm ⟨v, j⟩

omit [DecidableEq V] in






theorem globalSum_eq_zero : D.globalSum = 0 := by
  unfold globalSum
  apply Finset.sum_eq_zero
  intro v hv
  have h := D.relation v hv
  simpa [incTerm] using h

end HexDomain















namespace HexDomain

variable {V : Type*} [DecidableEq V] (D : HexDomain V)















structure InteriorPairing where
  
  interior : Finset (HexIncidence V)
  
  pair : HexIncidence V → HexIncidence V
  
  pair_mem : ∀ e ∈ interior, pair e ∈ interior
  
  pair_invol : ∀ e ∈ interior, pair (pair e) = e
  
  pair_ne : ∀ e ∈ interior, pair e ≠ e
  
  cancel : ∀ e ∈ interior, D.incTerm e = - D.incTerm (pair e)

omit [DecidableEq V] in







theorem interior_sum_zero (P : D.InteriorPairing) :
    ∑ e ∈ P.interior, D.incTerm e = 0 := by
  
  apply Finset.sum_involution (fun e _ => P.pair e)
  · 
    intro e he
    rw [P.cancel e he]; ring
  · 
    intro e he _; exact P.pair_ne e he
  · 
    intro e he; exact P.pair_mem e he
  · 
    intro e he; exact P.pair_invol e he




noncomputable def boundarySum (P : D.InteriorPairing) : ℂ :=
  ∑ e ∈ D.incidences \ P.interior, D.incTerm e




theorem globalSum_eq_incidences_sum (P : D.InteriorPairing)
    (hsub : P.interior ⊆ D.incidences) :
    ∑ e ∈ D.incidences, D.incTerm e
      = (∑ e ∈ P.interior, D.incTerm e) + D.boundarySum P := by
  rw [boundarySum, Finset.sum_sdiff_eq_sub hsub]; ring




theorem globalSum_eq_sum_incidences :
    D.globalSum = ∑ e ∈ D.incidences, D.incTerm e := by
  unfold globalSum incidences
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
  · 
    rintro ⟨v1, j1⟩ _ ⟨v2, j2⟩ _ h
    simp only [HexIncidence.mk.injEq] at h
    obtain ⟨hv, hj⟩ := h
    simp [hv, hj]











theorem hexBoundaryRaw (P : D.InteriorPairing) (hsub : P.interior ⊆ D.incidences) :
    D.boundarySum P = 0 := by
  have hglob : D.globalSum = 0 := D.globalSum_eq_zero
  rw [D.globalSum_eq_sum_incidences] at hglob
  rw [D.globalSum_eq_incidences_sum P hsub, D.interior_sum_zero P, zero_add] at hglob
  exact hglob

end HexDomain
















































theorem hexBoundary_of_decomp
    (lam tau ups Fa : ℝ) (raw : ℂ)
    (hraw : raw = 0)
    (hFa : Fa = 1)
    (hdecomp : raw
      = Complex.I * ((hexBdryCl * lam + hexBdryCt * tau + ups : ℝ) - (Fa : ℝ))) :
    hexBdryCl * lam + hexBdryCt * tau + ups = 1 := by
  
  rw [hraw] at hdecomp
  have hzero : Complex.I * (((hexBdryCl * lam + hexBdryCt * tau + ups : ℝ) - (Fa : ℝ)) : ℂ) = 0 :=
    hdecomp.symm
  
  have hbr : ((hexBdryCl * lam + hexBdryCt * tau + ups : ℝ) - (Fa : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h Complex.I_ne_zero
    · exact_mod_cast h
  
  have hbr' : (hexBdryCl * lam + hexBdryCt * tau + ups : ℝ) - (Fa : ℝ) = 0 := by
    have := hbr
    push_cast at this
    exact_mod_cast this
  
  rw [hFa] at hbr'
  linarith [hbr']












theorem hexBoundary_identity
    (lam tau ups : ℕ → ℝ) (Fa : ℕ → ℝ) (raw : ℕ → ℂ)
    (hraw : ∀ v, 1 ≤ v → raw v = 0)
    (hFa : ∀ v, 1 ≤ v → Fa v = 1)
    (hdecomp : ∀ v, 1 ≤ v → raw v
      = Complex.I * ((hexBdryCl * lam v + hexBdryCt * tau v + ups v : ℝ) - (Fa v : ℝ))) :
    ∀ v, 1 ≤ v → hexBdryCl * lam v + hexBdryCt * tau v + ups v = 1 := by
  intro v hv
  exact hexBoundary_of_decomp (lam v) (tau v) (ups v) (Fa v) (raw v)
    (hraw v hv) (hFa v hv) (hdecomp v hv)


















theorem hexBoundary_identity_of_domains {V : Type*} [DecidableEq V]
    (D : ℕ → HexDomain V) (P : ∀ v, (D v).InteriorPairing)
    (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
    (lam tau ups Fa : ℕ → ℝ)
    (hFa : ∀ v, 1 ≤ v → Fa v = 1)
    (hdecomp : ∀ v, 1 ≤ v → (D v).boundarySum (P v)
      = Complex.I * ((hexBdryCl * lam v + hexBdryCt * tau v + ups v : ℝ) - (Fa v : ℝ))) :
    ∀ v, 1 ≤ v → hexBdryCl * lam v + hexBdryCt * tau v + ups v = 1 := by
  intro v hv
  refine hexBoundary_of_decomp (lam v) (tau v) (ups v) (Fa v)
    ((D v).boundarySum (P v)) ?_ (hFa v hv) (hdecomp v hv)
  exact (D v).hexBoundaryRaw (P v) (hsub v)














theorem hexContour_tendsto_of_monotone_bdd (f : ℕ → ℝ) (B : ℝ)
    (hmono : Monotone f) (hbdd : ∀ n, f n ≤ B) :
    ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  have hbddAbove : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  exact ⟨_, tendsto_atTop_ciSup hmono hbddAbove⟩



















theorem hexContour_limits (lam tau ups : ℕ → ℝ)
    (hbdry : ∀ h, hexBdryCl * lam h + hexBdryCt * tau h + ups h = 1)
    (hlamMono : Monotone lam) (hupsMono : Monotone ups)
    (hlamNN : ∀ h, 0 ≤ lam h) (hupsNN : ∀ h, 0 ≤ ups h) (htauNN : ∀ h, 0 ≤ tau h) :
    ∃ Llam Ltau Lups : ℝ,
      Tendsto lam atTop (𝓝 Llam) ∧
      Tendsto tau atTop (𝓝 Ltau) ∧
      Tendsto ups atTop (𝓝 Lups) ∧
      hexBdryCl * Llam + hexBdryCt * Ltau + Lups = 1 := by
  have hcl := hexBdryCl_pos
  have hct := hexBdryCt_pos
  
  have hlamBdd : ∀ h, lam h ≤ 1 / hexBdryCl := by
    intro h
    have h1 := hbdry h
    have : hexBdryCl * lam h ≤ 1 := by
      nlinarith [mul_nonneg (le_of_lt hct) (htauNN h), hupsNN h]
    rw [le_div_iff₀ hcl]; linarith [this]
  
  have hupsBdd : ∀ h, ups h ≤ 1 := by
    intro h
    have h1 := hbdry h
    nlinarith [mul_nonneg (le_of_lt hcl) (hlamNN h), mul_nonneg (le_of_lt hct) (htauNN h)]
  
  obtain ⟨Llam, hLlam⟩ := hexContour_tendsto_of_monotone_bdd lam (1 / hexBdryCl) hlamMono hlamBdd
  obtain ⟨Lups, hLups⟩ := hexContour_tendsto_of_monotone_bdd ups 1 hupsMono hupsBdd
  
  set Ltau := (1 - hexBdryCl * Llam - Lups) / hexBdryCt with hLtaudef
  have hctne : hexBdryCt ≠ 0 := ne_of_gt hct
  have htauForm : ∀ h, tau h = (1 - hexBdryCl * lam h - ups h) / hexBdryCt := by
    intro h
    have h1 := hbdry h
    field_simp
    linarith [h1]
  have hLtau : Tendsto tau atTop (𝓝 Ltau) := by
    have : Tendsto (fun h => (1 - hexBdryCl * lam h - ups h) / hexBdryCt) atTop (𝓝 Ltau) := by
      rw [hLtaudef]
      apply Tendsto.div_const
      exact ((tendsto_const_nhds.sub (hLlam.const_mul hexBdryCl)).sub hLups)
    exact this.congr (fun h => (htauForm h).symm)
  refine ⟨Llam, Ltau, Lups, hLlam, hLtau, hLups, ?_⟩
  
  rw [hLtaudef]
  field_simp
  ring

end StatMech.Universality
