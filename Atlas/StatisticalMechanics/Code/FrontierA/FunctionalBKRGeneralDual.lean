/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.FunctionalBKRMonotoneDual
import Code.Walls.rb3reimerclose
import Code.Walls.rc4_core
import Code.Walls.rc3_keyflipinvolutive

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.ConfigSpace
open StatMech.Walls
open StatMech.Walls.Reimer

variable {E : Type*} [Fintype E] [DecidableEq E]

private theorem kss_sum_four_comm {A B C D R : Type*} [AddCommMonoid R]
    (sA : Finset A) (sB : Finset B) (sC : Finset C) (sD : Finset D)
    (f : A → B → C → D → R) :
    (∑ a ∈ sA, ∑ b ∈ sB, ∑ c ∈ sC, ∑ d ∈ sD, f a b c d) =
      ∑ c ∈ sC, ∑ d ∈ sD, ∑ a ∈ sA, ∑ b ∈ sB, f a b c d := by
  calc
    (∑ a ∈ sA, ∑ b ∈ sB, ∑ c ∈ sC, ∑ d ∈ sD, f a b c d) =
        ∑ a ∈ sA, ∑ c ∈ sC, ∑ b ∈ sB, ∑ d ∈ sD, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c ∈ sC, ∑ a ∈ sA, ∑ b ∈ sB, ∑ d ∈ sD, f a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ sC, ∑ a ∈ sA, ∑ d ∈ sD, ∑ b ∈ sB, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c ∈ sC, ∑ d ∈ sD, ∑ a ∈ sA, ∑ b ∈ sB, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]


def kssTwist (k : ConfigSpace E × ConfigSpace E)
    (B : Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {omega | poc_keyFlip k omega ∈ B}

open Classical in

noncomputable def kssDualOrbit (A B : Set (ConfigSpace E))
    (k : ConfigSpace E × ConfigSpace E) :
    Finset (ConfigSpace E × ConfigSpace E) :=
  Finset.univ.filter fun p =>
    p ∈ dualDisjointOccurrence A B ∧ orbitKey p = k

open Classical in

noncomputable def kssDiagonalOrbit (A B : Set (ConfigSpace E))
    (k : ConfigSpace E × ConfigSpace E) :
    Finset (ConfigSpace E × ConfigSpace E) :=
  Finset.univ.filter fun p => p.1 ∈ A ∩ B ∧ orbitKey p = k

omit [Fintype E] [DecidableEq E] in


theorem dualOccurrence_to_twisted_box {A B : Set (ConfigSpace E)}
    {p : ConfigSpace E × ConfigSpace E}
    {k : ConfigSpace E × ConfigSpace E}
    (hp : p ∈ dualDisjointOccurrence A B) (hpk : orbitKey p = k) :
    p.1 ∈ disjointOccurrence A (kssTwist k B) := by
  obtain ⟨K, L, hKL, hA, hB⟩ := hp
  refine ⟨K, L, hKL, hA, ?_⟩
  intro tau htau
  change poc_keyFlip k tau ∈ B
  apply hB
  intro e he
  have heq := htau e he
  have hsnd := poc_snd_eq p k hpk
  rw [hsnd]
  simp only [poc_keyFlip, poc_flip]
  split <;> simp_all


theorem rb3_slabCardAll : poc_SlabCardAll := by
  apply rc4_residue_of_reimerCardFormAll
  apply rc17_reimerCardFormAll_of_nonMonotone
  apply rc18_nonMonotone_of_cylBoxReflInter
  exact rc20_cylBoxReflInter_of_famCylBoxResidue rb3_famCylBoxResidue



theorem imgOrbit_twist_eq_diagonalOrbit (A B : Set (ConfigSpace E))
    (k : ConfigSpace E × ConfigSpace E) :
    imgOrbit A (kssTwist k B) k = kssDiagonalOrbit A B k := by
  classical
  ext p
  simp only [imgOrbit, kssDiagonalOrbit, Finset.mem_filter,
    Finset.mem_univ, true_and, kssTwist, Set.mem_setOf_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨hpA, hpB, hpk⟩
    have hsnd := poc_snd_eq p k hpk
    rw [hsnd, rc3_keyFlip_keyFlip] at hpB
    exact ⟨⟨hpA, hpB⟩, hpk⟩
  · rintro ⟨⟨hpA, hpB⟩, hpk⟩
    have hsnd := poc_snd_eq p k hpk
    rw [hsnd, rc3_keyFlip_keyFlip]
    exact ⟨hpA, hpB, hpk⟩



theorem kssDualOrbit_card_le {n : ℕ}
    (A B : Set (ConfigSpace (Fin n)))
    (k : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    #(kssDualOrbit A B k) ≤ #(kssDiagonalOrbit A B k) := by
  classical
  calc
    #(kssDualOrbit A B k) ≤ #(boxOrbit A (kssTwist k B) k) := by
      apply Finset.card_le_card
      intro p hp
      simp only [kssDualOrbit, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp
      simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨dualOccurrence_to_twisted_box hp.1 hp.2, hp.2⟩
    _ ≤ #(imgOrbit A (kssTwist k B) k) :=
      ((poc_perOrbitCard_iff_slabCard A (kssTwist k B)).mpr
        (rb3_slabCardAll n A (kssTwist k B))) k
    _ = #(kssDiagonalOrbit A B k) := by
      rw [imgOrbit_twist_eq_diagonalOrbit]

omit [DecidableEq E] in


theorem pairWeight_eq_of_sameOrbit (phi : E → Bool → ℝ)
    {p q : ConfigSpace E × ConfigSpace E} (h : sameOrbit p q) :
    pweight phi q.1 * pweight phi q.2 =
      pweight phi p.1 * pweight phi p.2 := by
  rw [swapPair_eq_of_sameOrbit p q h]
  simp only [swapPair_fst, swapPair_snd]
  exact swapPair_weight phi _ p.1 p.2



def KSSWeightInjection (A B : Set (ConfigSpace E)) : Prop :=
  ∃ Phi : ConfigSpace E × ConfigSpace E → ConfigSpace E × ConfigSpace E,
    (∀ p, p ∈ dualDisjointOccurrence A B → (Phi p).1 ∈ A ∩ B) ∧
    (∀ (phi : E → Bool → ℝ) p, p ∈ dualDisjointOccurrence A B →
      pweight phi (Phi p).1 * pweight phi (Phi p).2 =
        pweight phi p.1 * pweight phi p.2) ∧
    Set.InjOn Phi (dualDisjointOccurrence A B)



theorem kssWeightInjection_fin {n : ℕ}
    (A B : Set (ConfigSpace (Fin n))) : KSSWeightInjection A B := by
  classical
  set Dom := {p : ConfigSpace (Fin n) × ConfigSpace (Fin n) //
    p ∈ dualDisjointOccurrence A B} with hDom
  set r : Dom → (ConfigSpace (Fin n) × ConfigSpace (Fin n)) → Prop :=
    fun p q => sameOrbit p.val q ∧ q.1 ∈ A ∩ B with hr
  have key : ∃ f : Dom → (ConfigSpace (Fin n) × ConfigSpace (Fin n)),
      Function.Injective f ∧ ∀ x, r x (f x) := by
    rw [← Fintype.all_card_le_filter_rel_iff_exists_injective r]
    intro S
    set K := S.image (fun p : Dom => orbitKey p.val) with hK
    have hfib : #S = ∑ k ∈ K, #(S.filter (fun p => orbitKey p.val = k)) := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    rw [hfib]
    have hkstep : ∀ k ∈ K,
        #(S.filter (fun p => orbitKey p.val = k)) ≤
          #(kssDiagonalOrbit A B k) := by
      intro k _
      refine le_trans ?_ (kssDualOrbit_card_le A B k)
      apply Finset.card_le_card_of_injOn (fun p => p.val)
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        rw [Finset.mem_coe, kssDualOrbit, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, p.property, hp.2⟩
      · intro p _ q _ hpq
        exact Subtype.ext hpq
    calc
      ∑ k ∈ K, #(S.filter (fun p => orbitKey p.val = k))
          ≤ ∑ k ∈ K, #(kssDiagonalOrbit A B k) :=
        Finset.sum_le_sum hkstep
      _ = #(K.biUnion fun k => kssDiagonalOrbit A B k) := by
        rw [Finset.card_biUnion]
        intro k1 _ k2 _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        simp only [kssDiagonalOrbit, Finset.mem_filter] at hq1 hq2
        exact hne (hq1.2.2 ▸ hq2.2.2)
      _ ≤ #{q | ∃ p ∈ S, r p q} := by
        apply Finset.card_le_card
        intro q hq
        rw [Finset.mem_biUnion] at hq
        obtain ⟨k, hkK, hqdiag⟩ := hq
        simp only [kssDiagonalOrbit, Finset.mem_filter] at hqdiag
        rw [hK, Finset.mem_image] at hkK
        obtain ⟨p, hpS, hpk⟩ := hkK
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ q, p, hpS, ?_, hqdiag.2.1⟩
        rw [sameOrbit_iff_orbitKey, hpk, ← hqdiag.2.2]
  obtain ⟨f, hfinj, hfr⟩ := key
  let Phi : ConfigSpace (Fin n) × ConfigSpace (Fin n) →
      ConfigSpace (Fin n) × ConfigSpace (Fin n) := fun p =>
    if hp : p ∈ dualDisjointOccurrence A B then f ⟨p, hp⟩ else p
  refine ⟨Phi, ?_, ?_, ?_⟩
  · intro p hp
    simpa only [Phi, dif_pos hp] using (hfr ⟨p, hp⟩).2
  · intro phi p hp
    exact pairWeight_eq_of_sameOrbit phi
      (by simpa only [Phi, dif_pos hp] using (hfr ⟨p, hp⟩).1)
  · intro p hp q hq hpq
    simp only [Phi, dif_pos hp, dif_pos hq] at hpq
    exact Subtype.ext_iff.mp (hfinj hpq)



theorem dualBKR_wprob_fin {n : ℕ} (phi : Fin n → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (A B : Set (ConfigSpace (Fin n))) :
    dualWprob phi (dualDisjointOccurrence A B) ≤ wprob phi (A ∩ B) := by
  classical
  obtain ⟨Phi, hmem, hwt, hinj⟩ := kssWeightInjection_fin A B
  set D := dualDisjointOccurrence A B with hD
  set C := A ∩ B with hC
  set target := C ×ˢ (Set.univ : Set (ConfigSpace (Fin n))) with htarget
  set g : ConfigSpace (Fin n) × ConfigSpace (Fin n) → ℝ := fun p =>
    target.indicator (fun _ => (1 : ℝ)) p *
      (pweight phi p.1 * pweight phi p.2) with hg
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (mul_nonneg (pweight_nonneg hphi0 _) (pweight_nonneg hphi0 _))
  have htargetprob : dualWprob phi target = wprob phi C := by
    rw [htarget, dualWprob_prod]
    have huniv : wprob phi (Set.univ : Set (ConfigSpace (Fin n))) = 1 := by
      simp only [wprob, Set.indicator_univ, one_mul]
      exact sum_pweight_eq_one hphi1
    rw [huniv, mul_one]
  rw [← htargetprob]
  have hlhs : dualWprob phi D =
      ∑ p : ConfigSpace (Fin n) × ConfigSpace (Fin n),
        D.indicator (fun _ => (1 : ℝ)) p *
          (pweight phi p.1 * pweight phi p.2) := by
    unfold dualWprob
    rw [Fintype.sum_prod_type]
  have hrhs : dualWprob phi target =
      ∑ p : ConfigSpace (Fin n) × ConfigSpace (Fin n), g p := by
    unfold dualWprob
    rw [Fintype.sum_prod_type]
  rw [hlhs, hrhs]
  set domainPairs := Finset.univ.filter
    (fun p : ConfigSpace (Fin n) × ConfigSpace (Fin n) => p ∈ D) with hdomain
  have hlhs' :
      (∑ p : ConfigSpace (Fin n) × ConfigSpace (Fin n),
        D.indicator (fun _ => (1 : ℝ)) p *
          (pweight phi p.1 * pweight phi p.2)) =
      ∑ p ∈ domainPairs, pweight phi p.1 * pweight phi p.2 := by
    rw [hdomain, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun p : ConfigSpace (Fin n) × ConfigSpace (Fin n) => p ∈ D)]
    have hz :
        (∑ p ∈ Finset.univ.filter
          (fun p : ConfigSpace (Fin n) × ConfigSpace (Fin n) => ¬p ∈ D),
          D.indicator (fun _ => (1 : ℝ)) p *
            (pweight phi p.1 * pweight phi p.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Set.indicator_of_notMem hp.2, zero_mul]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Set.indicator_of_mem hp.2, one_mul]
  rw [hlhs']
  have hwp :
      (∑ p ∈ domainPairs, pweight phi p.1 * pweight phi p.2) =
        ∑ p ∈ domainPairs, g (Phi p) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hdomain, Finset.mem_filter] at hp
    have hpD : p ∈ D := hp.2
    have hpDual : p ∈ dualDisjointOccurrence A B := by simpa [hD] using hpD
    have hpC : (Phi p).1 ∈ C := by simpa [hC] using hmem p hpDual
    have hpTarget : Phi p ∈ target := by
      exact ⟨hpC, Set.mem_univ _⟩
    simp only [hg]
    rw [Set.indicator_of_mem hpTarget, one_mul, hwt phi p hpDual]
  rw [hwp]
  rw [← Finset.sum_image (g := Phi) (f := g)
    (by
      intro p hp q hq hpq
      rw [hdomain, Finset.mem_coe, Finset.mem_filter] at hp hq
      apply hinj hp.2 hq.2 hpq)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _ => hg0 p)



theorem dualWprob_inter_univ {n : ℕ} (phi : Fin n → Bool → ℝ)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (C : Set (ConfigSpace (Fin n))) :
    dualWprob phi (C ×ˢ (Set.univ : Set (ConfigSpace (Fin n)))) =
      wprob phi C := by
  rw [dualWprob_prod]
  have huniv : wprob phi (Set.univ : Set (ConfigSpace (Fin n))) = 1 := by
    simp only [wprob, Set.indicator_univ, one_mul]
    exact sum_pweight_eq_one hphi1
  rw [huniv, mul_one]



def dualPull {F : Type*} (e : E ≃ F)
    (C : Set (ConfigSpace E × ConfigSpace E)) :
    Set (ConfigSpace F × ConfigSpace F) :=
  {p | (cfgEquiv e p.1, cfgEquiv e p.2) ∈ C}

omit [Fintype E] [DecidableEq E] in

theorem dualPull_dualDisjointOccurrence {F : Type*} (e : E ≃ F)
    (A B : Set (ConfigSpace E)) :
    dualPull e (dualDisjointOccurrence A B) =
      dualDisjointOccurrence ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B) := by
  ext p
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨e '' K, e '' L, (Set.disjoint_image_iff e.injective).mpr hKL,
      (occursOn_cfgEquiv e A K p.1).mpr hA,
      (occursOn_cfgEquiv e B L p.2).mpr hB⟩
  · rintro ⟨K, L, hKL, hA, hB⟩
    refine ⟨e.symm '' K, e.symm '' L,
      (Set.disjoint_image_iff e.symm.injective).mpr hKL, ?_, ?_⟩
    · have h := (occursOn_cfgEquiv e A (e.symm '' K) p.1).mp
      rw [Set.image_image] at h
      simp only [Equiv.apply_symm_apply, Set.image_id'] at h
      exact h hA
    · have h := (occursOn_cfgEquiv e B (e.symm '' L) p.2).mp
      rw [Set.image_image] at h
      simp only [Equiv.apply_symm_apply, Set.image_id'] at h
      exact h hB



theorem dualWprob_transfer {F : Type*} [Fintype F] [DecidableEq F]
    (e : E ≃ F) (phi : E → Bool → ℝ)
    (C : Set (ConfigSpace E × ConfigSpace E)) :
    dualWprob phi C =
      dualWprob (fun y => phi (e.symm y)) (dualPull e C) := by
  unfold dualWprob
  rw [← Equiv.sum_comp (cfgEquiv e) (fun omega =>
    ∑ eta : ConfigSpace E,
      C.indicator (fun _ => (1 : ℝ)) (omega, eta) *
        (pweight phi omega * pweight phi eta))]
  apply Finset.sum_congr rfl
  intro omega _
  rw [← Equiv.sum_comp (cfgEquiv e) (fun eta =>
    C.indicator (fun _ => (1 : ℝ)) (cfgEquiv e omega, eta) *
      (pweight phi (cfgEquiv e omega) * pweight phi eta))]
  apply Finset.sum_congr rfl
  intro eta _
  rw [pweight_transfer, pweight_transfer]
  rfl


theorem dualBKR_wprob (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (A B : Set (ConfigSpace E)) :
    dualWprob phi (dualDisjointOccurrence A B) ≤ wprob phi (A ∩ B) := by
  classical
  set n := Fintype.card E
  obtain ⟨e⟩ := Fintype.truncEquivFin E
  set psi : Fin n → Bool → ℝ := fun y => phi (e.symm y)
  have hpsi0 : ∀ i b, 0 ≤ psi i b := fun i b => hphi0 (e.symm i) b
  have hpsi1 : ∀ i, psi i false + psi i true = 1 := fun i => hphi1 (e.symm i)
  have h := dualBKR_wprob_fin psi hpsi0 hpsi1
    ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B)
  rw [← dualPull_dualDisjointOccurrence e A B] at h
  rw [← dualWprob_transfer e phi (dualDisjointOccurrence A B)] at h
  have hinter :
      ((cfgEquiv e) ⁻¹' A) ∩ ((cfgEquiv e) ⁻¹' B) =
        (cfgEquiv e) ⁻¹' (A ∩ B) := by
    ext omega
    simp
  rw [hinter, ← wprob_transfer e phi (A ∩ B)] at h
  exact h



theorem dualFunctionalBKR_real (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (f g : ConfigSpace E → ℝ)
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega) :
    dualProductExpectation phi
        (fun pair => functionalDisjointMaxAt f g pair.1 pair.2) ≤
      productExpectation phi (fun omega => f omega * g omega) := by
  calc
    dualProductExpectation phi
        (fun pair => functionalDisjointMaxAt f g pair.1 pair.2) ≤
        ∑ omega : ConfigSpace E, ∑ eta : ConfigSpace E,
          pweight phi omega * pweight phi eta *
            (∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
              layerF.2 * layerG.2 *
                (dualDisjointOccurrence (realUpperLevel f layerF.1)
                  (realUpperLevel g layerG.1)).indicator
                    (fun _ => (1 : ℝ)) (omega, eta)) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      exact mul_le_mul_of_nonneg_left
        (functionalDisjointMaxAt_real_le_dualLevels hf0 hg0 omega eta)
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
    _ = ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
          layerF.2 * layerG.2 *
            dualWprob phi
              (dualDisjointOccurrence (realUpperLevel f layerF.1)
                (realUpperLevel g layerG.1)) := by
      simp_rw [Finset.mul_sum]
      rw [kss_sum_four_comm (Finset.univ : Finset (ConfigSpace E))
        (Finset.univ : Finset (ConfigSpace E))
        (realLayerSet f) (realLayerSet g)]
      apply Finset.sum_congr rfl
      intro layerF _
      apply Finset.sum_congr rfl
      intro layerG _
      unfold dualWprob
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro omega _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro eta _
      ring
    _ ≤ ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
          layerF.2 * layerG.2 *
            wprob phi
              (realUpperLevel f layerF.1 ∩ realUpperLevel g layerG.1) := by
      apply Finset.sum_le_sum
      intro layerF hlayerF
      apply Finset.sum_le_sum
      intro layerG hlayerG
      apply mul_le_mul_of_nonneg_left
      · exact dualBKR_wprob phi hphi0 hphi1 _ _
      · exact mul_nonneg (realLayer_increment_nonneg hf0 hlayerF)
          (realLayer_increment_nonneg hg0 hlayerG)
    _ = productExpectation phi (fun omega => f omega * g omega) :=
      (productExpectation_real_mul_eq_levelIntersections phi hf0 hg0).symm

end StatMech.FrontierA
