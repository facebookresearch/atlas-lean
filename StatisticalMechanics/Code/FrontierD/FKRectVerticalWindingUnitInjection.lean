/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectVerticalWindingLevelPlateau
import Code.FrontierD.FKRectPrimalBoundaryCompanionUnique










open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectBlackBoundaryCycleInPrimalCluster_iff_component
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) :
    fkRectBlackBoundaryCycleInPrimalCluster R omega x C ↔
      fkRectBlackBoundaryCyclePrimalComponent R omega C =
        (fkRectOpenGraph R omega).connectedComponentMk x := by
  induction C using Quot.ind with
  | _ d =>
      rw [fkRectBlackBoundaryCycleInPrimalCluster_mk,
        fkRectBlackBoundaryCyclePrimalComponent_mk,
        ConnectedComponent.eq]
      exact ⟨fun h => h.symm, fun h => h.symm⟩



theorem fkRectBlackBoundaryCycleWinding_det_eq_zero_of_not_componentHasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K)
    {C D : FKRectConfigurationBlackBoundaryCycle R omega}
    (hC : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C)
    (hD : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out D) :
    (fkRectBlackBoundaryCycleWinding R omega C).1 *
          (fkRectBlackBoundaryCycleWinding R omega D).2 -
        (fkRectBlackBoundaryCycleWinding R omega C).2 *
          (fkRectBlackBoundaryCycleWinding R omega D).1 = 0 := by
  induction C using Quot.ind with
  | _ d =>
      induction D using Quot.ind with
      | _ e =>
          have hdK : (fkRectOpenGraph R omega).connectedComponentMk
              (fkRectMedialDartPrimalLabel R d.1) = K := by
            calc
              _ = fkRectBlackBoundaryCyclePrimalComponent R omega
                  (Quot.mk _ d) :=
                (fkRectBlackBoundaryCyclePrimalComponent_mk R omega d).symm
              _ = (fkRectOpenGraph R omega).connectedComponentMk K.out :=
                (fkRectBlackBoundaryCycleInPrimalCluster_iff_component
                  R omega K.out (Quot.mk _ d)).mp hC
              _ = K := K.out_eq
          have heK : (fkRectOpenGraph R omega).connectedComponentMk
              (fkRectMedialDartPrimalLabel R e.1) = K := by
            calc
              _ = fkRectBlackBoundaryCyclePrimalComponent R omega
                  (Quot.mk _ e) :=
                (fkRectBlackBoundaryCyclePrimalComponent_mk R omega e).symm
              _ = (fkRectOpenGraph R omega).connectedComponentMk K.out :=
                (fkRectBlackBoundaryCycleInPrimalCluster_iff_component
                  R omega K.out (Quot.mk _ e)).mp hD
              _ = K := K.out_eq
          by_contra hind
          apply hnoNet
          apply FKRectPrimalComponentHasNet.of_closedWalks R omega K
            hdK heK
            (fkRectBlackBoundaryPrimalCycleWalk R omega d)
            (fkRectBlackBoundaryPrimalCycleWalk R omega e)
          unfold FKRectWindingIndependent
          simpa only [fkRectBlackBoundaryCycleWinding_mk,
            ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
            using hind



theorem card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_sameSignUnique
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K)
    (hsame : ∀ C D : FKRectConfigurationBlackBoundaryCycle R omega,
      C ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out →
      D ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out →
      (0 < (fkRectBlackBoundaryCycleWinding R omega C).1 *
          (fkRectBlackBoundaryCycleWinding R omega D).1 ∨
        0 < (fkRectBlackBoundaryCycleWinding R omega C).2 *
          (fkRectBlackBoundaryCycleWinding R omega D).2) →
      C = D) :
    (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2 := by
  classical
  let S := fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out
  by_cases hS : S.Nonempty
  · obtain ⟨C, hC⟩ := hS
    have hCspec : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C ∧
        fkRectBlackBoundaryCycleWinding R omega C ≠ 0 := by
      simpa [S, fkRectPrimalClusterNonzeroBoundaryCycles] using hC
    obtain ⟨D, hDC, hDcluster, hDne⟩ :=
      exists_other_nonzero_blackBoundaryCycle_in_primalCluster
        R omega K.out C hCspec.1 hCspec.2
    have hD : D ∈ S := by
      simp [S, fkRectPrimalClusterNonzeroBoundaryCycles, hDcluster, hDne]
    have hsub : S ⊆ {C, D} := by
      intro E hE
      by_cases hEC : E = C
      · simp [hEC]
      have hEspec : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out E ∧
          fkRectBlackBoundaryCycleWinding R omega E ≠ 0 := by
        simpa [S, fkRectPrimalClusterNonzeroBoundaryCycles] using hE
      have hCDdet :=
        fkRectBlackBoundaryCycleWinding_det_eq_zero_of_not_componentHasNet
          R omega K hnoNet hCspec.1 hDcluster
      have hCEdet :=
        fkRectBlackBoundaryCycleWinding_det_eq_zero_of_not_componentHasNet
          R omega K hnoNet hCspec.1 hEspec.1
      let wC := fkRectBlackBoundaryCycleWinding R omega C
      let wD := fkRectBlackBoundaryCycleWinding R omega D
      let wE := fkRectBlackBoundaryCycleWinding R omega E
      have hDEsign : 0 < wD.1 * wE.1 ∨ 0 < wD.2 * wE.2 := by
        by_cases hCfst : wC.1 = 0
        · have hCsnd : wC.2 ≠ 0 := by
            intro h
            apply hCspec.2
            exact Prod.ext hCfst h
          have hDsnd : wD.2 ≠ 0 := by
            intro h
            have hDfst : wD.1 = 0 := by
              rw [hCfst, h] at hCDdet
              simp only [mul_zero, zero_sub] at hCDdet
              exact (mul_eq_zero.mp (neg_eq_zero.mp hCDdet)).resolve_left hCsnd
            apply hDne
            exact Prod.ext hDfst h
          have hEsnd : wE.2 ≠ 0 := by
            intro h
            have hEfst : wE.1 = 0 := by
              rw [hCfst, h] at hCEdet
              simp only [mul_zero, zero_sub] at hCEdet
              exact (mul_eq_zero.mp (neg_eq_zero.mp hCEdet)).resolve_left hCsnd
            apply hEspec.2
            exact Prod.ext hEfst h
          have hCDneg : wC.2 * wD.2 < 0 := by
            rcases lt_or_gt_of_ne (mul_ne_zero hCsnd hDsnd) with hneg | hpos
            · exact hneg
            · exact False.elim (hDC (hsame C D hC hD (Or.inr hpos)).symm)
          have hCEneg : wC.2 * wE.2 < 0 := by
            rcases lt_or_gt_of_ne (mul_ne_zero hCsnd hEsnd) with hneg | hpos
            · exact hneg
            · exact False.elim (hEC (hsame C E hC hE (Or.inr hpos)).symm)
          right
          rcases (mul_neg_iff.mp hCDneg) with h | h <;>
            rcases (mul_neg_iff.mp hCEneg) with h' | h'
          · exact mul_pos_of_neg_of_neg h.2 h'.2
          · exact (lt_asymm h.1 h'.1).elim
          · exact (lt_asymm h'.1 h.1).elim
          · exact mul_pos h.2 h'.2
        · have hDfst : wD.1 ≠ 0 := by
            intro h
            have hDsnd : wD.2 = 0 := by
              rw [h] at hCDdet
              simp only [mul_zero, sub_zero] at hCDdet
              exact (mul_eq_zero.mp hCDdet).resolve_left hCfst
            apply hDne
            exact Prod.ext h hDsnd
          have hEfst : wE.1 ≠ 0 := by
            intro h
            have hEsnd : wE.2 = 0 := by
              rw [h] at hCEdet
              simp only [mul_zero, sub_zero] at hCEdet
              exact (mul_eq_zero.mp hCEdet).resolve_left hCfst
            apply hEspec.2
            exact Prod.ext h hEsnd
          have hCDneg : wC.1 * wD.1 < 0 := by
            rcases lt_or_gt_of_ne (mul_ne_zero hCfst hDfst) with hneg | hpos
            · exact hneg
            · exact False.elim (hDC (hsame C D hC hD (Or.inl hpos)).symm)
          have hCEneg : wC.1 * wE.1 < 0 := by
            rcases lt_or_gt_of_ne (mul_ne_zero hCfst hEfst) with hneg | hpos
            · exact hneg
            · exact False.elim (hEC (hsame C E hC hE (Or.inl hpos)).symm)
          left
          rcases (mul_neg_iff.mp hCDneg) with h | h <;>
            rcases (mul_neg_iff.mp hCEneg) with h' | h'
          · exact mul_pos_of_neg_of_neg h.2 h'.2
          · exact (lt_asymm h.1 h'.1).elim
          · exact (lt_asymm h'.1 h.1).elim
          · exact mul_pos h.2 h'.2
      have hED : E = D := hsame E D hE hD (by
        rcases hDEsign with h | h
        · exact Or.inl (by simpa [wD, wE, mul_comm] using h)
        · exact Or.inr (by simpa [wD, wE, mul_comm] using h))
      simp [hED]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [show fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out = ∅ by
      simpa [S] using hzero]
    simp



theorem eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_snd_mul_pos
    {D : Type*} [Fintype D]
    (p : D → Prop) [DecidablePred p] (w : D → Int × Int)
    (hsum : (∑ d : D, if p d then w d else 0) = 0)
    (hcard : (Finset.univ.filter fun d => p d ∧ w d ≠ 0).card ≤ 2)
    {a b : D} (ha : p a) (hb : p b)
    (hsign : 0 < (w a).2 * (w b).2) : a = b := by
  classical
  by_contra hab
  let S := Finset.univ.filter fun d => p d ∧ w d ≠ 0
  have hwa : w a ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    simp at hsign
  have hwb : w b ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    simp at hsign
  have haS : a ∈ S := by simp [S, ha, hwa]
  have hbS : b ∈ S := by simp [S, hb, hwb]
  have hpS : ({a, b} : Finset D) ⊆ S := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact haS
    · exact hbS
  have hcardS : S.card ≤ 2 := by simpa [S] using hcard
  have hpair : ({a, b} : Finset D) = S := by
    apply Finset.eq_of_subset_of_card_le hpS
    simpa [hab] using hcardS
  have hsumS : (∑ d ∈ S, w d) = 0 := by
    change (∑ d ∈ Finset.univ.filter (fun d => p d ∧ w d ≠ 0),
      w d) = 0
    rw [Finset.sum_filter]
    calc
      (∑ d : D, if p d ∧ w d ≠ 0 then w d else 0) =
          ∑ d : D, if p d then w d else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : p d <;> by_cases hw : w d = 0 <;> simp [hd, hw]
      _ = 0 := hsum
  rw [← hpair] at hsumS
  have hsnd := congrArg Prod.snd hsumS
  simp [hab] at hsnd
  have hbneg : (w b).2 = -(w a).2 := by omega
  rw [hbneg] at hsign
  nlinarith [sq_nonneg (w a).2]



theorem fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_snd_pos
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (hcard : (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2)
    {C D : FKRectConfigurationBlackBoundaryCycle R omega}
    (hC : fkRectBlackBoundaryCycleInPrimalCluster R omega x C)
    (hD : fkRectBlackBoundaryCycleInPrimalCluster R omega x D)
    (hCpos : 0 < (fkRectBlackBoundaryCycleWinding R omega C).2)
    (hDpos : 0 < (fkRectBlackBoundaryCycleWinding R omega D).2) :
    C = D := by
  classical
  apply eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_snd_mul_pos
    (fun A : FKRectConfigurationBlackBoundaryCycle R omega =>
      fkRectBlackBoundaryCycleInPrimalCluster R omega x A)
    (fkRectBlackBoundaryCycleWinding R omega)
    (fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero R omega x)
    (by simpa [fkRectPrimalClusterNonzeroBoundaryCycles] using hcard)
    hC hD
  exact mul_pos hCpos hDpos



noncomputable def fkRectMedialBoundaryPrimalTraceBetween
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (a b : Nat) (hab : a ≤ b) :
    (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R
        ((fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))^[a] d))
      (fkRectMedialDartPrimalLabel R
        ((fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))^[b] d)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let p := fkRectMedialBoundaryPrimalTrace R omega
    ((fkMedialBoundaryStep pairing)^[a] d) (b - a)
  have hend :
      (fkMedialBoundaryStep pairing)^[b - a]
          ((fkMedialBoundaryStep pairing)^[a] d) =
        (fkMedialBoundaryStep pairing)^[b] d := by
    rw [← Function.iterate_add_apply]
    congr 2
    omega
  exact p.copy rfl (congrArg (fkRectMedialDartPrimalLabel R) hend)



theorem fkRectMedialBoundaryPrimalTraceBetween_winding_snd
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (a b : Nat) (hab : a ≤ b) :
    (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalTraceBetween
        R omega d a b hab)).2 =
      (fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d b).2 -
      (fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d a).2 := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  change (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalTraceBetween
        R omega d a b hab)).2 =
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d b).2 -
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d a).2
  have hadd := fkRectMedialBoundaryPrimalSeamTrace_add
    R pairing d a (b - a)
  rw [Nat.add_sub_of_le hab] at hadd
  change fkRectMedialBoundaryPrimalSeamTrace R pairing d b =
    fkRectMedialBoundaryPrimalSeamTrace R pairing d a +
      fkRectMedialBoundaryPrimalSeamTrace R pairing
        ((fkMedialBoundaryStep pairing)^[a] d) (b - a) at hadd
  have hsnd := congrArg Prod.snd hadd
  simp only [Prod.snd_add] at hsnd
  unfold fkRectMedialBoundaryPrimalTraceBetween
  rw [fkRectWalkWinding_copy,
    fkRectMedialBoundaryPrimalTrace_winding]
  change
    (fkRectMedialBoundaryPrimalSeamTrace R pairing
      ((fkMedialBoundaryStep pairing)^[a] d) (b - a)).2 = _
  omega



theorem fkRectBlackBoundaryUnitPlateauEntry_level
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    let a := (fkRectBlackBoundaryUnitPlateauEndpoints
      R omega d hpos j).1
    (fkRectMedialBoundaryPrimalSeamTrace R
      (fkRectConfigurationToMedialPairing R omega) d.1 a).2 =
        (j.val : Int) + 1 := by
  dsimp only
  have hs := fkRectBlackBoundaryUnitPlateauEndpoints_spec
    R omega d hpos j
  exact hs.2.2.2.2.1 _ le_rfl hs.2.1



theorem fkRectBlackBoundaryUnitPlateauEntry_strictMono
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    {j k : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat}
    (hjk : j < k) :
    (fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j).1 <
      (fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos k).1 := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let aj := (fkRectBlackBoundaryUnitPlateauEndpoints
    R omega d hpos j).1
  let bj := (fkRectBlackBoundaryUnitPlateauEndpoints
    R omega d hpos j).2
  let ak := (fkRectBlackBoundaryUnitPlateauEndpoints
    R omega d hpos k).1
  have hsj := fkRectBlackBoundaryUnitPlateauEndpoints_spec
    R omega d hpos j
  have hsk := fkRectBlackBoundaryUnitPlateauEndpoints_spec
    R omega d hpos k
  change 0 < aj ∧ aj ≤ bj ∧ _ ∧ _ ∧ _ ∧
    (∀ m < bj + 1,
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 <
        (j.val : Int) + 1 + 1) ∧ _ at hsj
  have hakLevel :
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 ak).2 =
        (k.val : Int) + 1 := by
    exact fkRectBlackBoundaryUnitPlateauEntry_level R omega d hpos k
  by_contra hnot
  change ¬ aj < ak at hnot
  have hak : ak < bj + 1 := by omega
  have hfirst := hsj.2.2.2.2.2.1 ak hak
  omega



theorem fkRectBlackBoundaryUnitCutComponent_torusComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    fkRectHorizontalCutComponentTorusComponent R omega
        (fkRectBlackBoundaryUnitCutComponent R omega d hpos j) =
      (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectMedialDartPrimalLabel R d.1) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let a := (fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j).1
  unfold fkRectBlackBoundaryUnitCutComponent
  dsimp only
  rw [fkRectHorizontalCutComponentTorusComponent_mk]
  exact (ConnectedComponent.sound
    (fkRectMedialBoundaryPrimalTrace R omega d.1 a).reachable).symm



theorem fkRectPrimalComponentHasNet_of_boundaryUnitCutComponent_eq
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (d : FKMedialBlackDart R.medialTorus)
    (hdK : (fkRectOpenGraph R omega).connectedComponentMk
      (fkRectMedialDartPrimalLabel R d.1) = K)
    (hprimitive : FKRectPrimitiveWinding
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)))
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    {j k : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat}
    (hjk : j < k)
    (heq : fkRectBlackBoundaryUnitCutComponent R omega d hpos j =
      fkRectBlackBoundaryUnitCutComponent R omega d hpos k) :
    FKRectPrimalComponentHasNet R omega K := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let a := (fkRectBlackBoundaryUnitPlateauEndpoints
    R omega d hpos j).1
  let b := (fkRectBlackBoundaryUnitPlateauEndpoints
    R omega d hpos k).1
  have hab : a ≤ b := (fkRectBlackBoundaryUnitPlateauEntry_strictMono
    R omega d hpos hjk).le
  let p := fkRectMedialBoundaryPrimalTraceBetween R omega d.1 a b hab
  have haLevel :
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 a).2 =
        (j.val : Int) + 1 :=
    fkRectBlackBoundaryUnitPlateauEntry_level R omega d hpos j
  have hbLevel :
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 b).2 =
        (k.val : Int) + 1 :=
    fkRectBlackBoundaryUnitPlateauEntry_level R omega d hpos k
  have hpwind : (fkRectWalkWinding R p).2 =
      (k.val : Int) - j.val := by
    rw [fkRectMedialBoundaryPrimalTraceBetween_winding_snd,
      haLevel, hbLevel]
    ring
  have hxK : (fkRectOpenGraph R omega).connectedComponentMk
      (fkRectMedialDartPrimalLabel R
        ((fkMedialBoundaryStep pairing)^[a] d.1)) = K := by
    exact (ConnectedComponent.sound
      (fkRectMedialBoundaryPrimalTrace R omega d.1 a).reachable).symm.trans hdK
  have hxy :
      (fkRectOpenGraph R
          (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk
            (fkRectMedialDartPrimalLabel R
              ((fkMedialBoundaryStep pairing)^[a] d.1)) =
        (fkRectOpenGraph R
          (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk
            (fkRectMedialDartPrimalLabel R
              ((fkMedialBoundaryStep pairing)^[b] d.1)) := by
    simpa only [fkRectBlackBoundaryUnitCutComponent, a, b, pairing] using heq
  have hpath : 0 < (fkRectWalkWinding R p).2 := by
    rw [hpwind]
    have hjk' : (j.val : Int) < k.val := by exact_mod_cast hjk
    omega
  have hkBound : (k.val : Int) <
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
    calc
      (k.val : Int) <
          ((fkRectWalkWinding R
            (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat : Int) := by
        exact_mod_cast k.isLt
      _ = _ := by rw [Int.toNat_of_nonneg hpos.le]
  have hstrict : (fkRectWalkWinding R p).2 <
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
    rw [hpwind]
    omega
  exact fkRectPrimalComponentHasNet_of_primitiveBoundary_cutCollision
    R omega K d hdK hprimitive p hxK hxy hpos hpath hstrict




theorem nonempty_boundaryUnitEmbedding_horizontalCutCrossingInFiber
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (d : FKMedialBlackDart R.medialTorus)
    (hdK : (fkRectOpenGraph R omega).connectedComponentMk
      (fkRectMedialDartPrimalLabel R d.1) = K)
    (hprimitive : FKRectPrimitiveWinding
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)))
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K) :
    Nonempty
      (Fin (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat ↪
        FKRectHorizontalCutCrossingInFiber R omega K) := by
  let f : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat →
      FKRectHorizontalCutCrossingInFiber R omega K := fun j =>
    ⟨⟨fkRectBlackBoundaryUnitCutComponent R omega d hpos j,
      fkRectBlackBoundaryUnitCutComponent_crossing R omega d hpos j⟩,
      (fkRectBlackBoundaryUnitCutComponent_torusComponent
        R omega d hpos j).trans hdK⟩
  refine ⟨⟨f, ?_⟩⟩
  intro j k heq
  apply Fin.ext
  by_contra hjk
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · apply hnoNet
    apply fkRectPrimalComponentHasNet_of_boundaryUnitCutComponent_eq
      R omega K d hdK hprimitive hpos hlt
    exact congrArg (fun X => X.1.1) heq
  · apply hnoNet
    apply fkRectPrimalComponentHasNet_of_boundaryUnitCutComponent_eq
      R omega K d hdK hprimitive hpos hgt
    exact (congrArg (fun X => X.1.1) heq).symm

set_option maxHeartbeats 1000000 in




theorem nonempty_positiveBoundaryUnitEmbedding_of_card_nonzero_le_two
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hcard :
      (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2)
    (hprimitive : ∀ d : FKMedialBlackDart R.medialTorus,
      0 < (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 →
      FKRectPrimitiveWinding
        (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)))
    (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K) :
    Nonempty (FKRectPositiveBoundaryUnit R omega K ↪
      FKRectHorizontalCutCrossingInFiber R omega K) := by
  classical
  let f : FKRectPositiveBoundaryUnit R omega K →
      FKRectHorizontalCutCrossingInFiber R omega K := fun u => by
    let d : FKMedialBlackDart R.medialTorus := Quot.out u.1
    have hdC : Quot.mk _ d = u.1 := Quot.out_eq u.1
    have hwind : fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d) =
      fkRectBlackBoundaryCycleWinding R omega u.1 := by
      calc
        _ = fkRectBlackBoundaryCycleClassWinding R
            (fkRectConfigurationToMedialPairing R omega) d :=
          fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass
            R omega d
        _ = fkRectBlackBoundaryCycleWinding R omega (Quot.mk _ d) :=
          (fkRectBlackBoundaryCycleWinding_mk R omega d).symm
        _ = _ := by rw [hdC]
    have hpos : 0 < (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
      rw [hwind]
      exact FKRectPositiveBoundaryUnit.winding_snd_pos R omega K u
    have huLt : u.2.val <
        (fkRectBlackBoundaryCycleWinding R omega u.1).2.toNat := by
      simpa [fkRectPositiveBoundaryUnitMultiplicity,
        FKRectPositiveBoundaryUnit.component R omega K u] using u.2.isLt
    have huLt' : u.2.val < (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat := by
      rwa [hwind]
    let j : Fin (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat :=
      ⟨u.2.val, huLt'⟩
    have hdK : (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectMedialDartPrimalLabel R d.1) = K := by
      calc
        _ = fkRectBlackBoundaryCyclePrimalComponent R omega
            (Quot.mk _ d) :=
          (fkRectBlackBoundaryCyclePrimalComponent_mk R omega d).symm
        _ = fkRectBlackBoundaryCyclePrimalComponent R omega u.1 := by
          rw [hdC]
        _ = K := FKRectPositiveBoundaryUnit.component R omega K u
    exact ⟨⟨fkRectBlackBoundaryUnitCutComponent R omega d hpos j,
      fkRectBlackBoundaryUnitCutComponent_crossing R omega d hpos j⟩,
      (fkRectBlackBoundaryUnitCutComponent_torusComponent
        R omega d hpos j).trans hdK⟩
  refine ⟨⟨f, ?_⟩⟩
  intro u v huv
  have huCluster : fkRectBlackBoundaryCycleInPrimalCluster
      R omega K.out u.1 := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_component]
    exact (FKRectPositiveBoundaryUnit.component R omega K u).trans
      K.out_eq.symm
  have hvCluster : fkRectBlackBoundaryCycleInPrimalCluster
      R omega K.out v.1 := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_component]
    exact (FKRectPositiveBoundaryUnit.component R omega K v).trans
      K.out_eq.symm
  have hcycle : u.1 = v.1 :=
    fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_snd_pos
      R omega K.out hcard huCluster hvCluster
        (FKRectPositiveBoundaryUnit.winding_snd_pos R omega K u)
        (FKRectPositiveBoundaryUnit.winding_snd_pos R omega K v)
  cases u with
  | mk C j =>
    cases v with
    | mk D k =>
      dsimp only at hcycle
      subst D
      congr 1
      apply Fin.ext
      let d : FKMedialBlackDart R.medialTorus := Quot.out C
      have hdC : Quot.mk _ d = C := Quot.out_eq C
      have hwind : fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d) =
          fkRectBlackBoundaryCycleWinding R omega C := by
        calc
          _ = fkRectBlackBoundaryCycleClassWinding R
              (fkRectConfigurationToMedialPairing R omega) d :=
            fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass
              R omega d
          _ = fkRectBlackBoundaryCycleWinding R omega (Quot.mk _ d) :=
            (fkRectBlackBoundaryCycleWinding_mk R omega d).symm
          _ = _ := by rw [hdC]
      have hCcomponent : fkRectBlackBoundaryCyclePrimalComponent
          R omega C = K := by
        exact FKRectPositiveBoundaryUnit.component R omega K ⟨C, j⟩
      have hposC : 0 < (fkRectBlackBoundaryCycleWinding R omega C).2 :=
        FKRectPositiveBoundaryUnit.winding_snd_pos R omega K ⟨C, j⟩
      have hpos : 0 < (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
        rw [hwind]
        exact hposC
      have hjLt : j.val < (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat := by
        rw [hwind]
        simpa [fkRectPositiveBoundaryUnitMultiplicity, hCcomponent]
          using j.isLt
      have hkLt : k.val < (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat := by
        rw [hwind]
        simpa [fkRectPositiveBoundaryUnitMultiplicity, hCcomponent]
          using k.isLt
      let j' : Fin (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat :=
        ⟨j.val, hjLt⟩
      let k' : Fin (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat :=
        ⟨k.val, hkLt⟩
      have hdK : (fkRectOpenGraph R omega).connectedComponentMk
          (fkRectMedialDartPrimalLabel R d.1) = K := by
        calc
          _ = fkRectBlackBoundaryCyclePrimalComponent R omega
              (Quot.mk _ d) :=
            (fkRectBlackBoundaryCyclePrimalComponent_mk R omega d).symm
          _ = fkRectBlackBoundaryCyclePrimalComponent R omega C := by
            rw [hdC]
          _ = K := hCcomponent
      have hcomponents :
          fkRectBlackBoundaryUnitCutComponent R omega d hpos j' =
            fkRectBlackBoundaryUnitCutComponent R omega d hpos k' := by
        exact congrArg (fun X => X.1.1) huv
      by_contra hjk
      rcases lt_or_gt_of_ne hjk with hlt | hgt
      · apply hnoNet
        exact fkRectPrimalComponentHasNet_of_boundaryUnitCutComponent_eq
          R omega K d hdK (hprimitive d hpos) hpos hlt hcomponents
      · apply hnoNet
        exact fkRectPrimalComponentHasNet_of_boundaryUnitCutComponent_eq
          R omega K d hdK (hprimitive d hpos) hpos hgt hcomponents.symm



theorem rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two
    (R : FKRectTorus) (omega : R.Configuration)
    (hcard : ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
      ¬ FKRectPrimalComponentHasNet R omega K →
        (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2)
    (hprimitive : ∀ d : FKMedialBlackDart R.medialTorus,
      0 < (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 →
      FKRectPrimitiveWinding
        (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d))) :
    FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega := by
  rw [rankOnePositiveBoundaryCutFiberBound_iff_unitEmbedding]
  intro K hnoNet
  exact nonempty_positiveBoundaryUnitEmbedding_of_card_nonzero_le_two
    R omega K (hcard K hnoNet) hprimitive hnoNet

end

end StatMech.FrontierD
