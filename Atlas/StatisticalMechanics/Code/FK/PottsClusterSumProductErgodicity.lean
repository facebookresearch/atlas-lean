/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumErgodicFactor
import Code.FK.FreePairMixingFromTail
import Code.FK.FreeTailTriviality
import Code.Percolation.BurtonKeaneClose











open Filter Function MeasureTheory MeasurableSpace Set Topology
open scoped ENNReal symmDiff

namespace StatMech.FK




def MixingAgainst {Beta : Type*} [MeasurableSpace Beta]
    (S : Beta -> Beta) (nu : Measure Beta) (D : Set (Set Beta)) : Prop :=
  forall (A : Set Beta), MeasurableSet A -> forall B, B ∈ D ->
    Tendsto (fun n : Nat =>
      nu.real (A ∩ (S^[n]) ⁻¹' B)) atTop
      (nhds (nu.real A * nu.real B))

private theorem section_preimage_prodMap_iterate
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (T : Alpha -> Alpha) (S : Beta -> Beta)
    {A : Set (Alpha × Beta)}
    (hA : (Prod.map T S) ⁻¹' A = A) (n : Nat) (x : Alpha) :
    (S^[n]) ⁻¹' (Prod.mk (T^[n] x) ⁻¹' A) = Prod.mk x ⁻¹' A := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      ext y
      simp only [Set.mem_preimage, iterate_succ_apply]
      rw [show (T^[n] (T x), S^[n] (S y)) ∈ A ↔ (T x, S y) ∈ A from
        Set.ext_iff.mp (ih (T x)) (S y)]
      exact Set.ext_iff.mp hA (x, y)

private theorem measurable_sectionReal
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {nu : Measure Beta} [IsFiniteMeasure nu]
    {A : Set (Alpha × Beta)} (hA : MeasurableSet A) :
    Measurable fun x => nu.real (Prod.mk x ⁻¹' A) := by
  exact ENNReal.measurable_toReal.comp
    (measurable_measure_prodMk_left hA)

private theorem sectionReal_comp_iterate
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {nu : Measure Beta} [IsFiniteMeasure nu]
    (T : Alpha -> Alpha) (S : Beta -> Beta)
    (hS : MeasurePreserving S nu nu)
    {A : Set (Alpha × Beta)}
    (hA : MeasurableSet A) (hinv : (Prod.map T S) ⁻¹' A = A)
    (B : Set Beta) (hB : MeasurableSet B) (n : Nat) (x : Alpha) :
    nu.real ((Prod.mk (T^[n] x) ⁻¹' A) ∩ B) =
      nu.real ((Prod.mk x ⁻¹' A) ∩ (S^[n]) ⁻¹' B) := by
  let Axn := Prod.mk (T^[n] x) ⁻¹' A
  have hAxn : MeasurableSet Axn := measurable_prodMk_left hA
  have hmp := hS.iterate n
  calc
    nu.real (Axn ∩ B) =
        nu.real ((S^[n]) ⁻¹' (Axn ∩ B)) :=
      (hmp.measureReal_preimage (hAxn.inter hB).nullMeasurableSet).symm
    _ = nu.real ((Prod.mk x ⁻¹' A) ∩ (S^[n]) ⁻¹' B) := by
      congr 1
      rw [preimage_inter, section_preimage_prodMap_iterate T S hinv]

set_option maxHeartbeats 2000000 in




theorem ergodic_prod_of_mixingAgainst
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {mu : Measure Alpha} {nu : Measure Beta}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (T : Alpha -> Alpha) (S : Beta -> Beta)
    (hT : _root_.Ergodic T mu) (hS : MeasurePreserving S nu nu)
    (D : Set (Set Beta))
    (hDgen : generateFrom D = (inferInstance : MeasurableSpace Beta))
    (hDpi : IsPiSystem D) (hDspan : IsCountablySpanning D)
    (hDmeas : forall B, B ∈ D -> MeasurableSet B)
    (hmix : MixingAgainst S nu D) :
    _root_.Ergodic (Prod.map T S) (mu.prod nu) := by
  classical
  refine ⟨hT.toMeasurePreserving.prod hS, ⟨?_⟩⟩
  intro A hA hinv
  let r : Alpha -> Real := fun x => nu.real (Prod.mk x ⁻¹' A)
  have hrmeas : Measurable r := measurable_sectionReal hA
  have hrinv : r ∘ T = r := by
    funext x
    have hpre := section_preimage_prodMap_iterate T S hinv 1 x
    simp only [iterate_one] at hpre
    calc
      r (T x) = nu.real (Prod.mk (T x) ⁻¹' A) := rfl
      _ = nu.real (S ⁻¹' (Prod.mk (T x) ⁻¹' A)) :=
        (hS.measureReal_preimage
          (measurable_prodMk_left hA).nullMeasurableSet).symm
      _ = r x := congrArg nu.real hpre
  obtain ⟨c, hc⟩ := hT.toPreErgodic.ae_eq_const_of_ae_eq_comp
    hrmeas hrinv
  have hc_nonneg : 0 <= c := by
    obtain ⟨x, hx⟩ := hc.exists
    simpa only [r, const_apply, hx] using
      (measureReal_nonneg (μ := nu) (s := Prod.mk x ⁻¹' A))
  have hc_le_one : c <= 1 := by
    obtain ⟨x, hx⟩ := hc.exists
    simpa only [r, const_apply, hx] using
      (measureReal_le_one (μ := nu) (s := Prod.mk x ⁻¹' A))

  have hsection (B : Set Beta) (hBD : B ∈ D) :
      (fun x => nu.real ((Prod.mk x ⁻¹' A) ∩ B)) =ᵐ[mu]
        (fun _ => c * nu.real B) := by
    have hB := hDmeas B hBD
    let phi : Alpha -> Real := fun x =>
      nu.real ((Prod.mk x ⁻¹' A) ∩ B)
    have hphimeas : Measurable phi := by
      have hset : MeasurableSet (A ∩ (Set.univ ×ˢ B)) :=
        hA.inter (MeasurableSet.univ.prod hB)
      have hm := measurable_sectionReal (nu := nu) hset
      convert hm using 1
      funext x
      apply congrArg nu.real
      ext y
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
        Set.mem_univ, true_and]
    have hpoint : forall x, Tendsto (fun n : Nat => phi (T^[n] x)) atTop
        (nhds (r x * nu.real B)) := by
      intro x
      have hxmeas : MeasurableSet (Prod.mk x ⁻¹' A) :=
        measurable_prodMk_left hA
      simpa only [phi, r,
        sectionReal_comp_iterate T S hS hA hinv B hB] using
        hmix (Prod.mk x ⁻¹' A) hxmeas B hBD
    have hpointc : ∀ᵐ x ∂mu,
        Tendsto (fun n : Nat => phi (T^[n] x)) atTop
          (nhds (c * nu.real B)) := by
      filter_upwards [hc] with x hx
      simpa only [r, const_apply, hx] using hpoint x
    have hnormlim : Tendsto (fun n : Nat =>
        ∫ x, |phi (T^[n] x) - c * nu.real B| ∂mu)
        atTop (nhds 0) := by
      have hdct := tendsto_integral_of_dominated_convergence
        (μ := mu) (F := fun n x =>
          |phi (T^[n] x) - c * nu.real B|)
        (f := fun _ => (0 : Real)) (fun _ => (1 : Real))
        (fun n => ((hphimeas.comp (hT.measurable.iterate n)).sub
          measurable_const).abs.aestronglyMeasurable)
        (integrable_const 1)
        (by
          intro n
          filter_upwards with x
          rw [Real.norm_eq_abs, abs_abs]
          have hphi0 : 0 <= phi (T^[n] x) := measureReal_nonneg
          have hphi1 : phi (T^[n] x) <= 1 := measureReal_le_one
          have hB0 : 0 <= nu.real B := measureReal_nonneg
          have hB1 : nu.real B <= 1 := measureReal_le_one
          have hprod0 : 0 <= c * nu.real B := mul_nonneg hc_nonneg hB0
          have hprod1 : c * nu.real B <= 1 :=
            mul_le_one₀ hc_le_one hB0 hB1
          exact abs_le.mpr ⟨by linarith, by linarith⟩)
        (by
          filter_upwards [hpointc] with x hx
          have hconst : Tendsto (fun _ : Nat => c * nu.real B) atTop
              (nhds (c * nu.real B)) := tendsto_const_nhds
          simpa only [sub_self, abs_zero] using (hx.sub hconst).abs)
      simpa using hdct
    have hintegral_eq (n : Nat) :
        (∫ x, |phi (T^[n] x) - c * nu.real B| ∂mu) =
          ∫ x, |phi x - c * nu.real B| ∂mu := by
      let f : Alpha -> Real := fun x => |phi x - c * nu.real B|
      have hfmeas : Measurable f :=
        (hphimeas.sub measurable_const).abs
      have hfint : Integrable f mu := by
        apply Integrable.mono' (integrable_const 1) hfmeas.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_abs]
        have hphi0 : 0 <= phi x := measureReal_nonneg
        have hphi1 : phi x <= 1 := measureReal_le_one
        have hB0 : 0 <= nu.real B := measureReal_nonneg
        have hB1 : nu.real B <= 1 := measureReal_le_one
        have hprod0 : 0 <= c * nu.real B := mul_nonneg hc_nonneg hB0
        have hprod1 : c * nu.real B <= 1 :=
          mul_le_one₀ hc_le_one hB0 hB1
        simpa only [f, Real.norm_eq_abs, abs_abs] using
          (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hmp := hT.toMeasurePreserving.iterate n
      calc
        (∫ x, |phi (T^[n] x) - c * nu.real B| ∂mu) =
            ∫ x, f (T^[n] x) ∂mu := rfl
        _ = ∫ x, f x ∂mu := by
          calc
            (∫ x, f (T^[n] x) ∂mu) =
                ∫ x, f x ∂Measure.map (T^[n]) mu :=
              (integral_map (hT.measurable.iterate n).aemeasurable
                (by rw [hmp.map_eq]; exact hfmeas.aestronglyMeasurable)).symm
            _ = ∫ x, f x ∂mu := by rw [hmp.map_eq]
        _ = ∫ x, |phi x - c * nu.real B| ∂mu := rfl
    have hzero : (∫ x, |phi x - c * nu.real B| ∂mu) = 0 := by
      have ht : Tendsto (fun _ : Nat =>
          ∫ x, |phi x - c * nu.real B| ∂mu) atTop (nhds 0) := by
        simpa only [hintegral_eq] using hnormlim
      exact tendsto_nhds_unique tendsto_const_nhds ht
    have hae_zero : (fun x => |phi x - c * nu.real B|) =ᵐ[mu] 0 := by
      have hint : Integrable (fun x => |phi x - c * nu.real B|) mu := by
        apply Integrable.mono' (integrable_const 1)
          (hphimeas.sub measurable_const).abs.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_abs]
        have hphi0 : 0 <= phi x := measureReal_nonneg
        have hphi1 : phi x <= 1 := measureReal_le_one
        have hB0 : 0 <= nu.real B := measureReal_nonneg
        have hB1 : nu.real B <= 1 := measureReal_le_one
        have hprod0 : 0 <= c * nu.real B := mul_nonneg hc_nonneg hB0
        have hprod1 : c * nu.real B <= 1 :=
          mul_le_one₀ hc_le_one hB0 hB1
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hint).mp hzero
    filter_upwards [hae_zero] with x hx
    exact sub_eq_zero.mp (abs_eq_zero.mp hx)

  let lambda : Measure (Alpha × Beta) := (mu.prod nu).restrict A
  let cE : ENNReal := ENNReal.ofReal c
  have hmassE : (mu.prod nu) A = cE := by
    rw [Measure.prod_apply hA]
    have hsecE :
        (fun x => nu (Prod.mk x ⁻¹' A)) =ᵐ[mu] (fun _ => cE) := by
      filter_upwards [hc] with x hx
      apply (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top nu _) ENNReal.ofReal_ne_top).mp
      simpa only [Measure.real, cE, ENNReal.toReal_ofReal hc_nonneg] using hx
    rw [lintegral_congr_ae hsecE, lintegral_const, measure_univ, mul_one]
  have hlambda : lambda = cE • (mu.prod nu) := by
    let C : Set (Set (Alpha × Beta)) :=
      Set.image2 (fun U V => U ×ˢ V)
        {U : Set Alpha | MeasurableSet U} D
    have hAlphaSpan : IsCountablySpanning
        {U : Set Alpha | MeasurableSet U} :=
      isCountablySpanning_measurableSet
    have hgen : (inferInstance : MeasurableSpace (Alpha × Beta)) =
        generateFrom C := by
      symm
      exact generateFrom_eq_prod generateFrom_measurableSet hDgen
        hAlphaSpan hDspan
    have hpi : IsPiSystem C := isPiSystem_measurableSet.prod hDpi
    apply ext_of_generate_finite C hgen hpi
    · intro R hR
      obtain ⟨U, hU, B, hBD, rfl⟩ := hR
      have hB := hDmeas B hBD
      have hrect : MeasurableSet (U ×ˢ B) := hU.prod hB
      dsimp only [lambda]
      rw [Measure.smul_apply, Measure.restrict_apply hrect,
        Set.inter_comm (U ×ˢ B) A,
        Measure.prod_apply (hA.inter hrect), Measure.prod_prod]
      have hsecE :
          (fun x => nu (Prod.mk x ⁻¹' (A ∩ (U ×ˢ B)))) =ᵐ[mu]
            (fun x => if x ∈ U then cE * nu B else 0) := by
        filter_upwards [hsection B hBD] with x hx
        have hrectsec : Prod.mk x ⁻¹' (U ×ˢ B) =
            if x ∈ U then B else ∅ := by
          ext y
          simp
        rw [Set.preimage_inter, hrectsec]
        by_cases hxU : x ∈ U
        · simp only [hxU, if_true]
          apply (ENNReal.toReal_eq_toReal_iff'
            (measure_ne_top nu _) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (measure_ne_top nu B))).mp
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc_nonneg,
            ← Measure.real, ← Measure.real]
          exact hx
        · simp only [hxU, if_false, Set.inter_empty, measure_empty]
      rw [lintegral_congr_ae hsecE]
      have hfun : (fun x : Alpha => if x ∈ U then cE * nu B else 0) =
          U.indicator (fun _ => cE * nu B) := by
        funext x
        by_cases hx : x ∈ U <;> simp [Set.indicator, hx]
      rw [hfun, lintegral_indicator hU, lintegral_const]
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter, smul_eq_mul]
      ac_rfl
    · simp [lambda, cE, hmassE]

  have hmass : (mu.prod nu).real A = c := by
    rw [Measure.real, hmassE]
    dsimp only [cE]
    rw [ENNReal.toReal_ofReal hc_nonneg]
  have hidem : c = c * c := by
    have h := congrArg (fun m : Measure (Alpha × Beta) => m A) hlambda
    simp only [lambda, Measure.restrict_apply hA, Set.inter_self,
      Measure.smul_apply, cE] at h
    apply_fun ENNReal.toReal at h
    simp only [smul_eq_mul] at h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc_nonneg,
      ← Measure.real, hmass] at h
    exact h
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by nlinarith [hidem]
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rw [eventuallyConst_set']
  rcases hc01 with rfl | rfl
  · left
    apply ae_eq_empty.mpr
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (mu.prod nu) A) (by simp)).mp
    simpa [Measure.real] using hmass
  · right
    apply ae_eq_univ.mpr
    have hone : (mu.prod nu) A = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top (mu.prod nu) A) (by simp)).mp
      simpa [Measure.real] using hmass
    rw [measure_compl hA (measure_ne_top (mu.prod nu) A), hone]
    simp



open Lattice

theorem pottsLabelShift_eq_piCongrLeft {d q : Nat}
    (g : Multiplicative (Site d)) :
    (pottsLabelShift g : (Site d -> Fin q) -> (Site d -> Fin q)) =
      ⇑(Equiv.piCongrLeft (fun _ : Site d => Fin q)
        (MulAction.toPerm g)) := by
  funext label x
  set e := MulAction.toPerm (β := Site d) g with he
  conv_rhs => rw [show x = e (e.symm x) from (e.apply_symm_apply x).symm,
    Equiv.piCongrLeft_apply_apply (a := e.symm x)]
  rw [pottsLabelShift, he, MulAction.toPerm_symm_apply]


theorem pottsIIDLabelMeasure_measurePreserving {d q : Nat} [NeZero q]
    (g : Multiplicative (Site d)) :
    MeasurePreserving (pottsLabelShift g)
      (pottsIIDLabelMeasure d q) (pottsIIDLabelMeasure d q) := by
  have hmeas : Measurable (pottsLabelShift g :
      (Site d -> Fin q) -> (Site d -> Fin q)) := by
    rw [pottsLabelShift_eq_piCongrLeft]
    exact (MeasurableEquiv.piCongrLeft (fun _ : Site d => Fin q)
      (MulAction.toPerm g)).measurable
  refine ⟨hmeas, ?_⟩
  rw [pottsLabelShift_eq_piCongrLeft]
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : Site d => (PMF.uniformOfFintype (Fin q)).toMeasure)
    (MulAction.toPerm (β := Site d) g)
  simpa only [pottsIIDLabelMeasure] using h

theorem pottsLabelShift_mul {d q : Nat}
    (g h : Multiplicative (Site d)) :
    (pottsLabelShift (g * h) : (Site d -> Fin q) -> (Site d -> Fin q)) =
      pottsLabelShift g ∘ pottsLabelShift h := by
  funext label x
  simp [pottsLabelShift, mul_smul]

theorem pottsLabelShift_freeAxisTranslationPower {d q : Nat}
    (hd : 1 <= d) (n : Nat) :
    (pottsLabelShift (freeAxisTranslationPower hd n) :
      (Site d -> Fin q) -> (Site d -> Fin q)) =
      (pottsLabelShift (freeAxisTranslation hd))^[n] := by
  rw [freeAxisTranslationPower_eq_pow]
  induction n with
  | zero =>
      funext label x
      simp [pottsLabelShift]
  | succ n ih =>
      rw [pow_succ, pottsLabelShift_mul, ih, Function.iterate_succ]

theorem pottsLabelShift_preimage_cylinder {d q : Nat}
    (g : Multiplicative (Site d)) (t : Finset (Site d))
    (T : Set (t -> Fin q)) :
    (pottsLabelShift g : (Site d -> Fin q) -> (Site d -> Fin q)) ⁻¹'
        cylinder t T =
      cylinder (t.image (fun x => g⁻¹ • x))
        ((fun (label : (t.image (fun x => g⁻¹ • x)) -> Fin q) (x : t) =>
          label ⟨g⁻¹ • (x : Site d), Finset.mem_image_of_mem _ x.2⟩) ⁻¹' T) := by
  ext label
  simp only [cylinder, Set.mem_preimage]
  rfl

private noncomputable def pottsInverseAxisFinset {d : Nat}
    (hd : 1 <= d) (n : Nat) (B : Finset (Site d)) : Finset (Site d) :=
  B.image fun x => (freeAxisTranslationPower hd n)⁻¹ • x

private theorem pottsInverseAxisFinset_eventually_outside_box {d : Nat}
    (hd : 1 <= d) (B : Finset (Site d)) (m : Nat) :
    ∀ᶠ n in atTop, (pottsInverseAxisFinset hd n B : Set (Site d)) ⊆
      (box d m)ᶜ := by
  let M := B.sup fun x => (x ⟨0, hd⟩).natAbs
  filter_upwards [eventually_ge_atTop (M + m + 1)] with n hn
  intro z hz
  simp only [pottsInverseAxisFinset, Finset.coe_image, Set.mem_image,
    Finset.mem_coe] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [Set.mem_compl_iff]
  intro hbox
  have hxBound : x ⟨0, hd⟩ <= (M : Int) := by
    exact (Int.le_natAbs.trans (by exact_mod_cast
      (Finset.le_sup (f := fun x => (x ⟨0, hd⟩).natAbs) hx)))
  have hcoord := hbox ⟨0, hd⟩
  have hval :
      (((freeAxisTranslationPower hd n)⁻¹ • x) ⟨0, hd⟩) =
        x ⟨0, hd⟩ - n := by
    change (-(Multiplicative.toAdd (freeAxisTranslationPower hd n)) + x)
      ⟨0, hd⟩ = _
    simp [freeAxisTranslationPower]
    ring
  rw [hval] at hcoord
  have hneg : x ⟨0, hd⟩ - (n : Int) <= -(m + 1 : Int) := by omega
  have habs : ((x ⟨0, hd⟩ - (n : Int)).natAbs : Int) =
      -(x ⟨0, hd⟩ - (n : Int)) := by
    rw [← Int.natAbs_neg, Int.natAbs_of_nonneg]
    omega
  have hcoord' : ((x ⟨0, hd⟩ - (n : Int)).natAbs : Int) <= m := by
    exact_mod_cast hcoord
  rw [habs] at hcoord'
  omega

private theorem pottsAxisFinsets_eventually_disjoint {d : Nat}
    (hd : 1 <= d) (s t : Finset (Site d)) :
    ∀ᶠ n in atTop, Disjoint s
      (t.image (fun x => (freeAxisTranslationPower hd n)⁻¹ • x)) := by
  obtain ⟨m, hm⟩ := Percolation.finite_subset_box
    (s : Set (Site d)) s.finite_toSet
  filter_upwards [pottsInverseAxisFinset_eventually_outside_box hd t m]
    with n hn
  rw [Finset.disjoint_left]
  intro x hxs hxt
  have hxbox : x ∈ box d m := hm hxs
  have hxout : x ∈ (box d m)ᶜ := hn hxt
  exact hxout hxbox

private theorem pottsIIDLabel_cylinders_axis_factor {d q : Nat} [NeZero q]
    (hd : 1 <= d) (s t : Finset (Site d))
    (S : Set (s -> Fin q)) (T : Set (t -> Fin q))
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᶠ n in atTop,
      (pottsIIDLabelMeasure d q).real
          (cylinder s S ∩
            ((pottsLabelShift (freeAxisTranslation hd))^[n]) ⁻¹'
              cylinder t T) =
        (pottsIIDLabelMeasure d q).real (cylinder s S) *
          (pottsIIDLabelMeasure d q).real (cylinder t T) := by
  filter_upwards [pottsAxisFinsets_eventually_disjoint hd s t] with n hn
  rw [← pottsLabelShift_freeAxisTranslationPower hd n,
    pottsLabelShift_preimage_cylinder]
  let t' := t.image
    (fun x => (freeAxisTranslationPower hd n)⁻¹ • x)
  let T' : Set (t' -> Fin q) :=
    (fun (label : t' -> Fin q) (x : t) =>
      label ⟨(freeAxisTranslationPower hd n)⁻¹ • (x : Site d),
        Finset.mem_image_of_mem _ x.2⟩) ⁻¹' T
  have hT' : MeasurableSet T' := hT.preimage (by fun_prop)
  have hfactor := Percolation.bkc_infinitePi_disjoint_cylinder
    (fun _ : Site d => (PMF.uniformOfFintype (Fin q)).toMeasure)
    hS hT' hn
  have htranslated : (pottsIIDLabelMeasure d q).real (cylinder t' T') =
      (pottsIIDLabelMeasure d q).real (cylinder t T) := by
    rw [← pottsLabelShift_preimage_cylinder
      (freeAxisTranslationPower hd n) t T]
    exact (pottsIIDLabelMeasure_measurePreserving
      (q := q) (freeAxisTranslationPower hd n)).measureReal_preimage
        (MeasurableSet.cylinder t hT).nullMeasurableSet
  unfold pottsIIDLabelMeasure at htranslated ⊢
  rw [Measure.real, hfactor, ENNReal.toReal_mul,
    ← Measure.real, ← Measure.real, htranslated]

private theorem pottsIIDLabel_exists_cylinder_symmDiff_lt {d q : Nat}
    [NeZero q] {A : Set (Site d -> Fin q)} (hA : MeasurableSet A)
    {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    ∃ C ∈ measurableCylinders (fun _ : Site d => Fin q),
      pottsIIDLabelMeasure d q (C ∆ A) < epsilon := by
  have hring : IsSetRing
      (measurableCylinders (fun _ : Site d => Fin q)) :=
    { empty_mem := empty_mem_measurableCylinders _
      union_mem := fun _ _ hs ht => union_mem_measurableCylinders hs ht
      diff_mem := fun _ _ hs ht => diff_mem_measurableCylinders hs ht }
  refine exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    hring ?_ generateFrom_measurableCylinders.symm hA hepsilon
  exact ⟨{Set.univ}, Set.countable_singleton _,
    by simpa using (univ_mem_measurableCylinders
      (fun _ : Site d => Fin q)), by simp⟩

set_option maxHeartbeats 2000000 in



theorem pottsIIDLabel_axis_mixingAgainst {d q : Nat} [NeZero q]
    (hd : 1 <= d) :
    MixingAgainst (pottsLabelShift (freeAxisTranslation hd))
      (pottsIIDLabelMeasure d q)
      (measurableCylinders (fun _ : Site d => Fin q)) := by
  classical
  intro A hA B hB
  rw [mem_measurableCylinders] at hB
  obtain ⟨t, T, hT, rfl⟩ := hB
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let delta := epsilon / 4
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hCcyl, hCA⟩ :=
    pottsIIDLabel_exists_cylinder_symmDiff_lt (d := d) (q := q) hA
      (epsilon := ENNReal.ofReal delta) (by simpa using hdelta)
  rw [mem_measurableCylinders] at hCcyl
  obtain ⟨s, S, hS, rfl⟩ := hCcyl
  have hCmeas : MeasurableSet
      (cylinder (α := fun _ : Site d => Fin q) s S) :=
    MeasurableSet.cylinder s hS
  have hCAreal : (pottsIIDLabelMeasure d q).real
      (cylinder s S ∆ A) < delta := by
    have h := (ENNReal.toReal_lt_toReal
      (measure_ne_top (pottsIIDLabelMeasure d q) _) (by simp)).2 hCA
    rwa [ENNReal.toReal_ofReal hdelta.le] at h
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    (pottsIIDLabel_cylinders_axis_factor hd s t S T hS hT))
  refine ⟨N, ?_⟩
  intro n hnN
  have hn := hN n hnN
  rw [Real.dist_eq]
  let Dn := ((pottsLabelShift (freeAxisTranslation hd))^[n]) ⁻¹'
    cylinder t T
  have hDn : MeasurableSet Dn :=
    (MeasurableSet.cylinder t hT).preimage
      ((pottsIIDLabelMeasure_measurePreserving (q := q)
        (freeAxisTranslation hd)).measurable.iterate n)
  have hinter : abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
      (pottsIIDLabelMeasure d q).real (cylinder s S ∩ Dn)) <=
      (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := by
    calc
      abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
          (pottsIIDLabelMeasure d q).real (cylinder s S ∩ Dn)) <=
          (pottsIIDLabelMeasure d q).real
            ((A ∩ Dn) ∆ (cylinder s S ∩ Dn)) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hA.inter hDn).nullMeasurableSet
          (hCmeas.inter hDn).nullMeasurableSet
      _ <= (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := by
        rw [← Set.inter_symmDiff_distrib_right,
          symmDiff_comm A (cylinder s S)]
        exact measureReal_mono (Set.inter_subset_left) (by finiteness)
  have hmarg : abs ((pottsIIDLabelMeasure d q).real (cylinder s S) *
        (pottsIIDLabelMeasure d q).real (cylinder t T) -
      (pottsIIDLabelMeasure d q).real A *
        (pottsIIDLabelMeasure d q).real (cylinder t T)) <=
      (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := by
    rw [← sub_mul, abs_mul]
    calc
      abs ((pottsIIDLabelMeasure d q).real (cylinder s S) -
          (pottsIIDLabelMeasure d q).real A) *
          abs ((pottsIIDLabelMeasure d q).real (cylinder t T)) <=
          (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) * 1 := by
        gcongr
        · exact abs_measureReal_sub_le_measureReal_symmDiff
            hCmeas.nullMeasurableSet hA.nullMeasurableSet
        · rw [abs_of_nonneg measureReal_nonneg]
          exact measureReal_le_one
      _ = (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := mul_one _
  change abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
    (pottsIIDLabelMeasure d q).real A *
      (pottsIIDLabelMeasure d q).real (cylinder t T)) < epsilon
  rw [show (pottsIIDLabelMeasure d q).real (cylinder s S ∩ Dn) =
      (pottsIIDLabelMeasure d q).real (cylinder s S) *
        (pottsIIDLabelMeasure d q).real (cylinder t T) from hn] at hinter
  calc
    abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
        (pottsIIDLabelMeasure d q).real A *
          (pottsIIDLabelMeasure d q).real (cylinder t T)) <=
      abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
        (pottsIIDLabelMeasure d q).real (cylinder s S) *
          (pottsIIDLabelMeasure d q).real (cylinder t T)) +
      abs ((pottsIIDLabelMeasure d q).real (cylinder s S) *
        (pottsIIDLabelMeasure d q).real (cylinder t T) -
        (pottsIIDLabelMeasure d q).real A *
          (pottsIIDLabelMeasure d q).real (cylinder t T)) := abs_sub_le _ _ _
    _ <= 2 * (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := by
      linarith
    _ < epsilon := by
      calc
        2 * (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) <
            2 * delta := mul_lt_mul_of_pos_left hCAreal (by norm_num)
        _ < epsilon := by dsimp [delta]; linarith





theorem freeInfiniteVolume_axisShift_ergodic_generalQ
    {d : Nat} (hd : 1 <= d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    _root_.Ergodic
      (ConfigSpace.shift (freeAxisTranslation hd) :
        ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  have hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu :=
    fkgqt_freeIV_isTranslationInvariant hp hp1 hq
  refine ⟨hti (freeAxisTranslation hd), ⟨?_⟩⟩
  intro s hs hinv
  have hinvPow : forall n : Nat,
      ConfigSpace.shift (freeAxisTranslationPower hd n) ⁻¹' s = s := by
    intro n
    rw [shift_freeAxisTranslationPower]
    exact Function.IsFixedPt.preimage_iterate hinv n
  obtain ⟨t, ht, hae⟩ :=
    ati_sequenceInvariant_aeTail (fkTailEdgeWindow d)
      fkTailEdgeWindow_mono (freeAxisTranslationPower hd)
      (freeAxisTranslationPower_escape hd) hti s hs hinvPow
  rw [eventuallyConst_set']
  rcases freeInfiniteVolume_tail_trivial_generalQ hp hp1 hq t ht with
      ht0 | ht1
  · exact Or.inl (hae.trans (ae_eq_empty.mpr ht0))
  · right
    apply hae.trans
    rw [ae_eq_univ]
    rw [measure_compl ht.measurableSet (measure_ne_top mu t), ht1,
      measure_univ]
    simp



theorem freeInfiniteVolume_prod_pottsIIDLabel_axis_ergodic
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) :
    let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    _root_.Ergodic
      (Prod.map
        (ConfigSpace.shift (freeAxisTranslation hd) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
        (pottsLabelShift (freeAxisTranslation hd)))
      ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod
        (pottsIIDLabelMeasure d q)) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure :=
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) :
      Measure (ConfigSpace (Sym2 (Site d))))
  apply ergodic_prod_of_mixingAgainst
    (ConfigSpace.shift (freeAxisTranslation hd))
    (pottsLabelShift (freeAxisTranslation hd))
    (freeInfiniteVolume_axisShift_ergodic_generalQ hd hp hp1 hqR)
    (pottsIIDLabelMeasure_measurePreserving (q := q)
      (freeAxisTranslation hd))
    (measurableCylinders (fun _ : Site d => Fin q))
  · exact generateFrom_measurableCylinders
  · exact isPiSystem_measurableCylinders
  · exact ⟨fun _ => Set.univ,
      fun _ => univ_mem_measurableCylinders _, by rw [iUnion_const]⟩
  · intro B hB
    exact MeasurableSet.of_mem_measurableCylinders hB
  · exact pottsIIDLabel_axis_mixingAgainst hd



theorem freeInfiniteVolume_pottsClusterFactorInput_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) :
    let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    IsErgodicFor pottsClusterFactorInputShift
      ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod
        (pottsIIDLabelMeasure d q)) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure :=
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) :
      Measure (ConfigSpace (Sym2 (Site d))))
  let sourceMeasure := edgeMeasure.prod (pottsIIDLabelMeasure d q)
  have hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) edgeMeasure :=
    fkgqt_freeIV_isTranslationInvariant hp hp1 hqR
  have haxis : _root_.Ergodic
      (Prod.map
        (ConfigSpace.shift (freeAxisTranslation hd) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
        (pottsLabelShift (freeAxisTranslation hd))) sourceMeasure :=
    freeInfiniteVolume_prod_pottsIIDLabel_axis_ergodic hd hp hp1
  refine ⟨?_, ?_⟩
  · intro g
    have hprod := (hti g).prod
      (pottsIIDLabelMeasure_measurePreserving (q := q) g)
    convert hprod using 1
  · intro s hs hinv
    have hinvAxis : (Prod.map
        (ConfigSpace.shift (freeAxisTranslation hd) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
        (pottsLabelShift (freeAxisTranslation hd))) ⁻¹' s = s := by
      simpa only [pottsClusterFactorInputShift, Prod.map_apply] using
        hinv (freeAxisTranslation hd)
    rcases haxis.toPreErgodic.prob_eq_zero_or_one hs hinvAxis with
      hzero | hone
    · exact Or.inl hzero
    · right
      simpa only [measure_univ] using hone


theorem freePottsClusterSumJointMeasure_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (boundaryColor : Fin q) :
    let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    IsErgodicFor (pottsJointShift (d := d) (q := q))
      (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _)) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR)
  exact pottsClusterSumJointMeasure_isErgodicFor
    (d := d) (q := q) boundaryColor edgeMeasure
    (freeInfiniteVolume_pottsClusterFactorInput_isErgodicFor
      (d := d) (q := q) hd hp hp1)



theorem freePottsClusterSumSpinMarginal_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (boundaryColor : Fin q) :
    let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    IsErgodicFor (pottsSpinShift (d := d) (q := q))
      (Measure.map Prod.fst
        (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor
          (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _))) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR)
  exact pottsClusterSumSpinMarginal_isErgodicFor
    (d := d) (q := q) boundaryColor edgeMeasure
    (freePottsClusterSumJointMeasure_isErgodicFor
      (d := d) (q := q) hd hp hp1 boundaryColor)




def pottsAllClustersFiniteEvent (d : Nat) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  ⋂ x : Site d,
    {omega : ConfigSpace (Sym2 (Site d)) | (cluster d omega x).Infinite}ᶜ

theorem measurableSet_pottsAllClustersFiniteEvent (d : Nat) :
    MeasurableSet (pottsAllClustersFiniteEvent d) := by
  exact MeasurableSet.iInter fun x =>
    (Percolation.measurableSet_clusterInfinite x).compl

theorem mem_pottsAllClustersFiniteEvent_iff {d : Nat}
    (omega : ConfigSpace (Sym2 (Site d))) :
    omega ∈ pottsAllClustersFiniteEvent d ↔
      forall x : Site d, (cluster d omega x).Finite := by
  simp only [pottsAllClustersFiniteEvent, Set.mem_iInter, Set.mem_compl_iff,
    Set.mem_setOf_eq]
  exact forall_congr' fun _ => not_infinite



theorem ae_pottsAllClustersFinite_of_translationInvariant_of_origin_zero
    {d : Nat} (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    (htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) edgeMeasure)
    (horigin : edgeMeasure
      {omega : ConfigSpace (Sym2 (Site d)) |
        (cluster d omega (Percolation.origin d)).Infinite} = 0) :
    ∀ᵐ omega ∂edgeMeasure, omega ∈ pottsAllClustersFiniteEvent d := by
  have hsite : forall x : Site d,
      edgeMeasure
        {omega : ConfigSpace (Sym2 (Site d)) |
          (cluster d omega x).Infinite} = 0 := by
    intro x
    let g : Multiplicative (Site d) := Multiplicative.ofAdd x
    have hgx : g • Percolation.origin d = x := by
      show Multiplicative.toAdd g + (0 : Site d) = x
      simp [g]
    have hpre :
        (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
          ConfigSpace (Sym2 (Site d))) ⁻¹'
            {omega | (cluster d omega x).Infinite} =
          {omega | (cluster d omega (Percolation.origin d)).Infinite} := by
      ext omega
      change (cluster d (ConfigSpace.shift g omega) x).Infinite <->
        (cluster d omega (Percolation.origin d)).Infinite
      rw [← hgx, Percolation.cluster_shift]
      exact Set.infinite_image_iff
        (Set.injOn_of_injective fun _ _ h => smul_left_cancel g h)
    have hinv := htrans.measure_preimage g
      (Percolation.measurableSet_clusterInfinite x)
    rw [hpre] at hinv
    exact hinv.symm.trans horigin
  rw [ae_iff]
  change edgeMeasure (pottsAllClustersFiniteEvent d)ᶜ = 0
  rw [pottsAllClustersFiniteEvent, compl_iInter]
  simp only [compl_compl]
  exact measure_iUnion_null hsite



theorem pottsClusterSumJointFactor_eq_of_allClustersFinite
    {d q : Nat} [NeZero q] (a b : Fin q)
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
    (hfinite : input.1 ∈ pottsAllClustersFiniteEvent d) :
    pottsClusterSumJointFactor a input =
      pottsClusterSumJointFactor b input := by
  apply Prod.ext
  · funext x
    simp only [pottsClusterSumJointFactor]
    unfold pottsClusterSumSpin
    rw [
      dif_pos ((mem_pottsAllClustersFiniteEvent_iff input.1).mp hfinite x),
      dif_pos ((mem_pottsAllClustersFiniteEvent_iff input.1).mp hfinite x)]
  · rfl



theorem pottsClusterSumJointMeasure_eq_of_ae_allClustersFinite
    {d q : Nat} [NeZero q] (a b : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    (hfinite : ∀ᵐ omega ∂edgeMeasure,
      omega ∈ pottsAllClustersFiniteEvent d) :
    pottsClusterSumJointMeasure a edgeMeasure =
      pottsClusterSumJointMeasure b edgeMeasure := by
  rw [pottsClusterSumJointMeasure, pottsClusterSumJointMeasure]
  apply Measure.map_congr
  have hprod : ∀ᵐ input ∂edgeMeasure.prod (pottsIIDLabelMeasure d q),
      input.1 ∈ pottsAllClustersFiniteEvent d := by
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hfinite] with omega homega
      exact Filter.Eventually.of_forall fun _ => homega
    · exact (measurableSet_pottsAllClustersFiniteEvent d).preimage measurable_fst
  filter_upwards [hprod] with input hinput
  exact pottsClusterSumJointFactor_eq_of_allClustersFinite a b input hinput

end StatMech.FK
