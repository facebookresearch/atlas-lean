/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Sharpness.ABFiniteSymmetry

open Filter Topology Set

namespace StatMech
namespace Sharpness



theorem abtp_aizenmanBarsky_of_deriv_tendsto
    (Mn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real) (J : Real)
    (hfinite : forall n beta h,
      deriv (fun b => Mn n b h) beta <=
        J * (Mn n beta h * deriv (fun t => Mn n beta t) h))
    (hmag : forall beta h,
      Tendsto (fun n => Mn n beta h) atTop (nhds (M beta h)))
    (hbeta : forall beta h,
      Tendsto (fun n => deriv (fun b => Mn n b h) beta) atTop
        (nhds (deriv (fun b => M b h) beta)))
    (hfield : forall beta h,
      Tendsto (fun n => deriv (fun t => Mn n beta t) h) atTop
        (nhds (deriv (fun t => M beta t) h))) :
    AizenmanBarskyInequality M J := by
  intro beta h
  apply le_of_tendsto_of_tendsto (hbeta beta h)
    (tendsto_const_nhds.mul ((hmag beta h).mul (hfield beta h)))
  exact Filter.Eventually.of_forall (fun n => hfinite n beta h)




theorem abtp_inequality_at_of_deriv_tendsto
    (Mn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real) (J beta h : Real)
    (hfinite : forall n,
      deriv (fun b => Mn n b h) beta <=
        J * (Mn n beta h * deriv (fun t => Mn n beta t) h))
    (hmag : Tendsto (fun n => Mn n beta h) atTop (nhds (M beta h)))
    (hbeta : Tendsto (fun n => deriv (fun b => Mn n b h) beta) atTop
      (nhds (deriv (fun b => M b h) beta)))
    (hfield : Tendsto (fun n => deriv (fun t => Mn n beta t) h) atTop
      (nhds (deriv (fun t => M beta t) h))) :
    deriv (fun b => M b h) beta <=
      J * (M beta h * deriv (fun t => M beta t) h) := by
  exact le_of_tendsto_of_tendsto hbeta
    (tendsto_const_nhds.mul (hmag.mul hfield))
    (Filter.Eventually.of_forall hfinite)



theorem abtp_hasDerivAt_characteristic
    (F : Real -> Real -> Real) (b h c t : Real)
    (hF : DifferentiableAt Real (Function.uncurry F)
      (b + t, h - c * t)) :
    HasDerivAt (fun s => F (b + s) (h - c * s))
      (deriv (fun x => F x (h - c * t)) (b + t) -
        c * deriv (fun y => F (b + t) y) (h - c * t)) t := by
  let L := fderiv Real (Function.uncurry F) (b + t, h - c * t)
  have hbase : HasFDerivAt (Function.uncurry F) L
      (b + t, h - c * t) := hF.hasFDerivAt
  have hb : HasFDerivAt (fun x : Real => F x (h - c * t))
      (L.comp (ContinuousLinearMap.inl Real Real Real)) (b + t) := by
    simpa [Function.comp_def] using hbase.comp (b + t)
      (hasFDerivAt_prodMk_left (𝕜 := Real) (b + t) (h - c * t))
  have hh : HasFDerivAt (fun y : Real => F (b + t) y)
      (L.comp (ContinuousLinearMap.inr Real Real Real)) (h - c * t) := by
    simpa [Function.comp_def] using hbase.comp (h - c * t)
      (hasFDerivAt_prodMk_right (𝕜 := Real) (b + t) (h - c * t))
  have h1 : HasDerivAt (fun s : Real => b + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add b
  have h2 : HasDerivAt (fun s : Real => h - c * s) (-c) t := by
    convert (hasDerivAt_const t h).sub ((hasDerivAt_id t).const_mul c) using 1 <;> ring
  have hline := hbase.comp t (h1.hasFDerivAt.prodMk h2.hasFDerivAt)
  have hb' : deriv (fun x => F x (h - c * t)) (b + t) = L (1, 0) := by
    rw [hb.hasDerivAt.deriv]
    simp
  have hh' : deriv (fun y => F (b + t) y) (h - c * t) = L (0, 1) := by
    rw [hh.hasDerivAt.deriv]
    simp
  convert hline.hasDerivAt using 1
  rw [hb', hh']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [show ((1, -c) : Real × Real) =
      ((1, 0) : Real × Real) + (-c) • ((0, 1) : Real × Real) by ext <;> simp]
  rw [map_add, map_smul]
  ring













theorem abtp_inequality_at_of_characteristics
    (Mn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real)
    (J beta h : Real)
    (hJ : 0 <= J) (hM : 0 <= M beta h)
    (hfinite : forall n b t,
      deriv (fun x => Mn n x t) b <=
        J * (Mn n b t * deriv (fun y => Mn n b y) t))
    (hfield : forall n b t, 0 <= deriv (fun y => Mn n b y) t)
    (hmonoBeta : forall n t, Monotone (fun b => Mn n b t))
    (hmonoField : forall n b, Monotone (fun t => Mn n b t))
    (hle : forall n b t, Mn n b t <= M b t)
    (hconv : forall b t,
      Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
    (hcontBeta : ContinuousAt (fun b => M b h) beta)
    (hlineFinite : forall n c t,
      HasDerivAt (fun s => Mn n (beta + s) (h - c * s))
        (deriv (fun b => Mn n b (h - c * t)) (beta + t) -
          c * deriv (fun y => Mn n (beta + t) y) (h - c * t)) t)
    (hlineLimit : forall c,
      HasDerivAt (fun s => M (beta + s) (h - c * s))
        (deriv (fun b => M b h) beta -
          c * deriv (fun y => M beta y) h) 0) :
    deriv (fun b => M b h) beta <=
      J * (M beta h * deriv (fun y => M beta y) h) := by
  have hepsilon : forall epsilon : Real, 0 < epsilon ->
      deriv (fun b => M b h) beta <=
        J * ((M beta h + epsilon) * deriv (fun y => M beta y) h) := by
    intro epsilon hepsilon
    let c : Real := J * (M beta h + epsilon)
    have hc : 0 <= c := mul_nonneg hJ (add_nonneg hM hepsilon.le)
    have hopen : {b : Real | M b h < M beta h + epsilon} ∈ nhds beta :=
      hcontBeta (Iio_mem_nhds (lt_add_of_pos_right _ hepsilon))
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hopen
    let d : Real := r / 2
    have hd : 0 < d := by dsimp [d]; linarith
    have hMd : M (beta + d) h < M beta h + epsilon := by
      apply hrsub
      change dist (beta + d) beta < r
      rw [Real.dist_eq]
      have habs : |beta + d - beta| = d := by
        rw [add_sub_cancel_left, abs_of_pos hd]
      rw [habs]
      dsimp [d]
      linarith
    let fn : Nat -> Real -> Real :=
      fun n t => Mn n (beta + t) (h - c * t)
    let g : Real -> Real := fun t => M (beta + t) (h - c * t)
    have hbound : forall n t, t ∈ Icc (0 : Real) d ->
        Mn n (beta + t) (h - c * t) <= M beta h + epsilon := by
      intro n t ht
      calc
        Mn n (beta + t) (h - c * t) <=
            Mn n (beta + d) (h - c * t) :=
          hmonoBeta n (h - c * t) (by linarith [ht.2])
        _ <= Mn n (beta + d) h :=
          hmonoField n (beta + d) (by nlinarith [hc, ht.1])
        _ <= M (beta + d) h := hle n (beta + d) h
        _ <= M beta h + epsilon := hMd.le
    have hanti : forall n, AntitoneOn (fn n) (Icc (0 : Real) d) := by
      intro n
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 d)
      · intro t ht
        exact (hlineFinite n c t).continuousAt.continuousWithinAt
      · intro t ht
        exact (hlineFinite n c t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc, mem_Ioo] at ht
        change deriv (fn n) t <= 0
        rw [(hlineFinite n c t).deriv]
        let db := deriv (fun b => Mn n b (h - c * t)) (beta + t)
        let dh := deriv (fun y => Mn n (beta + t) y) (h - c * t)
        have hab : db <= J * (Mn n (beta + t) (h - c * t) * dh) :=
          hfinite n (beta + t) (h - c * t)
        have hdh : 0 <= dh := hfield n (beta + t) (h - c * t)
        have hcoef : J * Mn n (beta + t) (h - c * t) <= c := by
          dsimp [c]
          exact mul_le_mul_of_nonneg_left
            (hbound n t ⟨ht.1.le, ht.2.le⟩) hJ
        calc
          db - c * dh <= J * (Mn n (beta + t) (h - c * t) * dh) - c * dh :=
            sub_le_sub_right hab _
          _ = (J * Mn n (beta + t) (h - c * t) - c) * dh := by ring
          _ <= 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcoef) hdh
    have hgle : forall t, t ∈ Icc (0 : Real) d -> g t <= g 0 := by
      intro t ht
      apply le_of_tendsto_of_tendsto
        (hconv (beta + t) (h - c * t))
        (hconv (beta + 0) (h - c * 0))
      exact Filter.Eventually.of_forall (fun n =>
        hanti n (left_mem_Icc.mpr hd.le) ht ht.1)
    have hlocal : IsLocalMaxOn g (Ici (0 : Real)) 0 := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hd)] with t ht0 htd
      exact hgle t ⟨ht0, htd.le⟩
    have hone : (1 : Real) ∈ posTangentConeAt (Ici (0 : Real)) 0 := by
      rw [one_mem_posTangentConeAt_iff_mem_closure]
      rw [show Ioi (0 : Real) ∩ Ici 0 = Ioi 0 by
        ext x
        simp only [mem_inter_iff, mem_Ioi, mem_Ici]
        constructor
        · rintro ⟨hx, _⟩
          exact hx
        · intro hx
          exact ⟨hx, le_of_lt hx⟩]
      rw [closure_Ioi]
      exact mem_Ici.mpr le_rfl
    have hdir := hlocal.hasFDerivWithinAt_nonpos
      (hlineLimit c).hasFDerivAt.hasFDerivWithinAt hone
    have hchar : deriv (fun b => M b h) beta -
        c * deriv (fun y => M beta y) h <= 0 := by
      simpa using hdir
    dsimp [c] at hchar
    nlinarith
  let dh := deriv (fun y => M beta y) h
  by_cases hcoef : 0 < J * dh
  · apply le_of_forall_pos_le_add
    intro delta hdelta
    have he := hepsilon (delta / (J * dh)) (div_pos hdelta hcoef)
    have hprodne : J * dh ≠ 0 := hcoef.ne'
    have hJne : J ≠ 0 := fun hzero => hprodne (mul_eq_zero.mpr (Or.inl hzero))
    have hdhne : dh ≠ 0 := fun hzero => hprodne (mul_eq_zero.mpr (Or.inr hzero))
    calc
      deriv (fun b => M b h) beta <=
          J * ((M beta h + delta / (J * dh)) * dh) := he
      _ = J * (M beta h * dh) + delta := by
        field_simp [hJne, hdhne]
  · have he := hepsilon 1 zero_lt_one
    have hnonpos : J * dh <= 0 := le_of_not_gt hcoef
    calc
      deriv (fun b => M b h) beta <= J * ((M beta h + 1) * dh) := he
      _ <= J * (M beta h * dh) := by nlinarith





theorem abtp_inequality_at_of_jointDifferentiable
    (Mn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real)
    (J beta h : Real)
    (hJ : 0 <= J) (hM : 0 <= M beta h)
    (hfinite : forall n b t,
      deriv (fun x => Mn n x t) b <=
        J * (Mn n b t * deriv (fun y => Mn n b y) t))
    (hfield : forall n b t, 0 <= deriv (fun y => Mn n b y) t)
    (hmonoBeta : forall n t, Monotone (fun b => Mn n b t))
    (hmonoField : forall n b, Monotone (fun t => Mn n b t))
    (hle : forall n b t, Mn n b t <= M b t)
    (hconv : forall b t,
      Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
    (hcontBeta : ContinuousAt (fun b => M b h) beta)
    (hjointFinite : forall n b t,
      DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
    (hjointLimit : DifferentiableAt Real (Function.uncurry M) (beta, h)) :
    deriv (fun b => M b h) beta <=
      J * (M beta h * deriv (fun y => M beta y) h) := by
  apply abtp_inequality_at_of_characteristics Mn M J beta h hJ hM
    hfinite hfield hmonoBeta hmonoField hle hconv hcontBeta
  · intro n c t
    exact abtp_hasDerivAt_characteristic (Mn n) beta h c t
      (hjointFinite n (beta + t) (h - c * t))
  · intro c
    simpa using abtp_hasDerivAt_characteristic M beta h c 0 (by simpa using hjointLimit)




theorem abtp_inequality_at_of_characteristics_physical
    (Mn Cn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real)
    (J beta h : Real)
    (hJ : 0 <= J) (hbeta : 0 <= beta) (hh : 0 < h) (hM : 0 <= M beta h)
    (hfinite : forall n b t, 0 <= b -> 0 <= t ->
      deriv (fun x => Mn n x t) b <=
        J * (Cn n b t * deriv (fun y => Mn n b y) t))
    (hfield : forall n b t, 0 <= b -> 0 <= t ->
      0 <= deriv (fun y => Mn n b y) t)
    (hmonoBeta : forall n t, 0 <= t ->
      MonotoneOn (fun b => Cn n b t) (Ici 0))
    (hmonoField : forall n b, 0 <= b ->
      MonotoneOn (fun t => Cn n b t) (Ici 0))
    (hle : forall n b t, 0 <= b -> 0 <= t -> Cn n b t <= M b t)
    (hconv : forall b t, 0 <= b -> 0 <= t ->
      Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
    (hcontBeta : ContinuousAt (fun b => M b h) beta)
    (hlineFinite : forall n c t,
      HasDerivAt (fun s => Mn n (beta + s) (h - c * s))
        (deriv (fun b => Mn n b (h - c * t)) (beta + t) -
          c * deriv (fun y => Mn n (beta + t) y) (h - c * t)) t)
    (hlineLimit : forall c,
      HasDerivAt (fun s => M (beta + s) (h - c * s))
        (deriv (fun b => M b h) beta -
          c * deriv (fun y => M beta y) h) 0) :
    deriv (fun b => M b h) beta <=
      J * (M beta h * deriv (fun y => M beta y) h) := by
  have hepsilon : forall epsilon : Real, 0 < epsilon ->
      deriv (fun b => M b h) beta <=
        J * ((M beta h + epsilon) * deriv (fun y => M beta y) h) := by
    intro epsilon hepsilon
    let c : Real := J * (M beta h + epsilon)
    have hc : 0 <= c := mul_nonneg hJ (add_nonneg hM hepsilon.le)
    have hc1 : 0 < c + 1 := by linarith
    have hopen : {b : Real | M b h < M beta h + epsilon} ∈ nhds beta :=
      hcontBeta (Iio_mem_nhds (lt_add_of_pos_right _ hepsilon))
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hopen
    let d : Real := min (r / 2) (h / (c + 1))
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (by linarith) (div_pos hh hc1)
    have hdr : d <= r / 2 := min_le_left _ _
    have hdfield : d <= h / (c + 1) := min_le_right _ _
    have hcd : c * d < h := by
      calc
        c * d <= c * (h / (c + 1)) := mul_le_mul_of_nonneg_left hdfield hc
        _ = (c * h) / (c + 1) := by ring
        _ < h := (div_lt_iff₀ hc1).2 (by nlinarith)
    have hMd : M (beta + d) h < M beta h + epsilon := by
      apply hrsub
      change dist (beta + d) beta < r
      rw [Real.dist_eq]
      have habs : |beta + d - beta| = d := by
        rw [add_sub_cancel_left, abs_of_pos hd]
      rw [habs]
      linarith
    let fn : Nat -> Real -> Real :=
      fun n t => Mn n (beta + t) (h - c * t)
    let g : Real -> Real := fun t => M (beta + t) (h - c * t)
    have hphysical : forall t, t ∈ Icc (0 : Real) d ->
        0 <= beta + t ∧ 0 <= h - c * t := by
      intro t ht
      constructor
      · linarith [hbeta, ht.1]
      · have hct : c * t <= c * d :=
          mul_le_mul_of_nonneg_left ht.2 hc
        linarith
    have hbound : forall n t, t ∈ Icc (0 : Real) d ->
        Cn n (beta + t) (h - c * t) <= M beta h + epsilon := by
      intro n t ht
      have hpt := hphysical t ht
      have hbd : 0 <= beta + d := by linarith [hbeta, hd]
      calc
        Cn n (beta + t) (h - c * t) <=
            Cn n (beta + d) (h - c * t) :=
          hmonoBeta n (h - c * t) hpt.2 hpt.1 hbd (by linarith [ht.2])
        _ <= Cn n (beta + d) h :=
          hmonoField n (beta + d) hbd hpt.2 hh.le (by nlinarith [hc, ht.1])
        _ <= M (beta + d) h := hle n (beta + d) h hbd hh.le
        _ <= M beta h + epsilon := hMd.le
    have hanti : forall n, AntitoneOn (fn n) (Icc (0 : Real) d) := by
      intro n
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 d)
      · intro t ht
        exact (hlineFinite n c t).continuousAt.continuousWithinAt
      · intro t ht
        exact (hlineFinite n c t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc, mem_Ioo] at ht
        change deriv (fn n) t <= 0
        rw [(hlineFinite n c t).deriv]
        let db := deriv (fun b => Mn n b (h - c * t)) (beta + t)
        let dh := deriv (fun y => Mn n (beta + t) y) (h - c * t)
        have hpt := hphysical t ⟨ht.1.le, ht.2.le⟩
        have hab : db <= J * (Cn n (beta + t) (h - c * t) * dh) :=
          hfinite n (beta + t) (h - c * t) hpt.1 hpt.2
        have hdh : 0 <= dh := hfield n (beta + t) (h - c * t) hpt.1 hpt.2
        have hcoef : J * Cn n (beta + t) (h - c * t) <= c := by
          dsimp [c]
          exact mul_le_mul_of_nonneg_left
            (hbound n t ⟨ht.1.le, ht.2.le⟩) hJ
        calc
          db - c * dh <= J * (Cn n (beta + t) (h - c * t) * dh) - c * dh :=
            sub_le_sub_right hab _
          _ = (J * Cn n (beta + t) (h - c * t) - c) * dh := by ring
          _ <= 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcoef) hdh
    have hgle : forall t, t ∈ Icc (0 : Real) d -> g t <= g 0 := by
      intro t ht
      have hpt := hphysical t ht
      apply le_of_tendsto_of_tendsto
        (hconv (beta + t) (h - c * t) hpt.1 hpt.2)
        (hconv (beta + 0) (h - c * 0) (by simpa using hbeta) (by simpa using hh.le))
      exact Filter.Eventually.of_forall (fun n =>
        hanti n (left_mem_Icc.mpr hd.le) ht ht.1)
    have hlocal : IsLocalMaxOn g (Ici (0 : Real)) 0 := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hd)] with t ht0 htd
      exact hgle t ⟨ht0, htd.le⟩
    have hone : (1 : Real) ∈ posTangentConeAt (Ici (0 : Real)) 0 := by
      rw [one_mem_posTangentConeAt_iff_mem_closure]
      rw [show Ioi (0 : Real) ∩ Ici 0 = Ioi 0 by
        ext x
        simp only [mem_inter_iff, mem_Ioi, mem_Ici]
        constructor
        · rintro ⟨hx, _⟩
          exact hx
        · intro hx
          exact ⟨hx, le_of_lt hx⟩]
      rw [closure_Ioi]
      exact mem_Ici.mpr le_rfl
    have hdir := hlocal.hasFDerivWithinAt_nonpos
      (hlineLimit c).hasFDerivAt.hasFDerivWithinAt hone
    have hchar : deriv (fun b => M b h) beta -
        c * deriv (fun y => M beta y) h <= 0 := by
      simpa using hdir
    dsimp [c] at hchar
    nlinarith
  let dh := deriv (fun y => M beta y) h
  by_cases hcoef : 0 < J * dh
  · apply le_of_forall_pos_le_add
    intro delta hdelta
    have he := hepsilon (delta / (J * dh)) (div_pos hdelta hcoef)
    have hprodne : J * dh ≠ 0 := hcoef.ne'
    have hJne : J ≠ 0 := fun hzero => hprodne (mul_eq_zero.mpr (Or.inl hzero))
    have hdhne : dh ≠ 0 := fun hzero => hprodne (mul_eq_zero.mpr (Or.inr hzero))
    calc
      deriv (fun b => M b h) beta <=
          J * ((M beta h + delta / (J * dh)) * dh) := he
      _ = J * (M beta h * dh) + delta := by
        field_simp [hJne, hdhne]
  · have he := hepsilon 1 zero_lt_one
    have hnonpos : J * dh <= 0 := le_of_not_gt hcoef
    calc
      deriv (fun b => M b h) beta <= J * ((M beta h + 1) * dh) := he
      _ <= J * (M beta h * dh) := by nlinarith










theorem abtp_inequality_at_of_partialDifferentiable_physical_envelope
    (Mn Cn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real)
    (J beta h : Real)
    (hJ : 0 <= J) (hbeta : 0 <= beta) (hh : 0 < h) (hM : 0 <= M beta h)
    (hfinite : forall n b t, 0 <= b -> 0 <= t ->
      deriv (fun x => Mn n x t) b <=
        J * (Cn n b t * deriv (fun y => Mn n b y) t))
    (hfield : forall n b t, 0 <= b -> 0 <= t ->
      0 <= deriv (fun y => Mn n b y) t)
    (hmonoBeta : forall n t, 0 <= t ->
      MonotoneOn (fun b => Cn n b t) (Ici 0))
    (hmonoField : forall n b, 0 <= b ->
      MonotoneOn (fun t => Cn n b t) (Ici 0))
    (hle : forall n b t, 0 <= b -> 0 <= t -> Cn n b t <= M b t)
    (hconv : forall b t, 0 <= b -> 0 <= t ->
      Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
    (hcont : ContinuousAt (Function.uncurry M) (beta, h))
    (hjointFinite : forall n b t,
      DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
    (hbetaLimit : DifferentiableAt Real (fun b => M b h) beta)
    (hfieldLimit : DifferentiableAt Real (fun t => M beta t) h) :
    deriv (fun b => M b h) beta <=
      J * (M beta h * deriv (fun y => M beta y) h) := by
  have hepsilon : forall epsilon : Real, 0 < epsilon ->
      deriv (fun b => M b h) beta <=
        J * ((M beta h + epsilon) * deriv (fun y => M beta y) h) := by
    intro epsilon hepsilon
    let c : Real := J * (M beta h + epsilon)
    have hc : 0 <= c := mul_nonneg hJ (add_nonneg hM hepsilon.le)
    have hc1 : 0 < c + 1 := by linarith
    have hopen : {z : Real × Real |
        Function.uncurry M z < M beta h + epsilon} ∈ nhds (beta, h) :=
      hcont (Iio_mem_nhds (lt_add_of_pos_right _ hepsilon))
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hopen
    let d : Real := min (r / 2) (r / (2 * (c + 1)))
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (div_pos hr (by norm_num))
        (div_pos hr (mul_pos (by norm_num) hc1))
    have hdr : d <= r / 2 := min_le_left _ _
    have hdrc : d <= r / (2 * (c + 1)) := min_le_right _ _
    have hupper : M (beta + d) (h + c * d) < M beta h + epsilon := by
      change Function.uncurry M (beta + d, h + c * d) < M beta h + epsilon
      apply hrsub
      change dist ((beta + d, h + c * d) : Real × Real) (beta, h) < r
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have hbabs : |beta + d - beta| = d := by
        rw [add_sub_cancel_left, abs_of_pos hd]
      have hhabs : |h + c * d - h| = c * d := by
        rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg hc hd.le)]
      rw [hbabs, hhabs, max_lt_iff]
      constructor
      · linarith
      · have hcd : c * d <= c * (r / (2 * (c + 1))) :=
          mul_le_mul_of_nonneg_left hdrc hc
        have hfrac : c * (r / (2 * (c + 1))) < r := by
          rw [div_eq_mul_inv]
          have hratio : c / (c + 1) < 1 := by
            rw [div_lt_one hc1]
            linarith
          have hr2 : 0 < r / 2 := div_pos hr (by norm_num)
          calc
            c * (r * (2 * (c + 1))⁻¹) = (r / 2) * (c / (c + 1)) := by
              field_simp
            _ < (r / 2) * 1 := mul_lt_mul_of_pos_left hratio hr2
            _ < r := by linarith
        exact hcd.trans_lt hfrac
    have hendpoint : forall t, t ∈ Icc (0 : Real) d ->
        M (beta + t) h <= M beta (h + c * t) := by
      intro t ht
      have hbt : 0 <= beta + t := by linarith [hbeta, ht.1]
      have hct : 0 <= h + c * t := by nlinarith [hh.le, hc, ht.1]
      have hbd : 0 <= beta + d := by linarith [hbeta, hd]
      have hud : 0 <= h + c * d := by nlinarith [hh.le, hc, hd.le]
      let fn : Nat -> Real -> Real := fun n s =>
        Mn n (beta + s) (h + c * (t - s))
      have hline : forall n s,
          HasDerivAt (fn n)
            (deriv (fun b => Mn n b (h + c * (t - s))) (beta + s) -
              c * deriv (fun y => Mn n (beta + s) y) (h + c * (t - s))) s := by
        intro n s
        simpa [fn, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          mul_add, mul_sub] using
          (abtp_hasDerivAt_characteristic (Mn n) beta (h + c * t) c s
            (hjointFinite n (beta + s) (h + c * t - c * s)))
      have hbound : forall n s, s ∈ Icc (0 : Real) t ->
          Cn n (beta + s) (h + c * (t - s)) <= M beta h + epsilon := by
        intro n s hs
        have hbs : 0 <= beta + s := by linarith [hbeta, hs.1]
        have hfs : 0 <= h + c * (t - s) := by
          nlinarith [hh.le, hc, hs.2]
        have hfieldle : h + c * (t - s) <= h + c * d := by
          have hts : t - s <= d := by linarith [ht.2, hs.1]
          simpa [add_comm] using
            (add_le_add_left (mul_le_mul_of_nonneg_left hts hc) h)
        calc
          Cn n (beta + s) (h + c * (t - s)) <=
              Cn n (beta + d) (h + c * (t - s)) :=
            hmonoBeta n (h + c * (t - s)) hfs hbs hbd (by linarith [ht.2, hs.2])
          _ <= Cn n (beta + d) (h + c * d) :=
            hmonoField n (beta + d) hbd hfs hud hfieldle
          _ <= M (beta + d) (h + c * d) :=
            hle n (beta + d) (h + c * d) hbd hud
          _ <= M beta h + epsilon := hupper.le
      have hanti : forall n, AntitoneOn (fn n) (Icc (0 : Real) t) := by
        intro n
        apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
        · intro s hs
          exact (hline n s).continuousAt.continuousWithinAt
        · intro s hs
          exact (hline n s).differentiableAt.differentiableWithinAt
        · intro s hs
          rw [interior_Icc, mem_Ioo] at hs
          change deriv (fn n) s <= 0
          rw [(hline n s).deriv]
          let db := deriv (fun b => Mn n b (h + c * (t - s))) (beta + s)
          let dh := deriv (fun y => Mn n (beta + s) y) (h + c * (t - s))
          have hbs : 0 <= beta + s := by linarith [hbeta, hs.1]
          have hfs : 0 <= h + c * (t - s) := by
            nlinarith [hh.le, hc, hs.2]
          have hab : db <= J * (Cn n (beta + s) (h + c * (t - s)) * dh) :=
            hfinite n (beta + s) (h + c * (t - s)) hbs hfs
          have hdh : 0 <= dh := hfield n (beta + s) (h + c * (t - s)) hbs hfs
          have hcoef : J * Cn n (beta + s) (h + c * (t - s)) <= c := by
            dsimp [c]
            exact mul_le_mul_of_nonneg_left
              (hbound n s ⟨hs.1.le, hs.2.le⟩) hJ
          calc
            db - c * dh <=
                J * (Cn n (beta + s) (h + c * (t - s)) * dh) - c * dh :=
              sub_le_sub_right hab _
            _ = (J * Cn n (beta + s) (h + c * (t - s)) - c) * dh := by ring
            _ <= 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcoef) hdh
      apply le_of_tendsto_of_tendsto
        (hconv (beta + t) h hbt hh.le)
        (hconv beta (h + c * t) hbeta hct)
      exact Filter.Eventually.of_forall (fun n => by
        have hant := hanti n (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1) ht.1
        simpa [fn] using hant)
    have hquot : forall t, t ∈ Ioc (0 : Real) d ->
        (M (beta + t) h - M beta h) / t <=
          (M beta (h + c * t) - M beta h) / t := by
      intro t ht
      exact (div_le_div_iff_of_pos_right ht.1).2
        (sub_le_sub_right (hendpoint t ⟨ht.1.le, ht.2⟩) _)
    have hevent : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (M (beta + t) h - M beta h) / t <=
          (M beta (h + c * t) - M beta h) / t := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hd)] with t ht0 htd
      exact hquot t ⟨ht0, htd⟩
    have hbT : Tendsto
        (fun t => (M (beta + t) h - M beta h) / t)
        (nhdsWithin 0 (Ioi 0)) (nhds (deriv (fun b => M b h) beta)) := by
      simpa [div_eq_inv_mul, mul_comm] using
        hbetaLimit.hasDerivAt.tendsto_slope_zero_right
    have hinner : HasDerivAt (fun t : Real => h + c * t) c 0 := by
      convert (hasDerivAt_const (x := (0 : Real)) h).add
        ((hasDerivAt_id (0 : Real)).const_mul c) using 1 <;> ring
    have hcomp : HasDerivAt (fun t => M beta (h + c * t))
        (c * deriv (fun y => M beta y) h) 0 := by
      have hder := hfieldLimit.hasDerivAt.comp_of_eq 0 hinner (by ring)
      simpa [Function.comp_def, mul_comm] using hder
    have hhT : Tendsto
        (fun t => (M beta (h + c * t) - M beta h) / t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (c * deriv (fun y => M beta y) h)) := by
      simpa [div_eq_inv_mul, mul_comm] using hcomp.tendsto_slope_zero_right
    have hchar := le_of_tendsto_of_tendsto hbT hhT hevent
    dsimp [c] at hchar
    simpa [mul_assoc] using hchar
  let dh := deriv (fun y => M beta y) h
  by_cases hcoef : 0 < J * dh
  · apply le_of_forall_pos_le_add
    intro delta hdelta
    have he := hepsilon (delta / (J * dh)) (div_pos hdelta hcoef)
    have hprodne : J * dh ≠ 0 := hcoef.ne'
    have hJne : J ≠ 0 := fun hzero => hprodne (mul_eq_zero.mpr (Or.inl hzero))
    have hdhne : dh ≠ 0 := fun hzero => hprodne (mul_eq_zero.mpr (Or.inr hzero))
    calc
      deriv (fun b => M b h) beta <=
          J * ((M beta h + delta / (J * dh)) * dh) := he
      _ = J * (M beta h * dh) + delta := by
        field_simp [hJne, hdhne]
  · have he := hepsilon 1 zero_lt_one
    have hnonpos : J * dh <= 0 := le_of_not_gt hcoef
    calc
      deriv (fun b => M b h) beta <= J * ((M beta h + 1) * dh) := he
      _ <= J * (M beta h * dh) := by nlinarith




theorem abtp_inequality_at_of_fieldDifferentiable_physical_envelope
    (Mn Cn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real)
    (J beta h : Real)
    (hJ : 0 <= J) (hbeta : 0 <= beta) (hh : 0 < h) (hM : 0 <= M beta h)
    (hfinite : forall n b t, 0 <= b -> 0 <= t ->
      deriv (fun x => Mn n x t) b <=
        J * (Cn n b t * deriv (fun y => Mn n b y) t))
    (hfield : forall n b t, 0 <= b -> 0 <= t ->
      0 <= deriv (fun y => Mn n b y) t)
    (hmonoBeta : forall n t, 0 <= t ->
      MonotoneOn (fun b => Cn n b t) (Ici 0))
    (hmonoField : forall n b, 0 <= b ->
      MonotoneOn (fun t => Cn n b t) (Ici 0))
    (hle : forall n b t, 0 <= b -> 0 <= t -> Cn n b t <= M b t)
    (hconv : forall b t, 0 <= b -> 0 <= t ->
      Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
    (hcont : ContinuousAt (Function.uncurry M) (beta, h))
    (hjointFinite : forall n b t,
      DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
    (hfieldLimit : DifferentiableAt Real (fun t => M beta t) h)
    (hfieldNN : 0 <= deriv (fun t => M beta t) h) :
    deriv (fun b => M b h) beta <=
      J * (M beta h * deriv (fun y => M beta y) h) := by
  by_cases hb : DifferentiableAt Real (fun b => M b h) beta
  · exact abtp_inequality_at_of_partialDifferentiable_physical_envelope
      Mn Cn M J beta h hJ hbeta hh hM hfinite hfield hmonoBeta
      hmonoField hle hconv hcont hjointFinite hb hfieldLimit
  · rw [deriv_zero_of_not_differentiableAt hb]
    exact mul_nonneg hJ (mul_nonneg hM hfieldNN)




theorem abtp_inequality_at_of_jointDifferentiable_physical_envelope
    (Mn Cn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real)
    (J beta h : Real)
    (hJ : 0 <= J) (hbeta : 0 <= beta) (hh : 0 < h) (hM : 0 <= M beta h)
    (hfinite : forall n b t, 0 <= b -> 0 <= t ->
      deriv (fun x => Mn n x t) b <=
        J * (Cn n b t * deriv (fun y => Mn n b y) t))
    (hfield : forall n b t, 0 <= b -> 0 <= t ->
      0 <= deriv (fun y => Mn n b y) t)
    (hmonoBeta : forall n t, 0 <= t ->
      MonotoneOn (fun b => Cn n b t) (Ici 0))
    (hmonoField : forall n b, 0 <= b ->
      MonotoneOn (fun t => Cn n b t) (Ici 0))
    (hle : forall n b t, 0 <= b -> 0 <= t -> Cn n b t <= M b t)
    (hconv : forall b t, 0 <= b -> 0 <= t ->
      Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
    (hcontBeta : ContinuousAt (fun b => M b h) beta)
    (hjointFinite : forall n b t,
      DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
    (hjointLimit : DifferentiableAt Real (Function.uncurry M) (beta, h)) :
    deriv (fun b => M b h) beta <=
      J * (M beta h * deriv (fun y => M beta y) h) := by
  apply abtp_inequality_at_of_characteristics_physical Mn Cn M J beta h
    hJ hbeta hh hM hfinite hfield hmonoBeta hmonoField hle hconv hcontBeta
  · intro n c t
    exact abtp_hasDerivAt_characteristic (Mn n) beta h c t
      (hjointFinite n (beta + t) (h - c * t))
  · intro c
    simpa using abtp_hasDerivAt_characteristic M beta h c 0
      (by simpa using hjointLimit)




theorem abtp_inequality_at_of_jointDifferentiable_physical
    (Mn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real)
    (J beta h : Real)
    (hJ : 0 <= J) (hbeta : 0 <= beta) (hh : 0 < h) (hM : 0 <= M beta h)
    (hfinite : forall n b t, 0 <= b -> 0 <= t ->
      deriv (fun x => Mn n x t) b <=
        J * (Mn n b t * deriv (fun y => Mn n b y) t))
    (hfield : forall n b t, 0 <= b -> 0 <= t ->
      0 <= deriv (fun y => Mn n b y) t)
    (hmonoBeta : forall n t, 0 <= t ->
      MonotoneOn (fun b => Mn n b t) (Ici 0))
    (hmonoField : forall n b, 0 <= b ->
      MonotoneOn (fun t => Mn n b t) (Ici 0))
    (hle : forall n b t, 0 <= b -> 0 <= t -> Mn n b t <= M b t)
    (hconv : forall b t, 0 <= b -> 0 <= t ->
      Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
    (hcontBeta : ContinuousAt (fun b => M b h) beta)
    (hjointFinite : forall n b t,
      DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
    (hjointLimit : DifferentiableAt Real (Function.uncurry M) (beta, h)) :
    deriv (fun b => M b h) beta <=
      J * (M beta h * deriv (fun y => M beta y) h) := by
  exact abtp_inequality_at_of_jointDifferentiable_physical_envelope
    Mn Mn M J beta h hJ hbeta hh hM hfinite hfield hmonoBeta hmonoField
    hle hconv hcontBeta hjointFinite hjointLimit




theorem abtp_aizenmanBarskyPhysical_of_jointDifferentiable
    (Mn : Nat -> Real -> Real -> Real) (M : Real -> Real -> Real) (J : Real)
    (hJ : 0 <= J)
    (hM : forall beta h, 0 <= beta -> 0 < h -> 0 <= M beta h)
    (hfinite : forall n b t, 0 <= b -> 0 <= t ->
      deriv (fun x => Mn n x t) b <=
        J * (Mn n b t * deriv (fun y => Mn n b y) t))
    (hfield : forall n b t, 0 <= b -> 0 <= t ->
      0 <= deriv (fun y => Mn n b y) t)
    (hmonoBeta : forall n t, 0 <= t ->
      MonotoneOn (fun b => Mn n b t) (Ici 0))
    (hmonoField : forall n b, 0 <= b ->
      MonotoneOn (fun t => Mn n b t) (Ici 0))
    (hle : forall n b t, 0 <= b -> 0 <= t -> Mn n b t <= M b t)
    (hconv : forall b t, 0 <= b -> 0 <= t ->
      Tendsto (fun n => Mn n b t) atTop (nhds (M b t)))
    (hjointFinite : forall n b t,
      DifferentiableAt Real (Function.uncurry (Mn n)) (b, t))
    (hjointLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (Function.uncurry M) (beta, h)) :
    AizenmanBarskyInequalityPhysical M J := by
  intro beta hbeta h hh
  have hjoint := hjointLimit beta h hbeta hh
  have hline : ContinuousAt (fun b : Real => (b, h)) beta :=
    continuousAt_id.prodMk continuousAt_const
  have hcontBeta : ContinuousAt (fun b => M b h) beta := by
    simpa [Function.comp_def, Function.uncurry] using
      hjoint.continuousAt.comp (f := fun b : Real => (b, h)) hline
  exact abtp_inequality_at_of_jointDifferentiable_physical Mn M J beta h
    hJ hbeta hh (hM beta h hbeta hh) hfinite hfield hmonoBeta hmonoField
    hle hconv hcontBeta hjointFinite hjoint

end Sharpness
end StatMech
