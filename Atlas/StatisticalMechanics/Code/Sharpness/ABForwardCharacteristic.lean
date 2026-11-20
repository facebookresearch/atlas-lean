/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.ABLatticeUnconditional

open Filter Set Topology

namespace StatMech
namespace Sharpness



theorem abfc_forward_characteristic_physical_envelope
    (Mn Cn : Nat → Real → Real → Real) (M : Real → Real → Real)
    (J beta h : Real)
    (hJ : 0 ≤ J) (hbeta : 0 ≤ beta) (hh : 0 < h) (hM : 0 ≤ M beta h)
    (hfinite : ∀ n b t, 0 ≤ b → 0 ≤ t →
      deriv (fun x ↦ Mn n x t) b ≤
        J * (Cn n b t * deriv (fun y ↦ Mn n b y) t))
    (hfield : ∀ n b t, 0 ≤ b → 0 ≤ t →
      0 ≤ deriv (fun y ↦ Mn n b y) t)
    (hmonoBeta : ∀ n t, 0 ≤ t →
      MonotoneOn (fun b ↦ Cn n b t) (Ici 0))
    (hmonoField : ∀ n b, 0 ≤ b →
      MonotoneOn (fun t ↦ Cn n b t) (Ici 0))
    (hle : ∀ n b t, 0 ≤ b → 0 ≤ t → Cn n b t ≤ M b t)
    (hconv : ∀ b t, 0 ≤ b → 0 ≤ t →
      Tendsto (fun n ↦ Mn n b t) atTop (nhds (M b t)))
    (hcont : ContinuousAt (Function.uncurry M) (beta, h))
    (hjointFinite : ∀ n b t,
      DifferentiableAt Real (Function.uncurry (Mn n)) (b, t)) :
    ∀ epsilon, 0 < epsilon → ∃ d > 0, ∀ t ∈ Icc (0 : Real) d,
      M (beta + t) h ≤
        M beta (h + (J * (M beta h + epsilon)) * t) := by
  intro epsilon hepsilon
  let c : Real := J * (M beta h + epsilon)
  have hc : 0 ≤ c := mul_nonneg hJ (add_nonneg hM hepsilon.le)
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
  refine ⟨d, hd, ?_⟩
  have hdr : d ≤ r / 2 := min_le_left _ _
  have hdrc : d ≤ r / (2 * (c + 1)) := min_le_right _ _
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
    · have hcd : c * d ≤ c * (r / (2 * (c + 1))) :=
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
  intro t ht
  have hbt : 0 ≤ beta + t := by linarith [hbeta, ht.1]
  have hct : 0 ≤ h + c * t := by nlinarith [hh.le, hc, ht.1]
  have hbd : 0 ≤ beta + d := by linarith [hbeta, hd]
  have hud : 0 ≤ h + c * d := by nlinarith [hh.le, hc, hd.le]
  let fn : Nat → Real → Real := fun n s ↦
    Mn n (beta + s) (h + c * (t - s))
  have hline : ∀ n s,
      HasDerivAt (fn n)
        (deriv (fun b ↦ Mn n b (h + c * (t - s))) (beta + s) -
          c * deriv (fun y ↦ Mn n (beta + s) y) (h + c * (t - s))) s := by
    intro n s
    simpa [fn, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      mul_add, mul_sub] using
      (abtp_hasDerivAt_characteristic (Mn n) beta (h + c * t) c s
        (hjointFinite n (beta + s) (h + c * t - c * s)))
  have hbound : ∀ n s, s ∈ Icc (0 : Real) t →
      Cn n (beta + s) (h + c * (t - s)) ≤ M beta h + epsilon := by
    intro n s hs
    have hbs : 0 ≤ beta + s := by linarith [hbeta, hs.1]
    have hfs : 0 ≤ h + c * (t - s) := by
      nlinarith [hh.le, hc, hs.2]
    have hfieldle : h + c * (t - s) ≤ h + c * d := by
      have hts : t - s ≤ d := by linarith [ht.2, hs.1]
      simpa [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_left hts hc) h)
    calc
      Cn n (beta + s) (h + c * (t - s)) ≤
          Cn n (beta + d) (h + c * (t - s)) :=
        hmonoBeta n (h + c * (t - s)) hfs hbs hbd
          (by linarith [ht.2, hs.2])
      _ ≤ Cn n (beta + d) (h + c * d) :=
        hmonoField n (beta + d) hbd hfs hud hfieldle
      _ ≤ M (beta + d) (h + c * d) :=
        hle n (beta + d) (h + c * d) hbd hud
      _ ≤ M beta h + epsilon := hupper.le
  have hanti : ∀ n, AntitoneOn (fn n) (Icc (0 : Real) t) := by
    intro n
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
    · intro s hs
      exact (hline n s).continuousAt.continuousWithinAt
    · intro s hs
      exact (hline n s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc, mem_Ioo] at hs
      change deriv (fn n) s ≤ 0
      rw [(hline n s).deriv]
      let db := deriv (fun b ↦ Mn n b (h + c * (t - s))) (beta + s)
      let dh := deriv (fun y ↦ Mn n (beta + s) y) (h + c * (t - s))
      have hbs : 0 ≤ beta + s := by linarith [hbeta, hs.1]
      have hfs : 0 ≤ h + c * (t - s) := by
        nlinarith [hh.le, hc, hs.2]
      have hab : db ≤ J * (Cn n (beta + s) (h + c * (t - s)) * dh) :=
        hfinite n (beta + s) (h + c * (t - s)) hbs hfs
      have hdh : 0 ≤ dh := hfield n (beta + s) (h + c * (t - s)) hbs hfs
      have hcoef : J * Cn n (beta + s) (h + c * (t - s)) ≤ c := by
        dsimp [c]
        exact mul_le_mul_of_nonneg_left
          (hbound n s ⟨hs.1.le, hs.2.le⟩) hJ
      calc
        db - c * dh ≤
            J * (Cn n (beta + s) (h + c * (t - s)) * dh) - c * dh :=
          sub_le_sub_right hab _
        _ = (J * Cn n (beta + s) (h + c * (t - s)) - c) * dh := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcoef) hdh
  apply le_of_tendsto_of_tendsto
    (hconv (beta + t) h hbt hh.le)
    (hconv beta (h + c * t) hbeta hct)
  exact Filter.Eventually.of_forall (fun n ↦ by
    have hant := hanti n (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1) ht.1
    simpa [fn, c] using hant)



theorem abfc_abig_forward_characteristic_of_exhaustion
    {V : Type*} [Countable V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V → Real) (o : V) (J0 beta h : Real)
    (hJ0 : 0 ≤ J0) (hbeta : 0 ≤ beta) (hh : 0 < h)
    (hJ : ∀ e, 0 ≤ J e)
    (hJsupport : ∀ x y, ¬ G.Adj x y → J s(x, y) = 0)
    (S : Nat → Finset V) (ho : ∀ n, o ∈ S n)
    (hrow : ∀ n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x ≤ J0)
    (hInfiniteTarget : ∀ b t, 0 ≤ b → 0 ≤ t →
      ∀ n (x : S n), abigMag G J (x : V) b t ≤ abigMag G J o b t)
    (hmonoWindow : Monotone (fun n ↦ abigGhostWindow (S n)))
    (hcover : ∀ F : Finset (Option V), ∃ n, F ⊆ abigGhostWindow (S n)) :
    ∀ epsilon, 0 < epsilon → ∃ d > 0, ∀ t ∈ Icc (0 : Real) d,
      abigMag G J o (beta + t) h ≤
        abigMag G J o beta
          (h + (J0 * (abigMag G J o beta h + epsilon)) * t) := by
  let Mn : Nat → Real → Real → Real := fun n b t ↦
    abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
      ⟨o, ho n⟩ b t
  let Cn : Nat → Real → Real → Real := fun n b t ↦
    abigWindowEnvelope G J (S n) ⟨o, ho n⟩ b t
  apply abfc_forward_characteristic_physical_envelope Mn Cn
    (abigMag G J o) J0 beta h hJ0 hbeta hh
    (abigMag_nonneg G J o beta h)
  · intro n b t hb ht
    simpa [Mn, Cn, mul_assoc] using
      (abig_window_aizenmanBarsky_finiteEnvelope
        G J (S n) ⟨o, ho n⟩ b t J0 hb ht hJ (hrow n))
  · intro n b t hb ht
    apply abfa_deriv_field_nonneg
      (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
        ⟨o, ho n⟩ b t
    · intro e he
      induction e using Sym2.inductionOn with
      | _ x y => simpa using hJ s((x : V), (y : V))
    · exact hb
    · exact ht
  · intro n t ht
    exact abigWindowEnvelope_monotoneOn_beta
      G J (S n) ⟨o, ho n⟩ t hJ ht
  · intro n b hb
    exact abigWindowEnvelope_monotoneOn_field
      G J (S n) ⟨o, ho n⟩ b hJ hb
  · intro n b t hb ht
    exact abigWindowEnvelope_le_mag G J (S n) ⟨o, ho n⟩ b t
      hb ht hJ hJsupport (hInfiniteTarget b t hb ht n)
  · intro b t hb ht
    exact abig_tendsto_abfaMag_exhaustion G J o b t hb ht hJ hJsupport
      S ho hmonoWindow hcover
  · exact abigMag_continuousAt_joint_of_exhaustion
      G J o J0 beta h hJ0 hbeta hh hJ hJsupport S ho hrow
        hInfiniteTarget hmonoWindow hcover
  · intro n b t
    exact abfa_differentiableAt_mag_joint
      (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
        ⟨o, ho n⟩ b t

end Sharpness
end StatMech
