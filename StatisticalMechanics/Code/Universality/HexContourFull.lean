/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Code.Universality.HexFiniteRegion
import Code.Universality.HexContourDecomp
import Code.Universality.HexVertexClassification

namespace StatMech.Universality

open Complex Function HexWalk
open scoped BigOperators










theorem hxc_hexOmega_ne_zero : hexOmega ≠ 0 :=
  hexOmega_primRoot.ne_zero (by norm_num)

variable {a : ℂ} {h0 : ℤ} {v du : ℂ}



theorem hxc_paraf_support_subset_combined_p (R : HexFiniteRegion) (hdu : du ≠ 0) :
    Function.support (fun ts => parafSummand R.inRegion a h0 (v + du) (5/8) hexChi ts) ⊆
      Function.support (combinedSummand R.inRegion a h0 v du) := by
  intro ts hts
  simp only [Function.mem_support] at hts ⊢
  by_cases hend : (ofTurns a h0 ts).EndsAt (v + du)
  · rw [combinedSummand_at_p hdu hend]
    intro hz
    rcases mul_eq_zero.mp hz with h | h
    · exact hdu (by linear_combination h)
    · exact hts h
  · exact absurd (parafSummand_eq_zero_of_not_endsAt R.inRegion a h0 (v + du) _ _ ts hend) hts



theorem hxc_paraf_support_subset_combined_q (R : HexFiniteRegion) (hdu : du ≠ 0) :
    Function.support (fun ts => parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi ts) ⊆
      Function.support (combinedSummand R.inRegion a h0 v du) := by
  intro ts hts
  simp only [Function.mem_support] at hts ⊢
  by_cases hend : (ofTurns a h0 ts).EndsAt (v + hexOmega * du)
  · rw [combinedSummand_at_q hdu hend]
    intro hz
    rcases mul_eq_zero.mp hz with h | h
    · have hmul : hexOmega * du = 0 := by linear_combination h
      rcases mul_eq_zero.mp hmul with h1 | h1
      · exact hxc_hexOmega_ne_zero h1
      · exact hdu h1
    · exact hts h
  · exact absurd
      (parafSummand_eq_zero_of_not_endsAt R.inRegion a h0 (v + hexOmega * du) _ _ ts hend) hts



theorem hxc_paraf_support_subset_combined_r (R : HexFiniteRegion) (hdu : du ≠ 0) :
    Function.support
        (fun ts => parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) ⊆
      Function.support (combinedSummand R.inRegion a h0 v du) := by
  intro ts hts
  simp only [Function.mem_support] at hts ⊢
  by_cases hend : (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du)
  · rw [combinedSummand_at_r hdu hend]
    intro hz
    rcases mul_eq_zero.mp hz with h | h
    · have hmul : hexOmega ^ 2 * du = 0 := by linear_combination h
      rcases mul_eq_zero.mp hmul with h1 | h1
      · exact pow_ne_zero 2 hxc_hexOmega_ne_zero h1
      · exact hdu h1
    · exact hts h
  · exact absurd
      (parafSummand_eq_zero_of_not_endsAt R.inRegion a h0 (v + hexOmega ^ 2 * du) _ _ ts hend) hts













theorem hxc_paraf_summable_p (R : HexFiniteRegion) (hdu : du ≠ 0) :
    Summable fun ts => parafSummand R.inRegion a h0 (v + du) (5/8) hexChi ts :=
  summable_of_hasFiniteSupport
    (Set.Finite.subset (R.support_finite (a := a) (h0 := h0) (v := v) (du := du) hdu)
      (hxc_paraf_support_subset_combined_p R hdu))


theorem hxc_paraf_summable_q (R : HexFiniteRegion) (hdu : du ≠ 0) :
    Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi ts :=
  summable_of_hasFiniteSupport
    (Set.Finite.subset (R.support_finite (a := a) (h0 := h0) (v := v) (du := du) hdu)
      (hxc_paraf_support_subset_combined_q R hdu))


theorem hxc_paraf_summable_r (R : HexFiniteRegion) (hdu : du ≠ 0) :
    Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts :=
  summable_of_hasFiniteSupport
    (Set.Finite.subset (R.support_finite (a := a) (h0 := h0) (v := v) (du := du) hdu)
      (hxc_paraf_support_subset_combined_r R hdu))













theorem hxc_combinedSummand_tsum_eq_finset (R : HexFiniteRegion) (hdu : du ≠ 0) :
    ∑' ts, combinedSummand R.inRegion a h0 v du ts
      = ∑ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
          combinedSummand R.inRegion a h0 v du ts := by
  rw [tsum_eq_sum (s := R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu)]
  intro ts hts
  by_contra hne
  exact hts ((R.mem_supportFinset hdu ts).mpr hne)








theorem hxc_vertexSum_eq_finset_sum (R : HexFiniteRegion) (hdu : du ≠ 0) :
    ((v + du) - v) * parafObservable R.inRegion a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
      = ∑ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
          combinedSummand R.inRegion a h0 v du ts := by
  rw [vertexSum_eq_tsum_combinedSummand R.inRegion a h0 v du
        (hxc_paraf_summable_p R hdu) (hxc_paraf_summable_q R hdu) (hxc_paraf_summable_r R hdu)]
  exact hxc_combinedSummand_tsum_eq_finset R hdu












theorem hxc_vertex_relation_finite (R : HexFiniteRegion)
    (C : HexSawClassification R.inRegion a h0 v du) (hdu : du ≠ 0) :
    ((v + du) - v) * parafObservable R.inRegion a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  hexClass_vertex_relation C hdu
    (hxc_paraf_summable_p R hdu) (hxc_paraf_summable_q R hdu) (hxc_paraf_summable_r R hdu)






theorem hxc_finset_sum_eq_zero (R : HexFiniteRegion)
    (C : HexSawClassification R.inRegion a h0 v du) (hdu : du ≠ 0) :
    ∑ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
        combinedSummand R.inRegion a h0 v du ts = 0 := by
  rw [← hxc_vertexSum_eq_finset_sum R hdu]
  exact hxc_vertex_relation_finite R C hdu




















theorem hxc_paraf_support_finite (R : HexFiniteRegion) (z : ℂ) (σ x : ℝ) :
    (Function.support (fun ts => parafSummand R.inRegion a h0 z σ x ts)).Finite := by
  apply Set.Finite.subset (hexFinite_boundedLegal_finite R.verts.card)
  intro ts hts
  simp only [Function.mem_support] at hts
  have hguard : (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn R.inRegion
      ∧ (ofTurns a h0 ts).EndsAt z := by
    by_contra hcon
    apply hts
    unfold parafSummand
    rw [if_neg hcon]
  obtain ⟨⟨hturns, hsaw⟩, hstay, _⟩ := hguard
  exact ⟨fun t ht => hturns t ht, le_of_lt (R.length_lt a h0 ts hsaw hstay)⟩






theorem hxc_paraf_observable_eq_finset_sum (R : HexFiniteRegion) (z : ℂ) (σ x : ℝ) :
    parafObservable R.inRegion a h0 z σ x
      = ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0) z σ x).toFinset,
          parafSummand R.inRegion a h0 z σ x ts := by
  unfold parafObservable
  rw [tsum_eq_sum (s := (hxc_paraf_support_finite R (a := a) (h0 := h0) z σ x).toFinset)]
  intro ts hts
  by_contra hne
  exact hts ((hxc_paraf_support_finite R (a := a) (h0 := h0) z σ x).mem_toFinset.mpr hne)

variable {V : Type*} [DecidableEq V]







theorem hxc_familyFSum_finite (R : HexFiniteRegion) (D : HexDomain V) (s : HexSide D)
    (hObs : ∀ z, D.obs z = parafObservable R.inRegion a h0 z (5/8) hexChi) :
    s.fSum = ∑ e ∈ s.cells,
      ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
            (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
        parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts := by
  unfold HexSide.fSum
  apply Finset.sum_congr rfl
  intro e _
  rw [hObs (D.mid e.vtx e.edge)]
  exact hxc_paraf_observable_eq_finset_sum R (D.mid e.vtx e.edge) (5/8) hexChi


















theorem hxc_boundarySum_assignment (R : HexFiniteRegion) (D : HexDomain V)
    (P : D.InteriorPairing) (B : HexBoundaryDecomp D P)
    (hObs : ∀ z, D.obs z = parafObservable R.inRegion a h0 z (5/8) hexChi) :
    D.boundarySum P
      = B.A.dir * (∑ e ∈ B.A.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
              (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
            parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts)
        + B.L.dir * (∑ e ∈ B.L.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
              (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
            parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts)
        + B.Tp.dir * (∑ e ∈ B.Tp.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
              (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
            parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts)
        + B.Tm.dir * (∑ e ∈ B.Tm.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
              (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
            parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts)
        + B.U.dir * (∑ e ∈ B.U.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
              (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
            parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts) := by
  rw [B.boundarySum_eq_sum_sides]
  rw [B.A.incSum_eq_dir_mul_fSum, B.L.incSum_eq_dir_mul_fSum,
      B.Tp.incSum_eq_dir_mul_fSum, B.Tm.incSum_eq_dir_mul_fSum, B.U.incSum_eq_dir_mul_fSum]
  rw [hxc_familyFSum_finite R D B.A hObs, hxc_familyFSum_finite R D B.L hObs,
      hxc_familyFSum_finite R D B.Tp hObs, hxc_familyFSum_finite R D B.Tm hObs,
      hxc_familyFSum_finite R D B.U hObs]








theorem hxc_finite_enum_eq_contour_proj (R : HexFiniteRegion) (D : HexDomain V)
    (P : D.InteriorPairing) (B : HexBoundaryDecomp D P)
    (hObs : ∀ z, D.obs z = parafObservable R.inRegion a h0 z (5/8) hexChi) :
    B.A.dir * (∑ e ∈ B.A.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
            (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
          parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts)
        + B.L.dir * (∑ e ∈ B.L.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
              (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
            parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts)
        + B.Tp.dir * (∑ e ∈ B.Tp.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
              (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
            parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts)
        + B.Tm.dir * (∑ e ∈ B.Tm.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
              (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
            parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts)
        + B.U.dir * (∑ e ∈ B.U.cells, ∑ ts ∈ (hxc_paraf_support_finite R (a := a) (h0 := h0)
              (D.mid e.vtx e.edge) (5/8) hexChi).toFinset,
            parafSummand R.inRegion a h0 (D.mid e.vtx e.edge) (5/8) hexChi ts)
      = Complex.I * (((hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups : ℝ)
          - (B.Fa : ℝ)) : ℂ) := by
  rw [← hxc_boundarySum_assignment R D P B hObs]
  exact B.boundarySum_eq
















theorem hxc_boundary_identity_finite (R : HexFiniteRegion) (D : HexDomain V)
    (P : D.InteriorPairing) (hsub : P.interior ⊆ D.incidences)
    (B : HexBoundaryDecomp D P)
    (hObs : ∀ z, D.obs z = parafObservable R.inRegion a h0 z (5/8) hexChi)
    (hFa : B.Fa = 1) :
    hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups = 1 := by
  refine hexBoundary_of_decomp B.lam (B.taup + B.taum) B.ups B.Fa
    (D.boundarySum P) (D.hexBoundaryRaw P hsub) hFa ?_
  rw [hxc_boundarySum_assignment R D P B hObs]
  exact hxc_finite_enum_eq_contour_proj R D P B hObs

end StatMech.Universality
