/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedBoundaryDeckSupport








namespace StatMech.FrontierD

noncomputable section

private theorem fkRectEdgeCenter_intCast_four_mul_add_ne_four_mul
    {L : Nat} [NeZero L] (hL : (4 : Int) ∣ (L : Int))
    (x a k : Int) (hk : ¬ (4 : Int) ∣ k) :
    ((4 * x + k : Int) : ZMod L) ≠ ((4 * a : Int) : ZMod L) := by
  intro h
  have hd : (L : Int) ∣ (4 * a) - (4 * x + k) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ L).mp h
  obtain ⟨m, hm⟩ := hd
  obtain ⟨n, hn⟩ := hL
  apply hk
  refine ⟨a - x - n * m, ?_⟩
  rw [hn] at hm
  linarith



theorem fkRectRefinedPrimalEdgeCenter_eq_firstLift_normalForm
    (R : FKRectTorus) (e : R.EdgeIndex) :
    let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1
    fkRectRefinedPrimalEdgeCenter R e =
      if fkRectClosedPairingAtEdge e then
        (4 * p.1 - 2, 4 * p.2)
      else
        (4 * p.1, 4 * p.2 + 2) := by
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1
  let q := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2
  change fkRectRefinedPrimalEdgeCenter R e =
    if fkRectClosedPairingAtEdge e then
      (4 * p.1 - 2, 4 * p.2)
    else
      (4 * p.1, 4 * p.2 + 2)
  have hstep := fkRectCanonicalSquareEdgeStep_eq R e
  by_cases h : fkRectClosedPairingAtEdge e
  · simp only [h, if_true] at hstep ⊢
    unfold fkRectRefinedPrimalEdgeCenter
    have hx := congrArg Prod.fst hstep
    have hy := congrArg Prod.snd hstep
    change q.1 - p.1 = -1 at hx
    change q.2 - p.2 = 0 at hy
    change (2 * (p.1 + q.1), 2 * (p.2 + q.2)) = _
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · simp only [h, Bool.false_eq_true, if_false] at hstep ⊢
    unfold fkRectRefinedPrimalEdgeCenter
    have hx := congrArg Prod.fst hstep
    have hy := congrArg Prod.snd hstep
    change q.1 - p.1 = 0 at hx
    change q.2 - p.2 = 1 at hy
    change (2 * (p.1 + q.1), 2 * (p.2 + q.2)) = _
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega



theorem fkRectIndexedEdge_eq_of_closedPairing_eq_of_firstLift_eq
    (R : FKRectTorus) (e f : R.EdgeIndex)
    (hpair : fkRectClosedPairingAtEdge e =
      fkRectClosedPairingAtEdge f)
    (hfirst : fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1 =
      fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R f).1) :
    e = f := by
  rcases e with ⟨be, xe, ye⟩
  rcases f with ⟨bf, xf, yf⟩
  cases be <;> cases bf <;>
    by_cases he : Even ye.val <;> by_cases hf : Even yf.val
  all_goals
    simp [fkRectClosedPairingAtEdge, fkRectLiftedIndexedEdgeEnds,
      fkRectLiftedVertex, he, hf] at hpair hfirst ⊢
  all_goals try contradiction
  all_goals
    have hy : ye = yf := hfirst.2
    subst yf
  all_goals simp_all
  apply_fun finitePeriodicSucc R.width_pos at hfirst
  simpa only [finitePeriodicSucc_cyclicPred] using hfirst



theorem fkRectIndexedEdge_eq_of_refinedCenter_deck_mod_eq
    (R : FKRectTorus) (e f : R.EdgeIndex) (u : Int × Int)
    (hmod :
      let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
      let c := fkRectRefinedPrimalEdgeCenter R e
      let z := fkRectRefinedPrimalEdgeCenter R f
      let A := fkRectSquareDeckTranslation R u
      (((c.1 + 4 * A.1 : Int) : ZMod L),
          ((c.2 + 4 * A.2 : Int) : ZMod L)) =
        (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))) :
    e = f := by
  let N := fkRectSquareCoverSide R
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let pe := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1
  let pf := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R f).1
  let A := fkRectSquareDeckTranslation R u
  have hLN : (L : Int) = 4 * (N : Int) := by
    simp [L, N]
  have hLfour : (4 : Int) ∣ (L : Int) := ⟨N, by rw [hLN]⟩
  have he := fkRectRefinedPrimalEdgeCenter_eq_firstLift_normalForm R e
  have hf := fkRectRefinedPrimalEdgeCenter_eq_firstLift_normalForm R f
  dsimp only at hmod
  change
    ((((fkRectRefinedPrimalEdgeCenter R e).1 + 4 * A.1 : Int) : ZMod L),
      (((fkRectRefinedPrimalEdgeCenter R e).2 + 4 * A.2 : Int) : ZMod L)) =
    ((((fkRectRefinedPrimalEdgeCenter R f).1 : Int) : ZMod L),
      (((fkRectRefinedPrimalEdgeCenter R f).2 : Int) : ZMod L)) at hmod
  change fkRectRefinedPrimalEdgeCenter R e =
    (if fkRectClosedPairingAtEdge e then
      (4 * pe.1 - 2, 4 * pe.2) else (4 * pe.1, 4 * pe.2 + 2)) at he
  change fkRectRefinedPrimalEdgeCenter R f =
    (if fkRectClosedPairingAtEdge f then
      (4 * pf.1 - 2, 4 * pf.2) else (4 * pf.1, 4 * pf.2 + 2)) at hf
  have hpair : fkRectClosedPairingAtEdge e =
      fkRectClosedPairingAtEdge f := by
    by_cases hepair : fkRectClosedPairingAtEdge e <;>
      by_cases hfpair : fkRectClosedPairingAtEdge f
    · simp [hepair, hfpair]
    · have hx := congrArg Prod.fst hmod
      rw [he, hf] at hx
      simp only [hepair, hfpair, Bool.false_eq_true,
        if_true, if_false, Prod.fst] at hx
      have hx' :
          ((4 * (pe.1 + A.1) + (-2) : Int) : ZMod L) =
            ((4 * pf.1 : Int) : ZMod L) := by
        convert hx using 1 <;> ring
      exfalso
      exact fkRectEdgeCenter_intCast_four_mul_add_ne_four_mul hLfour
        (pe.1 + A.1) pf.1 (-2) (by norm_num) hx'
    · have hx := congrArg Prod.fst hmod
      rw [he, hf] at hx
      simp only [hepair, hfpair, Bool.false_eq_true,
        if_true, if_false, Prod.fst] at hx
      have hx' :
          ((4 * pf.1 + (-2) : Int) : ZMod L) =
            ((4 * (pe.1 + A.1) : Int) : ZMod L) := by
        convert hx.symm using 1 <;> ring
      exfalso
      exact fkRectEdgeCenter_intCast_four_mul_add_ne_four_mul hLfour
        pf.1 (pe.1 + A.1) (-2) (by norm_num)
        hx'
    · simp [hepair, hfpair]
  have hcoord (a b : Int)
      (h : ((4 * a : Int) : ZMod L) = ((4 * b : Int) : ZMod L)) :
      ((a : Int) : ZMod N) = ((b : Int) : ZMod N) := by
    have hd : (L : Int) ∣ 4 * b - 4 * a :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ L).mp h
    obtain ⟨m, hm⟩ := hd
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mpr
    refine ⟨m, ?_⟩
    rw [hLN] at hm
    linarith
  have hx : ((pe.1 + A.1 : Int) : ZMod N) =
      ((pf.1 : Int) : ZMod N) := by
    have hxL := congrArg Prod.fst hmod
    rw [he, hf] at hxL
    cases hp : fkRectClosedPairingAtEdge e
    · have hp' : fkRectClosedPairingAtEdge f = false := by simpa [hp] using hpair.symm
      simp only [hp, hp', Bool.false_eq_true, if_false, Prod.fst] at hxL
      apply hcoord
      convert hxL using 1 <;> ring
    · have hp' : fkRectClosedPairingAtEdge f = true := by simpa [hp] using hpair.symm
      simp only [hp, hp', Bool.false_eq_true, if_true, Prod.fst] at hxL
      push_cast at hxL
      apply hcoord
      push_cast
      linear_combination hxL
  have hy : ((pe.2 + A.2 : Int) : ZMod N) =
      ((pf.2 : Int) : ZMod N) := by
    have hyL := congrArg Prod.snd hmod
    rw [he, hf] at hyL
    cases hp : fkRectClosedPairingAtEdge e
    · have hp' : fkRectClosedPairingAtEdge f = false := by simpa [hp] using hpair.symm
      simp only [hp, hp', Bool.false_eq_true, if_false, Prod.snd] at hyL
      push_cast at hyL
      apply hcoord
      push_cast
      linear_combination hyL
    · have hp' : fkRectClosedPairingAtEdge f = true := by simpa [hp] using hpair.symm
      simp only [hp, hp', Bool.false_eq_true, if_true, Prod.snd] at hyL
      apply hcoord
      convert hyL using 1 <;> ring
  have hpoint : fkRectIntegralSquarePointMod N (pe + A) =
      fkRectIntegralSquarePointMod N pf := by
    apply Prod.ext
    · simpa [fkRectIntegralSquarePointMod] using hx
    · simpa [fkRectIntegralSquarePointMod] using hy
  have hfirst : fkRectLiftedVertex R
      (fkRectLiftedIndexedEdgeEnds R e).1 =
      fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R f).1 := by
    have hrep := fkRectSquareRepresentativeVertex_eq_of_pointMod_eq R hpoint
    change fkRectSquareRepresentativeVertex R (pe + A) =
      fkRectSquareRepresentativeVertex R pf at hrep
    rw [show A = fkRectSquareDeckTranslation R u by rfl,
      fkRectSquareRepresentativeVertex_add_deck,
      show pe = fkRectSquareDevelopPoint
          (fkRectLiftedIndexedEdgeEnds R e).1 by rfl,
      show pf = fkRectSquareDevelopPoint
          (fkRectLiftedIndexedEdgeEnds R f).1 by rfl,
      fkRectSquareRepresentativeVertex_developPoint,
      fkRectSquareRepresentativeVertex_developPoint] at hrep
    exact hrep
  exact fkRectIndexedEdge_eq_of_closedPairing_eq_of_firstLift_eq
    R e f hpair hfirst

end

end StatMech.FrontierD
