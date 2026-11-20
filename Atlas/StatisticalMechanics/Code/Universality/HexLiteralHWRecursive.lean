/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















import Code.Universality.HexLiteralHWContent
import Code.Universality.HexW2Summable
import Code.Universality.HexReturnUniqueness

namespace StatMech.Universality

open HexWalk
open scoped BigOperators





def hlhr_signed (up : Bool) (x : ℝ) : ℝ :=
  if up then x else -x


def HLHRIsExtremum (f : ℕ → ℝ) (up : Bool) (lo hi k : ℕ) : Prop :=
  lo ≤ k ∧ k ≤ hi ∧
    ∀ j, lo ≤ j → j ≤ hi → hlhr_signed up (f j) ≤ hlhr_signed up (f k)


theorem hlhr_exists_extremum (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlo : lo ≤ hi) : ∃ k, HLHRIsExtremum f up lo hi k := by
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image
    (Finset.Icc lo hi) (fun k => hlhr_signed up (f k))
    ⟨lo, Finset.mem_Icc.mpr ⟨le_rfl, hlo⟩⟩
  refine ⟨c, (Finset.mem_Icc.mp hc).1, (Finset.mem_Icc.mp hc).2, ?_⟩
  intro j hjlo hjhi
  exact hmax j (Finset.mem_Icc.mpr ⟨hjlo, hjhi⟩)




noncomputable def hlhr_lastExtremum (f : ℕ → ℝ) (up : Bool)
    (lo hi : ℕ) : ℕ := by
  classical
  exact if h : lo ≤ hi then
    Nat.findGreatest (HLHRIsExtremum f up lo hi) hi
  else lo


theorem hlhr_lastExtremum_spec (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlo : lo ≤ hi) :
    HLHRIsExtremum f up lo hi (hlhr_lastExtremum f up lo hi) := by
  classical
  unfold hlhr_lastExtremum
  rw [dif_pos hlo]
  obtain ⟨k, hk⟩ := hlhr_exists_extremum f up hlo
  exact Nat.findGreatest_spec hk.2.1 hk

theorem hlhr_lastExtremum_lo_le (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlo : lo ≤ hi) : lo ≤ hlhr_lastExtremum f up lo hi :=
  (hlhr_lastExtremum_spec f up hlo).1

theorem hlhr_lastExtremum_le_hi (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlo : lo ≤ hi) : hlhr_lastExtremum f up lo hi ≤ hi :=
  (hlhr_lastExtremum_spec f up hlo).2.1


theorem hlhr_lastExtremum_is_last (f : ℕ → ℝ) (up : Bool)
    {lo hi j : ℕ} (hlo : lo ≤ hi)
    (hj : hlhr_lastExtremum f up lo hi < j) (hjhi : j ≤ hi) :
    ¬ HLHRIsExtremum f up lo hi j := by
  classical
  unfold hlhr_lastExtremum at hj
  rw [dif_pos hlo] at hj
  exact Nat.findGreatest_is_greatest hj hjhi





noncomputable def hlhr_cut (f : ℕ → ℝ) (up : Bool) (lo hi : ℕ) : ℕ :=
  let k := hlhr_lastExtremum f up lo hi
  if lo < k then k else hi

theorem hlhr_cut_gt (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (h : lo < hi) : lo < hlhr_cut f up lo hi := by
  classical
  simp only [hlhr_cut]
  split_ifs with hk
  · exact hk
  · exact h

theorem hlhr_cut_le (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (h : lo ≤ hi) : hlhr_cut f up lo hi ≤ hi := by
  classical
  simp only [hlhr_cut]
  split_ifs
  · exact hlhr_lastExtremum_le_hi f up h
  · exact le_rfl



@[simp] theorem hlhr_signed_not (up : Bool) (x : ℝ) :
    hlhr_signed (!up) x = -hlhr_signed up x := by
  cases up <;> simp [hlhr_signed]





def HLHRAhead (f : ℕ → ℝ) (up : Bool) (lo hi : ℕ) : Prop :=
  ∀ j, lo < j → j ≤ hi →
    hlhr_signed up (f lo) < hlhr_signed up (f j)



theorem hlhr_lastExtremum_gt (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    lo < hlhr_lastExtremum f up lo hi := by
  let k := hlhr_lastExtremum f up lo hi
  have hspec := hlhr_lastExtremum_spec f up (le_of_lt hlt)
  have hj := hahead (lo + 1) (by omega) (by omega)
  have hjmax := hspec.2.2 (lo + 1) (by omega) (by omega)
  by_contra hnot
  have hklo := hspec.1
  have hk : hlhr_lastExtremum f up lo hi = lo := by omega
  rw [hk] at hjmax
  linarith



theorem hlhr_cut_eq_lastExtremum (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    hlhr_cut f up lo hi = hlhr_lastExtremum f up lo hi := by
  have hk := hlhr_lastExtremum_gt f up hlt hahead
  simp [hlhr_cut, hk]


theorem hlhr_lastExtremum_strict_after (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) {j : ℕ}
    (hj : hlhr_lastExtremum f up lo hi < j) (hjhi : j ≤ hi) :
    hlhr_signed up (f j) <
      hlhr_signed up (f (hlhr_lastExtremum f up lo hi)) := by
  let k := hlhr_lastExtremum f up lo hi
  have hspec := hlhr_lastExtremum_spec f up (le_of_lt hlt)
  have hjlo : lo ≤ j := by
    have hklo := hlhr_lastExtremum_lo_le f up (le_of_lt hlt)
    omega
  have hle := hspec.2.2 j hjlo hjhi
  apply lt_of_le_of_ne hle
  intro heq
  have hjext : HLHRIsExtremum f up lo hi j := by
    refine ⟨hjlo, hjhi, ?_⟩
    intro m hmlo hmhi
    have hm := hspec.2.2 m hmlo hmhi
    linarith
  exact (hlhr_lastExtremum_is_last f up (le_of_lt hlt) hj hjhi) hjext



theorem hlhr_ahead_next (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) :
    HLHRAhead f (!up) (hlhr_lastExtremum f up lo hi) hi := by
  intro j hj hjhi
  rw [hlhr_signed_not, hlhr_signed_not]
  have hs := hlhr_lastExtremum_strict_after f up hlt hj hjhi
  linarith


noncomputable def hlhr_orientedSpan (f : ℕ → ℝ) (up : Bool)
    (lo hi : ℕ) : ℝ :=
  hlhr_signed up (f hi) - hlhr_signed up (f lo)


theorem hlhr_orientedSpan_pos (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    0 < hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi) := by
  unfold hlhr_orientedSpan
  exact sub_pos.mpr (hahead _ (hlhr_lastExtremum_gt f up hlt hahead)
    (hlhr_lastExtremum_le_hi f up (le_of_lt hlt)))






theorem hlhr_orientedSpan_next_lt (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi)
    (hk : hlhr_lastExtremum f up lo hi < hi) :
    hlhr_orientedSpan f (!up) (hlhr_lastExtremum f up lo hi)
        (hlhr_lastExtremum f (!up) (hlhr_lastExtremum f up lo hi) hi)
      < hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi) := by
  let k := hlhr_lastExtremum f up lo hi
  let l := hlhr_lastExtremum f (!up) k hi
  have hnext := hlhr_ahead_next f up hlt
  have hkl : k < l := hlhr_lastExtremum_gt f (!up) hk hnext
  have hklo : lo < k := by
    dsimp [k]
    exact hlhr_lastExtremum_gt f up hlt hahead
  have hlo_l : lo < l := lt_trans hklo hkl
  have hlhi : l ≤ hi := hlhr_lastExtremum_le_hi f (!up) (le_of_lt hk)
  have hold := hahead l hlo_l hlhi
  unfold hlhr_orientedSpan
  rw [hlhr_signed_not, hlhr_signed_not]
  dsimp [k, l] at hold ⊢
  linarith




noncomputable def hlhr_intervalsAux (f : ℕ → ℝ) (hi : ℕ) :
    ℕ → Bool → ℕ → List (ℕ × ℕ)
  | 0, _, _ => []
  | fuel + 1, up, lo =>
      if lo < hi then
        let k := hlhr_lastExtremum f up lo hi
        (lo, k) :: hlhr_intervalsAux f hi fuel (!up) k
      else []


noncomputable def hlhr_intervalSpan (f : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  |f p.2 - f p.1|

noncomputable def hlhr_intervalSpans (f : ℕ → ℝ) (ps : List (ℕ × ℕ)) :
    List ℝ :=
  ps.map (hlhr_intervalSpan f)



theorem hlhr_intervalSpan_eq_oriented (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    hlhr_intervalSpan f (lo, hlhr_lastExtremum f up lo hi) =
      hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi) := by
  have hpos := hlhr_orientedSpan_pos f up hlt hahead
  cases up with
  | false =>
      simp only [hlhr_intervalSpan, hlhr_orientedSpan, hlhr_signed,
        Bool.false_eq_true, ↓reduceIte] at hpos ⊢
      rw [abs_of_neg (by linarith)]
      ring
  | true =>
      simp only [hlhr_intervalSpan, hlhr_orientedSpan, hlhr_signed,
        ↓reduceIte] at hpos ⊢
      exact abs_of_pos hpos






theorem hlhr_intervalSpans_ordered (f : ℕ → ℝ) (hi fuel lo : ℕ) (up : Bool)
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    let ws := hlhr_intervalSpans f (hlhr_intervalsAux f hi fuel up lo)
    ws.Pairwise (· > ·) ∧
      (∀ w ∈ ws, 0 < w) ∧
      (∀ w ∈ ws,
        w ≤ hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi)) := by
  induction fuel generalizing up lo with
  | zero =>
      simp [hlhr_intervalsAux, hlhr_intervalSpans]
  | succ fuel ih =>
      let k := hlhr_lastExtremum f up lo hi
      have hklo : lo < k := by
        dsimp [k]
        exact hlhr_lastExtremum_gt f up hlt hahead
      have hkhi : k ≤ hi := by
        dsimp [k]
        exact hlhr_lastExtremum_le_hi f up (le_of_lt hlt)
      have hfirst : hlhr_intervalSpan f (lo, k) =
          hlhr_orientedSpan f up lo k := by
        dsimp [k]
        exact hlhr_intervalSpan_eq_oriented f up hlt hahead
      have hfirstPos : 0 < hlhr_intervalSpan f (lo, k) := by
        rw [hfirst]
        dsimp [k]
        exact hlhr_orientedSpan_pos f up hlt hahead
      simp only [hlhr_intervalsAux, hlt, ↓reduceIte, hlhr_intervalSpans,
        List.map_cons]
      let tail := hlhr_intervalSpans f
        (hlhr_intervalsAux f hi fuel (!up) k)
      change
        (hlhr_intervalSpan f (lo, k) :: tail).Pairwise (· > ·) ∧
          (∀ w ∈ hlhr_intervalSpan f (lo, k) :: tail, 0 < w) ∧
          (∀ w ∈ hlhr_intervalSpan f (lo, k) :: tail,
            w ≤ hlhr_orientedSpan f up lo k)
      by_cases hk : k < hi
      · have hnext : HLHRAhead f (!up) k hi := by
          dsimp [k]
          exact hlhr_ahead_next f up hlt
        have htail := ih k (!up) hk hnext
        have hnextLt :
            hlhr_orientedSpan f (!up) k
                (hlhr_lastExtremum f (!up) k hi) <
              hlhr_intervalSpan f (lo, k) := by
          rw [hfirst]
          dsimp [k]
          exact hlhr_orientedSpan_next_lt f up hlt hahead hk
        rcases htail with ⟨htailPair, htailPos, htailBound⟩
        refine ⟨List.pairwise_cons.mpr ⟨?_, htailPair⟩, ?_, ?_⟩
        · intro w hw
          exact lt_of_le_of_lt (htailBound w hw) hnextLt
        · intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact hfirstPos
          · exact htailPos w hw
        · intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact le_of_eq hfirst
          · exact le_trans (htailBound w hw)
              (le_trans (le_of_lt hnextLt) (le_of_eq hfirst))
      · have hkeq : k = hi := by omega
        have htailNil : hlhr_intervalsAux f hi fuel (!up) hi = [] := by
          cases fuel <;> simp [hlhr_intervalsAux]
        have htail : tail = [] := by
          simp [tail, hkeq, htailNil, hlhr_intervalSpans]
        rw [htail]
        simp only [List.pairwise_singleton, List.mem_singleton, forall_eq]
        exact ⟨trivial, hfirstPos, le_of_eq hfirst⟩




def hlhr_intervalContent (ts : List ℤ) (p : ℕ × ℕ) : List ℤ :=
  (ts.drop p.1).take (p.2 - p.1)


def hlhr_intervalTurns (ts : List ℤ) (ps : List (ℕ × ℕ)) : List ℤ :=
  (ps.map (hlhr_intervalContent ts)).flatten




theorem hlhr_intervalsAux_reconstruct (f : ℕ → ℝ) (root : List ℤ)
    (fuel lo : ℕ) (up : Bool) (hlo : lo ≤ root.length)
    (hfuel : root.length - lo ≤ fuel)
    (hahead : lo < root.length → HLHRAhead f up lo root.length) :
    hlhr_intervalTurns root
        (hlhr_intervalsAux f root.length fuel up lo) = root.drop lo := by
  induction fuel generalizing up lo with
  | zero =>
      have heq : lo = root.length := by omega
      subst lo
      simp [hlhr_intervalsAux, hlhr_intervalTurns]
  | succ fuel ih =>
      by_cases hlt : lo < root.length
      · let k := hlhr_lastExtremum f up lo root.length
        have ha := hahead hlt
        have hklo : lo < k := by
          dsimp [k]
          exact hlhr_lastExtremum_gt f up hlt ha
        have hkhi : k ≤ root.length := by
          dsimp [k]
          exact hlhr_lastExtremum_le_hi f up (le_of_lt hlt)
        have hfuel' : root.length - k ≤ fuel := by omega
        have hnext : HLHRAhead f (!up) k root.length := by
          dsimp [k]
          exact hlhr_ahead_next f up hlt
        have hrec := ih k (!up) hkhi hfuel' (fun _ => hnext)
        simp only [hlhr_intervalsAux, hlt, ↓reduceIte, hlhr_intervalTurns,
          List.map_cons, List.flatten_cons]
        change hlhr_intervalContent root (lo, k) ++
            hlhr_intervalTurns root
              (hlhr_intervalsAux f root.length fuel (!up) k) = root.drop lo
        rw [hrec]
        unfold hlhr_intervalContent
        have hdrop : root.drop k = (root.drop lo).drop (k - lo) := by
          rw [List.drop_drop]
          congr 1
          omega
        rw [hdrop]
        exact List.take_append_drop (k - lo) (root.drop lo)
      · have heq : lo = root.length := by omega
        subst lo
        simp [hlhr_intervalsAux, hlhr_intervalTurns]


theorem hlhr_intervalsAux_bounds (f : ℕ → ℝ) (hi fuel lo : ℕ) (up : Bool)
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    ∀ p ∈ hlhr_intervalsAux f hi fuel up lo,
      lo ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ hi := by
  induction fuel generalizing up lo with
  | zero => simp [hlhr_intervalsAux]
  | succ fuel ih =>
      intro p hp
      let k := hlhr_lastExtremum f up lo hi
      have hklo : lo < k := by
        dsimp [k]
        exact hlhr_lastExtremum_gt f up hlt hahead
      have hkhi : k ≤ hi := by
        dsimp [k]
        exact hlhr_lastExtremum_le_hi f up (le_of_lt hlt)
      have hnext : HLHRAhead f (!up) k hi := by
        dsimp [k]
        exact hlhr_ahead_next f up hlt
      simp only [hlhr_intervalsAux, hlt, ↓reduceIte, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨le_rfl, hklo, hkhi⟩
      · by_cases hk : k < hi
        · obtain ⟨hkp, hp12, hp2hi⟩ := ih k (!up) hk hnext p hp
          exact ⟨le_trans (le_of_lt hklo) hkp, hp12, hp2hi⟩
        · have hkeq : k = hi := by omega
          have htailNil : hlhr_intervalsAux f hi fuel (!up) k = [] := by
            rw [hkeq]
            cases fuel <;> simp [hlhr_intervalsAux]
          rw [htailNil] at hp
          simp at hp



noncomputable def hlhr_height (h0 : ℤ) (ts : List ℤ) (k : ℕ) : ℝ :=
  hexW2_partialDisp h0 ts k



def HLHRLiteralHalfSpace (h0 : ℤ) (ts : List ℤ) : Prop :=
  ∀ k, 0 < k → k ≤ ts.length → hlhr_height h0 ts 0 < hlhr_height h0 ts k


theorem hlhr_literalHalfSpace_ahead (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) :
    HLHRAhead (hlhr_height h0 ts) true 0 ts.length := by
  intro k hk hklen
  simpa [hlhr_signed] using hhalf k hk hklen


noncomputable def hlhr_literalIntervals (h0 : ℤ) (ts : List ℤ) :
    List (ℕ × ℕ) :=
  hlhr_intervalsAux (hlhr_height h0 ts) ts.length ts.length true 0


noncomputable def hlhr_literalSpans (h0 : ℤ) (ts : List ℤ) : List ℝ :=
  hlhr_intervalSpans (hlhr_height h0 ts) (hlhr_literalIntervals h0 ts)



theorem hlhr_literalIntervals_reconstruct (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) :
    hlhr_intervalTurns ts (hlhr_literalIntervals h0 ts) = ts := by
  by_cases hempty : ts = []
  · simp [hempty, hlhr_literalIntervals, hlhr_intervalsAux, hlhr_intervalTurns]
  · apply hlhr_intervalsAux_reconstruct (hlhr_height h0 ts) ts ts.length 0 true
      (by omega) (by omega)
    intro _
    exact hlhr_literalHalfSpace_ahead h0 ts hhalf


theorem hlhr_literalSpans_pairwise (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) :
    (hlhr_literalSpans h0 ts).Pairwise (· > ·) := by
  by_cases hempty : ts = []
  · simp [hempty, hlhr_literalSpans, hlhr_literalIntervals,
      hlhr_intervalsAux, hlhr_intervalSpans]
  · have hlen : 0 < ts.length := List.length_pos_iff.mpr hempty
    exact (hlhr_intervalSpans_ordered (hlhr_height h0 ts) ts.length
      ts.length 0 true hlen (hlhr_literalHalfSpace_ahead h0 ts hhalf)).1


theorem hlhr_literalSpans_pos (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) :
    ∀ w ∈ hlhr_literalSpans h0 ts, 0 < w := by
  by_cases hempty : ts = []
  · simp [hempty, hlhr_literalSpans, hlhr_literalIntervals,
      hlhr_intervalsAux, hlhr_intervalSpans]
  · have hlen : 0 < ts.length := List.length_pos_iff.mpr hempty
    exact (hlhr_intervalSpans_ordered (hlhr_height h0 ts) ts.length
      ts.length 0 true hlen (hlhr_literalHalfSpace_ahead h0 ts hhalf)).2.1





abbrev HLHRPiece := ℕ × List ℤ





noncomputable def hlhr_piecesAux (f : ℕ → ℝ) (hi : ℕ) :
    ℕ → Bool → ℕ → List ℤ → List HLHRPiece
  | 0, _, lo, ts => if ts = [] then [] else [(lo, ts)]
  | fuel + 1, up, lo, ts =>
      if hts : ts = [] then []
      else
        let k := hlhr_cut f up lo hi
        let d := k - lo
        (lo, ts.take d) :: hlhr_piecesAux f hi fuel (!up) k (ts.drop d)


noncomputable def hlhr_pieces (f : ℕ → ℝ) (ts : List ℤ) :
    List HLHRPiece :=
  hlhr_piecesAux f ts.length ts.length true 0 ts


def hlhr_pieceTurns (ps : List HLHRPiece) : List ℤ :=
  (ps.map Prod.snd).flatten


theorem hlhr_piecesAux_reconstruct (f : ℕ → ℝ) (hi fuel lo : ℕ) (up : Bool)
    (ts : List ℤ) :
    hlhr_pieceTurns (hlhr_piecesAux f hi fuel up lo ts) = ts := by
  induction fuel generalizing up lo ts with
  | zero =>
      by_cases hts : ts = []
      · simp [hlhr_piecesAux, hlhr_pieceTurns, hts]
      · simp [hlhr_piecesAux, hlhr_pieceTurns, hts]
  | succ fuel ih =>
      classical
      by_cases hts : ts = []
      · simp [hlhr_piecesAux, hlhr_pieceTurns, hts]
      · simp only [hlhr_piecesAux, hts, ↓reduceDIte, hlhr_pieceTurns,
          List.map_cons, List.flatten_cons]
        change ts.take (hlhr_cut f up lo hi - lo) ++
            hlhr_pieceTurns
              (hlhr_piecesAux f hi fuel (!up) (hlhr_cut f up lo hi)
                (ts.drop (hlhr_cut f up lo hi - lo))) = ts
        rw [ih]
        exact List.take_append_drop _ _


theorem hlhr_pieces_reconstruct (f : ℕ → ℝ) (ts : List ℤ) :
    hlhr_pieceTurns (hlhr_pieces f ts) = ts := by
  unfold hlhr_pieces
  exact hlhr_piecesAux_reconstruct f ts.length ts.length 0 true ts



theorem hlhr_piecesAux_slice (f : ℕ → ℝ) (root : List ℤ) (fuel : ℕ)
    (up : Bool) (lo : ℕ) (hlo : lo ≤ root.length) :
    ∀ p ∈ hlhr_piecesAux f root.length fuel up lo (root.drop lo),
      p.2 = (root.drop p.1).take p.2.length ∧
        p.1 + p.2.length ≤ root.length := by
  induction fuel generalizing up lo with
  | zero =>
      intro p hp
      by_cases hempty : root.drop lo = []
      · simp [hlhr_piecesAux, hempty] at hp
      · simp only [hlhr_piecesAux, hempty, ↓reduceIte, List.mem_singleton] at hp
        rcases hp with rfl
        constructor
        · simp
        · simp [List.length_drop, hlo]
  | succ fuel ih =>
      intro p hp
      by_cases hempty : root.drop lo = []
      · simp [hlhr_piecesAux, hempty] at hp
      · have hlt : lo < root.length := by
          rw [List.drop_eq_nil_iff] at hempty
          omega
        let k := hlhr_cut f up lo root.length
        let d := k - lo
        have hlok : lo < k := by
          dsimp [k]
          exact hlhr_cut_gt f up hlt
        have hkhi : k ≤ root.length := by
          dsimp [k]
          exact hlhr_cut_le f up (le_of_lt hlt)
        have hdpos : 0 < d := by dsimp [d]; omega
        have hdle : d ≤ (root.drop lo).length := by
          simp only [List.length_drop]
          dsimp [d]
          omega
        simp only [hlhr_piecesAux, hempty, ↓reduceDIte, List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp with rfl
          have hdirect : hlhr_cut f up lo root.length - lo ≤
              (root.drop lo).length := by
            simpa [k, d] using hdle
          constructor
          · simp only
            rw [List.length_take_of_le hdirect]
          · simp only
            rw [List.length_take_of_le hdirect]
            omega
        · have hdrop : (root.drop lo).drop d = root.drop k := by
            rw [List.drop_drop]
            congr 1
            dsimp [d]
            omega
          rw [hdrop] at hp
          exact ih (!up) k hkhi p hp


theorem hlhr_pieces_slice (f : ℕ → ℝ) (root : List ℤ) :
    ∀ p ∈ hlhr_pieces f root,
      p.2 = (root.drop p.1).take p.2.length ∧
        p.1 + p.2.length ≤ root.length := by
  unfold hlhr_pieces
  exact hlhr_piecesAux_slice f root root.length true 0 (by omega)


theorem hlhr_piecesAux_content_ne (f : ℕ → ℝ) (root : List ℤ) (fuel : ℕ)
    (up : Bool) (lo : ℕ) (hlo : lo ≤ root.length) :
    ∀ p ∈ hlhr_piecesAux f root.length fuel up lo (root.drop lo), p.2 ≠ [] := by
  induction fuel generalizing up lo with
  | zero =>
      intro p hp
      by_cases hempty : root.drop lo = []
      · simp [hlhr_piecesAux, hempty] at hp
      · simp only [hlhr_piecesAux, hempty, ↓reduceIte, List.mem_singleton] at hp
        simpa [hp] using hempty
  | succ fuel ih =>
      intro p hp
      by_cases hempty : root.drop lo = []
      · simp [hlhr_piecesAux, hempty] at hp
      · have hlt : lo < root.length := by
          rw [List.drop_eq_nil_iff] at hempty
          omega
        let k := hlhr_cut f up lo root.length
        let d := k - lo
        have hlok : lo < k := by
          dsimp [k]
          exact hlhr_cut_gt f up hlt
        have hkhi : k ≤ root.length := by
          dsimp [k]
          exact hlhr_cut_le f up (le_of_lt hlt)
        have hdpos : 0 < d := by dsimp [d]; omega
        have hdle : d ≤ (root.drop lo).length := by
          simp only [List.length_drop]
          dsimp [d]
          omega
        simp only [hlhr_piecesAux, hempty, ↓reduceDIte, List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp with rfl
          intro hnil
          have hlen := congrArg List.length hnil
          rw [List.length_take_of_le hdle] at hlen
          simp only [List.length_nil] at hlen
          omega
        · have hdrop : (root.drop lo).drop d = root.drop k := by
            rw [List.drop_drop]
            congr 1
            dsimp [d]
            omega
          rw [hdrop] at hp
          exact ih (!up) k hkhi p hp


theorem hlhr_pieces_content_ne (f : ℕ → ℝ) (root : List ℤ) :
    ∀ p ∈ hlhr_pieces f root, p.2 ≠ [] := by
  unfold hlhr_pieces
  exact hlhr_piecesAux_content_ne f root root.length true 0 (by omega)






noncomputable def hlhr_pieceSpan (f : ℕ → ℝ) (p : HLHRPiece) : ℝ :=
  |f (p.1 + p.2.length) - f p.1|


noncomputable def hlhr_pieceMid (a : ℂ) (h0 : ℤ) (ts : List ℤ) (lo : ℕ) : ℂ :=
  hexDropMid a h0 ts lo


def hlhr_pieceHead (h0 : ℤ) (ts : List ℤ) (lo : ℕ) : ℤ :=
  h0 + (ts.take lo).sum



theorem hlhr_slice_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW) {lo len : ℕ}
    (hbound : lo + len ≤ ts.length) :
    (ofTurns (hlhr_pieceMid a h0 ts lo) (hlhr_pieceHead h0 ts lo)
      ((ts.drop lo).take len)).IsLegalSAW := by
  have hlo : lo ≤ ts.length := by omega
  have hsuf := hexCut_legal_drop a h0 ts lo hlo hleg
  apply hexCut_legal_take _ _ (ts.drop lo) len hsuf



theorem hlhr_slice_legal_rebase (a a' : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW) {lo len : ℕ}
    (hbound : lo + len ≤ ts.length) :
    (ofTurns a' (hlhr_pieceHead h0 ts lo) ((ts.drop lo).take len)).IsLegalSAW := by
  have hs := hlhr_slice_legal a h0 ts hleg hbound
  have ht := hexW2S_isLegalSAW_translate
    (a' - hlhr_pieceMid a h0 ts lo) (hlhr_pieceMid a h0 ts lo)
    (hlhr_pieceHead h0 ts lo) ((ts.drop lo).take len)
  rw [add_sub_cancel] at ht
  exact ht.mpr hs





theorem hlhr_literalInterval_bounds (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) :
    ∀ p ∈ hlhr_literalIntervals h0 ts,
      p.1 < p.2 ∧ p.2 ≤ ts.length := by
  intro p hp
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhr_literalIntervals, hempty, hlhr_intervalsAux] at hp
  have hlen : 0 < ts.length := List.length_pos_iff.mpr hne
  have hb := hlhr_intervalsAux_bounds (hlhr_height h0 ts) ts.length
    ts.length 0 true hlen (hlhr_literalHalfSpace_ahead h0 ts hhalf) p hp
  exact ⟨hb.2.1, hb.2.2⟩



theorem hlhr_literalInterval_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace h0 ts) {p : ℕ × ℕ}
    (hp : p ∈ hlhr_literalIntervals h0 ts) :
    (ofTurns (hlhr_pieceMid a h0 ts p.1) (hlhr_pieceHead h0 ts p.1)
      (hlhr_intervalContent ts p)).IsLegalSAW := by
  obtain ⟨hp12, hp2len⟩ := hlhr_literalInterval_bounds h0 ts hhalf p hp
  unfold hlhr_intervalContent
  apply hlhr_slice_legal a h0 ts hleg
  omega



theorem hlhr_literalInterval_legal_rebase (a a' : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace h0 ts) {p : ℕ × ℕ}
    (hp : p ∈ hlhr_literalIntervals h0 ts) :
    (ofTurns a' (hlhr_pieceHead h0 ts p.1)
      (hlhr_intervalContent ts p)).IsLegalSAW := by
  obtain ⟨hp12, hp2len⟩ := hlhr_literalInterval_bounds h0 ts hhalf p hp
  unfold hlhr_intervalContent
  apply hlhr_slice_legal_rebase a a' h0 ts hleg
  omega




theorem hlhr_literalInterval_reflected_legal (a a' : ℂ) (h0 : ℤ)
    (ts : List ℤ) (hleg : (ofTurns a h0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace h0 ts) {p : ℕ × ℕ}
    (hp : p ∈ hlhr_literalIntervals h0 ts) :
    (ofTurns a' (hlhr_pieceHead h0 ts p.1)
      (hsc_negTurns (hlhr_intervalContent ts p))).IsLegalSAW := by
  have hs := hlhr_literalInterval_legal_rebase a a' h0 ts hleg hhalf hp
  exact ⟨hsc_genLegalTurns a' (hlhr_pieceHead h0 ts p.1)
      (hlhr_intervalContent ts p) hs.1,
    hsc_genIsSAW a' (hlhr_pieceHead h0 ts p.1)
      (hlhr_intervalContent ts p) hs.2⟩


def hlhr_intervalWeight (x : ℝ) (ts : List ℤ) (p : ℕ × ℕ) : ℝ :=
  x ^ (hlhr_intervalContent ts p).length

theorem hlhr_intervalWeight_eq_pow_turns (x : ℝ) (ts : List ℤ)
    (ps : List (ℕ × ℕ)) :
    (ps.map (hlhr_intervalWeight x ts)).prod =
      x ^ (hlhr_intervalTurns ts ps).length := by
  induction ps with
  | nil => simp [hlhr_intervalTurns]
  | cons p ps ih =>
      simp only [hlhr_intervalWeight, hlhr_intervalTurns, List.map_cons,
        List.prod_cons, List.flatten_cons, List.length_append, pow_add]
      rw [ih]
      rfl


theorem hlhr_literalInterval_weight_factor (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) (x : ℝ) :
    ((hlhr_literalIntervals h0 ts).map (hlhr_intervalWeight x ts)).prod =
      x ^ ts.length := by
  rw [hlhr_intervalWeight_eq_pow_turns,
    hlhr_literalIntervals_reconstruct h0 ts hhalf]






structure HLHRCoordRun where
  pos : HexReturnCoord
  dir : HexReturnCoord

def hlhr_coordRun : HexReturnCoord → HexReturnCoord → List ℤ → HLHRCoordRun
  | p, d, [] => ⟨p, d⟩
  | p, d, t :: ts =>
      let e := d.turn t
      hlhr_coordRun (p.add e) e ts



theorem hlhr_coordRun_geometry (p d : HexReturnCoord) (m s : ℂ)
    (h : ℤ) (ts : List ℤ)
    (hdir : halfStep h = d.value * s)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    let r := hlhr_coordRun p d ts
    hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) =
        m + halfStep h + 2 * ((r.pos.value - p.value) * s) ∧
      halfStep (hexInfra_headAccum h ts) = r.dir.value * s := by
  induction ts generalizing p d m h with
  | nil =>
      constructor
      · simp [hlhr_coordRun]
      · simpa [hlhr_coordRun] using hdir
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : halfStep (h + t) = e.value * s :=
        hexReturn_halfStep_turn s h d t hdir ht
      have hrec := ih (p.add e) e
        (m + halfStep h + halfStep (h + t)) (h + t) he htail
      simp only [hlhr_coordRun, hexInfra_midAccum_cons,
        hexInfra_headAccum_cons]
      simp only [HexReturnCoord.value_add] at hrec
      constructor
      · rw [hrec.1, he]
        ring
      · exact hrec.2


theorem hlhr_halfStep_zero_re : (halfStep 0).re = Real.sqrt 3 / 4 := by
  rw [hexWall3_halfStep_re]
  rw [show Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 by norm_num,
    Real.cos_pi_div_six]
  ring


theorem hlhr_halfStep_two_re : (halfStep 2).re = -(Real.sqrt 3 / 4) := by
  rw [hexWall3_halfStep_re]
  rw [show Real.pi / 6 + ((2 : ℤ) : ℝ) * (Real.pi / 3) = 5 * Real.pi / 6 by
      push_cast; ring,
    show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_six]
  ring



def hlhr_latticeHeight (ts : List ℤ) (k : ℕ) : ℤ :=
  let p := (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
    (ts.take k)).pos
  p.x - p.y



theorem hlhr_eisenstein_horizontal (d : HexReturnCoord) :
    (2 * (d.value * halfStep 0)).re =
      (Real.sqrt 3 / 2) * (d.x - d.y) := by
  rw [show d.value * halfStep 0 =
      (d.x : ℂ) * halfStep 0 + (d.y : ℂ) * (hexOmega * halfStep 0) by
    simp [HexReturnCoord.value]
    ring]
  rw [← hexConcrete_halfStep_add2 0]
  norm_num [Complex.mul_re, Complex.add_re,
    hlhr_halfStep_zero_re, hlhr_halfStep_two_re]
  ring




theorem hlhr_height_eq_latticeHeight (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (k : ℕ) :
    hlhr_height 0 ts k = Real.sqrt 3 / 4 +
      (Real.sqrt 3 / 2) * hlhr_latticeHeight ts k := by
  have htake : ∀ t ∈ ts.take k, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)
  have hbase : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have hgeom := (hlhr_coordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base 0 (halfStep 0) 0 (ts.take k) hbase htake).1
  have hlast := hexInfra_ofTurns_last_re (0 : ℂ) 0 (ts.take k)
  rw [hgeom] at hlast
  rw [hlhr_height, hexW2_partialDisp]
  have hlast' : hexInfra_stepReSum 0 (ts.take k) +
      (halfStep (hexInfra_headAccum 0 (ts.take k))).re =
      (0 + halfStep 0 +
        2 * (((hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
          (ts.take k)).pos.value - HexReturnCoord.zero.value) * halfStep 0)).re := by
    simpa using hlast.symm
  rw [hlast']
  simp only [HexReturnCoord.value_zero, sub_zero, Complex.add_re,
    zero_add]
  rw [hlhr_halfStep_zero_re,
    hlhr_eisenstein_horizontal]
  simp [hlhr_latticeHeight]


def hlhr_latticeDelta (ts : List ℤ) (p : ℕ × ℕ) : ℤ :=
  hlhr_latticeHeight ts p.2 - hlhr_latticeHeight ts p.1




def hlhr_latticeWidth (ts : List ℤ) (p : ℕ × ℕ) : ℕ :=
  (hlhr_latticeDelta ts p).natAbs

theorem hlhr_natAbs_cast (z : ℤ) : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
  cases z with
  | ofNat n => simp
  | negSucc n =>
      rw [Int.natAbs_negSucc, Int.cast_negSucc, abs_neg,
        abs_of_nonneg (by positivity)]



theorem hlhr_intervalSpan_eq_latticeWidth (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (p : ℕ × ℕ) :
    hlhr_intervalSpan (hlhr_height 0 ts) p =
      (Real.sqrt 3 / 2) * hlhr_latticeWidth ts p := by
  rw [hlhr_intervalSpan, hlhr_height_eq_latticeHeight ts hlegal p.2,
    hlhr_height_eq_latticeHeight ts hlegal p.1]
  have hs : 0 < Real.sqrt 3 / 2 := by positivity
  rw [show Real.sqrt 3 / 4 + Real.sqrt 3 / 2 * (hlhr_latticeHeight ts p.2 : ℝ) -
      (Real.sqrt 3 / 4 + Real.sqrt 3 / 2 * (hlhr_latticeHeight ts p.1 : ℝ)) =
      (Real.sqrt 3 / 2) * (hlhr_latticeDelta ts p : ℝ) by
    unfold hlhr_latticeDelta
    push_cast
    ring]
  rw [abs_mul, abs_of_pos hs]
  rw [← hlhr_natAbs_cast (hlhr_latticeDelta ts p)]
  rfl


theorem hlhr_latticeWidth_pos_of_span_pos (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (p : ℕ × ℕ)
    (hspan : 0 < hlhr_intervalSpan (hlhr_height 0 ts) p) :
    0 < hlhr_latticeWidth ts p := by
  rw [hlhr_intervalSpan_eq_latticeWidth ts hlegal p] at hspan
  have hs : 0 < Real.sqrt 3 / 2 := by positivity
  have hw : (0 : ℝ) < (hlhr_latticeWidth ts p : ℝ) := by
    rcases mul_pos_iff.mp hspan with h | h
    · exact h.2
    · exact (not_lt_of_ge (le_of_lt hs) h.1).elim
  exact_mod_cast hw



theorem hlhr_latticeWidth_gt_of_span_gt (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (p q : ℕ × ℕ)
    (hspan : hlhr_intervalSpan (hlhr_height 0 ts) p >
      hlhr_intervalSpan (hlhr_height 0 ts) q) :
    hlhr_latticeWidth ts p > hlhr_latticeWidth ts q := by
  rw [hlhr_intervalSpan_eq_latticeWidth ts hlegal p,
    hlhr_intervalSpan_eq_latticeWidth ts hlegal q] at hspan
  have hs : 0 < Real.sqrt 3 / 2 := by positivity
  have hw : (hlhr_latticeWidth ts q : ℝ) <
      (hlhr_latticeWidth ts p : ℝ) :=
    lt_of_mul_lt_mul_left hspan (le_of_lt hs)
  exact_mod_cast hw


noncomputable def hlhr_literalWidths (ts : List ℤ) : List ℕ :=
  (hlhr_literalIntervals 0 ts).map (hlhr_latticeWidth ts)


theorem hlhr_literalWidths_pos (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    ∀ T ∈ hlhr_literalWidths ts, 0 < T := by
  intro T hT
  simp only [hlhr_literalWidths, List.mem_map] at hT
  obtain ⟨p, hp, rfl⟩ := hT
  apply hlhr_latticeWidth_pos_of_span_pos ts hleg.1 p
  exact hlhr_literalSpans_pos 0 ts hhalf
    (hlhr_intervalSpan (hlhr_height 0 ts) p) (by
      simpa [hlhr_literalSpans, hlhr_intervalSpans] using
        List.mem_map_of_mem hp)




theorem hlhr_literalWidths_pairwise (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    (hlhr_literalWidths ts).Pairwise (· > ·) := by
  have hreal := hlhr_literalSpans_pairwise 0 ts hhalf
  have hintervals : (hlhr_literalIntervals 0 ts).Pairwise
      (fun p q => hlhr_intervalSpan (hlhr_height 0 ts) p >
        hlhr_intervalSpan (hlhr_height 0 ts) q) := by
    unfold hlhr_literalSpans hlhr_intervalSpans at hreal
    exact List.pairwise_map.mp hreal
  unfold hlhr_literalWidths
  rw [List.pairwise_map]
  exact hintervals.imp (fun hpq =>
    hlhr_latticeWidth_gt_of_span_gt ts hleg.1 _ _ hpq)





noncomputable def hlhr_literalBridge (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts)
    (p : {p // p ∈ hlhr_literalIntervals 0 ts}) : HexBridge where
  width := hlhr_latticeWidth ts p.1
  width_pos := by
    apply hlhr_latticeWidth_pos_of_span_pos ts hleg.1 p.1
    exact hlhr_literalSpans_pos 0 ts hhalf
      (hlhr_intervalSpan (hlhr_height 0 ts) p.1) (by
        simpa [hlhr_literalSpans, hlhr_intervalSpans] using
          List.mem_map_of_mem p.2)
  content := hlhr_intervalContent ts p.1
  content_ne := by
    obtain ⟨hp12, hp2len⟩ :=
      hlhr_literalInterval_bounds 0 ts hhalf p.1 p.2
    unfold hlhr_intervalContent
    have hdle : p.1.2 - p.1.1 ≤ (ts.drop p.1.1).length := by
      simp only [List.length_drop]
      omega
    intro hnil
    have hlen := congrArg List.length hnil
    rw [List.length_take_of_le hdle] at hlen
    simp only [List.length_nil] at hlen
    omega

@[simp] theorem hlhr_literalBridge_width (ts : List ℤ) (hleg hhalf) (p) :
    (hlhr_literalBridge ts hleg hhalf p).width = hlhr_latticeWidth ts p.1 := rfl

@[simp] theorem hlhr_literalBridge_content (ts : List ℤ) (hleg hhalf) (p) :
    (hlhr_literalBridge ts hleg hhalf p).content =
      hlhr_intervalContent ts p.1 := rfl



noncomputable def hlhr_literalBridgeList (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) : List HexBridge :=
  (hlhr_literalIntervals 0 ts).attach.map
    (hlhr_literalBridge ts hleg hhalf)

theorem hlhr_literalBridgeList_contents (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    ((hlhr_literalBridgeList ts hleg hhalf).map HexBridge.content).flatten = ts := by
  have hr := hlhr_literalIntervals_reconstruct 0 ts hhalf
  unfold hlhr_literalBridgeList
  simpa [hlhr_intervalTurns] using hr

theorem hlhr_literalBridgeList_widths (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    (hlhr_literalBridgeList ts hleg hhalf).map HexBridge.width =
      hlhr_literalWidths ts := by
  unfold hlhr_literalBridgeList hlhr_literalWidths
  simp


theorem hlhr_literalBridgeList_strict (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    StrictDecreasingWidths (hlhr_literalBridgeList ts hleg hhalf) := by
  unfold StrictDecreasingWidths
  have hw := hlhr_literalWidths_pairwise ts hleg hhalf
  rw [← hlhr_literalBridgeList_widths ts hleg hhalf] at hw
  simpa [List.pairwise_map] using hw



noncomputable def hlhr_contentHalf (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) : HexHWContentHalf :=
  ⟨hlhr_literalBridgeList ts hleg hhalf,
    hlhr_literalBridgeList_strict ts hleg hhalf⟩


@[simp] theorem hlhr_contentHalf_turns (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    hhc_halfTurns (hlhr_contentHalf ts hleg hhalf) = ts := by
  exact hlhr_literalBridgeList_contents ts hleg hhalf











structure HLHRTwoHalfSpaceSplit (a : ℂ) (h0 : ℤ) (ts : List ℤ) where
  lower : List ℤ
  upper : List ℤ
  lowerHead : ℤ
  upperHead : ℤ
  reconstruct : ts = lower ++ upper
  lower_halfSpace : HLHRLiteralHalfSpace lowerHead lower
  upper_halfSpace : HLHRLiteralHalfSpace upperHead upper










structure HLHRTruncatedTwoHalfData (a : ℂ) (h0 : ℤ) (N : ℕ) where
  lower : hhc_Dn a h0 N → List ℤ
  upper : hhc_Dn a h0 N → List ℤ
  reconstruct : ∀ d, d.1 = lower d ++ upper d
  lower_legal : ∀ d, (ofTurns 0 0 (lower d)).IsLegalSAW
  upper_legal : ∀ d, (ofTurns 0 0 (upper d)).IsLegalSAW
  lower_halfSpace : ∀ d, HLHRLiteralHalfSpace 0 (lower d)
  upper_halfSpace : ∀ d, HLHRLiteralHalfSpace 0 (upper d)




theorem hlhr_singleLeft_legal :
    (ofTurns 0 0 [(1 : ℤ)]).IsLegalSAW := by
  have hr := hexW1Exit_singleRight_legal (0 : ℂ) 0
  refine ⟨?_, ?_⟩
  · simpa [hsc_negTurns] using
      hsc_genLegalTurns 0 0 [(-1 : ℤ)] hr.1
  · simpa [hsc_negTurns] using
      hsc_genIsSAW 0 0 [(-1 : ℤ)] hr.2




theorem hlhr_singleLeft_not_halfSpace :
    ¬ HLHRLiteralHalfSpace 0 [(1 : ℤ)] := by
  intro h
  have hk := h 1 (by omega) (by simp)
  have hone : (halfStep 1).re = 0 := by
    rw [hexWall3_halfStep_re]
    rw [show Real.pi / 6 + ((1 : ℤ) : ℝ) * (Real.pi / 3) =
        Real.pi / 2 by push_cast; ring,
      Real.cos_pi_div_two]
    ring
  norm_num [hlhr_height, hexW2_partialDisp, hexInfra_stepReSum,
    hexInfra_headAccum, hlhr_halfStep_zero_re, hone] at hk

private theorem hlhr_append_eq_singleLeft (lower upper : List ℤ)
    (h : [(1 : ℤ)] = lower ++ upper) :
    lower = [] ∧ upper = [1] ∨ lower = [1] ∧ upper = [] := by
  have hlen := congrArg List.length h
  simp only [List.length_singleton, List.length_append] at hlen
  cases lower with
  | nil =>
      left
      simp_all
  | cons l lower =>
      right
      simp only [List.length_cons] at hlen
      have hu : upper = [] := List.length_eq_zero_iff.mp (by omega)
      subst upper
      simp only [List.append_nil] at h
      exact ⟨h.symm, rfl⟩



theorem hlhr_no_unaugmented_split_singleLeft :
    ¬ ∃ lower upper : List ℤ,
      [(1 : ℤ)] = lower ++ upper ∧
      HLHRLiteralHalfSpace 0 lower ∧
        HLHRLiteralHalfSpace 0 upper := by
  rintro ⟨lower, upper, hrec, hlo, hup⟩
  rcases hlhr_append_eq_singleLeft lower upper hrec with h | h
  · exact hlhr_singleLeft_not_halfSpace (h.2 ▸ hup)
  · exact hlhr_singleLeft_not_halfSpace (h.1 ▸ hlo)


noncomputable def hlhr_singleLeft_Dn : hhc_Dn 0 0 2 := by
  refine ⟨[(1 : ℤ)], ?_⟩
  rw [hzc_mem_truncFinset]
  exact ⟨hlhr_singleLeft_legal, by simp [numVertices]⟩





theorem hlhr_truncatedTwoHalfData_isEmpty :
    IsEmpty (HLHRTruncatedTwoHalfData 0 0 2) := by
  constructor
  intro H
  apply hlhr_no_unaugmented_split_singleLeft
  exact ⟨H.lower hlhr_singleLeft_Dn, H.upper hlhr_singleLeft_Dn,
    H.reconstruct hlhr_singleLeft_Dn,
    H.lower_halfSpace hlhr_singleLeft_Dn,
    H.upper_halfSpace hlhr_singleLeft_Dn⟩

namespace HLHRTruncatedTwoHalfData

noncomputable def lowerHalf {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRTruncatedTwoHalfData a h0 N) (d : hhc_Dn a h0 N) :
    HexHWContentHalf :=
  hlhr_contentHalf (H.lower d) (H.lower_legal d) (H.lower_halfSpace d)

noncomputable def upperHalf {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRTruncatedTwoHalfData a h0 N) (d : hhc_Dn a h0 N) :
    HexHWContentHalf :=
  hlhr_contentHalf (H.upper d) (H.upper_legal d) (H.upper_halfSpace d)

theorem halves_reconstruct {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRTruncatedTwoHalfData a h0 N) (d : hhc_Dn a h0 N) :
    d.1 = hhc_halfTurns (H.lowerHalf d) ++ hhc_halfTurns (H.upperHalf d) := by
  unfold lowerHalf upperHalf
  rw [hlhr_contentHalf_turns, hlhr_contentHalf_turns]
  exact H.reconstruct d



noncomputable def contentDecomp {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRTruncatedTwoHalfData a h0 N) :
    HexHWContentDecomp (hhc_Dn a h0 N) :=
  hhc_literalDecomp a h0 N H.lowerHalf H.upperHalf H.halves_reconstruct







theorem finite_partial_bound {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRTruncatedTwoHalfData a h0 N) {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (∑ s ∈ H.contentDecomp.lowerImage, hhc_halfWeight x s) *
        (∑ s ∈ H.contentDecomp.upperImage, hhc_halfWeight x s) := by
  exact hhc_literal_partial_bound a h0 N H.lowerHalf H.upperHalf
    H.halves_reconstruct hx

end HLHRTruncatedTwoHalfData













structure HLHRAugmentedTwoHalfData (a : ℂ) (h0 : ℤ) (N : ℕ) where
  lowerBoundary : hhc_Dn a h0 N → ℤ
  upperBoundary : hhc_Dn a h0 N → ℤ
  lowerCore : hhc_Dn a h0 N → List ℤ
  upperCore : hhc_Dn a h0 N → List ℤ
  decode : ℤ → List ℤ → ℤ → List ℤ → List ℤ
  decode_source : ∀ d,
    decode (lowerBoundary d) (lowerCore d)
      (upperBoundary d) (upperCore d) = d.1
  core_length : ∀ d,
    (lowerCore d).length + (upperCore d).length = d.1.length
  lower_legal : ∀ d,
    (ofTurns 0 0 (lowerBoundary d :: lowerCore d)).IsLegalSAW
  upper_legal : ∀ d,
    (ofTurns 0 0 (upperBoundary d :: upperCore d)).IsLegalSAW
  lower_halfSpace : ∀ d,
    HLHRLiteralHalfSpace 0 (lowerBoundary d :: lowerCore d)
  upper_halfSpace : ∀ d,
    HLHRLiteralHalfSpace 0 (upperBoundary d :: upperCore d)

namespace HLHRAugmentedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N : ℕ}


def lower (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) : List ℤ :=
  H.lowerBoundary d :: H.lowerCore d


def upper (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) : List ℤ :=
  H.upperBoundary d :: H.upperCore d

@[simp] theorem lower_tail (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    (H.lower d).tail = H.lowerCore d := rfl

@[simp] theorem upper_tail (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    (H.upper d).tail = H.upperCore d := rfl



@[simp] theorem decode_augmented
    (H : HLHRAugmentedTwoHalfData a h0 N) (d : hhc_Dn a h0 N) :
    H.decode (H.lower d).head! (H.lower d).tail
      (H.upper d).head! (H.upper d).tail = d.1 := by
  exact H.decode_source d


theorem length_add_two (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    (H.lower d).length + (H.upper d).length = d.1.length + 2 := by
  simp only [lower, upper, List.length_cons]
  have hlen := H.core_length d
  omega


theorem lowerBoundary_legal (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    H.lowerBoundary d = 1 ∨ H.lowerBoundary d = -1 := by
  exact (H.lower_legal d).1 _ (by simp [lower])


theorem upperBoundary_legal (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    H.upperBoundary d = 1 ∨ H.upperBoundary d = -1 := by
  exact (H.upper_legal d).1 _ (by simp [upper])



theorem lowerBoundary_outward (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    hlhr_height 0 (H.lower d) 0 < hlhr_height 0 (H.lower d) 1 := by
  apply H.lower_halfSpace d 1 (by omega)
  simp [lower]



theorem upperBoundary_outward (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    hlhr_height 0 (H.upper d) 0 < hlhr_height 0 (H.upper d) 1 := by
  apply H.upper_halfSpace d 1 (by omega)
  simp [upper]



theorem listPair_injective (H : HLHRAugmentedTwoHalfData a h0 N) :
    Function.Injective (fun d => (H.lower d, H.upper d)) := by
  intro d e hpair
  apply Subtype.ext
  rw [← H.decode_source d, ← H.decode_source e]
  have hlo := congrArg Prod.fst hpair
  have hup := congrArg Prod.snd hpair
  have hlo' := List.cons.inj (by simpa [lower] using hlo)
  have hup' := List.cons.inj (by simpa [upper] using hup)
  rw [hlo'.1, hlo'.2, hup'.1, hup'.2]


noncomputable def lowerHalf (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hlhr_contentHalf (H.lower d) (H.lower_legal d) (H.lower_halfSpace d)


noncomputable def upperHalf (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hlhr_contentHalf (H.upper d) (H.upper_legal d) (H.upper_halfSpace d)

@[simp] theorem lowerHalf_turns (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (H.lowerHalf d) = H.lower d := by
  exact hlhr_contentHalf_turns _ (H.lower_legal d) (H.lower_halfSpace d)

@[simp] theorem upperHalf_turns (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (H.upperHalf d) = H.upper d := by
  exact hlhr_contentHalf_turns _ (H.upper_legal d) (H.upper_halfSpace d)


noncomputable def contentPair (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) : HexHWContentHalf × HexHWContentHalf :=
  (H.lowerHalf d, H.upperHalf d)


theorem contentPair_injective (H : HLHRAugmentedTwoHalfData a h0 N) :
    Function.Injective H.contentPair := by
  intro d e hpair
  apply H.listPair_injective
  apply Prod.ext
  · have h := congrArg
      (fun p : HexHWContentHalf × HexHWContentHalf => hhc_halfTurns p.1)
      hpair
    simpa [contentPair] using h
  · have h := congrArg
      (fun p : HexHWContentHalf × HexHWContentHalf => hhc_halfTurns p.2)
      hpair
    simpa [contentPair] using h


theorem source_weight_factor (H : HLHRAugmentedTwoHalfData a h0 N)
    (x : ℝ) (hx : 0 < x) (d : hhc_Dn a h0 N) :
    x ^ d.1.length = (x ^ 2)⁻¹ *
      (hhc_halfWeight x (H.lowerHalf d) *
        hhc_halfWeight x (H.upperHalf d)) := by
  rw [hhc_halfWeight_eq_pow, hhc_halfWeight_eq_pow,
    H.lowerHalf_turns, H.upperHalf_turns]
  exact hexHW_two_overcount_pow_factor x hx _ _ _ (H.length_add_two d)


noncomputable def lowerImage (H : HLHRAugmentedTwoHalfData a h0 N) :
    Finset HexHWContentHalf := by
  classical
  exact Finset.univ.image H.lowerHalf


noncomputable def upperImage (H : HLHRAugmentedTwoHalfData a h0 N) :
    Finset HexHWContentHalf := by
  classical
  exact Finset.univ.image H.upperHalf


noncomputable def pairImage (H : HLHRAugmentedTwoHalfData a h0 N) :
    Finset (HexHWContentHalf × HexHWContentHalf) := by
  classical
  exact Finset.univ.image H.contentPair



theorem sum_eq_pairImage (H : HLHRAugmentedTwoHalfData a h0 N) (x : ℝ) :
    ∑ d : hhc_Dn a h0 N,
        hhc_halfWeight x (H.lowerHalf d) *
          hhc_halfWeight x (H.upperHalf d) =
      ∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
  classical
  rw [pairImage, Finset.sum_image
    (fun d _ e _ hde => H.contentPair_injective hde)]
  rfl



theorem pairImage_subset_product (H : HLHRAugmentedTwoHalfData a h0 N) :
    H.pairImage ⊆ H.lowerImage ×ˢ H.upperImage := by
  classical
  intro p hp
  rw [pairImage, Finset.mem_image] at hp
  obtain ⟨d, _, rfl⟩ := hp
  rw [Finset.mem_product]
  exact ⟨Finset.mem_image_of_mem H.lowerHalf (Finset.mem_univ d),
    Finset.mem_image_of_mem H.upperHalf (Finset.mem_univ d)⟩


theorem pair_sum_le_product (H : HLHRAugmentedTwoHalfData a h0 N)
    {x : ℝ} (hx : 0 ≤ x) :
    (∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2) ≤
      (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
        (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
  classical
  calc
    (∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2) ≤
        ∑ p ∈ H.lowerImage ×ˢ H.upperImage,
          hhc_halfWeight x p.1 * hhc_halfWeight x p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg H.pairImage_subset_product
        (fun p _ _ => mul_nonneg (hhc_halfWeight_nonneg hx p.1)
          (hhc_halfWeight_nonneg hx p.2))
    _ = (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]





theorem finite_partial_bound (H : HLHRAugmentedTwoHalfData a h0 N)
    {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ 2)⁻¹ *
        ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s)) := by
  rw [← hhc_partial_eq a h0 x N]
  calc
    (∑ d : hhc_Dn a h0 N, x ^ d.1.length) =
        (x ^ 2)⁻¹ *
          ∑ d : hhc_Dn a h0 N,
            hhc_halfWeight x (H.lowerHalf d) *
              hhc_halfWeight x (H.upperHalf d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact H.source_weight_factor x hx d
    _ = (x ^ 2)⁻¹ *
        ∑ p ∈ H.pairImage,
          hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
      rw [H.sum_eq_pairImage x]
    _ ≤ (x ^ 2)⁻¹ *
        ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s)) :=
      mul_le_mul_of_nonneg_left (H.pair_sum_le_product (le_of_lt hx))
        (by positivity)

end HLHRAugmentedTwoHalfData







structure HLHRStripColumnRealization (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) where
  column : (p : ℕ × ℕ) → p ∈ hlhr_literalIntervals h0 ts → ℕ
  column_pos : ∀ p hp, 0 < column p hp
  span_strict : ∀ p hp q hq,
    hlhr_intervalSpan (hlhr_height h0 ts) p >
        hlhr_intervalSpan (hlhr_height h0 ts) q →
      column p hp > column q hq

end StatMech.Universality
