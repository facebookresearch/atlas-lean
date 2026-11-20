/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationEmbeddingTurns








namespace StatMech.Onsager

open BigOperators
open StatMech.Onsager.BaseCase
open StatMech.Onsager.NoDoubleWind


def ons_windingTranslation (L : ℕ) (mx my : ℤ) : ℤ × ℤ :=
  ((L : ℤ) * mx, (L : ℤ) * my)



def ons_periodicLiftVertex {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) (mx my r : ℤ) (i : Fin n) : ℤ × ℤ :=
  pos (ons_liftDir v) i +
    ((L : ℤ) * (r * mx), (L : ℤ) * (r * my))


def ons_liftBase {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) : ℤ × ℤ :=
  (((ons_liftSite v 0).1.val : ℤ),
    ((ons_liftSite v 0).2.val : ℤ))



def ons_anchoredPeriodicLiftVertex {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) (mx my r : ℤ) (i : Fin n) : ℤ × ℤ :=
  ons_liftBase v + ons_periodicLiftVertex v mx my r i


theorem ons_pos_last_add_step {m : ℕ} (d : Fin (m + 1) → Fin 4) :
    pos d (Fin.last m) + stepOf (d (Fin.last m)) =
      ∑ i, stepOf (d i) := by
  have hfilter :
      (Finset.univ.filter (· < Fin.last m) : Finset (Fin (m + 1))) =
        Finset.univ.erase (Fin.last m) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · exact ne_of_lt
    · intro hi
      exact lt_of_le_of_ne (Fin.le_last i) hi
  rw [pos, hfilter, add_comm,
    Finset.add_sum_erase Finset.univ (fun i => stepOf (d i))
      (Finset.mem_univ (Fin.last m))]

theorem ons_liftDir_totalStep_eq_windingTranslation
    {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) (mx my : ℤ)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
    ∑ k, stepOf (ons_liftDir v k) =
      ons_windingTranslation L mx my := by
  rw [ons_liftDir_sum_step, hmx, hmy]
  rfl



theorem ons_periodicLiftVertex_injective
    {L n : ℕ} [NeZero L] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k => (v k).1))
    (mx my : ℤ) (hne : mx ≠ 0 ∨ my ≠ 0) :
    Function.Injective
      (fun z : ℤ × Fin n =>
        ons_periodicLiftVertex v mx my z.1 z.2) := by
  rintro ⟨r, i⟩ ⟨s, j⟩ hij
  have htranslate :
      pos (ons_liftDir v) i =
        pos (ons_liftDir v) j +
          ((L : ℤ) * ((s - r) * mx),
            (L : ℤ) * ((s - r) * my)) := by
    apply Prod.ext
    · have h := congrArg Prod.fst hij
      simp only [ons_periodicLiftVertex, Prod.fst_add] at h ⊢
      linear_combination h
    · have h := congrArg Prod.snd hij
      simp only [ons_periodicLiftVertex, Prod.snd_add] at h ⊢
      linear_combination h
  obtain ⟨hijFin, hx, hy⟩ :=
    ons_liftDir_no_period_translate v hvalid hsite htranslate
  have hrs : r = s := by
    rcases hne with hmx | hmy
    · have hsr : s - r = 0 :=
        (mul_eq_zero.mp hx).resolve_right hmx
      omega
    · have hsr : s - r = 0 :=
        (mul_eq_zero.mp hy).resolve_right hmy
      omega
  exact Prod.ext hrs hijFin

theorem ons_anchoredPeriodicLiftVertex_injective
    {L n : ℕ} [NeZero L] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k => (v k).1))
    (mx my : ℤ) (hne : mx ≠ 0 ∨ my ≠ 0) :
    Function.Injective
      (fun z : ℤ × Fin n =>
        ons_anchoredPeriodicLiftVertex v mx my z.1 z.2) := by
  intro x y hxy
  apply ons_periodicLiftVertex_injective v hvalid hsite mx my hne
  apply add_left_cancel (a := ons_liftBase v)
  simpa [ons_anchoredPeriodicLiftVertex] using hxy



theorem ons_reduceSite_anchoredPeriodicLiftVertex
    {L n : ℕ} [NeZero L] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (mx my r : ℤ) (i : Fin n) :
    ons_reduceSite L (ons_anchoredPeriodicLiftVertex v mx my r i) =
      ons_liftSite v i := by
  rw [ons_liftSite_eq_reduce_pos v hvalid i]
  apply Prod.ext
  · simp [ons_anchoredPeriodicLiftVertex, ons_liftBase,
      ons_periodicLiftVertex, ons_reduceSite, add_comm]
  · simp [ons_anchoredPeriodicLiftVertex, ons_liftBase,
      ons_periodicLiftVertex, ons_reduceSite, add_comm]



theorem ons_anchoredPeriodicLiftVertex_ne_of_torus_disjoint
    {L n m : ℕ} [NeZero L] [NeZero n] [NeZero m]
    (v : Fin n → ons_Dart L) (w : Fin m → ons_Dart L)
    (hvvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hwvalid : ∀ k : Fin m,
      (w k).1 = ons_dirStep L (w (k + 1)).2 (w (k + 1)).1)
    (hdisj : ∀ i j, (v i).1 ≠ (w j).1)
    (vmx vmy wmx wmy r s : ℤ) (i : Fin n) (j : Fin m) :
    ons_anchoredPeriodicLiftVertex v vmx vmy r i ≠
      ons_anchoredPeriodicLiftVertex w wmx wmy s j := by
  intro h
  have hred := congrArg (ons_reduceSite L) h
  rw [ons_reduceSite_anchoredPeriodicLiftVertex v hvvalid,
    ons_reduceSite_anchoredPeriodicLiftVertex w hwvalid] at hred
  exact hdisj (-i) (-j) hred



theorem ons_simpleLoop_nonzeroHomology_periodicLift
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k => (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hhom : ons_evenHomology L (ons_dartEdgeSet v) ≠ 0) :
    ∃ mx my : ℤ,
      (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx ∧
      (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my ∧
      (mx ≠ 0 ∨ my ≠ 0) ∧
      Function.Injective
        (fun z : ℤ × Fin n =>
          ons_anchoredPeriodicLiftVertex v mx my z.1 z.2) := by
  obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists v hvalid
  have hparity := ons_evenHomology_dartEdgeSet_eq_windingParity
    v hvalid hsite hnu mx my hmx hmy
  have hne : mx ≠ 0 ∨ my ≠ 0 := by
    by_contra h
    push_neg at h
    rcases h with ⟨rfl, rfl⟩
    apply hhom
    rw [hparity]
    simp [ons_windingParity, ons_intParity]
  exact ⟨mx, my, hmx, hmy, hne,
    ons_anchoredPeriodicLiftVertex_injective
      v hvalid hsite mx my hne⟩



theorem ons_decCycles_anchoredPeriodicLifts_disjoint
    (L : ℕ) [Fact (2 < L)]
    {d e : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (p : (ons_decGraph L).Walk e e)
    (hq : q.IsCycle) (hp : p.IsCycle)
    (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts)
    (qmx qmy pmx pmy r s : ℤ)
    (i : Fin (ons_decExpandedDartList L q).length)
    (j : Fin (ons_decExpandedDartList L p).length) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    letI : NeZero (ons_decExpandedDartList L p).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L p hp)⟩
    ons_anchoredPeriodicLiftVertex
        (ons_decExpandedKWLoop L q hq) qmx qmy r i ≠
      ons_anchoredPeriodicLiftVertex
        (ons_decExpandedKWLoop L p hp) pmx pmy s j := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  letI : NeZero (ons_decExpandedDartList L p).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L p hp)⟩
  exact ons_anchoredPeriodicLiftVertex_ne_of_torus_disjoint
    (ons_decExpandedKWLoop L q hq)
    (ons_decExpandedKWLoop L p hp)
    (ons_decExpandedKWLoop_valid L q hq)
    (ons_decExpandedKWLoop_valid L p hp)
    (ons_decExpandedKWLoop_sites_disjoint L q p hq hp hdisj)
    qmx qmy pmx pmy r s i j


theorem ons_periodicLiftVertex_step
    {L m : ℕ} (v : Fin (m + 1) → ons_Dart L)
    (mx my r : ℤ) (i : Fin m) :
    ons_periodicLiftVertex v mx my r i.succ =
      ons_periodicLiftVertex v mx my r i.castSucc +
        stepOf (ons_liftDir v i.castSucc) := by
  unfold ons_periodicLiftVertex
  rw [ons_pos_succ_cast]
  abel



theorem ons_periodicLiftVertex_last_step
    {L m : ℕ} (v : Fin (m + 1) → ons_Dart L)
    (mx my r : ℤ)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
    ons_periodicLiftVertex v mx my (r + 1) 0 =
      ons_periodicLiftVertex v mx my r (Fin.last m) +
        stepOf (ons_liftDir v (Fin.last m)) := by
  have hsum := ons_liftDir_totalStep_eq_windingTranslation v mx my hmx hmy
  have hlast := ons_pos_last_add_step (ons_liftDir v)
  rw [hsum] at hlast
  unfold ons_windingTranslation at hlast
  unfold ons_periodicLiftVertex
  rw [pos_zero]
  apply Prod.ext
  · have h := congrArg Prod.fst hlast
    simp only [Prod.fst_add, Prod.fst_zero] at h ⊢
    linear_combination -h
  · have h := congrArg Prod.snd hlast
    simp only [Prod.snd_add, Prod.snd_zero] at h ⊢
    linear_combination -h

end StatMech.Onsager
