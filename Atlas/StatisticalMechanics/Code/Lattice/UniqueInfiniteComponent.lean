/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.SegmentConn

open Set SimpleGraph

namespace StatMech

namespace Lattice

variable {d : ℕ}






def exterior (d R : ℕ) : Set (Site d) := {x | ∃ i, R < (x i).natAbs}

@[simp]
theorem mem_exterior {d R : ℕ} {x : Site d} :
    x ∈ exterior d R ↔ ∃ i, R < (x i).natAbs := Iff.rfl


theorem exterior_eq_compl_box (d R : ℕ) : exterior d R = (box d R)ᶜ := by
  ext x
  simp only [mem_exterior, mem_box, Set.mem_compl_iff, not_forall, not_le]






theorem segment_up (S : Set (Site d)) (j : Fin d) (p : Site d) (c : ℤ) (hpc : p j ≤ c)
    (hp : p ∈ S) (hc : Function.update p j c ∈ S)
    (hseg : ∀ z : ℤ, (p j ≤ z ∧ z ≤ c) → Function.update p j z ∈ S) :
    ((hypercubicLattice d).induce S).Reachable ⟨p, hp⟩ ⟨Function.update p j c, hc⟩ := by
  set n := (c - p j).toNat with hn
  have hntoNat : (n : ℤ) = c - p j := by rw [hn]; exact Int.toNat_of_nonneg (by linarith)
  have hmem : ∀ t ≤ n, Function.update p j (p j + (t : ℤ)) ∈ S := by
    intro t ht
    apply hseg
    refine ⟨by linarith, ?_⟩
    have : (t : ℤ) ≤ (n : ℤ) := by exact_mod_cast ht
    linarith [hntoNat]
  have key := segment_connectedWithin S j p n hmem
  have hstart : Function.update p j (p j + (0 : ℤ)) = p := by
    rw [add_zero, Function.update_eq_self]
  have hend : Function.update p j (p j + (n : ℤ)) = Function.update p j c := by
    rw [hntoNat]; ring_nf
  convert key using 2
  · rw [hstart]
  · rw [hend]




theorem segment_gen (S : Set (Site d)) (j : Fin d) (p : Site d) (c : ℤ)
    (hp : p ∈ S) (hc : Function.update p j c ∈ S)
    (hseg : ∀ z : ℤ, (min (p j) c ≤ z ∧ z ≤ max (p j) c) → Function.update p j z ∈ S) :
    ((hypercubicLattice d).induce S).Reachable ⟨p, hp⟩ ⟨Function.update p j c, hc⟩ := by
  rcases le_total (p j) c with h | h
  · apply segment_up S j p c h hp hc
    intro z hz
    apply hseg
    rw [min_eq_left h, max_eq_right h]; exact hz
  · set q := Function.update p j c with hq
    have hqj : q j = c := Function.update_self j c p
    have hupd : Function.update q j (p j) = p := by
      rw [hq, Function.update_idem, Function.update_eq_self]
    have hcp : Function.update q j (p j) ∈ S := by rw [hupd]; exact hp
    have hqle : q j ≤ p j := by rw [hqj]; exact h
    have hsegq : ∀ z : ℤ, (q j ≤ z ∧ z ≤ p j) → Function.update q j z ∈ S := by
      intro z hz
      rw [hqj] at hz
      have hqz : Function.update q j z = Function.update p j z := by rw [hq, Function.update_idem]
      rw [hqz]
      apply hseg
      rw [min_eq_right h, max_eq_left h]; exact hz
    have key := (segment_up S j q (p j) hqle hc hcp hsegq).symm
    convert key using 2
    rw [hupd]




def setOn (p : Site d) (T : Finset (Fin d)) (v : ℤ) : Site d :=
  fun k => if k ∈ T then v else p k

@[simp]
theorem setOn_empty (p : Site d) (v : ℤ) : setOn p ∅ v = p := by funext k; simp [setOn]

theorem setOn_insert (p : Site d) (T : Finset (Fin d)) (j : Fin d) (v : ℤ) (hj : j ∉ T) :
    setOn p (insert j T) v = Function.update (setOn p T v) j v := by
  funext k
  simp only [setOn, Function.update]
  by_cases hk : k = j
  · subst hk; simp [hj]
  · simp [hk, Finset.mem_insert]

theorem setOn_notMem (p : Site d) (T : Finset (Fin d)) (v : ℤ) {i0 : Fin d} (h : i0 ∉ T) :
    setOn p T v i0 = p i0 := by simp [setOn, h]





theorem exterior_reachable_setOn (R : ℕ) (p : Site d) (i0 : Fin d)
    (hi0 : R < (p i0).natAbs) (T : Finset (Fin d)) (hT : i0 ∉ T)
    (hpext : p ∈ exterior d R) (htgt : setOn p T ((R : ℤ) + 1) ∈ exterior d R) :
    ((hypercubicLattice d).induce (exterior d R)).Reachable ⟨p, hpext⟩
      ⟨setOn p T ((R : ℤ) + 1), htgt⟩ := by
  induction T using Finset.induction_on with
  | empty =>
    have heq : (⟨setOn p ∅ ((R : ℤ) + 1), htgt⟩ : exterior d R) = ⟨p, hpext⟩ :=
      Subtype.ext (setOn_empty p ((R : ℤ) + 1))
    rw [heq]
  | insert j T hjT ih =>
    have hi0T : i0 ∉ T := fun h => hT (Finset.mem_insert_of_mem h)
    have hji0 : j ≠ i0 := fun h => hT (h ▸ Finset.mem_insert_self j T)
    set q := setOn p T ((R : ℤ) + 1) with hq
    have hqi0 : q i0 = p i0 := setOn_notMem p T _ hi0T
    have hqext : q ∈ exterior d R := ⟨i0, by rw [hqi0]; exact hi0⟩
    have hstep_tgt : Function.update q j ((R : ℤ) + 1) ∈ exterior d R := by
      refine ⟨i0, ?_⟩; rw [Function.update_of_ne (Ne.symm hji0), hqi0]; exact hi0
    have hseg : ∀ z : ℤ, (min (q j) ((R : ℤ) + 1) ≤ z ∧ z ≤ max (q j) ((R : ℤ) + 1)) →
        Function.update q j z ∈ exterior d R := by
      intro z _
      refine ⟨i0, ?_⟩; rw [Function.update_of_ne (Ne.symm hji0), hqi0]; exact hi0
    have step := segment_gen (exterior d R) j q ((R : ℤ) + 1) hqext hstep_tgt hseg
    have hchain := (ih hi0T hqext).trans step
    have hval : setOn p (insert j T) ((R : ℤ) + 1) = Function.update q j ((R : ℤ) + 1) :=
      setOn_insert p T j ((R : ℤ) + 1) hjT
    have heq : (⟨setOn p (insert j T) ((R : ℤ) + 1), htgt⟩ : exterior d R)
        = ⟨Function.update q j ((R : ℤ) + 1), hstep_tgt⟩ := Subtype.ext hval
    rw [heq]; exact hchain


def beacon (d R : ℕ) : Site d := fun _ => (R : ℤ) + 1

theorem beacon_natAbs (R : ℕ) (k : Fin d) : ((beacon d R) k).natAbs = R + 1 := by
  show ((R : ℤ) + 1).natAbs = R + 1
  rw [Int.natAbs_eq_iff]; left; push_cast; ring

theorem beacon_mem_exterior (R : ℕ) (hd : 1 ≤ d) : beacon d R ∈ exterior d R := by
  refine ⟨⟨0, by omega⟩, ?_⟩
  rw [beacon_natAbs]; omega




theorem exterior_reachable_beacon (R : ℕ) (hd : 2 ≤ d) (p : Site d)
    (hp : p ∈ exterior d R) :
    ((hypercubicLattice d).induce (exterior d R)).Reachable ⟨p, hp⟩
      ⟨beacon d R, beacon_mem_exterior R (by omega)⟩ := by
  classical
  obtain ⟨i0, hi0⟩ := hp
  
  set T := Finset.univ \ {i0} with hT
  have hi0T : i0 ∉ T := by simp [hT]
  have hp' : p ∈ exterior d R := ⟨i0, hi0⟩
  
  set p1 := setOn p T ((R : ℤ) + 1) with hp1
  have hp1_i0 : p1 i0 = p i0 := setOn_notMem p T _ hi0T
  have hp1_ext : p1 ∈ exterior d R := ⟨i0, by rw [hp1_i0]; exact hi0⟩
  have phase1 := exterior_reachable_setOn R p i0 hi0 T hi0T hp' hp1_ext
  
  
  have hcard : 1 < Fintype.card (Fin d) := by simpa using hd
  obtain ⟨i1, hi1ne⟩ := Fintype.exists_ne_of_one_lt_card hcard i0
  have hi1T : i1 ∈ T := by simp [hT, hi1ne]
  have hp1_i1 : p1 i1 = (R : ℤ) + 1 := by simp [hp1, setOn, hi1T]
  
  have hupd_beacon : Function.update p1 i0 ((R : ℤ) + 1) = beacon d R := by
    funext k
    by_cases hk : k = i0
    · subst hk; simp [beacon]
    · rw [Function.update_of_ne hk]
      
      have hkT : k ∈ T := by simp [hT, hk]
      simp [hp1, setOn, hkT, beacon]
  have hbeacon_ext : Function.update p1 i0 ((R : ℤ) + 1) ∈ exterior d R := by
    rw [hupd_beacon]; exact beacon_mem_exterior R (by omega)
  have hseg2 : ∀ z : ℤ, (min (p1 i0) ((R : ℤ) + 1) ≤ z ∧ z ≤ max (p1 i0) ((R : ℤ) + 1)) →
      Function.update p1 i0 z ∈ exterior d R := by
    intro z _
    refine ⟨i1, ?_⟩
    rw [Function.update_of_ne hi1ne, hp1_i1]
    have : ((R : ℤ) + 1).natAbs = R + 1 := by rw [Int.natAbs_eq_iff]; left; push_cast; ring
    rw [this]; omega
  have phase2 := segment_gen (exterior d R) i0 p1 ((R : ℤ) + 1) hp1_ext hbeacon_ext hseg2
  have hchain := phase1.trans phase2
  
  have heq : (⟨Function.update p1 i0 ((R : ℤ) + 1), hbeacon_ext⟩ : exterior d R)
      = ⟨beacon d R, beacon_mem_exterior R (by omega)⟩ := Subtype.ext hupd_beacon
  rw [heq] at hchain
  exact hchain



theorem box_exterior_connected (R : ℕ) (hd : 2 ≤ d) (x y : Site d)
    (hx : x ∈ exterior d R) (hy : y ∈ exterior d R) :
    ((hypercubicLattice d).induce (exterior d R)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  (exterior_reachable_beacon R hd x hx).trans (exterior_reachable_beacon R hd y hy).symm



theorem exterior_infinite (R : ℕ) (hd : 2 ≤ d) : (exterior d R).Infinite := by
  have hcard : 1 < Fintype.card (Fin d) := by simpa using hd
  obtain ⟨i1, _⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, by omega⟩
  obtain ⟨i0, hi0ne⟩ := Fintype.exists_ne_of_one_lt_card hcard i1
  set b : Site d := beacon d R with hb
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℤ => Function.update b i1 m) ?_ ?_
  · intro a c hac
    have := congrFun hac i1
    simpa using this
  · intro m
    refine ⟨i0, ?_⟩
    show R < (Function.update b i1 m i0).natAbs
    rw [Function.update_of_ne hi0ne, hb, beacon_natAbs]
    omega




theorem finite_subset_box (F : Set (Site d)) (hF : F.Finite) : ∃ R : ℕ, F ⊆ box d R := by
  classical
  set g : Site d → ℕ := fun x => Finset.univ.sup (fun i => (x i).natAbs) with hg
  refine ⟨hF.toFinset.sup g, ?_⟩
  intro x hx i
  have hxF : x ∈ hF.toFinset := by rwa [Set.Finite.mem_toFinset]
  have h1 : (x i).natAbs ≤ g x := Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
  have h2 : g x ≤ hF.toFinset.sup g := Finset.le_sup hxF
  exact h1.trans h2




theorem exterior_subset_compl (F : Set (Site d)) (R : ℕ) (hF : F ⊆ box d R) :
    exterior d R ⊆ Fᶜ := by
  rw [exterior_eq_compl_box]
  exact Set.compl_subset_compl.mpr hF



theorem exterior_reachable_compl (F : Set (Site d)) (R : ℕ) (hd : 2 ≤ d)
    (hsub : exterior d R ⊆ Fᶜ) (x y : Site d)
    (hx : x ∈ exterior d R) (hy : y ∈ exterior d R) :
    ((hypercubicLattice d).induce Fᶜ).Reachable ⟨x, hsub hx⟩ ⟨y, hsub hy⟩ := by
  have h := box_exterior_connected R hd x y hx hy
  simpa using h.map ((hypercubicLattice d).induceHomOfLE hsub).toHom






theorem unique_infinite_component (hd : 2 ≤ d) (F : Set (Site d)) (hF : F.Finite) :
    ∃! C : ((hypercubicLattice d).induce Fᶜ).ConnectedComponent, C.supp.Infinite := by
  classical
  obtain ⟨R, hR⟩ := finite_subset_box F hF
  set G := (hypercubicLattice d).induce Fᶜ with hG
  have hsub : exterior d R ⊆ Fᶜ := exterior_subset_compl F R hR
  have hb_ext : beacon d R ∈ exterior d R := beacon_mem_exterior R (by omega)
  set v0 : ↥Fᶜ := ⟨beacon d R, hsub hb_ext⟩ with hv0
  set C0 := G.connectedComponentMk v0 with hC0
  
  have hExtComp : ∀ (x : Site d) (hx : x ∈ exterior d R),
      G.connectedComponentMk ⟨x, hsub hx⟩ = C0 := by
    intro x hx
    exact ConnectedComponent.sound
      (exterior_reachable_compl F R hd hsub x (beacon d R) hx hb_ext)
  
  have hC0_inf : C0.supp.Infinite := by
    have : Infinite ↥(exterior d R) := (exterior_infinite R hd).to_subtype
    refine Set.infinite_of_injective_forall_mem
      (f := fun w : ↥(exterior d R) => (⟨(w : Site d), hsub w.2⟩ : ↥Fᶜ)) ?_ ?_
    · intro a b hab
      exact Subtype.ext (by simpa using congrArg Subtype.val hab)
    · intro w
      rw [ConnectedComponent.mem_supp_iff]
      exact hExtComp (w : Site d) w.2
  refine ⟨C0, hC0_inf, ?_⟩
  
  intro C hCinf
  obtain ⟨v, hv_supp, hv_ext⟩ : ∃ v : ↥Fᶜ, v ∈ C.supp ∧ (v : Site d) ∈ exterior d R := by
    by_contra hcon
    have hcon' : ∀ v ∈ C.supp, (v : Site d) ∉ exterior d R := by
      intro v hv hve; exact hcon ⟨v, hv, hve⟩
    have hsubbox : C.supp ⊆ (Subtype.val ⁻¹' (box d R)) := by
      intro v hv
      have hvb : (v : Site d) ∈ (exterior d R)ᶜ := hcon' v hv
      rw [exterior_eq_compl_box, compl_compl] at hvb
      exact hvb
    have hfin : (Subtype.val ⁻¹' (box d R) : Set ↥Fᶜ).Finite :=
      Set.Finite.preimage Subtype.val_injective.injOn (box_finite d R)
    exact hCinf (hfin.subset hsubbox)
  have h1 : G.connectedComponentMk v = C := (C.mem_supp_iff v).mp hv_supp
  have h2 : G.connectedComponentMk v = C0 := hExtComp (v : Site d) hv_ext
  rw [← h1, h2]

end Lattice

end StatMech
