/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectSeamForcing










open Finset SimpleGraph

set_option maxHeartbeats 800000

namespace StatMech.FrontierD

noncomputable section

open StatMech

local instance fkRectCutPushforwardDecidableRel (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _

local instance fkRectCutPushforwardEdgeFintype (R : FKRectTorus) :
    Fintype {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
  (fkRectTorusGraph R).fintypeEdgeSet

local instance fkRectCutPushforwardConfigurationFintype (R : FKRectTorus) :
    Fintype (FKRectGraphConfiguration R) :=
  Pi.instFintype


def fkRectGraphForceClosed (R : FKRectTorus)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) : FKRectGraphConfiguration R :=
  fun e => if e ∈ I then false else eta e

@[simp] theorem fkRectGraphForceClosed_of_mem
    (R : FKRectTorus)
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (eta : FKRectGraphConfiguration R) {e} (he : e ∈ I) :
    fkRectGraphForceClosed R I eta e = false := by
  simp [fkRectGraphForceClosed, he]

@[simp] theorem fkRectGraphForceClosed_of_not_mem
    (R : FKRectTorus)
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (eta : FKRectGraphConfiguration R) {e} (he : e ∉ I) :
    fkRectGraphForceClosed R I eta e = eta e := by
  simp [fkRectGraphForceClosed, he]

@[simp] theorem fkRectGraphForceClosed_empty
    (R : FKRectTorus) (eta : FKRectGraphConfiguration R) :
    fkRectGraphForceClosed R ∅ eta = eta := by
  funext e
  simp [fkRectGraphForceClosed]

theorem fkRectGraphForceClosed_insert
    (R : FKRectTorus)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    fkRectGraphForceClosed R (insert e I) eta =
      fkRectGraphForceClosed R I (setClosed e eta) := by
  funext x
  by_cases hx : x = e
  · subst x
    simp [fkRectGraphForceClosed]
  · by_cases hxI : x ∈ I
    · simp [fkRectGraphForceClosed, hx, hxI]
    · simp [fkRectGraphForceClosed, hx, hxI, setClosed_of_ne]


def fkRectGraphCriticalEventMass
    (R : FKRectTorus) (q : Real)
    (A : Set (FKRectGraphConfiguration R)) : Real :=
  ∑ eta : FKRectGraphConfiguration R,
    A.indicator
      (fun eta => fkRectGraphCriticalRandomClusterProb R q eta) eta

theorem fkRectGraphCriticalEventMass_mono
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    {A B : Set (FKRectGraphConfiguration R)} (hAB : A ⊆ B) :
    fkRectGraphCriticalEventMass R q A ≤
      fkRectGraphCriticalEventMass R q B := by
  unfold fkRectGraphCriticalEventMass
  apply Finset.sum_le_sum
  intro eta heta
  by_cases hA : eta ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hAB hA)]
  · rw [Set.indicator_of_notMem hA]
    exact Set.indicator_nonneg
      (fun _ _ => fkRectGraphCriticalRandomClusterProb_nonneg R hq _) _

section FiniteBoolPushforward

variable {E : Type*} [Fintype E] [DecidableEq E]

private def finiteBoolEventMass
    (mu : ConfigSpace E → Real) (A : Set (ConfigSpace E)) : Real :=
  ∑ omega : ConfigSpace E, A.indicator mu omega

private def finiteBoolForceClosed (I : Finset E)
    (omega : ConfigSpace E) : ConfigSpace E :=
  fun e => if e ∈ I then false else omega e

private def finiteBoolForceOpen (I : Finset E)
    (omega : ConfigSpace E) : ConfigSpace E :=
  fun e => if e ∈ I then true else omega e

omit [Fintype E] in
private theorem finiteBoolForceClosed_empty (omega : ConfigSpace E) :
    finiteBoolForceClosed ∅ omega = omega := by
  funext e
  simp [finiteBoolForceClosed]

omit [Fintype E] in
private theorem finiteBoolForceClosed_insert
    (I : Finset E) (e : E) (omega : ConfigSpace E) :
    finiteBoolForceClosed (insert e I) omega =
      finiteBoolForceClosed I (setClosed e omega) := by
  funext x
  by_cases hx : x = e <;> by_cases hxI : x ∈ I <;>
    simp [finiteBoolForceClosed, hx, hxI, setClosed_of_ne]

omit [Fintype E] in
private theorem finiteBoolForceOpen_empty (omega : ConfigSpace E) :
    finiteBoolForceOpen ∅ omega = omega := by
  funext e
  simp [finiteBoolForceOpen]

omit [Fintype E] in
private theorem finiteBoolForceOpen_insert
    (I : Finset E) (e : E) (omega : ConfigSpace E) :
    finiteBoolForceOpen (insert e I) omega =
      finiteBoolForceOpen I (setOpen e omega) := by
  funext x
  by_cases hx : x = e <;> by_cases hxI : x ∈ I <;>
    simp [finiteBoolForceOpen, hx, hxI, setOpen_of_ne]

private theorem finiteBoolEventMass_preimage_setClosed
    (mu : ConfigSpace E → Real) (e : E) (A : Set (ConfigSpace E)) :
    finiteBoolEventMass mu (setClosed e ⁻¹' A) =
      ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setOpen e eta) + mu (setClosed e eta))
          (setClosed e eta) := by
  classical
  unfold finiteBoolEventMass
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ConfigSpace E)) (fun eta => eta e = false)]
  calc
    _ = (∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
            eta e = false),
          A.indicator (fun _ => mu (setClosed e eta)) (setClosed e eta)) +
        ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
            eta e = false),
          A.indicator (fun _ => mu (setOpen e eta)) (setClosed e eta) := by
      congr 1
      · apply Finset.sum_bij (fun eta _ => eta)
        · intro eta heta
          simpa using heta
        · intro a ha b hb hab
          exact hab
        · intro eta heta
          exact ⟨eta, heta, rfl⟩
        · intro eta heta
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
          have hclose : setClosed e eta = eta := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [heta]
            · rw [setClosed_of_ne hx]
          rw [hclose]
          by_cases hA : eta ∈ A <;>
            simp [Set.indicator, hA, hclose]
      · apply Finset.sum_bij (fun omega _ => setClosed e omega)
        · intro omega homega
          simp
        · intro omega homega rho hrho heq
          funext x
          by_cases hx : x = e
          · subst x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.not_eq_false] at homega hrho
            rw [homega, hrho]
          · have hxval := congrFun heq x
            simpa [setClosed_of_ne hx] using hxval
        · intro eta heta
          refine ⟨setOpen e eta, by simp, ?_⟩
          funext x
          by_cases hx : x = e
          · subst x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
            simp [heta]
          · rw [setClosed_of_ne hx, setOpen_of_ne hx]
        · intro omega homega
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.not_eq_false] at homega
          have hopenClosed : setOpen e (setClosed e omega) = omega := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [homega]
            · rw [setOpen_of_ne hx, setClosed_of_ne hx]
          have hclosed : setClosed e (setClosed e omega) = setClosed e omega := by
            funext x
            by_cases hx : x = e
            · subst x
              simp
            · rw [setClosed_of_ne hx, setClosed_of_ne hx]
          rw [hopenClosed, hclosed]
          by_cases hA : setClosed e omega ∈ A <;>
            simp [Set.indicator, hA]
    _ = ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
          eta e = false),
        A.indicator (fun _ => mu (setOpen e eta) + mu (setClosed e eta))
          (setClosed e eta) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro eta heta
      by_cases hA : setClosed e eta ∈ A <;> simp [hA, add_comm]

private theorem finiteBoolEventMass_preimage_setOpen
    (mu : ConfigSpace E → Real) (e : E) (A : Set (ConfigSpace E)) :
    finiteBoolEventMass mu (setOpen e ⁻¹' A) =
      ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setOpen e eta) + mu (setClosed e eta))
          (setOpen e eta) := by
  classical
  unfold finiteBoolEventMass
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ConfigSpace E)) (fun eta => eta e = false)]
  calc
    _ = (∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
            eta e = false),
          A.indicator (fun _ => mu (setClosed e eta)) (setOpen e eta)) +
        ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
            eta e = false),
          A.indicator (fun _ => mu (setOpen e eta)) (setOpen e eta) := by
      congr 1
      · apply Finset.sum_bij (fun eta _ => eta)
        · intro eta heta
          simpa using heta
        · intro a ha b hb hab
          exact hab
        · intro eta heta
          exact ⟨eta, heta, rfl⟩
        · intro eta heta
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
          have hclose : setClosed e eta = eta := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [heta]
            · rw [setClosed_of_ne hx]
          rw [hclose]
          by_cases hA : setOpen e eta ∈ A <;>
            simp [Set.indicator, hA]
      · apply Finset.sum_bij (fun omega _ => setClosed e omega)
        · intro omega homega
          simp
        · intro omega homega rho hrho heq
          funext x
          by_cases hx : x = e
          · subst x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.not_eq_false] at homega hrho
            rw [homega, hrho]
          · have hxval := congrFun heq x
            simpa [setClosed_of_ne hx] using hxval
        · intro eta heta
          refine ⟨setOpen e eta, by simp, ?_⟩
          funext x
          by_cases hx : x = e
          · subst x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
            simp [heta]
          · rw [setClosed_of_ne hx, setOpen_of_ne hx]
        · intro omega homega
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.not_eq_false] at homega
          have hopen : setOpen e omega = omega := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [homega]
            · rw [setOpen_of_ne hx]
          have hopenClosed : setOpen e (setClosed e omega) = omega := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [homega]
            · rw [setOpen_of_ne hx, setClosed_of_ne hx]
          rw [hopenClosed]
          by_cases hA : omega ∈ A <;>
            simp [Set.indicator, hA, hopen]
    _ = ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
          eta e = false),
        A.indicator (fun _ => mu (setOpen e eta) + mu (setClosed e eta))
          (setOpen e eta) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro eta heta
      by_cases hA : setOpen e eta ∈ A <;> simp [hA, add_comm]

private theorem finiteBoolClosedEventSum_le
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (e : E) (A : Set (ConfigSpace E)) :
    (∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setClosed e eta)) (setClosed e eta)) ≤
      finiteBoolEventMass mu A := by
  classical
  unfold finiteBoolEventMass
  calc
    _ = ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator mu eta := by
      apply Finset.sum_congr rfl
      intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
      have hclose : setClosed e eta = eta := by
        funext x
        by_cases hx : x = e
        · subst x
          simp [heta]
        · rw [setClosed_of_ne hx]
      rw [hclose]
      by_cases hA : eta ∈ A <;> simp [hA]
    _ ≤ ∑ eta ∈ (Finset.univ : Finset (ConfigSpace E)),
        A.indicator mu eta := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro eta heta hnot
      exact Set.indicator_nonneg (fun _ _ => hmu _) _

private theorem finiteBoolOpenEventSum_le
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (e : E) (A : Set (ConfigSpace E)) :
    (∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setOpen e eta)) (setOpen e eta)) ≤
      finiteBoolEventMass mu A := by
  classical
  unfold finiteBoolEventMass
  calc
    _ = ∑ omega ∈ (Finset.univ.filter fun omega : ConfigSpace E =>
          omega e = true), A.indicator mu omega := by
      apply Finset.sum_bij (fun eta _ => setOpen e eta)
      · intro eta heta
        simp
      · intro eta heta rho hrho heq
        funext x
        by_cases hx : x = e
        · subst x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta hrho
          rw [heta, hrho]
        · have hxval := congrFun heq x
          simpa [setOpen_of_ne hx] using hxval
      · intro omega homega
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega
        refine ⟨setClosed e omega, by simp, ?_⟩
        funext x
        by_cases hx : x = e
        · subst x
          simp [homega]
        · rw [setOpen_of_ne hx, setClosed_of_ne hx]
      · intro eta heta
        by_cases hA : setOpen e eta ∈ A <;> simp [hA]
    _ ≤ ∑ omega ∈ (Finset.univ : Finset (ConfigSpace E)),
        A.indicator mu omega := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro omega homega hnot
      exact Set.indicator_nonneg (fun _ _ => hmu _) _

private theorem finiteBool_c_mul_preimage_setClosed_le_event
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (c : Real)
    (hpair : ∀ e eta, c * (mu (setOpen e eta) + mu (setClosed e eta)) ≤
      mu (setClosed e eta)) (e : E) (A : Set (ConfigSpace E)) :
    c * finiteBoolEventMass mu (setClosed e ⁻¹' A) ≤
      finiteBoolEventMass mu A := by
  rw [finiteBoolEventMass_preimage_setClosed]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setClosed e eta)) (setClosed e eta) := by
      apply Finset.sum_le_sum
      intro eta heta
      by_cases hA : setClosed e eta ∈ A
      · simp only [Set.indicator_of_mem hA]
        exact hpair e eta
      · simp [Set.indicator_of_notMem hA]
    _ ≤ finiteBoolEventMass mu A :=
      finiteBoolClosedEventSum_le mu hmu e A

private theorem finiteBool_c_mul_preimage_setOpen_le_event
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (c : Real)
    (hpair : ∀ e eta, c * (mu (setOpen e eta) + mu (setClosed e eta)) ≤
      mu (setOpen e eta)) (e : E) (A : Set (ConfigSpace E)) :
    c * finiteBoolEventMass mu (setOpen e ⁻¹' A) ≤
      finiteBoolEventMass mu A := by
  rw [finiteBoolEventMass_preimage_setOpen]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setOpen e eta)) (setOpen e eta) := by
      apply Finset.sum_le_sum
      intro eta heta
      by_cases hA : setOpen e eta ∈ A
      · simp only [Set.indicator_of_mem hA]
        exact hpair e eta
      · simp [Set.indicator_of_notMem hA]
    _ ≤ finiteBoolEventMass mu A :=
      finiteBoolOpenEventSum_le mu hmu e A

private theorem finiteBool_c_pow_mul_forceClosed_preimage_le_event
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (c : Real) (hc : 0 ≤ c)
    (hpair : ∀ e eta, c * (mu (setOpen e eta) + mu (setClosed e eta)) ≤
      mu (setClosed e eta)) (I : Finset E) (A : Set (ConfigSpace E)) :
    c ^ I.card * finiteBoolEventMass mu (finiteBoolForceClosed I ⁻¹' A) ≤
      finiteBoolEventMass mu A := by
  classical
  induction I using Finset.induction with
  | empty =>
      have hpre : finiteBoolForceClosed ∅ ⁻¹' A = A := by
        ext omega
        simp only [Set.mem_preimage]
        rw [finiteBoolForceClosed_empty]
      rw [Finset.card_empty, pow_zero, one_mul, hpre]
  | @insert e I he ih =>
      rw [Finset.card_insert_of_notMem he, pow_succ]
      have hpre : finiteBoolForceClosed (insert e I) ⁻¹' A =
          setClosed e ⁻¹' (finiteBoolForceClosed I ⁻¹' A) := by
        ext omega
        simp only [Set.mem_preimage]
        rw [finiteBoolForceClosed_insert]
      rw [hpre]
      calc
        _ = c ^ I.card *
            (c * finiteBoolEventMass mu
              (setClosed e ⁻¹' (finiteBoolForceClosed I ⁻¹' A))) := by ring
        _ ≤ c ^ I.card * finiteBoolEventMass mu
              (finiteBoolForceClosed I ⁻¹' A) :=
          mul_le_mul_of_nonneg_left
            (finiteBool_c_mul_preimage_setClosed_le_event
              mu hmu c hpair e _) (pow_nonneg hc _)
        _ ≤ finiteBoolEventMass mu A := ih

private theorem finiteBool_c_pow_mul_forceOpen_preimage_le_event
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (c : Real) (hc : 0 ≤ c)
    (hpair : ∀ e eta, c * (mu (setOpen e eta) + mu (setClosed e eta)) ≤
      mu (setOpen e eta)) (I : Finset E) (A : Set (ConfigSpace E)) :
    c ^ I.card * finiteBoolEventMass mu (finiteBoolForceOpen I ⁻¹' A) ≤
      finiteBoolEventMass mu A := by
  classical
  induction I using Finset.induction with
  | empty =>
      have hpre : finiteBoolForceOpen ∅ ⁻¹' A = A := by
        ext omega
        simp only [Set.mem_preimage]
        rw [finiteBoolForceOpen_empty]
      rw [Finset.card_empty, pow_zero, one_mul, hpre]
  | @insert e I he ih =>
      rw [Finset.card_insert_of_notMem he, pow_succ]
      have hpre : finiteBoolForceOpen (insert e I) ⁻¹' A =
          setOpen e ⁻¹' (finiteBoolForceOpen I ⁻¹' A) := by
        ext omega
        simp only [Set.mem_preimage]
        rw [finiteBoolForceOpen_insert]
      rw [hpre]
      calc
        _ = c ^ I.card *
            (c * finiteBoolEventMass mu
              (setOpen e ⁻¹' (finiteBoolForceOpen I ⁻¹' A))) := by ring
        _ ≤ c ^ I.card * finiteBoolEventMass mu
              (finiteBoolForceOpen I ⁻¹' A) :=
          mul_le_mul_of_nonneg_left
            (finiteBool_c_mul_preimage_setOpen_le_event
              mu hmu c hpair e _) (pow_nonneg hc _)
        _ ≤ finiteBoolEventMass mu A := ih

end FiniteBoolPushforward



theorem fkRectGraphCritical_cFE_mul_preimage_setClosed_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (A : Set (FKRectGraphConfiguration R)) :
    FK.cFE (fkRectCriticalP q) q *
        fkRectGraphCriticalEventMass R q (setClosed e ⁻¹' A) ≤
      fkRectGraphCriticalEventMass R q A := by
  exact finiteBool_c_mul_preimage_setClosed_le_event
    (fun eta => fkRectGraphCriticalRandomClusterProb R q eta)
    (fun eta => fkRectGraphCriticalRandomClusterProb_nonneg R
      (lt_of_lt_of_le zero_lt_one hq) eta)
    (FK.cFE (fkRectCriticalP q) q)
    (fkRectGraphCriticalProb_setClosed_ge R hq) e A



theorem fkRectGraphCritical_cFE_pow_mul_forceClosed_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (A : Set (FKRectGraphConfiguration R)) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectGraphCriticalEventMass R q
          (fkRectGraphForceClosed R I ⁻¹' A) ≤
      fkRectGraphCriticalEventMass R q A := by
  simpa [fkRectGraphCriticalEventMass, fkRectGraphForceClosed,
    finiteBoolEventMass, finiteBoolForceClosed] using
    finiteBool_c_pow_mul_forceClosed_preimage_le_event
      (fun eta => fkRectGraphCriticalRandomClusterProb R q eta)
      (fun eta => fkRectGraphCriticalRandomClusterProb_nonneg R
        (lt_of_lt_of_le zero_lt_one hq) eta)
      (FK.cFE (fkRectCriticalP q) q) (fkRectCritical_cFE_nonneg hq)
      (fkRectGraphCriticalProb_setClosed_ge R hq) I A


def fkRectGraphForceOpen (R : FKRectTorus)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) : FKRectGraphConfiguration R :=
  fun e => if e ∈ I then true else eta e

@[simp] theorem fkRectGraphForceOpen_of_mem
    (R : FKRectTorus)
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (eta : FKRectGraphConfiguration R) {e} (he : e ∈ I) :
    fkRectGraphForceOpen R I eta e = true := by
  simp [fkRectGraphForceOpen, he]

@[simp] theorem fkRectGraphForceOpen_of_not_mem
    (R : FKRectTorus)
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (eta : FKRectGraphConfiguration R) {e} (he : e ∉ I) :
    fkRectGraphForceOpen R I eta e = eta e := by
  simp [fkRectGraphForceOpen, he]



theorem fkRectGraphCritical_cFE_pow_mul_forceOpen_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (A : Set (FKRectGraphConfiguration R)) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectGraphCriticalEventMass R q
          (fkRectGraphForceOpen R I ⁻¹' A) ≤
      fkRectGraphCriticalEventMass R q A := by
  simpa [fkRectGraphCriticalEventMass, fkRectGraphForceOpen,
    finiteBoolEventMass, finiteBoolForceOpen] using
    finiteBool_c_pow_mul_forceOpen_preimage_le_event
      (fun eta => fkRectGraphCriticalRandomClusterProb R q eta)
      (fun eta => fkRectGraphCriticalRandomClusterProb_nonneg R
        (lt_of_lt_of_le zero_lt_one hq) eta)
      (FK.cFE (fkRectCriticalP q) q) (fkRectCritical_cFE_nonneg hq)
      (fkRectGraphCriticalProb_setOpen_ge R hq) I A


def fkRectForceEdgesClosed (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (omega : R.Configuration) : R.Configuration :=
  fun a => if a ∈ I then false else omega a

@[simp] theorem fkRectForceEdgesClosed_of_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (omega : R.Configuration) {a : R.EdgeIndex} (ha : a ∈ I) :
    fkRectForceEdgesClosed R I omega a = false := by
  simp [fkRectForceEdgesClosed, ha]

@[simp] theorem fkRectForceEdgesClosed_of_not_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (omega : R.Configuration) {a : R.EdgeIndex} (ha : a ∉ I) :
    fkRectForceEdgesClosed R I omega a = omega a := by
  simp [fkRectForceEdgesClosed, ha]


def fkRectForceEdgesOpen (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (omega : R.Configuration) : R.Configuration :=
  fun a => if a ∈ I then true else omega a

@[simp] theorem fkRectForceEdgesOpen_of_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (omega : R.Configuration) {a : R.EdgeIndex} (ha : a ∈ I) :
    fkRectForceEdgesOpen R I omega a = true := by
  simp [fkRectForceEdgesOpen, ha]

@[simp] theorem fkRectForceEdgesOpen_of_not_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (omega : R.Configuration) {a : R.EdgeIndex} (ha : a ∉ I) :
    fkRectForceEdgesOpen R I omega a = omega a := by
  simp [fkRectForceEdgesOpen, ha]


def fkRectGraphEdgesOfIndices (R : FKRectTorus)
    (I : Finset R.EdgeIndex) :
    Finset {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
  I.map (fkRectEdgeGraphEquiv R).toEmbedding

@[simp] theorem mem_fkRectGraphEdgesOfIndices
    (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (a : R.EdgeIndex) :
    fkRectEdgeGraphEquiv R a ∈ fkRectGraphEdgesOfIndices R I ↔ a ∈ I := by
  simp [fkRectGraphEdgesOfIndices]

@[simp] theorem fkRectGraphEdgesOfIndices_card
    (R : FKRectTorus) (I : Finset R.EdgeIndex) :
    (fkRectGraphEdgesOfIndices R I).card = I.card := by
  simp [fkRectGraphEdgesOfIndices]


theorem fkRectConfigurationGraphEquiv_forceEdgesClosed
    (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (omega : R.Configuration) :
    fkRectConfigurationGraphEquiv R (fkRectForceEdgesClosed R I omega) =
      fkRectGraphForceClosed R (fkRectGraphEdgesOfIndices R I)
        (fkRectConfigurationGraphEquiv R omega) := by
  funext e
  let a := (fkRectEdgeGraphEquiv R).symm e
  have he : e = fkRectEdgeGraphEquiv R a := by
    exact ((fkRectEdgeGraphEquiv R).apply_symm_apply e).symm
  rw [he]
  by_cases ha : a ∈ I
  · simp [ha]
  · simp [ha]


theorem fkRectConfigurationGraphEquiv_forceEdgesOpen
    (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (omega : R.Configuration) :
    fkRectConfigurationGraphEquiv R (fkRectForceEdgesOpen R I omega) =
      fkRectGraphForceOpen R (fkRectGraphEdgesOfIndices R I)
        (fkRectConfigurationGraphEquiv R omega) := by
  funext e
  let a := (fkRectEdgeGraphEquiv R).symm e
  have he : e = fkRectEdgeGraphEquiv R a := by
    exact ((fkRectEdgeGraphEquiv R).apply_symm_apply e).symm
  rw [he]
  by_cases ha : a ∈ I
  · simp [ha]
  · simp [ha]


def fkRectCriticalEventMass
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) : Real :=
  ∑ omega : R.Configuration,
    A.indicator (fun omega =>
      fkRectCriticalRandomClusterProb R q omega) omega

theorem fkRectCriticalEventMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    0 ≤ fkRectCriticalEventMass R q A := by
  unfold fkRectCriticalEventMass
  apply Finset.sum_nonneg
  intro omega homega
  exact Set.indicator_nonneg
    (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _

theorem fkRectCriticalEventMass_mono
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    {A B : Set R.Configuration} (hAB : A ⊆ B) :
    fkRectCriticalEventMass R q A ≤ fkRectCriticalEventMass R q B := by
  unfold fkRectCriticalEventMass
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (hAB hA)]
  · rw [Set.indicator_of_notMem hA]
    exact Set.indicator_nonneg
      (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _

theorem fkRectCriticalEventMass_cutClosed_eq_closedMass
    (R : FKRectTorus) (q : Real) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta} =
      fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) := by
  classical
  unfold fkRectCriticalEventMass fkRectCriticalClosedMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro eta heta
  by_cases hclosed : FKRectCutClosedConfiguration R eta
  · have hall := (fkRectCutClosedConfiguration_iff R eta).1 hclosed
    have hmem : eta ∈ {eta | FKRectCutClosedConfiguration R eta} := hclosed
    rw [Set.indicator_of_mem hmem, if_pos hall]
  · have hnotall : ¬ ∀ a ∈ fkRectTorusCutEdges R, eta a = false :=
      fun hall => hclosed ((fkRectCutClosedConfiguration_iff R eta).2 hall)
    have hnotmem : eta ∉ {eta | FKRectCutClosedConfiguration R eta} :=
      hclosed
    rw [Set.indicator_of_notMem hnotmem, if_neg hnotall]



def fkRectCriticalCutFreeEventMass
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) : Real :=
  fkRectCriticalEventMass R q
      {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} /
    fkRectCriticalClosedMass R q (fkRectTorusCutEdges R)

theorem fkRectCriticalClosedMass_cut_pos
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    0 < fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) := by
  have hlower := fkRectCritical_cutClosedMass_lower R hq
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq
  exact (pow_pos hc _).trans_le hlower

theorem closedMass_mul_fkRectCriticalCutFreeEventMass
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (A : Set R.Configuration) :
    fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) *
        fkRectCriticalCutFreeEventMass R q A =
      fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := by
  unfold fkRectCriticalCutFreeEventMass
  field_simp [ne_of_gt (fkRectCriticalClosedMass_cut_pos R hq)]

theorem fkRectCriticalCutFreeEventMass_univ
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    fkRectCriticalCutFreeEventMass R q Set.univ = 1 := by
  unfold fkRectCriticalCutFreeEventMass
  rw [show {eta : R.Configuration |
      FKRectCutClosedConfiguration R eta ∧ eta ∈ Set.univ} =
      {eta | FKRectCutClosedConfiguration R eta} by ext; simp]
  rw [fkRectCriticalEventMass_cutClosed_eq_closedMass]
  exact div_self (ne_of_gt (fkRectCriticalClosedMass_cut_pos R hq))


theorem fkRectGraphCriticalEventMass_eq_indexed_preimage
    (R : FKRectTorus) (q : Real)
    (B : Set (FKRectGraphConfiguration R)) :
    fkRectGraphCriticalEventMass R q B =
      fkRectCriticalEventMass R q
        (fkRectConfigurationGraphEquiv R ⁻¹' B) := by
  unfold fkRectGraphCriticalEventMass fkRectCriticalEventMass
  symm
  apply Fintype.sum_equiv (fkRectConfigurationGraphEquiv R)
  intro omega
  by_cases hB : fkRectConfigurationGraphEquiv R omega ∈ B
  · have hpre : omega ∈ fkRectConfigurationGraphEquiv R ⁻¹' B := hB
    rw [Set.indicator_of_mem hpre,
      Set.indicator_of_mem hB]
    exact (fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv
      R q omega).symm
  · have hpre : omega ∉ fkRectConfigurationGraphEquiv R ⁻¹' B := hB
    rw [Set.indicator_of_notMem hpre,
      Set.indicator_of_notMem hB]



theorem fkRectCritical_cFE_pow_mul_forceEdgesClosed_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q
          (fkRectForceEdgesClosed R I ⁻¹' A) ≤
      fkRectCriticalEventMass R q A := by
  let J := fkRectGraphEdgesOfIndices R I
  let B : Set (FKRectGraphConfiguration R) :=
    (fkRectConfigurationGraphEquiv R).symm ⁻¹' A
  have hpush :=
    fkRectGraphCritical_cFE_pow_mul_forceClosed_preimage_le_event
      R hq J B
  rw [show J.card = I.card by simp [J]] at hpush
  rw [fkRectGraphCriticalEventMass_eq_indexed_preimage,
    fkRectGraphCriticalEventMass_eq_indexed_preimage] at hpush
  have hright : fkRectConfigurationGraphEquiv R ⁻¹' B = A := by
    ext omega
    simp [B]
  have hleft : fkRectConfigurationGraphEquiv R ⁻¹'
        (fkRectGraphForceClosed R J ⁻¹' B) =
      fkRectForceEdgesClosed R I ⁻¹' A := by
    ext omega
    simp only [Set.mem_preimage]
    rw [← fkRectConfigurationGraphEquiv_forceEdgesClosed R I omega]
    simp [B]
  rwa [hleft, hright] at hpush



theorem fkRectCritical_cFE_pow_mul_forceEdgesOpen_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q
          (fkRectForceEdgesOpen R I ⁻¹' A) ≤
      fkRectCriticalEventMass R q A := by
  let J := fkRectGraphEdgesOfIndices R I
  let B : Set (FKRectGraphConfiguration R) :=
    (fkRectConfigurationGraphEquiv R).symm ⁻¹' A
  have hpush :=
    fkRectGraphCritical_cFE_pow_mul_forceOpen_preimage_le_event
      R hq J B
  rw [show J.card = I.card by simp [J]] at hpush
  rw [fkRectGraphCriticalEventMass_eq_indexed_preimage,
    fkRectGraphCriticalEventMass_eq_indexed_preimage] at hpush
  have hright : fkRectConfigurationGraphEquiv R ⁻¹' B = A := by
    ext omega
    simp [B]
  have hleft : fkRectConfigurationGraphEquiv R ⁻¹'
        (fkRectGraphForceOpen R J ⁻¹' B) =
      fkRectForceEdgesOpen R I ⁻¹' A := by
    ext omega
    simp only [Set.mem_preimage]
    rw [← fkRectConfigurationGraphEquiv_forceEdgesOpen R I omega]
    simp [B]
  rwa [hleft, hright] at hpush

theorem fkRectForceEdgesClosed_torusCut
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectForceEdgesClosed R (fkRectTorusCutEdges R) omega =
      fkRectForceCutClosed R omega := by
  rfl



theorem fkRectCritical_cutPushforward_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
        fkRectCriticalEventMass R q
          (fkRectForceCutClosed R ⁻¹' A) ≤
      fkRectCriticalEventMass R q A := by
  have hbase :=
    fkRectCritical_cFE_pow_mul_forceEdgesClosed_preimage_le_event
      R hq (fkRectTorusCutEdges R) A
  rw [show fkRectForceEdgesClosed R (fkRectTorusCutEdges R) =
      fkRectForceCutClosed R by
    funext omega
    exact fkRectForceEdgesClosed_torusCut R omega] at hbase
  have hpow : FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) ≤
      FK.cFE (fkRectCriticalP q) q ^
        (fkRectTorusCutEdges R).card :=
    pow_le_pow_of_le_one (fkRectCritical_cFE_nonneg hq)
      (fkRectCritical_cFE_le_one hq)
      (fkRectTorusCutEdges_card_le R)
  exact (mul_le_mul_of_nonneg_right hpow
    (fkRectCriticalEventMass_nonneg R
      (lt_of_lt_of_le zero_lt_one hq) _)).trans hbase

theorem fkRectCriticalZeroTurnAboveMass_eq_eventMass
    (R : FKRectTorus) (q : Real) (L : Nat) :
    fkRectCriticalZeroTurnAboveMass R q L =
      fkRectCriticalEventMass R q
        {omega | L < fkRectZeroTurnLoopCount R omega} := by
  unfold fkRectCriticalZeroTurnAboveMass fkRectCriticalEventMass
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases habove : L < fkRectZeroTurnLoopCount R omega <;>
    simp [Set.indicator, habove]




theorem fkRectCritical_zeroTurnAbove_cut_transfer
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (K : R.Configuration → Nat)
    (htop : ∀ omega : R.Configuration,
      fkRectZeroTurnLoopCount R omega ≤
        2 * R.width + K (fkRectForceCutClosed R omega))
    (n : Nat) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
        fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) ≤
      fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ n < K eta} := by
  let Bad : Set R.Configuration :=
    {omega | 2 * R.width + n < fkRectZeroTurnLoopCount R omega}
  let Crossing : Set R.Configuration :=
    {eta | FKRectCutClosedConfiguration R eta ∧ n < K eta}
  have hsubset : Bad ⊆ fkRectForceCutClosed R ⁻¹' Crossing := by
    intro omega homega
    change FKRectCutClosedConfiguration R
        (fkRectForceCutClosed R omega) ∧
      n < K (fkRectForceCutClosed R omega)
    refine ⟨fkRectCutClosedConfiguration_forceCutClosed R omega, ?_⟩
    have hbound := htop omega
    change 2 * R.width + n < fkRectZeroTurnLoopCount R omega at homega
    omega
  rw [fkRectCriticalZeroTurnAboveMass_eq_eventMass]
  change FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
      fkRectCriticalEventMass R q Bad ≤
    fkRectCriticalEventMass R q Crossing
  calc
    _ ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
          fkRectCriticalEventMass R q
            (fkRectForceCutClosed R ⁻¹' Crossing) :=
      mul_le_mul_of_nonneg_left
        (fkRectCriticalEventMass_mono R
          (lt_of_lt_of_le zero_lt_one hq) hsubset)
        (pow_nonneg (fkRectCritical_cFE_nonneg hq) _)
    _ ≤ fkRectCriticalEventMass R q Crossing :=
      fkRectCritical_cutPushforward_event R hq Crossing

end

end StatMech.FrontierD
