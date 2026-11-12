/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.PottsInfiniteVolume
import Code.IsingFK.FvES

open scoped BigOperators

namespace StatMech
namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]


def pottsBoundaryObservable (q : Nat) (b a : Fin q) : Real :=
  (q : Real) * (if a = b then 1 else 0) - 1

theorem sum_pottsBoundaryObservable (q : Nat) [NeZero q] (b : Fin q) :
    ∑ a : Fin q, pottsBoundaryObservable q b a = 0 := by
  classical
  unfold pottsBoundaryObservable
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

theorem sum_pinned_eq_filterQ
    {C : Type*} [Fintype C] [DecidableEq C] {q : Nat}
    (c0 : C) (b : Fin q) (F : (C → Fin q) → Real) :
    (∑ tau : {tau : C → Fin q // tau c0 = b}, F tau.1) =
      ∑ tau ∈ Finset.univ.filter (fun tau : C → Fin q => tau c0 = b), F tau :=
  (Finset.sum_subtype
    (Finset.univ.filter (fun tau : C → Fin q => tau c0 = b))
    (fun tau => by simp) F).symm

theorem colour_pottsBoundary_cancel
    {C : Type*} [Fintype C] [DecidableEq C]
    (q : Nat) [NeZero q] (b : Fin q) (c0 cx : C) (h : cx ≠ c0) :
    (∑ tau ∈ Finset.univ.filter (fun tau : C → Fin q => tau c0 = b),
      pottsBoundaryObservable q b (tau cx)) = 0 := by
  classical
  rw [← sum_pinned_eq_filterQ c0 b
    (fun tau => pottsBoundaryObservable q b (tau cx))]
  rw [← (pinnedFunEquiv c0 b).symm.sum_comp
    (fun tau : {tau : C → Fin q // tau c0 = b} =>
      pottsBoundaryObservable q b (tau.1 cx))]
  have hval : ∀ g : {c : C // c ≠ c0} → Fin q,
      (fun tau : {tau : C → Fin q // tau c0 = b} =>
        pottsBoundaryObservable q b (tau.1 cx))
          ((pinnedFunEquiv c0 b).symm g) =
        pottsBoundaryObservable q b (g ⟨cx, h⟩) := by
    intro g
    show pottsBoundaryObservable q b (((pinnedFunEquiv c0 b).symm g).1 cx) =
      pottsBoundaryObservable q b (g ⟨cx, h⟩)
    congr 1
    show (if hh : cx = c0 then b else g ⟨cx, hh⟩) = g ⟨cx, h⟩
    rw [dif_neg h]
  rw [Finset.sum_congr rfl (fun g _ => hval g)]
  rw [sum_eval_factor (⟨cx, h⟩ : {c : C // c ≠ c0})
    (pottsBoundaryObservable q b), sum_pottsBoundaryObservable, smul_zero]

theorem colour_pottsBoundary_const
    {C : Type*} [Fintype C] [DecidableEq C]
    (q : Nat) [NeZero q] (b : Fin q) (c0 cx : C) (h : cx = c0) :
    (∑ tau ∈ Finset.univ.filter (fun tau : C → Fin q => tau c0 = b),
      pottsBoundaryObservable q b (tau cx)) =
        ((q : Real) - 1) * (q : Real) ^ (Fintype.card C - 1) := by
  classical
  rw [← sum_pinned_eq_filterQ c0 b
    (fun tau => pottsBoundaryObservable q b (tau cx))]
  have hconst : ∀ tau : {tau : C → Fin q // tau c0 = b},
      pottsBoundaryObservable q b (tau.1 cx) = (q : Real) - 1 := by
    intro tau
    rw [h, tau.2]
    simp [pottsBoundaryObservable]
  rw [Finset.sum_congr rfl (fun tau _ => hconst tau), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, card_pinned c0 b]
  push_cast
  ring

theorem colour_pottsBoundary_sum
    {q : Nat} [NeZero q] (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (v0 : V) (hv0 : bdry v0) (x : V) :
    (∑ sigma ∈ Finset.univ.filter
        (fun sigma : V → Fin q =>
          ConstOnWired G bdry omega sigma ∧ BoundaryFixed bdry b sigma),
      pottsBoundaryObservable q b (sigma x)) =
      if ConnToBdry G bdry omega x then
        ((q : Real) - 1) *
          (q : Real) ^ (Fintype.card (wiredSub G bdry omega).ConnectedComponent - 1)
      else 0 := by
  classical
  have hreindex :
      (∑ sigma ∈ Finset.univ.filter
          (fun sigma : V → Fin q =>
            ConstOnWired G bdry omega sigma ∧ BoundaryFixed bdry b sigma),
        pottsBoundaryObservable q b (sigma x)) =
      ∑ tau ∈ Finset.univ.filter
          (fun tau : (wiredSub G bdry omega).ConnectedComponent → Fin q =>
            tau ((wiredSub G bdry omega).connectedComponentMk v0) = b),
        pottsBoundaryObservable q b
          (tau ((wiredSub G bdry omega).connectedComponentMk x)) := by
    rw [Finset.sum_subtype (p := fun sigma : V → Fin q =>
          ConstOnWired G bdry omega sigma ∧ BoundaryFixed bdry b sigma)
      (Finset.univ.filter (fun sigma : V → Fin q =>
        ConstOnWired G bdry omega sigma ∧ BoundaryFixed bdry b sigma))
      (fun sigma => by simp)
      (fun sigma => pottsBoundaryObservable q b (sigma x))]
    rw [Finset.sum_subtype
      (p := fun tau : (wiredSub G bdry omega).ConnectedComponent → Fin q =>
        tau ((wiredSub G bdry omega).connectedComponentMk v0) = b)
      (Finset.univ.filter
        (fun tau : (wiredSub G bdry omega).ConnectedComponent → Fin q =>
          tau ((wiredSub G bdry omega).connectedComponentMk v0) = b))
      (fun tau => by simp)
      (fun tau => pottsBoundaryObservable q b
        (tau ((wiredSub G bdry omega).connectedComponentMk x)))]
    rw [← (wiredColourEquiv G bdry b omega v0 hv0).sum_comp
      (fun tau => pottsBoundaryObservable q b
        (tau.1 ((wiredSub G bdry omega).connectedComponentMk x)))]
    apply Finset.sum_congr rfl
    intro sigma _
    rw [wiredColourEquiv_apply_val]
  rw [hreindex]
  have hiff := connToBdry_iff_componentMk_eq G bdry v0 hv0 omega x
  by_cases h : (wiredSub G bdry omega).connectedComponentMk x =
      (wiredSub G bdry omega).connectedComponentMk v0
  · rw [if_pos (hiff.mpr h)]
    exact colour_pottsBoundary_const q b _ _ h
  · rw [if_neg (fun hc => h (hiff.mp hc))]
    exact colour_pottsBoundary_cancel q b _ _ h

theorem esWeightWired_pottsBoundary_sum
    {q : Nat} [NeZero q] (b : Fin q) (p : Real)
    (omega : ConfigSpace (Sym2 V)) (v0 : V) (hv0 : bdry v0) (x : V) :
    (∑ sigma : V → Fin q,
      esWeightWired G bdry b p sigma omega *
        pottsBoundaryObservable q b (sigma x)) =
      edgeProduct G p omega *
        (if ConnToBdry G bdry omega x then
          ((q : Real) - 1) *
            (q : Real) ^ (numClustersBC G (boundaryCliqueGraph bdry) omega - 1)
        else 0) := by
  classical
  have hterm : ∀ sigma : V → Fin q,
      esWeightWired G bdry b p sigma omega *
          pottsBoundaryObservable q b (sigma x) =
        (if ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma then
          edgeProduct G p omega else 0) *
            pottsBoundaryObservable q b (sigma x) := by
    intro sigma
    unfold esWeightWired
    rw [esWeight_eq_of_compatible]
    simp only [compatible_iff_constOnOpen]
    by_cases hb : BoundaryFixed bdry b sigma <;>
      by_cases hc : ConstOnOpen G omega sigma <;> simp [hb, hc]
  rw [Finset.sum_congr rfl (fun sigma _ => hterm sigma)]
  rw [Finset.sum_congr rfl (fun sigma _ => by rw [ite_mul, zero_mul])]
  rw [← Finset.sum_filter]
  rw [Finset.sum_congr (Finset.filter_congr (fun sigma _ => by
    rw [constOnOpen_boundaryFixed_iff])) (fun sigma _ => rfl)]
  rw [← Finset.mul_sum, colour_pottsBoundary_sum G bdry b omega v0 hv0 x]
  rw [numClustersBC_eq_card_wiredSub]


noncomputable def wiredConnToBdryProbQ
    (q : Nat) (p : Real) (x : V) : Real :=
  ∑ omega ∈ Finset.univ.filter
      (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
    bcProb G (boundaryCliqueGraph bdry) p (q : Real) omega


noncomputable def esWiredPottsCenteredOnePoint
    (q : Nat) (b : Fin q) (p : Real) (x : V) : Real :=
  (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V → Fin q,
      esWeightWired G bdry b p sigma omega *
        pottsBoundaryObservable q b (sigma x)) /
    esZWired G bdry q b p

theorem esWiredPottsCenteredOnePoint_eq_conn
    (q : Nat) [NeZero q] (b : Fin q) (p : Real) (x v0 : V)
    (hv0 : bdry v0) :
    esWiredPottsCenteredOnePoint G bdry q b p x =
      ((q : Real) - 1) * wiredConnToBdryProbQ G bdry q p x := by
  classical
  unfold esWiredPottsCenteredOnePoint wiredConnToBdryProbQ
  have hk : ∀ omega : ConfigSpace (Sym2 V),
      1 ≤ numClustersBC G (boundaryCliqueGraph bdry) omega :=
    fun omega => one_le_numClustersBC G bdry v0 omega
  have hnum : (q : Real) *
      (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V → Fin q,
        esWeightWired G bdry b p sigma omega *
          pottsBoundaryObservable q b (sigma x)) =
      ((q : Real) - 1) *
        (∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
          bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega) := by
    rw [Finset.mul_sum]
    have hterm : ∀ omega : ConfigSpace (Sym2 V),
        (q : Real) * (∑ sigma : V → Fin q,
          esWeightWired G bdry b p sigma omega *
            pottsBoundaryObservable q b (sigma x)) =
        if ConnToBdry G bdry omega x then
          ((q : Real) - 1) *
            bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega
        else 0 := by
      intro omega
      rw [esWeightWired_pottsBoundary_sum G bdry b p omega v0 hv0 x]
      by_cases hconn : ConnToBdry G bdry omega x
      · rw [if_pos hconn, if_pos hconn]
        have hweight := esWeightWired_sum_spins_eq_bcWeight
          G bdry b p omega v0 hv0 (hk omega)
        rw [esWeightWired_sum_spins] at hweight
        have hcard :
            ((Finset.univ.filter (fun sigma : V → Fin q =>
              ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma)).card : Real) =
              (q : Real) ^
                (numClustersBC G (boundaryCliqueGraph bdry) omega - 1) := by
          have hN := card_constOnOpen_boundaryFixed G bdry b omega v0 hv0
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hN
          rw [hN]
          push_cast
          rfl
        rw [hcard] at hweight
        nlinarith
      · rw [if_neg hconn, if_neg hconn, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun omega _ => hterm omega)]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x)]
    have hzero : (∑ omega ∈ Finset.univ.filter
        (fun omega : ConfigSpace (Sym2 V) => ¬ ConnToBdry G bdry omega x),
        (if ConnToBdry G bdry omega x then
          ((q : Real) - 1) *
            bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega
        else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro omega homega
      rw [if_neg (Finset.mem_filter.1 homega).2]
    rw [hzero, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro omega homega
    rw [if_pos (Finset.mem_filter.1 homega).2]
  have hden : (q : Real) * esZWired G bdry q b p =
      bcZ G (boundaryCliqueGraph bdry) p (q : Real) :=
    esZWired_eq_bcZ G bdry b p v0 hv0 hk
  have hq : (q : Real) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [show (∑ omega ∈ Finset.univ.filter
      (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
      bcProb G (boundaryCliqueGraph bdry) p (q : Real) omega) =
        (∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
          bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega) /
            bcZ G (boundaryCliqueGraph bdry) p (q : Real) by
    unfold bcProb
    rw [Finset.sum_div]]
  calc
    (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V → Fin q,
        esWeightWired G bdry b p sigma omega *
          pottsBoundaryObservable q b (sigma x)) /
        esZWired G bdry q b p =
      ((q : Real) * (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V → Fin q,
        esWeightWired G bdry b p sigma omega *
          pottsBoundaryObservable q b (sigma x))) /
        ((q : Real) * esZWired G bdry q b p) :=
          (mul_div_mul_left _ _ hq).symm
    _ = (((q : Real) - 1) *
        (∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
          bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega)) /
        bcZ G (boundaryCliqueGraph bdry) p (q : Real) := by rw [hnum, hden]
    _ = ((q : Real) - 1) *
        ((∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
          bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega) /
        bcZ G (boundaryCliqueGraph bdry) p (q : Real)) := by ring


noncomputable def pottsBoundaryProbWired
    (q : Nat) (b : Fin q) (beta J : Real) (x : V) : Real :=
  ∑ sigma : V → Fin q,
    pottsProbWired G bdry q b beta J sigma *
      (if sigma x = b then 1 else 0)

theorem esWiredPottsCenteredOnePoint_eq_potts
    (q : Nat) [NeZero q] (b : Fin q) (beta J : Real) (x : V) :
    esWiredPottsCenteredOnePoint G bdry q b
        (1 - Real.exp (-(beta * J))) x =
      ∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          pottsBoundaryObservable q b (sigma x) := by
  classical
  unfold esWiredPottsCenteredOnePoint
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [← esWiredFirstMarginal_eq_pottsProbWired G bdry b beta J sigma]
  unfold esWiredFirstMarginal
  rw [← Finset.sum_mul]
  ring

theorem pottsBoundaryObservable_expectation
    (q : Nat) [NeZero q] (b : Fin q) (beta J : Real) (x : V) :
    (∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          pottsBoundaryObservable q b (sigma x)) =
      (q : Real) * pottsBoundaryProbWired G bdry q b beta J x - 1 := by
  classical
  unfold pottsBoundaryObservable pottsBoundaryProbWired
  calc
    ∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          ((q : Real) * (if sigma x = b then 1 else 0) - 1) =
      ∑ sigma : V → Fin q,
        ((q : Real) * (pottsProbWired G bdry q b beta J sigma *
          (if sigma x = b then 1 else 0)) -
            pottsProbWired G bdry q b beta J sigma) := by
      apply Finset.sum_congr rfl
      intro sigma _
      ring
    _ = (q : Real) * (∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          (if sigma x = b then 1 else 0)) -
        ∑ sigma : V → Fin q, pottsProbWired G bdry q b beta J sigma := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (q : Real) * (∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          (if sigma x = b then 1 else 0)) - 1 := by
      rw [pottsProbWired_sum_eq_one]


theorem pottsBoundaryProbWired_sub_inv_eq_conn
    (q : Nat) [NeZero q] (b : Fin q) (beta J : Real) (x v0 : V)
    (hv0 : bdry v0) :
    pottsBoundaryProbWired G bdry q b beta J x - 1 / (q : Real) =
      ((q : Real) - 1) / q *
        wiredConnToBdryProbQ G bdry q
          (1 - Real.exp (-(beta * J))) x := by
  have hcenter := (esWiredPottsCenteredOnePoint_eq_potts
    G bdry q b beta J x).symm.trans
      (esWiredPottsCenteredOnePoint_eq_conn G bdry q b
        (1 - Real.exp (-(beta * J))) x v0 hv0)
  rw [pottsBoundaryObservable_expectation G bdry q b beta J x] at hcenter
  have hq : (q : Real) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp
  nlinarith

theorem wiredConnToBdryProbQ_eq_wiredFkProb_sum
    (q : Nat) (p : Real) (x : V) :
    wiredConnToBdryProbQ G bdry q p x =
      ∑ omega ∈ Finset.univ.filter
        (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
        wiredFkProb G bdry p (q : Real) omega := by
  unfold wiredConnToBdryProbQ
  exact Finset.sum_congr rfl (fun omega _ =>
    (wiredFkProb_eq_bcProb G bdry p (q : Real) omega).symm)


end IsingFK
end StatMech
