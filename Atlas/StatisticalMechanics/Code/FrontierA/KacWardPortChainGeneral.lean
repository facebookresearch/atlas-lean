/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAcyclicElimination
import Code.FrontierA.KacWardStraightLineEmbedding
import Mathlib.Data.Finset.Sort










open scoped BigOperators

namespace StatMech.FrontierA

open SimpleGraph Finset


def kwPortChainState {n : ℕ} (b : Fin n → Fin 2) : Fin (n + 1) → Fin 2 :=
  (List.Vector.scanl (fun x bit : Fin 2 ↦ x + bit) (0 : Fin 2)
    (List.Vector.ofFn b)).get



def KWPortChainEven {n : ℕ} (b : Fin n → Fin 2)
    (y : Fin (n + 1) → Fin 2) : Prop :=
  y 0 = 0 ∧
    (∀ i : Fin n, y i.succ = y i.castSucc + b i) ∧
    y (Fin.last n) = 0

theorem kwPortChainState_zero {n : ℕ} (b : Fin n → Fin 2) :
    kwPortChainState b 0 = 0 := by
  unfold kwPortChainState
  rw [List.Vector.get_zero, List.Vector.scanl_head]

theorem kwPortChainState_succ {n : ℕ} (b : Fin n → Fin 2)
    (i : Fin n) :
    kwPortChainState b i.succ = kwPortChainState b i.castSucc + b i := by
  unfold kwPortChainState
  simpa only [List.Vector.get_ofFn] using
    List.Vector.scanl_get (fun x bit : Fin 2 ↦ x + bit) (0 : Fin 2)
      (List.Vector.ofFn b) i


theorem kwPortChainState_unique {n : ℕ} (b : Fin n → Fin 2)
    (y : Fin (n + 1) → Fin 2) (hy0 : y 0 = 0)
    (hrec : ∀ i : Fin n, y i.succ = y i.castSucc + b i) :
    y = kwPortChainState b := by
  funext k
  induction k using Fin.induction with
  | zero => rw [hy0, kwPortChainState_zero]
  | succ i ih =>
      rw [hrec i, kwPortChainState_succ, ih]

theorem kw_fin_two_self_add (x : Fin 2) : x + x = 0 := by
  fin_cases x <;> decide



theorem kwPortChain_sum_eq_endpoints {n : ℕ} (b : Fin n → Fin 2)
    (y : Fin (n + 1) → Fin 2)
    (hrec : ∀ i : Fin n, y i.succ = y i.castSucc + b i) :
    (∑ i, b i) = y 0 + y (Fin.last n) := by
  have hb (i : Fin n) : b i = y i.succ + y i.castSucc := by
    have h := hrec i
    calc
      b i = b i + 0 := (add_zero _).symm
      _ = b i + (y i.castSucc + y i.castSucc) := by
        rw [kw_fin_two_self_add]
      _ = (y i.castSucc + b i) + y i.castSucc := by ac_rfl
      _ = y i.succ + y i.castSucc := by rw [h]
  rw [Finset.sum_congr rfl (fun i _ ↦ hb i), Finset.sum_add_distrib]
  have hsucc := Fin.sum_univ_succ y
  have hcast := Fin.sum_univ_castSucc y
  have hmiddle :
      (∑ i : Fin n, y i.succ) + ∑ i : Fin n, y i.castSucc =
        y 0 + y (Fin.last n) := by
    let A := ∑ i : Fin n, y i.succ
    let B := ∑ i : Fin n, y i.castSucc
    have hab : y 0 + A = B + y (Fin.last n) := by
      calc
        y 0 + A = ∑ i : Fin (n + 1), y i := hsucc.symm
        _ = B + y (Fin.last n) := hcast
    change A + B = y 0 + y (Fin.last n)
    calc
      A + B = (y 0 + (y 0 + A)) + B := by
        rw [← add_assoc, kw_fin_two_self_add, zero_add]
      _ = (y 0 + (B + y (Fin.last n))) + B := by rw [hab]
      _ = y 0 + y (Fin.last n) := by
        rw [add_assoc, add_assoc, add_comm (y (Fin.last n)) B,
          ← add_assoc B B, kw_fin_two_self_add, zero_add]
  exact hmiddle



theorem kwPortChainState_last_eq_zero_iff {n : ℕ} (b : Fin n → Fin 2) :
    kwPortChainState b (Fin.last n) = 0 ↔ (∑ i, b i) = 0 := by
  have hsum := kwPortChain_sum_eq_endpoints b (kwPortChainState b)
    (kwPortChainState_succ b)
  rw [kwPortChainState_zero, zero_add] at hsum
  rw [hsum]



theorem kwPortChain_existsUnique {n : ℕ} (b : Fin n → Fin 2) :
    (∑ i, b i) = 0 ↔ ∃! y : Fin (n + 1) → Fin 2,
      KWPortChainEven b y := by
  constructor
  · intro heven
    refine ⟨kwPortChainState b, ?_, ?_⟩
    · exact ⟨kwPortChainState_zero b, kwPortChainState_succ b,
        (kwPortChainState_last_eq_zero_iff b).2 heven⟩
    · intro y hy
      exact kwPortChainState_unique b y hy.1 hy.2.1
  · rintro ⟨y, hy, -⟩
    have hsum := kwPortChain_sum_eq_endpoints b y hy.2.1
    rw [hy.1, hy.2.2, add_zero] at hsum
    exact hsum




abbrev KWOutgoingDart
    {V : Type*} {G : SimpleGraph V} (v : V) :=
  {d : G.Dart // d.fst = v}



noncomputable def kwDartPortIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : G.Dart) :
    Fin (Fintype.card (KWOutgoingDart (G := G) d.fst)) :=
  Fintype.equivFin (KWOutgoingDart (G := G) d.fst) ⟨d, rfl⟩


def KWDartPort
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  Σ v : V, Fin (Fintype.card (KWOutgoingDart (G := G) v))


noncomputable def kwDartPortEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : KWDartPort G ≃ G.Dart :=
  (Equiv.sigmaCongrRight fun v ↦
    (Fintype.equivFin (KWOutgoingDart (G := G) v)).symm).trans
      (Equiv.sigmaFiberEquiv fun d : G.Dart ↦ d.fst)


noncomputable def kwDartOfPort
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : KWDartPort G → G.Dart :=
  kwDartPortEquiv G


noncomputable def kwPortOfDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : G.Dart → KWDartPort G :=
  (kwDartPortEquiv G).symm

@[simp] theorem kwDartOfPort_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : KWDartPort G) :
    (kwDartOfPort G p).fst = p.1 := by
  rcases p with ⟨v, i⟩
  change (((Fintype.equivFin (KWOutgoingDart (G := G) v)).symm i).1).fst = v
  exact ((Fintype.equivFin (KWOutgoingDart (G := G) v)).symm i).2

@[simp] theorem kwDartOfPort_portOfDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : G.Dart) :
    kwDartOfPort G (kwPortOfDart G d) = d :=
  (kwDartPortEquiv G).apply_symm_apply d

@[simp] theorem kwPortOfDart_dartOfPort
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : KWDartPort G) :
    kwPortOfDart G (kwDartOfPort G p) = p :=
  (kwDartPortEquiv G).symm_apply_apply p

noncomputable instance KWDartPort_fintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (KWDartPort G) :=
  Fintype.ofEquiv G.Dart (kwDartPortEquiv G).symm

noncomputable instance KWDartPort_decidableEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableEq (KWDartPort G) :=
  Classical.decEq _

theorem kwDartOfPort_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Injective (kwDartOfPort G) :=
  (kwDartPortEquiv G).injective

theorem kwDartPort_eq_of_fst_of_val
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : KWDartPort G}
    (hfst : p.1 = q.1) (hidx : p.2.val = q.2.val) : p = q := by
  rcases p with ⟨v, i⟩
  rcases q with ⟨w, j⟩
  dsimp only at hfst hidx
  subst w
  congr
  exact Fin.ext hidx




noncomputable def kwDartPortSplitGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph (KWDartPort G) where
  Adj p q :=
    kwDartOfPort G q = (kwDartOfPort G p).symm ∨
      (p.1 = q.1 ∧
        (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val))
  symm := by
    intro p q h
    rcases h with h | ⟨hfst, hidx⟩
    · left
      rw [h]
      exact (kwDartOfPort G p).symm_symm.symm
    · right
      exact ⟨hfst.symm, hidx.symm⟩
  loopless := ⟨by
    intro p h
    rcases h with h | ⟨-, hidx⟩
    · exact (kwDartOfPort G p).symm_ne h.symm
    · omega⟩

noncomputable instance kwDartPortSplitGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (kwDartPortSplitGraph G).Adj :=
  Classical.decRel _

@[simp] theorem kwDartPortSplitGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : KWDartPort G) :
    (kwDartPortSplitGraph G).Adj p q ↔
      kwDartOfPort G q = (kwDartOfPort G p).symm ∨
        (p.1 = q.1 ∧
          (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) :=
  Iff.rfl



theorem kwDartPortSplitGraph_degree_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : KWDartPort G) :
    (kwDartPortSplitGraph G).degree p ≤ 3 := by
  classical
  let code : (kwDartPortSplitGraph G).neighborSet p → Fin 3 := fun q ↦
    if kwDartOfPort G q.1 = (kwDartOfPort G p).symm then 0
    else if q.1.2.val + 1 = p.2.val then 1
    else 2
  have hcode : Function.Injective code := by
    intro q r hqr
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    simp only [code] at hqr
    rw [SimpleGraph.mem_neighborSet, kwDartPortSplitGraph_adj] at hq hr
    by_cases hqext : kwDartOfPort G q = (kwDartOfPort G p).symm
    · have hrext : kwDartOfPort G r = (kwDartOfPort G p).symm := by
        by_contra hne
        simp only [hqext, ↓reduceIte, hne] at hqr
        split at hqr <;> omega
      apply Subtype.ext
      exact kwDartOfPort_injective G (hqext.trans hrext.symm)
    · by_cases hrext : kwDartOfPort G r = (kwDartOfPort G p).symm
      · simp only [hqext, hrext, ↓reduceIte] at hqr
        split at hqr <;> omega
      · have hqdata := hq.resolve_left hqext
        have hrdata := hr.resolve_left hrext
        by_cases hqpred : q.2.val + 1 = p.2.val
        · have hrpred : r.2.val + 1 = p.2.val := by
            by_contra hne
            simp [hqext, hrext, hqpred, hne] at hqr
          apply Subtype.ext
          apply kwDartPort_eq_of_fst_of_val G
              (hqdata.1.symm.trans hrdata.1)
          omega
        · have hrpred : ¬(r.2.val + 1 = p.2.val) := by
            intro hp
            simp [hqext, hrext, hqpred, hp] at hqr
          have hqsucc : p.2.val + 1 = q.2.val :=
            hqdata.2.resolve_right hqpred
          have hrsucc : p.2.val + 1 = r.2.val :=
            hrdata.2.resolve_right hrpred
          apply Subtype.ext
          apply kwDartPort_eq_of_fst_of_val G
              (hqdata.1.symm.trans hrdata.1)
          omega
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective code hcode






def KWPortOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (v : V) → Equiv.Perm (Fin (Fintype.card (KWOutgoingDart (G := G) v)))

def kwIdentityPortOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : KWPortOrder G :=
  fun _ ↦ Equiv.refl _




noncomputable def kwAngularPortOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : KWPortOrder G := fun v ↦ by
  let key : KWOutgoingDart (G := G) v → ℝ ×ₗ ℕ := fun d ↦
    toLex ((embedding.dartAngle d.1).toReal,
      (Fintype.equivFin (KWOutgoingDart (G := G) v) d).val)
  have hkey : Function.Injective key := by
    intro d e h
    apply (Fintype.equivFin (KWOutgoingDart (G := G) v)).injective
    apply Fin.ext
    exact congrArg (fun z ↦ (ofLex z).2) h
  letI : LinearOrder (KWOutgoingDart (G := G) v) :=
    LinearOrder.lift' key hkey
  exact (Fintype.equivFin (KWOutgoingDart (G := G) v)).symm |>.trans
    (Fintype.orderIsoFinOfCardEq (KWOutgoingDart (G := G) v) rfl).symm

def kwOrderedPortRank
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) : ℕ :=
  (order p.1 p.2).val



theorem KWStraightLineEmbedding.outgoing_dartAngle_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {d e : G.Dart}
    (hfst : d.fst = e.fst) (hne : d ≠ e) :
    embedding.dartAngle d ≠ embedding.dartAngle e := by
  have hedge : d.edge ≠ e.edge := by
    intro h
    rw [SimpleGraph.dart_edge_eq_iff] at h
    rcases h with h | h
    · exact hne h
    · have := congrArg (fun delta : G.Dart ↦ delta.fst) h
      apply e.fst_ne_snd
      simpa [hfst] using this.symm
  have hadj : G.DartAdj d.symm e := by
    change d.symm.snd = e.fst
    simp [hfst]
  have hnon := embedding.nonantipodal_of_nonbacktracking d.symm e hadj (by
    simpa using hedge)
  intro hangle
  apply hnon
  rw [embedding.dartAngle_symm, ← hangle]
  simp




theorem kwAngularPortOrder_rank_lt_of_angle_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {p q : KWDartPort G}
    (hfst : p.1 = q.1)
    (hangle : (embedding.dartAngle (kwDartOfPort G p)).toReal <
      (embedding.dartAngle (kwDartOfPort G q)).toReal) :
    kwOrderedPortRank (kwAngularPortOrder embedding) p <
      kwOrderedPortRank (kwAngularPortOrder embedding) q := by
  rcases p with ⟨v, i⟩
  rcases q with ⟨w, j⟩
  dsimp only at hfst ⊢
  subst w
  let outgoing := KWOutgoingDart (G := G) v
  let key : outgoing → ℝ ×ₗ ℕ := fun d ↦
    toLex ((embedding.dartAngle d.1).toReal,
      (Fintype.equivFin outgoing d).val)
  have hkey : Function.Injective key := by
    intro d e h
    apply (Fintype.equivFin outgoing).injective
    apply Fin.ext
    exact congrArg (fun z ↦ (ofLex z).2) h
  letI : LinearOrder outgoing := LinearOrder.lift' key hkey
  let oi := Fintype.orderIsoFinOfCardEq outgoing rfl
  have hdart :
      (Fintype.equivFin outgoing).symm i <
        (Fintype.equivFin outgoing).symm j := by
    change key ((Fintype.equivFin outgoing).symm i) <
      key ((Fintype.equivFin outgoing).symm j)
    rw [Prod.Lex.toLex_lt_toLex]
    left
    simpa only [outgoing, key, kwDartOfPort, kwDartPortEquiv] using hangle
  change (oi.symm ((Fintype.equivFin outgoing).symm i)).val <
    (oi.symm ((Fintype.equivFin outgoing).symm j)).val
  exact (oi.symm.lt_iff_lt).2 hdart

theorem kwAngularPortOrder_rank_lt_iff_angle_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {p q : KWDartPort G}
    (hfst : p.1 = q.1) :
    kwOrderedPortRank (kwAngularPortOrder embedding) p <
        kwOrderedPortRank (kwAngularPortOrder embedding) q ↔
      (embedding.dartAngle (kwDartOfPort G p)).toReal <
        (embedding.dartAngle (kwDartOfPort G q)).toReal := by
  constructor
  · intro hrank
    have hpq : p ≠ q := by
      intro h
      subst q
      omega
    have hdart : kwDartOfPort G p ≠ kwDartOfPort G q :=
      (kwDartOfPort_injective G).ne hpq
    have hangle := embedding.outgoing_dartAngle_ne
      (kwDartOfPort_fst G p |>.trans (hfst.trans (kwDartOfPort_fst G q).symm))
      hdart
    have hreal : (embedding.dartAngle (kwDartOfPort G p)).toReal ≠
        (embedding.dartAngle (kwDartOfPort G q)).toReal := by
      intro h
      apply hangle
      rw [← Real.Angle.coe_toReal (embedding.dartAngle (kwDartOfPort G p)),
        ← Real.Angle.coe_toReal (embedding.dartAngle (kwDartOfPort G q)), h]
    rcases lt_or_gt_of_ne hreal with hlt | hgt
    · exact hlt
    · have hreverse := kwAngularPortOrder_rank_lt_of_angle_lt embedding
          hfst.symm hgt
      omega
  · exact kwAngularPortOrder_rank_lt_of_angle_lt embedding hfst



theorem kw_oppositeTurn_toReal_of_lt (a b : Real.Angle)
    (h : a.toReal < b.toReal) :
    (b - (a + (Real.pi : Real.Angle))).toReal =
      b.toReal - a.toReal - Real.pi := by
  have hcoe : ((b.toReal - a.toReal - Real.pi : ℝ) : Real.Angle) =
      b - (a + (Real.pi : Real.Angle)) := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_sub,
      Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    abel
  rw [← hcoe]
  apply Real.Angle.toReal_coe_eq_self_iff.mpr
  constructor
  · linarith
  · nlinarith [Real.Angle.neg_pi_lt_toReal a,
      Real.Angle.toReal_le_pi b, Real.pi_pos]



theorem kw_oppositeTurn_toReal_of_gt (a b : Real.Angle)
    (h : b.toReal < a.toReal) :
    (b - (a + (Real.pi : Real.Angle))).toReal =
      b.toReal - a.toReal + Real.pi := by
  have hcoe : ((b.toReal - a.toReal + Real.pi : ℝ) : Real.Angle) =
      b - (a + (Real.pi : Real.Angle)) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_sub,
      Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    rw [← Real.Angle.sub_coe_pi_eq_add_coe_pi]
    abel
  rw [← hcoe]
  apply Real.Angle.toReal_coe_eq_self_iff.mpr
  constructor
  · nlinarith [Real.Angle.neg_pi_lt_toReal b,
      Real.Angle.toReal_le_pi a, Real.pi_pos]
  · linarith



noncomputable def kwPortAngleRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) : ℂ :=
  Complex.exp
    ((((embedding.dartAngle (kwDartOfPort G p)).toReal : ℂ) * Complex.I) / 2)

theorem kwPortAngleRoot_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) :
    kwPortAngleRoot embedding p ≠ 0 :=
  Complex.exp_ne_zero _



theorem KWStraightLineEmbedding.turnPhase_eq_portRoots_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G d.symm) <
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e)) :
    embedding.turnPhase d e =
      -Complex.I * (kwPortAngleRoot embedding (kwPortOfDart G d.symm))⁻¹ *
        kwPortAngleRoot embedding (kwPortOfDart G e) := by
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  have hpfirst : p.1 = d.snd := by
    have h := kwDartOfPort_fst G p
    simpa [p] using h.symm
  have hqfirst : q.1 = e.fst := by
    have h := kwDartOfPort_fst G q
    simpa [q] using h.symm
  have hreal : (embedding.dartAngle (kwDartOfPort G p)).toReal <
      (embedding.dartAngle (kwDartOfPort G q)).toReal := by
    apply (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
      (hpfirst.trans (hde.trans hqfirst.symm))).1
    exact hrank
  have hdangle : embedding.dartAngle d =
      embedding.dartAngle (kwDartOfPort G p) + (Real.pi : Real.Angle) := by
    simpa [p] using embedding.dartAngle_symm d.symm
  rw [← embedding.principalPhase_eq_turnPhase d e]
  unfold kwPrincipalHalfAnglePhase kwPortAngleRoot
  rw [hdangle, show embedding.dartAngle e =
      embedding.dartAngle (kwDartOfPort G q) by simp [q],
    kw_oppositeTurn_toReal_of_lt _ _ hreal]
  have hcalc :
      (((((embedding.dartAngle (kwDartOfPort G q)).toReal -
        (embedding.dartAngle (kwDartOfPort G p)).toReal - Real.pi : ℝ) : ℂ) *
          Complex.I) / 2) =
      (-(Real.pi : ℂ) / 2 * Complex.I) +
        (-((((embedding.dartAngle (kwDartOfPort G p)).toReal : ℂ) *
          Complex.I) / 2)) +
        (((embedding.dartAngle (kwDartOfPort G q)).toReal : ℂ) *
          Complex.I) / 2 := by
    push_cast
    ring
  rw [hcalc]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_neg,
    Complex.exp_neg_pi_div_two_mul_I]



theorem KWStraightLineEmbedding.turnPhase_eq_portRoots_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e) <
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G d.symm)) :
    embedding.turnPhase d e =
      Complex.I * (kwPortAngleRoot embedding (kwPortOfDart G d.symm))⁻¹ *
        kwPortAngleRoot embedding (kwPortOfDart G e) := by
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  have hpfirst : p.1 = d.snd := by
    have h := kwDartOfPort_fst G p
    simpa [p] using h.symm
  have hqfirst : q.1 = e.fst := by
    have h := kwDartOfPort_fst G q
    simpa [q] using h.symm
  have hreal : (embedding.dartAngle (kwDartOfPort G q)).toReal <
      (embedding.dartAngle (kwDartOfPort G p)).toReal := by
    apply (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
      (hqfirst.trans (hde.symm.trans hpfirst.symm))).1
    exact hrank
  have hdangle : embedding.dartAngle d =
      embedding.dartAngle (kwDartOfPort G p) + (Real.pi : Real.Angle) := by
    simpa [p] using embedding.dartAngle_symm d.symm
  rw [← embedding.principalPhase_eq_turnPhase d e]
  unfold kwPrincipalHalfAnglePhase kwPortAngleRoot
  rw [hdangle, show embedding.dartAngle e =
      embedding.dartAngle (kwDartOfPort G q) by simp [q],
    kw_oppositeTurn_toReal_of_gt _ _ hreal]
  have hcalc :
      (((((embedding.dartAngle (kwDartOfPort G q)).toReal -
        (embedding.dartAngle (kwDartOfPort G p)).toReal + Real.pi : ℝ) : ℂ) *
          Complex.I) / 2) =
      (((Real.pi : ℂ) / 2) * Complex.I) +
        (-((((embedding.dartAngle (kwDartOfPort G p)).toReal : ℂ) *
          Complex.I) / 2)) +
        (((embedding.dartAngle (kwDartOfPort G q)).toReal : ℂ) *
          Complex.I) / 2 := by
    push_cast
    ring
  rw [hcalc]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_neg,
    Complex.exp_pi_div_two_mul_I]


noncomputable def kwOrderedDartPortSplitGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) : SimpleGraph (KWDartPort G) where
  Adj p q :=
    kwDartOfPort G q = (kwDartOfPort G p).symm ∨
      (p.1 = q.1 ∧
        (kwOrderedPortRank order p + 1 = kwOrderedPortRank order q ∨
          kwOrderedPortRank order q + 1 = kwOrderedPortRank order p))
  symm := by
    intro p q h
    rcases h with h | ⟨hfst, hidx⟩
    · left
      rw [h]
      exact (kwDartOfPort G p).symm_symm.symm
    · right
      exact ⟨hfst.symm, hidx.symm⟩
  loopless := ⟨by
    intro p h
    rcases h with h | ⟨-, hidx⟩
    · exact (kwDartOfPort G p).symm_ne h.symm
    · omega⟩

noncomputable instance kwOrderedDartPortSplitGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) :
    DecidableRel (kwOrderedDartPortSplitGraph G order).Adj :=
  Classical.decRel _

noncomputable instance kwOrderedDartPortSplitGraph_dart_decidableEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    DecidableEq (kwOrderedDartPortSplitGraph G order).Dart :=
  Classical.decEq _

@[simp] theorem kwOrderedDartPortSplitGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p q : KWDartPort G) :
    (kwOrderedDartPortSplitGraph G order).Adj p q ↔
      kwDartOfPort G q = (kwDartOfPort G p).symm ∨
        (p.1 = q.1 ∧
          (kwOrderedPortRank order p + 1 = kwOrderedPortRank order q ∨
            kwOrderedPortRank order q + 1 = kwOrderedPortRank order p)) :=
  Iff.rfl



def KWOrderedExternalSplitDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :=
  {delta : (kwOrderedDartPortSplitGraph G order).Dart //
    kwDartOfPort G delta.snd = (kwDartOfPort G delta.fst).symm}



noncomputable def kwOrderedExternalSplitDartOfDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : G.Dart) : KWOrderedExternalSplitDart G order := by
  let p := kwPortOfDart G d
  let q := kwPortOfDart G d.symm
  have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q := by
    rw [kwOrderedDartPortSplitGraph_adj]
    left
    simp [p, q]
  refine ⟨⟨(p, q), hpq⟩, ?_⟩
  simp [p, q]

@[simp] theorem kwOrderedExternalSplitDartOfDart_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : G.Dart) :
    (kwOrderedExternalSplitDartOfDart G order d).1.fst =
      kwPortOfDart G d := by
  rfl

@[simp] theorem kwOrderedExternalSplitDartOfDart_snd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : G.Dart) :
    (kwOrderedExternalSplitDartOfDart G order d).1.snd =
      kwPortOfDart G d.symm := by
  rfl


noncomputable def kwOrderedExternalSplitDartEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    G.Dart ≃ KWOrderedExternalSplitDart G order where
  toFun := kwOrderedExternalSplitDartOfDart G order
  invFun delta := kwDartOfPort G delta.1.fst
  left_inv d := by simp
  right_inv delta := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · simp
    · have hmatch := delta.2
      apply kwDartOfPort_injective G
      simpa using hmatch.symm


def KWOrderedInternalSplitDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :=
  {delta : (kwOrderedDartPortSplitGraph G order).Dart //
    ¬kwDartOfPort G delta.snd = (kwDartOfPort G delta.fst).symm}

noncomputable instance KWOrderedInternalSplitDart_decidableEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    DecidableEq (KWOrderedInternalSplitDart G order) :=
  Classical.decEq _

noncomputable instance KWOrderedInternalSplitDart_fintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    Fintype (KWOrderedInternalSplitDart G order) := by
  classical
  unfold KWOrderedInternalSplitDart
  infer_instance


noncomputable def kwOrderedSplitDartPartitionEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWOrderedExternalSplitDart G order ⊕
        KWOrderedInternalSplitDart G order ≃
      (kwOrderedDartPortSplitGraph G order).Dart := by
  classical
  exact Equiv.sumCompl (fun delta :
      (kwOrderedDartPortSplitGraph G order).Dart ↦
    kwDartOfPort G delta.snd = (kwDartOfPort G delta.fst).symm)



noncomputable def kwOrderedSplitDartBlockEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    G.Dart ⊕ KWOrderedInternalSplitDart G order ≃
      (kwOrderedDartPortSplitGraph G order).Dart :=
  (Equiv.sumCongr (kwOrderedExternalSplitDartEquiv G order) (Equiv.refl _)).trans
    (kwOrderedSplitDartPartitionEquiv G order)

@[simp] theorem kwOrderedSplitDartBlockEquiv_inl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : G.Dart) :
    kwOrderedSplitDartBlockEquiv G order (Sum.inl d) =
      (kwOrderedExternalSplitDartOfDart G order d).1 := by
  rfl

@[simp] theorem kwOrderedSplitDartBlockEquiv_inr
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) :
    kwOrderedSplitDartBlockEquiv G order (Sum.inr d) = d.1 := by
  rfl



noncomputable def kwOrderedSplitTransitionInBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (M : Matrix (kwOrderedDartPortSplitGraph G order).Dart
      (kwOrderedDartPortSplitGraph G order).Dart ℂ) :
    Matrix (G.Dart ⊕ KWOrderedInternalSplitDart G order)
      (G.Dart ⊕ KWOrderedInternalSplitDart G order) ℂ :=
  Matrix.reindex (kwOrderedSplitDartBlockEquiv G order).symm
    (kwOrderedSplitDartBlockEquiv G order).symm M

theorem kwOrderedSplitTransitionInBlocks_eq_fromBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (M : Matrix (kwOrderedDartPortSplitGraph G order).Dart
      (kwOrderedDartPortSplitGraph G order).Dart ℂ) :
    kwOrderedSplitTransitionInBlocks G order M = Matrix.fromBlocks
      (kwOrderedSplitTransitionInBlocks G order M).toBlocks₁₁
      (kwOrderedSplitTransitionInBlocks G order M).toBlocks₁₂
      (kwOrderedSplitTransitionInBlocks G order M).toBlocks₂₁
      (kwOrderedSplitTransitionInBlocks G order M).toBlocks₂₂ := by
  exact (Matrix.fromBlocks_toBlocks _).symm

theorem kwOrderedSplitTransitionInBlocks_det
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (M : Matrix (kwOrderedDartPortSplitGraph G order).Dart
      (kwOrderedDartPortSplitGraph G order).Dart ℂ) :
    (kwOrderedSplitTransitionInBlocks G order M).det = M.det := by
  classical
  exact Matrix.det_reindex_self
    (kwOrderedSplitDartBlockEquiv G order).symm M



theorem kw_pathGraph_edgeFinset
    (n : ℕ) :
    (SimpleGraph.pathGraph (n + 1)).edgeFinset =
      Finset.univ.image (fun i : Fin n ↦ s(i.castSucc, i.succ)) := by
  ext edge
  induction edge using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.pathGraph_adj]
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Sym2.eq_iff]
      constructor
      · intro huv
        rcases huv with huv | huv
        · let i : Fin n := ⟨u.val, by omega⟩
          refine ⟨i, ?_⟩
          left
          exact ⟨Fin.ext rfl, Fin.ext huv⟩
        · let i : Fin n := ⟨v.val, by omega⟩
          refine ⟨i, ?_⟩
          right
          exact ⟨Fin.ext rfl, Fin.ext huv⟩
      · rintro ⟨i, hi⟩
        rcases hi with hi | hi
        · left
          have h₁ := congrArg Fin.val hi.1
          have h₂ := congrArg Fin.val hi.2
          simp only [Fin.val_castSucc, Fin.succ] at h₁ h₂
          omega
        · right
          have h₁ := congrArg Fin.val hi.1
          have h₂ := congrArg Fin.val hi.2
          simp only [Fin.val_castSucc, Fin.succ] at h₁ h₂
          omega

theorem kw_pathGraph_edgeFinset_card (n : ℕ) :
    (SimpleGraph.pathGraph (n + 1)).edgeFinset.card = n := by
  rw [kw_pathGraph_edgeFinset]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    rw [Sym2.eq_iff] at hij
    rcases hij with hij | hij
    · apply Fin.ext
      have h₁ := congrArg Fin.val hij.1
      simp only [Fin.val_castSucc] at h₁
      exact h₁
    · have h₁ := congrArg Fin.val hij.1
      have h₂ := congrArg Fin.val hij.2
      simp only [Fin.val_castSucc, Fin.succ] at h₁ h₂
      exfalso
      omega


theorem kw_pathGraph_isAcyclic (n : ℕ) :
    (SimpleGraph.pathGraph n).IsAcyclic := by
  cases n with
  | zero => exact SimpleGraph.IsAcyclic.of_subsingleton
  | succ n =>
      have htree : (SimpleGraph.pathGraph (n + 1)).IsTree := by
        rw [SimpleGraph.isTree_iff_connected_and_card]
        constructor
        · exact SimpleGraph.pathGraph_connected n
        · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
            kw_pathGraph_edgeFinset_card, Nat.card_eq_fintype_card]
          simp
      exact htree.isAcyclic



def kwOrderedPortInternalGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    SimpleGraph (KWDartPort G) where
  Adj p q := p.1 = q.1 ∧
    (kwOrderedPortRank order p + 1 = kwOrderedPortRank order q ∨
      kwOrderedPortRank order q + 1 = kwOrderedPortRank order p)
  symm := by
    rintro p q ⟨hfst, hrank⟩
    exact ⟨hfst.symm, hrank.symm⟩
  loopless := ⟨by
    rintro p ⟨-, hrank⟩
    omega⟩

noncomputable instance kwOrderedPortInternalGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    DecidableRel (kwOrderedPortInternalGraph G order).Adj :=
  Classical.decRel _

theorem kwOutgoingDart_card_le_port_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fintype.card (KWOutgoingDart (G := G) v) ≤
      Fintype.card (KWDartPort G) := by
  let f : KWOutgoingDart (G := G) v → KWDartPort G := fun d ↦
    ⟨v, Fintype.equivFin (KWOutgoingDart (G := G) v) d⟩
  apply Fintype.card_le_of_injective f
  intro d e h
  have hindex : Fintype.equivFin (KWOutgoingDart (G := G) v) d =
      Fintype.equivFin (KWOutgoingDart (G := G) v) e := by
    exact Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
  exact (Fintype.equivFin (KWOutgoingDart (G := G) v)).injective hindex




noncomputable def kwOrderedPortForestCode
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G) :
    Fin (Fintype.card V * (Fintype.card (KWDartPort G) + 1)) := by
  let block := Fintype.card (KWDartPort G) + 1
  let vertexRank := (Fintype.equivFin V p.1).val
  let portRank := kwOrderedPortRank order p
  have hport : portRank < block := by
    have hp := (order p.1 p.2).isLt
    have hc := kwOutgoingDart_card_le_port_card G p.1
    dsimp only [portRank, block]
    exact (lt_of_lt_of_le hp hc).trans (Nat.lt_succ_self _)
  refine ⟨vertexRank * block + portRank, ?_⟩
  calc
    vertexRank * block + portRank < vertexRank * block + block :=
      Nat.add_lt_add_left hport _
    _ = (vertexRank + 1) * block := by rw [Nat.succ_mul]
    _ ≤ Fintype.card V * block := by
      exact Nat.mul_le_mul_right block (Fintype.equivFin V p.1).isLt

theorem kwOrderedPortForestCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    Function.Injective (kwOrderedPortForestCode G order) := by
  intro p q hpq
  let block := Fintype.card (KWDartPort G) + 1
  have hpbound : kwOrderedPortRank order p < block := by
    have hp := (order p.1 p.2).isLt
    have hc := kwOutgoingDart_card_le_port_card G p.1
    dsimp only [block]
    exact (lt_of_lt_of_le hp hc).trans (Nat.lt_succ_self _)
  have hqbound : kwOrderedPortRank order q < block := by
    have hp := (order q.1 q.2).isLt
    have hc := kwOutgoingDart_card_le_port_card G q.1
    dsimp only [block]
    exact (lt_of_lt_of_le hp hc).trans (Nat.lt_succ_self _)
  have hval := congrArg Fin.val hpq
  change (Fintype.equivFin V p.1).val * block +
      kwOrderedPortRank order p =
    (Fintype.equivFin V q.1).val * block +
      kwOrderedPortRank order q at hval
  have hvertex : (Fintype.equivFin V p.1).val =
      (Fintype.equivFin V q.1).val := by
    have hdiv := congrArg (fun z : ℕ ↦ z / block) hval
    have hpdiv : ((Fintype.equivFin V p.1).val * block +
        kwOrderedPortRank order p) / block =
        (Fintype.equivFin V p.1).val := by
      rw [Nat.mul_comm (Fintype.equivFin V p.1).val block,
        Nat.mul_add_div (m := block) (by omega),
        Nat.div_eq_of_lt hpbound, add_zero]
    have hqdiv : ((Fintype.equivFin V q.1).val * block +
        kwOrderedPortRank order q) / block =
        (Fintype.equivFin V q.1).val := by
      rw [Nat.mul_comm (Fintype.equivFin V q.1).val block,
        Nat.mul_add_div (m := block) (by omega),
        Nat.div_eq_of_lt hqbound, add_zero]
    exact hpdiv.symm.trans (hdiv.trans hqdiv)
  have hpfirst : p.1 = q.1 := by
    apply (Fintype.equivFin V).injective
    exact Fin.ext hvertex
  have hrank : kwOrderedPortRank order p = kwOrderedPortRank order q := by
    have hmod := congrArg (fun z : ℕ ↦ z % block) hval
    have hpmod : ((Fintype.equivFin V p.1).val * block +
        kwOrderedPortRank order p) % block =
        kwOrderedPortRank order p := by
      rw [Nat.add_comm,
        Nat.mul_comm (Fintype.equivFin V p.1).val block,
        Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hpbound]
    have hqmod : ((Fintype.equivFin V q.1).val * block +
        kwOrderedPortRank order q) % block =
        kwOrderedPortRank order q := by
      rw [Nat.add_comm,
        Nat.mul_comm (Fintype.equivFin V q.1).val block,
        Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hqbound]
    exact hpmod.symm.trans (hmod.trans hqmod)
  rcases p with ⟨v, i⟩
  rcases q with ⟨w, j⟩
  dsimp only at hpfirst hrank
  subst w
  have hij : order v i = order v j := Fin.ext hrank
  have : i = j := (order v).injective hij
  subst j
  rfl

noncomputable def kwOrderedPortInternalGraphHom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    kwOrderedPortInternalGraph G order →g
      SimpleGraph.pathGraph
        (Fintype.card V * (Fintype.card (KWDartPort G) + 1)) where
  toFun := kwOrderedPortForestCode G order
  map_rel' := by
    rintro p q ⟨hfst, hrank⟩
    rw [SimpleGraph.pathGraph_adj]
    rcases hrank with hrank | hrank
    · left
      dsimp only [kwOrderedPortForestCode]
      rw [hfst]
      omega
    · right
      dsimp only [kwOrderedPortForestCode]
      rw [hfst]
      omega


theorem kwOrderedPortInternalGraph_isAcyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    (kwOrderedPortInternalGraph G order).IsAcyclic :=
  (kw_pathGraph_isAcyclic _).comap
    (kwOrderedPortInternalGraphHom G order)
    (kwOrderedPortForestCode_injective G order)



noncomputable def kwOrderedInternalSplitDartEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWOrderedInternalSplitDart G order ≃
      (kwOrderedPortInternalGraph G order).Dart where
  toFun delta := by
    refine ⟨delta.1.toProd, ?_⟩
    have hadj := delta.1.adj
    rw [kwOrderedDartPortSplitGraph_adj] at hadj
    exact hadj.resolve_left delta.2
  invFun delta := by
    have hfull : (kwOrderedDartPortSplitGraph G order).Adj
        delta.fst delta.snd := by
      rw [kwOrderedDartPortSplitGraph_adj]
      exact Or.inr delta.adj
    have hnot : ¬kwDartOfPort G delta.snd =
        (kwDartOfPort G delta.fst).symm := by
      intro hext
      have htails := congrArg (fun d : G.Dart ↦ d.fst) hext
      have hsame : delta.fst.1 = delta.snd.1 := delta.adj.1
      apply (kwDartOfPort G delta.fst).fst_ne_snd
      rw [kwDartOfPort_fst, hsame]
      simpa using htails
    exact ⟨⟨delta.toProd, hfull⟩, hnot⟩
  left_inv delta := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    rfl
  right_inv delta := by
    apply SimpleGraph.Dart.ext
    rfl

@[simp] theorem kwOrderedInternalSplitDartEquiv_toProd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (delta : KWOrderedInternalSplitDart G order) :
    (kwOrderedInternalSplitDartEquiv G order delta).toProd =
      delta.1.toProd := by
  rfl

@[simp] theorem kwOrderedInternalSplitDartEquiv_symm_toProd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (delta : (kwOrderedPortInternalGraph G order).Dart) :
    ((kwOrderedInternalSplitDartEquiv G order).symm delta).1.toProd =
      delta.toProd := by
  rfl



noncomputable def kwOrderedSplitInternalBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (M : Matrix (kwOrderedDartPortSplitGraph G order).Dart
      (kwOrderedDartPortSplitGraph G order).Dart ℂ) :
    Matrix (KWOrderedInternalSplitDart G order)
      (KWOrderedInternalSplitDart G order) ℂ :=
  (kwOrderedSplitTransitionInBlocks G order M).toBlocks₂₂


noncomputable def kwOrderedInternalPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ)
    (d e : (kwOrderedPortInternalGraph G order).Dart) : ℂ :=
  phase ((kwOrderedInternalSplitDartEquiv G order).symm d).1
    ((kwOrderedInternalSplitDartEquiv G order).symm e).1

theorem kwOrderedSplitInternalBlock_reindex_eq_transition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    Matrix.reindex (kwOrderedInternalSplitDartEquiv G order)
        (kwOrderedInternalSplitDartEquiv G order)
        (kwOrderedSplitInternalBlock G order
          (kwGraphTransition (kwOrderedDartPortSplitGraph G order)
            weight phase)) =
      kwGraphTransition (kwOrderedPortInternalGraph G order) weight
        (kwOrderedInternalPhase G order phase) := by
  ext d e
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition kwOrderedInternalPhase
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl



theorem kwOrderedSplitInternalBlock_isNilpotent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    IsNilpotent (kwOrderedSplitInternalBlock G order
      (kwGraphTransition (kwOrderedDartPortSplitGraph G order)
        weight phase)) := by
  let B := kwOrderedSplitInternalBlock G order
    (kwGraphTransition (kwOrderedDartPortSplitGraph G order) weight phase)
  let e := kwOrderedInternalSplitDartEquiv G order
  let A := Matrix.reindexAlgEquiv ℂ ℂ e
  let T := kwGraphTransition (kwOrderedPortInternalGraph G order) weight
    (kwOrderedInternalPhase G order phase)
  have hAB : A B = T := by
    simpa only [A, B, T, Matrix.reindexAlgEquiv_apply] using
      kwOrderedSplitInternalBlock_reindex_eq_transition
        G order weight phase
  obtain ⟨n, hn⟩ := kwGraphTransition_isNilpotent_of_isAcyclic
    (kwOrderedPortInternalGraph G order)
    (kwOrderedPortInternalGraph_isAcyclic G order) weight
    (kwOrderedInternalPhase G order phase)
  refine ⟨n, ?_⟩
  apply A.injective
  rw [map_pow, hAB, hn, map_zero]




theorem kwOrderedSplit_det_eq_effective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order)
      weight phase
    let R := kwOrderedSplitTransitionInBlocks G order M
    ∃ n : ℕ,
      (1 - M).det =
        (1 - kwEliminateAcyclicInternal R.toBlocks₁₁ R.toBlocks₁₂
          R.toBlocks₂₁ R.toBlocks₂₂ n).det := by
  classical
  dsimp only
  let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order)
    weight phase
  let R := kwOrderedSplitTransitionInBlocks G order M
  obtain ⟨n, hn⟩ := kwOrderedSplitInternalBlock_isNilpotent
    G order weight phase
  refine ⟨n, ?_⟩
  have hnR : R.toBlocks₂₂ ^ n = 0 := by
    exact hn
  have hsub : kwOrderedSplitTransitionInBlocks G order (1 - M) = 1 - R := by
    ext i j
    simp [kwOrderedSplitTransitionInBlocks, Matrix.reindex_apply,
      Matrix.one_apply, R]
  calc
    (1 - M).det =
        (kwOrderedSplitTransitionInBlocks G order (1 - M)).det :=
      (kwOrderedSplitTransitionInBlocks_det G order (1 - M)).symm
    _ = (1 - R).det := by rw [hsub]
    _ = (1 - Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂).det := by
      rw [Matrix.fromBlocks_toBlocks]
    _ = (1 - kwEliminateAcyclicInternal R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n).det :=
      kw_det_eliminateAcyclicInternal R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n hnR




theorem kwOrderedSplit_externalBlock_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    (kwOrderedSplitTransitionInBlocks G order
      (kwGraphTransition (kwOrderedDartPortSplitGraph G order)
        weight phase)).toBlocks₁₁ = 0 := by
  ext d e
  unfold Matrix.toBlocks₁₁ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.zero_apply,
    Matrix.of_apply]
  split
  · rename_i hstep
    exfalso
    rcases hstep with ⟨hconsecutive, hne⟩
    simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
      kwOrderedExternalSplitDartOfDart_fst,
      kwOrderedExternalSplitDartOfDart_snd] at hconsecutive hne
    have hdart : e = d.symm := by
      have h := congrArg (kwDartOfPort G) hconsecutive
      simpa using h.symm
    subst e
    apply hne
    simp [SimpleGraph.Dart.edge]
  · rfl



theorem kwOrderedSplit_det_eq_pathEffective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order)
      weight phase
    let R := kwOrderedSplitTransitionInBlocks G order M
    ∃ n : ℕ,
      (1 - M).det =
        (1 - R.toBlocks₁₂ *
          kwNilpotentResolvent R.toBlocks₂₂ n * R.toBlocks₂₁).det := by
  classical
  dsimp only
  let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order)
    weight phase
  let R := kwOrderedSplitTransitionInBlocks G order M
  obtain ⟨n, hn⟩ := kwOrderedSplit_det_eq_effective G order weight phase
  refine ⟨n, ?_⟩
  rw [hn]
  unfold kwEliminateAcyclicInternal
  have hzero : R.toBlocks₁₁ = 0 := by
    exact kwOrderedSplit_externalBlock_eq_zero G order weight phase
  rw [hzero, zero_add]





noncomputable def kwOrderedSplitWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) : Sym2 (KWDartPort G) → ℂ :=
  Sym2.lift ⟨fun p q ↦
    if kwDartOfPort G q = (kwDartOfPort G p).symm
      then weight (kwDartOfPort G p).edge else 1, by
    intro p q
    change (if kwDartOfPort G q = (kwDartOfPort G p).symm
        then weight (kwDartOfPort G p).edge else 1) =
      if kwDartOfPort G p = (kwDartOfPort G q).symm
        then weight (kwDartOfPort G q).edge else 1
    by_cases hpq : kwDartOfPort G q = (kwDartOfPort G p).symm
    · have hqp : kwDartOfPort G p = (kwDartOfPort G q).symm := by
        rw [hpq]
        exact (kwDartOfPort G p).symm_symm.symm
      rw [if_pos hpq, if_pos hqp]
      rw [hpq]
      exact (congrArg weight (kwDartOfPort G p).edge_symm).symm
    · have hqp : ¬kwDartOfPort G p = (kwDartOfPort G q).symm := by
        intro h
        apply hpq
        rw [h]
        exact (kwDartOfPort G q).symm_symm.symm
      rw [if_neg hpq, if_neg hqp]⟩

@[simp] theorem kwOrderedSplitWeight_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (order : KWPortOrder G) (d : G.Dart) :
    kwOrderedSplitWeight G weight
        (kwOrderedExternalSplitDartOfDart G order d).1.edge =
      weight d.edge := by
  unfold kwOrderedSplitWeight SimpleGraph.Dart.edge
  rw [Sym2.lift_mk]
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd,
    kwDartOfPort_portOfDart, if_pos]

theorem kwOrderedSplitWeight_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) :
    kwOrderedSplitWeight G weight d.1.edge = 1 := by
  unfold kwOrderedSplitWeight SimpleGraph.Dart.edge
  rw [Sym2.lift_mk]
  change (if kwDartOfPort G d.1.snd = (kwDartOfPort G d.1.fst).symm
    then weight (kwDartOfPort G d.1.fst).edge else 1) = 1
  rw [if_neg d.2]








noncomputable def kwAngularSplitPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) : ℂ :=
  if _hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then
    if _he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm then 1
    else if kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
        kwOrderedPortRank (kwAngularPortOrder embedding) e.snd then
      -Complex.I * (kwPortAngleRoot embedding e.fst)⁻¹
    else
      Complex.I * (kwPortAngleRoot embedding e.fst)⁻¹
  else if _he : kwDartOfPort G e.snd =
      (kwDartOfPort G e.fst).symm then
    kwPortAngleRoot embedding e.fst
  else 1

@[simp] theorem kwAngularSplitPhase_external_internal_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) e.1.fst <
      kwOrderedPortRank (kwAngularPortOrder embedding) e.1.snd) :
    kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 e.1 =
      -Complex.I * (kwPortAngleRoot embedding e.1.fst)⁻¹ := by
  unfold kwAngularSplitPhase
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd, kwDartOfPort_portOfDart]
  simp [e.2, hrank]

@[simp] theorem kwAngularSplitPhase_external_internal_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) e.1.snd <
      kwOrderedPortRank (kwAngularPortOrder embedding) e.1.fst) :
    kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 e.1 =
      Complex.I * (kwPortAngleRoot embedding e.1.fst)⁻¹ := by
  unfold kwAngularSplitPhase
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd, kwDartOfPort_portOfDart]
  simp [e.2, not_lt_of_ge (le_of_lt hrank)]

@[simp] theorem kwAngularSplitPhase_internal_external
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) :
    kwAngularSplitPhase embedding d.1
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) e).1 =
      kwPortAngleRoot embedding (kwPortOfDart G e) := by
  unfold kwAngularSplitPhase
  simp [d.2]

@[simp] theorem kwAngularSplitPhase_internal_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)) :
    kwAngularSplitPhase embedding d.1 e.1 = 1 := by
  unfold kwAngularSplitPhase
  simp [d.2, e.2]




theorem kwAngularSplitPhase_endpointProduct_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G d.symm) <
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e))
    (first last : KWOrderedInternalSplitDart G
      (kwAngularPortOrder embedding))
    (hfirst : first.1.fst = kwPortOfDart G d.symm)
    (hfirstRank : kwOrderedPortRank (kwAngularPortOrder embedding)
        first.1.fst <
      kwOrderedPortRank (kwAngularPortOrder embedding) first.1.snd) :
    kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 first.1 *
      kwAngularSplitPhase embedding last.1
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) e).1 =
      embedding.turnPhase d e := by
  rw [kwAngularSplitPhase_external_internal_of_rank_lt
      embedding d first hfirstRank,
    kwAngularSplitPhase_internal_external]
  rw [embedding.turnPhase_eq_portRoots_of_rank_lt d e hde hrank]
  simp only [hfirst]



theorem kwAngularSplitPhase_endpointProduct_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e) <
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G d.symm))
    (first last : KWOrderedInternalSplitDart G
      (kwAngularPortOrder embedding))
    (hfirst : first.1.fst = kwPortOfDart G d.symm)
    (hfirstRank : kwOrderedPortRank (kwAngularPortOrder embedding)
        first.1.snd <
      kwOrderedPortRank (kwAngularPortOrder embedding) first.1.fst) :
    kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 first.1 *
      kwAngularSplitPhase embedding last.1
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) e).1 =
      embedding.turnPhase d e := by
  rw [kwAngularSplitPhase_external_internal_of_rank_gt
      embedding d first hfirstRank,
    kwAngularSplitPhase_internal_external]
  rw [embedding.turnPhase_eq_portRoots_of_rank_gt d e hde hrank]
  simp only [hfirst]



theorem kwAngularSplit_internalPhase_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    kwOrderedInternalPhase G (kwAngularPortOrder embedding)
        (kwAngularSplitPhase embedding) = fun _ _ ↦ 1 := by
  funext d e
  unfold kwOrderedInternalPhase
  exact kwAngularSplitPhase_internal_internal embedding
    ((kwOrderedInternalSplitDartEquiv G
      (kwAngularPortOrder embedding)).symm d)
    ((kwOrderedInternalSplitDartEquiv G
      (kwAngularPortOrder embedding)).symm e)

theorem kwDartPort_eq_of_fst_of_orderRank
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) {p q : KWDartPort G}
    (hfst : p.1 = q.1)
    (hidx : kwOrderedPortRank order p = kwOrderedPortRank order q) :
    p = q := by
  rcases p with ⟨v, i⟩
  rcases q with ⟨w, j⟩
  dsimp only at hfst hidx
  subst w
  have hij : order v i = order v j := Fin.ext hidx
  have : i = j := (order v).injective hij
  subst j
  rfl



def KWOrderedInternalDartStep
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d e : KWOrderedInternalSplitDart G order) : Prop :=
  d.1.snd = e.1.fst ∧ d.1.edge ≠ e.1.edge

theorem kwOrderedInternalSplitDart_adj_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) :
    d.1.fst.1 = d.1.snd.1 ∧
      (kwOrderedPortRank order d.1.fst + 1 =
          kwOrderedPortRank order d.1.snd ∨
        kwOrderedPortRank order d.1.snd + 1 =
          kwOrderedPortRank order d.1.fst) := by
  have hd := d.1.adj
  rw [kwOrderedDartPortSplitGraph_adj] at hd
  exact hd.resolve_left d.2


theorem kwOrderedInternalDartStep_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order}
    (hstep : KWOrderedInternalDartStep G order d e)
    (hd : kwOrderedPortRank order d.1.fst <
      kwOrderedPortRank order d.1.snd) :
    kwOrderedPortRank order e.1.fst <
      kwOrderedPortRank order e.1.snd := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  rcases hddata.2 with hdinc | hddec
  · rcases hedata.2 with heinc | hedec
    · omega
    · exfalso
      apply hstep.2
      rw [SimpleGraph.dart_edge_eq_iff]
      right
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · change d.1.fst = e.1.snd
        apply kwDartPort_eq_of_fst_of_orderRank order
        · exact hddata.1.trans
            ((congrArg Sigma.fst hstep.1).trans hedata.1)
        · have hrank := congrArg (kwOrderedPortRank order) hstep.1
          omega
      · exact hstep.1
  · omega


theorem kwOrderedInternalDartStep_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order}
    (hstep : KWOrderedInternalDartStep G order d e)
    (hd : kwOrderedPortRank order d.1.snd <
      kwOrderedPortRank order d.1.fst) :
    kwOrderedPortRank order e.1.snd <
      kwOrderedPortRank order e.1.fst := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  rcases hddata.2 with hdinc | hddec
  · omega
  · rcases hedata.2 with heinc | hedec
    · exfalso
      apply hstep.2
      rw [SimpleGraph.dart_edge_eq_iff]
      right
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · change d.1.fst = e.1.snd
        apply kwDartPort_eq_of_fst_of_orderRank order
        · exact hddata.1.trans
            ((congrArg Sigma.fst hstep.1).trans hedata.1)
        · have hrank := congrArg (kwOrderedPortRank order) hstep.1
          omega
      · exact hstep.1
    · omega


theorem kwOrderedInternalDartStep_rightUnique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e f : KWOrderedInternalSplitDart G order}
    (he : KWOrderedInternalDartStep G order d e)
    (hf : KWOrderedInternalDartStep G order d f) : e = f := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hfdata := kwOrderedInternalSplitDart_adj_data G order f
  apply Subtype.ext
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact he.1.symm.trans hf.1
  · apply kwDartPort_eq_of_fst_of_orderRank order
    · exact hedata.1.symm.trans
        ((congrArg Sigma.fst (he.1.symm.trans hf.1)).trans hfdata.1)
    · rcases hddata.2 with hdinc | hddec
      · have hdlt : kwOrderedPortRank order d.1.fst <
            kwOrderedPortRank order d.1.snd := by omega
        have helt := kwOrderedInternalDartStep_rank_lt G order he hdlt
        have hflt := kwOrderedInternalDartStep_rank_lt G order hf hdlt
        have herank := congrArg (kwOrderedPortRank order) he.1
        have hfrank := congrArg (kwOrderedPortRank order) hf.1
        rcases hedata.2 with heinc | hedec <;>
          rcases hfdata.2 with hfinc | hfdec <;> omega
      · have hdgt : kwOrderedPortRank order d.1.snd <
            kwOrderedPortRank order d.1.fst := by omega
        have hegt := kwOrderedInternalDartStep_rank_gt G order he hdgt
        have hfgt := kwOrderedInternalDartStep_rank_gt G order hf hdgt
        have herank := congrArg (kwOrderedPortRank order) he.1
        have hfrank := congrArg (kwOrderedPortRank order) hf.1
        rcases hedata.2 with heinc | hedec <;>
          rcases hfdata.2 with hfinc | hfdec <;> omega



def KWOrderedInternalDartFacesPort
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (d : KWOrderedInternalSplitDart G order)
    (q : KWDartPort G) : Prop :=
  d.1.snd.1 = q.1 ∧
    ((kwOrderedPortRank order d.1.fst <
        kwOrderedPortRank order d.1.snd ∧
      kwOrderedPortRank order d.1.snd ≤ kwOrderedPortRank order q) ∨
    (kwOrderedPortRank order d.1.snd <
        kwOrderedPortRank order d.1.fst ∧
      kwOrderedPortRank order q ≤ kwOrderedPortRank order d.1.snd))

theorem kwOrderedInternalDartFacesPort_of_snd_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) (q : KWDartPort G)
    (h : d.1.snd = q) : KWOrderedInternalDartFacesPort order d q := by
  have hd := kwOrderedInternalSplitDart_adj_data G order d
  have hrank := congrArg (kwOrderedPortRank order) h
  unfold KWOrderedInternalDartFacesPort
  constructor
  · exact congrArg Sigma.fst h
  · rcases hd.2 with hinc | hdec
    · left
      constructor <;> omega
    · right
      constructor <;> omega


theorem kwOrderedInternalDartFacesPort_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order} {q : KWDartPort G}
    (hstep : KWOrderedInternalDartStep G order d e)
    (heq : KWOrderedInternalDartFacesPort order e q) :
    KWOrderedInternalDartFacesPort order d q := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hsteprank := congrArg (kwOrderedPortRank order) hstep.1
  rcases heq with ⟨heqfst, heqdir⟩
  constructor
  · exact (congrArg Sigma.fst hstep.1).trans
      (hedata.1.trans heqfst)
  · rcases heqdir with ⟨heinc, hetarget⟩ | ⟨hedec, hetarget⟩
    · rcases hddata.2 with hdinc | hddec
      · left
        constructor <;> omega
      · have hdgt : kwOrderedPortRank order d.1.snd <
            kwOrderedPortRank order d.1.fst := by omega
        have := kwOrderedInternalDartStep_rank_gt G order hstep hdgt
        omega
    · rcases hddata.2 with hdinc | hddec
      · have hdlt : kwOrderedPortRank order d.1.fst <
            kwOrderedPortRank order d.1.snd := by omega
        have := kwOrderedInternalDartStep_rank_lt G order hstep hdlt
        omega
      · right
        constructor <;> omega


theorem kwOrderedInternalDartFacesPort_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order} {q : KWDartPort G}
    (hstep : KWOrderedInternalDartStep G order d e)
    (hdq : KWOrderedInternalDartFacesPort order d q)
    (hne : d.1.snd ≠ q) :
    KWOrderedInternalDartFacesPort order e q := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hsteprank := congrArg (kwOrderedPortRank order) hstep.1
  rcases hdq with ⟨hdqfst, hdqdir⟩
  have hrankne : kwOrderedPortRank order d.1.snd ≠
      kwOrderedPortRank order q := by
    intro hrank
    apply hne
    exact kwDartPort_eq_of_fst_of_orderRank order hdqfst hrank
  constructor
  · exact hedata.1.symm.trans
      ((congrArg Sigma.fst hstep.1).symm.trans hdqfst)
  · rcases hdqdir with ⟨hdinc, hdtarget⟩ | ⟨hddec, hdtarget⟩
    · have heinc := kwOrderedInternalDartStep_rank_lt
        G order hstep hdinc
      left
      constructor
      · exact heinc
      · rcases hedata.2 with heinc' | hedec' <;> omega
    · have hedec := kwOrderedInternalDartStep_rank_gt
        G order hstep hddec
      right
      constructor
      · exact hedec
      · rcases hedata.2 with heinc' | hedec' <;> omega



theorem kwOrderedInternalDartStep_not_faces_snd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order}
    (hstep : KWOrderedInternalDartStep G order d e) :
    ¬KWOrderedInternalDartFacesPort order e d.1.snd := by
  intro hfaces
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hsteprank := congrArg (kwOrderedPortRank order) hstep.1
  rcases hddata.2 with hdinc | hddec
  · have hdlt : kwOrderedPortRank order d.1.fst <
        kwOrderedPortRank order d.1.snd := by omega
    have helt := kwOrderedInternalDartStep_rank_lt G order hstep hdlt
    rcases hfaces.2 with ⟨heinc, htarget⟩ | ⟨hedec, htarget⟩
    · rcases hedata.2 with heinc' | hedec' <;> omega
    · omega
  · have hdgt : kwOrderedPortRank order d.1.snd <
        kwOrderedPortRank order d.1.fst := by omega
    have hegt := kwOrderedInternalDartStep_rank_gt G order hstep hdgt
    rcases hfaces.2 with ⟨heinc, htarget⟩ | ⟨hedec, htarget⟩
    · omega
    · rcases hedata.2 with heinc' | hedec' <;> omega

theorem kwOrderedInternalDart_not_faces_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) :
    ¬KWOrderedInternalDartFacesPort order d d.1.fst := by
  intro hfaces
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  rcases hfaces.2 with ⟨hinc, htarget⟩ | ⟨hdec, htarget⟩ <;>
    rcases hddata.2 with hdinc | hddec <;> omega



theorem kwOrderedInternalDart_eq_of_fst_eq_of_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order} {q : KWDartPort G}
    (hfst : d.1.fst = e.1.fst)
    (hdq : KWOrderedInternalDartFacesPort order d q)
    (heq : KWOrderedInternalDartFacesPort order e q) : d = e := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hfstrank := congrArg (kwOrderedPortRank order) hfst
  apply Subtype.ext
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact hfst
  · apply kwDartPort_eq_of_fst_of_orderRank order
    · exact hddata.1.symm.trans
        ((congrArg Sigma.fst hfst).trans hedata.1)
    · rcases hdq.2 with ⟨hdinc, hdtarget⟩ | ⟨hddec, hdtarget⟩ <;>
        rcases heq.2 with ⟨heinc, hetarget⟩ | ⟨hedec, hetarget⟩ <;>
        rcases hddata.2 with hdinc' | hddec' <;>
        rcases hedata.2 with heinc' | hedec' <;> omega


noncomputable def kwOrderedPortAtRank
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v))) : KWDartPort G :=
  ⟨v, (order v).symm i⟩

@[simp] theorem kwOrderedPortAtRank_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v))) :
    (kwOrderedPortAtRank order v i).1 = v := rfl

@[simp] theorem kwOrderedPortAtRank_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v))) :
    kwOrderedPortRank order (kwOrderedPortAtRank order v i) = i.val := by
  change ((order v) ((order v).symm i)).val = i.val
  rw [Equiv.apply_symm_apply]


noncomputable def kwOrderedIncreasingInternalDartFrom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G)
    (h : kwOrderedPortRank order p + 1 <
      Fintype.card (KWOutgoingDart (G := G) p.1)) :
    KWOrderedInternalSplitDart G order :=
  (kwOrderedInternalSplitDartEquiv G order).symm ⟨
    (p, kwOrderedPortAtRank order p.1
      ⟨kwOrderedPortRank order p + 1, h⟩), by
      exact ⟨rfl, Or.inl (by simp)⟩⟩

@[simp] theorem kwOrderedIncreasingInternalDartFrom_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G)
    (h : kwOrderedPortRank order p + 1 <
      Fintype.card (KWOutgoingDart (G := G) p.1)) :
    (kwOrderedIncreasingInternalDartFrom G order p h).1.fst = p := by
  change ((kwOrderedInternalSplitDartEquiv G order).symm
    ⟨(p, kwOrderedPortAtRank order p.1
      ⟨kwOrderedPortRank order p + 1, h⟩), _⟩).1.fst = p
  rfl

@[simp] theorem kwOrderedIncreasingInternalDartFrom_rank_snd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G)
    (h : kwOrderedPortRank order p + 1 <
      Fintype.card (KWOutgoingDart (G := G) p.1)) :
    kwOrderedPortRank order
        (kwOrderedIncreasingInternalDartFrom G order p h).1.snd =
      kwOrderedPortRank order p + 1 := by
  change kwOrderedPortRank order (kwOrderedPortAtRank order p.1
    ⟨kwOrderedPortRank order p + 1, h⟩) = _
  simp


noncomputable def kwOrderedDecreasingInternalDartFrom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G) (h : 0 < kwOrderedPortRank order p) :
    KWOrderedInternalSplitDart G order :=
  (kwOrderedInternalSplitDartEquiv G order).symm ⟨
    (p, kwOrderedPortAtRank order p.1
      ⟨kwOrderedPortRank order p - 1, by
        exact lt_of_le_of_lt (Nat.sub_le _ _) (order p.1 p.2).isLt⟩), by
      exact ⟨rfl, Or.inr (by simp; omega)⟩⟩

@[simp] theorem kwOrderedDecreasingInternalDartFrom_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G) (h : 0 < kwOrderedPortRank order p) :
    (kwOrderedDecreasingInternalDartFrom G order p h).1.fst = p := by
  change ((kwOrderedInternalSplitDartEquiv G order).symm
    ⟨(p, kwOrderedPortAtRank order p.1
      ⟨kwOrderedPortRank order p - 1, _⟩), _⟩).1.fst = p
  rfl

@[simp] theorem kwOrderedDecreasingInternalDartFrom_rank_snd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G) (h : 0 < kwOrderedPortRank order p) :
    kwOrderedPortRank order
        (kwOrderedDecreasingInternalDartFrom G order p h).1.snd + 1 =
      kwOrderedPortRank order p := by
  change kwOrderedPortRank order (kwOrderedPortAtRank order p.1
    ⟨kwOrderedPortRank order p - 1, _⟩) + 1 = _
  simp
  omega

theorem kwOrderedIncreasingInternalDartFrom_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p q : KWDartPort G) (hpq : p.1 = q.1)
    (hlt : kwOrderedPortRank order p < kwOrderedPortRank order q)
    (hbound : kwOrderedPortRank order p + 1 <
      Fintype.card (KWOutgoingDart (G := G) p.1)) :
    KWOrderedInternalDartFacesPort order
      (kwOrderedIncreasingInternalDartFrom G order p hbound) q := by
  unfold KWOrderedInternalDartFacesPort
  constructor
  · change p.1 = q.1
    exact hpq
  · left
    constructor
    · rw [kwOrderedIncreasingInternalDartFrom_fst,
        kwOrderedIncreasingInternalDartFrom_rank_snd]
      omega
    · rw [kwOrderedIncreasingInternalDartFrom_rank_snd]
      omega

theorem kwOrderedDecreasingInternalDartFrom_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p q : KWDartPort G) (hpq : p.1 = q.1)
    (hlt : kwOrderedPortRank order q < kwOrderedPortRank order p)
    (hbound : 0 < kwOrderedPortRank order p) :
    KWOrderedInternalDartFacesPort order
      (kwOrderedDecreasingInternalDartFrom G order p hbound) q := by
  unfold KWOrderedInternalDartFacesPort
  constructor
  · change p.1 = q.1
    exact hpq
  · right
    constructor
    · rw [kwOrderedDecreasingInternalDartFrom_fst]
      have hs := kwOrderedDecreasingInternalDartFrom_rank_snd
        G order p hbound
      omega
    · have hs := kwOrderedDecreasingInternalDartFrom_rank_snd
        G order p hbound
      omega

theorem kwOrderedInternalDartStep_increasingFrom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order)
    (hd : kwOrderedPortRank order d.1.fst <
      kwOrderedPortRank order d.1.snd)
    (hbound : kwOrderedPortRank order d.1.snd + 1 <
      Fintype.card (KWOutgoingDart (G := G) d.1.snd.1)) :
    KWOrderedInternalDartStep G order d
      (kwOrderedIncreasingInternalDartFrom G order d.1.snd hbound) := by
  constructor
  · simp
  · intro hedge
    rw [SimpleGraph.dart_edge_eq_iff] at hedge
    have hddata := kwOrderedInternalSplitDart_adj_data G order d
    rcases hedge with hedge | hedge
    · have h := congrArg (fun delta :
          (kwOrderedDartPortSplitGraph G order).Dart ↦
          kwOrderedPortRank order delta.snd) hedge
      simp only [kwOrderedIncreasingInternalDartFrom_rank_snd] at h
      omega
    · have h := congrArg (fun delta :
          (kwOrderedDartPortSplitGraph G order).Dart ↦
          kwOrderedPortRank order delta.fst) hedge
      change kwOrderedPortRank order d.1.fst =
        kwOrderedPortRank order
          (kwOrderedIncreasingInternalDartFrom G order
            d.1.snd hbound).1.snd at h
      rw [kwOrderedIncreasingInternalDartFrom_rank_snd] at h
      rcases hddata.2 with hinc | hdec <;> omega

theorem kwOrderedInternalDartStep_decreasingFrom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order)
    (hd : kwOrderedPortRank order d.1.snd <
      kwOrderedPortRank order d.1.fst)
    (hbound : 0 < kwOrderedPortRank order d.1.snd) :
    KWOrderedInternalDartStep G order d
      (kwOrderedDecreasingInternalDartFrom G order d.1.snd hbound) := by
  constructor
  · simp
  · intro hedge
    rw [SimpleGraph.dart_edge_eq_iff] at hedge
    have hddata := kwOrderedInternalSplitDart_adj_data G order d
    rcases hedge with hedge | hedge
    · have h := congrArg (fun delta :
          (kwOrderedDartPortSplitGraph G order).Dart ↦
          kwOrderedPortRank order delta.snd) hedge
      have hs := kwOrderedDecreasingInternalDartFrom_rank_snd
        G order d.1.snd hbound
      simp only at h
      change kwOrderedPortRank order d.1.snd =
        kwOrderedPortRank order
          (kwOrderedDecreasingInternalDartFrom G order
            d.1.snd hbound).1.snd at h
      omega
    · have h := congrArg (fun delta :
          (kwOrderedDartPortSplitGraph G order).Dart ↦
          kwOrderedPortRank order delta.fst) hedge
      change kwOrderedPortRank order d.1.fst =
        kwOrderedPortRank order
          (kwOrderedDecreasingInternalDartFrom G order
            d.1.snd hbound).1.snd at h
      have hs := kwOrderedDecreasingInternalDartFrom_rank_snd
        G order d.1.snd hbound
      rcases hddata.2 with hinc | hdec <;> omega



theorem kwAngularSplit_internalBlock_apply_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G
      (kwAngularPortOrder embedding))
    (hstep : KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d e) :
    kwOrderedSplitInternalBlock G (kwAngularPortOrder embedding)
        (kwGraphTransition
          (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
          (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)) d e =
      1 := by
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inr]
  change d.1.snd = e.1.fst ∧ d.1.edge ≠ e.1.edge at hstep
  rw [if_pos hstep,
    kwOrderedSplitWeight_internal G weight
      (kwAngularPortOrder embedding) d,
    kwAngularSplitPhase_internal_internal]
  exact one_mul 1


theorem kwAngularSplit_internalBlock_apply_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G
      (kwAngularPortOrder embedding))
    (hstep : ¬KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d e) :
    kwOrderedSplitInternalBlock G (kwAngularPortOrder embedding)
        (kwGraphTransition
          (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
          (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)) d e =
      0 := by
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inr]
  change ¬(d.1.snd = e.1.fst ∧ d.1.edge ≠ e.1.edge) at hstep
  rw [if_neg hstep]

theorem kwOrderedExternalSplitDart_edge_ne_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : G.Dart) (e : KWOrderedInternalSplitDart G order) :
    (kwOrderedExternalSplitDartOfDart G order d).1.edge ≠ e.1.edge := by
  intro hedge
  rw [SimpleGraph.dart_edge_eq_iff] at hedge
  rcases hedge with hedge | hedge
  · apply e.2
    rw [← hedge]
    exact (kwOrderedExternalSplitDartOfDart G order d).2
  · apply e.2
    have hmatch := (kwOrderedExternalSplitDartOfDart G order d).2
    rw [hedge] at hmatch
    have hs := congrArg SimpleGraph.Dart.symm hmatch
    simpa using hs.symm



theorem kwAngularSplit_enterBlock_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hconnect : kwPortOfDart G d.symm = e.1.fst) :
    (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding))).toBlocks₁₂ d e =
      weight d.edge * kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 e.1 := by
  unfold Matrix.toBlocks₁₂ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_pos ⟨by simpa using hconnect, by
      exact kwOrderedExternalSplitDart_edge_ne_internal G
        (kwAngularPortOrder embedding) d e⟩,
    kwOrderedSplitWeight_matching]

theorem kwAngularSplit_enterBlock_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
    (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding))).toBlocks₁₂ d e = 0 := by
  unfold Matrix.toBlocks₁₂ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_neg (by
    intro h
    apply hconnect
    simpa using h.1)]



theorem kwAngularSplit_exitBlock_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hconnect : d.1.snd = kwPortOfDart G e) :
    (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding))).toBlocks₂₁ d e =
      kwPortAngleRoot embedding (kwPortOfDart G e) := by
  unfold Matrix.toBlocks₂₁ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_pos ⟨by simpa using hconnect,
      (kwOrderedExternalSplitDart_edge_ne_internal G
        (kwAngularPortOrder embedding) e d).symm⟩,
    kwOrderedSplitWeight_internal, kwAngularSplitPhase_internal_external,
    one_mul]

theorem kwAngularSplit_exitBlock_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hconnect : d.1.snd ≠ kwPortOfDart G e) :
    (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding))).toBlocks₂₁ d e = 0 := by
  unfold Matrix.toBlocks₂₁ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_neg (by
    intro h
    apply hconnect
    simpa using h.1)]


noncomputable def kwAngularSplitBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ) :=
  kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding)
    (kwGraphTransition
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding))

theorem kwAngularSplitBlocks_internal_apply_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hstep : KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d e) :
    (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d e = 1 :=
  kwAngularSplit_internalBlock_apply_of_step embedding weight d e hstep

theorem kwAngularSplitBlocks_internal_apply_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hstep : ¬KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d e) :
    (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d e = 0 :=
  kwAngularSplit_internalBlock_apply_of_not_step embedding weight d e hstep

theorem kwAngularSplitBlocks_enter_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hconnect : kwPortOfDart G d.symm = e.1.fst) :
    (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d e =
      weight d.edge * kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 e.1 :=
  kwAngularSplit_enterBlock_apply_of_connect
    embedding weight d e hconnect

theorem kwAngularSplitBlocks_enter_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
    (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d e = 0 :=
  kwAngularSplit_enterBlock_apply_of_not_connect
    embedding weight d e hconnect

theorem kwAngularSplitBlocks_exit_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hconnect : d.1.snd = kwPortOfDart G e) :
    (kwAngularSplitBlocks embedding weight).toBlocks₂₁ d e =
      kwPortAngleRoot embedding (kwPortOfDart G e) :=
  kwAngularSplit_exitBlock_apply_of_connect
    embedding weight d e hconnect

theorem kwAngularSplitBlocks_exit_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hconnect : d.1.snd ≠ kwPortOfDart G e) :
    (kwAngularSplitBlocks embedding weight).toBlocks₂₁ d e = 0 :=
  kwAngularSplit_exitBlock_apply_of_not_connect
    embedding weight d e hconnect




noncomputable def kwAngularInternalExitSolution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    Matrix (KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
      G.Dart ℂ := fun d e ↦ by
        classical
        exact if KWOrderedInternalDartFacesPort (kwAngularPortOrder embedding)
            d (kwPortOfDart G e) then
          kwPortAngleRoot embedding (kwPortOfDart G e) else 0

theorem kwAngularInternalExitSolution_of_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart)
    (hfaces : KWOrderedInternalDartFacesPort
      (kwAngularPortOrder embedding) d (kwPortOfDart G e)) :
    kwAngularInternalExitSolution embedding d e =
      kwPortAngleRoot embedding (kwPortOfDart G e) := by
  unfold kwAngularInternalExitSolution
  rw [if_pos hfaces]

theorem kwAngularInternalExitSolution_of_not_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart)
    (hfaces : ¬KWOrderedInternalDartFacesPort
      (kwAngularPortOrder embedding) d (kwPortOfDart G e)) :
    kwAngularInternalExitSolution embedding d e = 0 := by
  unfold kwAngularInternalExitSolution
  rw [if_neg hfaces]



theorem kwAngularSplit_internal_mul_exitSolution_of_faces_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart)
    (hfaces : KWOrderedInternalDartFacesPort
      (kwAngularPortOrder embedding) d (kwPortOfDart G e))
    (hne : d.1.snd ≠ kwPortOfDart G e) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₂₂ *
      kwAngularInternalExitSolution embedding) d e =
      kwPortAngleRoot embedding (kwPortOfDart G e) := by
  classical
  rw [Matrix.mul_apply]
  have hddata := kwOrderedInternalSplitDart_adj_data G
    (kwAngularPortOrder embedding) d
  have hrankne : kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd ≠
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e) := by
    intro hrank
    apply hne
    exact kwDartPort_eq_of_fst_of_orderRank
      (kwAngularPortOrder embedding) hfaces.1 hrank
  rcases hfaces.2 with ⟨hdinc, hdtarget⟩ | ⟨hddec, hdtarget⟩
  · have htarget : kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd <
        kwOrderedPortRank (kwAngularPortOrder embedding)
          (kwPortOfDart G e) := by omega
    have hqcard := ((kwAngularPortOrder embedding)
      (kwPortOfDart G e).1 (kwPortOfDart G e).2).isLt
    change kwOrderedPortRank (kwAngularPortOrder embedding)
      (kwPortOfDart G e) <
        Fintype.card (KWOutgoingDart (G := G) (kwPortOfDart G e).1) at hqcard
    have hcardeq :
        Fintype.card (KWOutgoingDart (G := G) d.1.snd.1) =
          Fintype.card (KWOutgoingDart (G := G) (kwPortOfDart G e).1) :=
      congrArg (fun v ↦ Fintype.card (KWOutgoingDart (G := G) v)) hfaces.1
    have hbound : kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd + 1 <
        Fintype.card (KWOutgoingDart (G := G) d.1.snd.1) := by omega
    let next := kwOrderedIncreasingInternalDartFrom G
      (kwAngularPortOrder embedding) d.1.snd hbound
    have hstep : KWOrderedInternalDartStep G
        (kwAngularPortOrder embedding) d next :=
      kwOrderedInternalDartStep_increasingFrom G
        (kwAngularPortOrder embedding) d hdinc hbound
    have hnextfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) next (kwPortOfDart G e) :=
      kwOrderedInternalDartFacesPort_step G
        (kwAngularPortOrder embedding) hstep
        ⟨hfaces.1, Or.inl ⟨hdinc, hdtarget⟩⟩ hne
    calc
      ∑ f, (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d f *
          kwAngularInternalExitSolution embedding f e =
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d next *
            kwAngularInternalExitSolution embedding next e := by
        apply Fintype.sum_eq_single next
        intro f hfn
        by_cases hs : KWOrderedInternalDartStep G
            (kwAngularPortOrder embedding) d f
        · have hnf := kwOrderedInternalDartStep_rightUnique G
            (kwAngularPortOrder embedding) hstep hs
          exact (hfn hnf.symm).elim
        · rw [kwAngularSplitBlocks_internal_apply_of_not_step
            embedding weight d f hs, zero_mul]
      _ = kwPortAngleRoot embedding (kwPortOfDart G e) := by
        rw [kwAngularSplitBlocks_internal_apply_of_step
            embedding weight d next hstep, one_mul,
          kwAngularInternalExitSolution_of_faces
            embedding next e hnextfaces]
  · have htarget : kwOrderedPortRank (kwAngularPortOrder embedding)
          (kwPortOfDart G e) <
        kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd := by omega
    have hbound : 0 <
        kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd := by omega
    let next := kwOrderedDecreasingInternalDartFrom G
      (kwAngularPortOrder embedding) d.1.snd hbound
    have hstep : KWOrderedInternalDartStep G
        (kwAngularPortOrder embedding) d next :=
      kwOrderedInternalDartStep_decreasingFrom G
        (kwAngularPortOrder embedding) d hddec hbound
    have hnextfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) next (kwPortOfDart G e) :=
      kwOrderedInternalDartFacesPort_step G
        (kwAngularPortOrder embedding) hstep
        ⟨hfaces.1, Or.inr ⟨hddec, hdtarget⟩⟩ hne
    calc
      ∑ f, (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d f *
          kwAngularInternalExitSolution embedding f e =
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d next *
            kwAngularInternalExitSolution embedding next e := by
        apply Fintype.sum_eq_single next
        intro f hfn
        by_cases hs : KWOrderedInternalDartStep G
            (kwAngularPortOrder embedding) d f
        · have hnf := kwOrderedInternalDartStep_rightUnique G
            (kwAngularPortOrder embedding) hstep hs
          exact (hfn hnf.symm).elim
        · rw [kwAngularSplitBlocks_internal_apply_of_not_step
            embedding weight d f hs, zero_mul]
      _ = kwPortAngleRoot embedding (kwPortOfDart G e) := by
        rw [kwAngularSplitBlocks_internal_apply_of_step
            embedding weight d next hstep, one_mul,
          kwAngularInternalExitSolution_of_faces
            embedding next e hnextfaces]



theorem kwAngularSplit_internal_mul_exitSolution_of_snd_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hsnd : d.1.snd = kwPortOfDart G e) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₂₂ *
      kwAngularInternalExitSolution embedding) d e = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro f _
  by_cases hstep : KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d f
  · have hnot : ¬KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) f (kwPortOfDart G e) := by
      intro hfaces
      apply kwOrderedInternalDartStep_not_faces_snd G
        (kwAngularPortOrder embedding) hstep
      rwa [hsnd]
    rw [kwAngularSplitBlocks_internal_apply_of_step
        embedding weight d f hstep, one_mul,
      kwAngularInternalExitSolution_of_not_faces embedding f e hnot]
  · rw [kwAngularSplitBlocks_internal_apply_of_not_step
        embedding weight d f hstep, zero_mul]



theorem kwAngularSplit_internal_mul_exitSolution_of_not_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart)
    (hfaces : ¬KWOrderedInternalDartFacesPort
      (kwAngularPortOrder embedding) d (kwPortOfDart G e)) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₂₂ *
      kwAngularInternalExitSolution embedding) d e = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro f _
  by_cases hstep : KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d f
  · have hfnot : ¬KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) f (kwPortOfDart G e) := by
      intro hffaces
      apply hfaces
      exact kwOrderedInternalDartFacesPort_of_step G
        (kwAngularPortOrder embedding) hstep hffaces
    rw [kwAngularSplitBlocks_internal_apply_of_step
        embedding weight d f hstep, one_mul,
      kwAngularInternalExitSolution_of_not_faces embedding f e hfnot]
  · rw [kwAngularSplitBlocks_internal_apply_of_not_step
        embedding weight d f hstep, zero_mul]


theorem kwAngularSplit_exitSolution_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ) :
    (1 - (kwAngularSplitBlocks embedding weight).toBlocks₂₂) *
        kwAngularInternalExitSolution embedding =
      (kwAngularSplitBlocks embedding weight).toBlocks₂₁ := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  ext d e
  by_cases hsnd : d.1.snd = kwPortOfDart G e
  · have hfaces := kwOrderedInternalDartFacesPort_of_snd_eq G
      (kwAngularPortOrder embedding) d (kwPortOfDart G e) hsnd
    rw [Matrix.sub_apply,
      kwAngularInternalExitSolution_of_faces embedding d e hfaces,
      kwAngularSplit_internal_mul_exitSolution_of_snd_eq
        embedding weight d e hsnd,
      kwAngularSplitBlocks_exit_apply_of_connect
        embedding weight d e hsnd,
      sub_zero]
  · by_cases hfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) d (kwPortOfDart G e)
    · rw [Matrix.sub_apply,
        kwAngularInternalExitSolution_of_faces embedding d e hfaces,
        kwAngularSplit_internal_mul_exitSolution_of_faces_of_ne
          embedding weight d e hfaces hsnd,
        kwAngularSplitBlocks_exit_apply_of_not_connect
          embedding weight d e hsnd,
        sub_self]
    · rw [Matrix.sub_apply,
        kwAngularInternalExitSolution_of_not_faces embedding d e hfaces,
        kwAngularSplit_internal_mul_exitSolution_of_not_faces
          embedding weight d e hfaces,
        kwAngularSplitBlocks_exit_apply_of_not_connect
          embedding weight d e hsnd,
        sub_zero]



theorem kwAngularSplit_resolvent_mul_exit_eq_solution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (n : ℕ)
    (hpow : (kwAngularSplitBlocks embedding weight).toBlocks₂₂ ^ n = 0) :
    kwNilpotentResolvent
        (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
        (kwAngularSplitBlocks embedding weight).toBlocks₂₁ =
      kwAngularInternalExitSolution embedding := by
  calc
    kwNilpotentResolvent
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
          (kwAngularSplitBlocks embedding weight).toBlocks₂₁ =
        kwNilpotentResolvent
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
          ((1 - (kwAngularSplitBlocks embedding weight).toBlocks₂₂) *
            kwAngularInternalExitSolution embedding) := by
      rw [kwAngularSplit_exitSolution_equation embedding weight]
    _ = (kwNilpotentResolvent
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
          (1 - (kwAngularSplitBlocks embedding weight).toBlocks₂₂)) *
          kwAngularInternalExitSolution embedding := by
      rw [Matrix.mul_assoc]
    _ = kwAngularInternalExitSolution embedding := by
      rw [kwNilpotentResolvent_mul _ n hpow, Matrix.one_mul]




theorem kwAngularSplit_enter_mul_exitSolution_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : G.Dart) (hde : d.snd = e.fst) (hnb : d.edge ≠ e.edge) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₁₂ *
      kwAngularInternalExitSolution embedding) d e =
      weight d.edge * embedding.turnPhase d e := by
  classical
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  have hpfirst : p.1 = d.snd := by
    have h := kwDartOfPort_fst G p
    simpa [p] using h.symm
  have hqfirst : q.1 = e.fst := by
    have h := kwDartOfPort_fst G q
    simpa [q] using h.symm
  have hpqfirst : p.1 = q.1 := hpfirst.trans (hde.trans hqfirst.symm)
  have hpq : p ≠ q := by
    intro hpq
    have hdart := congrArg (kwDartOfPort G) hpq
    apply hnb
    have heq : d.symm = e := by simpa [p, q] using hdart
    rw [← heq]
    exact d.edge_symm.symm
  have hrankne : kwOrderedPortRank (kwAngularPortOrder embedding) p ≠
      kwOrderedPortRank (kwAngularPortOrder embedding) q := by
    intro hrank
    exact hpq (kwDartPort_eq_of_fst_of_orderRank
      (kwAngularPortOrder embedding) hpqfirst hrank)
  rw [Matrix.mul_apply]
  rcases lt_or_gt_of_ne hrankne with hrank | hrank
  · have hqcard := ((kwAngularPortOrder embedding) q.1 q.2).isLt
    change kwOrderedPortRank (kwAngularPortOrder embedding) q <
      Fintype.card (KWOutgoingDart (G := G) q.1) at hqcard
    have hcardeq : Fintype.card (KWOutgoingDart (G := G) p.1) =
        Fintype.card (KWOutgoingDart (G := G) q.1) :=
      congrArg (fun v ↦ Fintype.card (KWOutgoingDart (G := G) v)) hpqfirst
    have hbound : kwOrderedPortRank (kwAngularPortOrder embedding) p + 1 <
        Fintype.card (KWOutgoingDart (G := G) p.1) := by omega
    let first := kwOrderedIncreasingInternalDartFrom G
      (kwAngularPortOrder embedding) p hbound
    have hfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) first q :=
      kwOrderedIncreasingInternalDartFrom_faces G
        (kwAngularPortOrder embedding) p q hpqfirst hrank hbound
    have hconnect : p = first.1.fst := by simp [first]
    calc
      ∑ f, (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d f *
          kwAngularInternalExitSolution embedding f e =
          (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d first *
            kwAngularInternalExitSolution embedding first e := by
        apply Fintype.sum_eq_single first
        intro f hne
        by_cases hfconnect : p = f.1.fst
        · by_cases hffaces : KWOrderedInternalDartFacesPort
              (kwAngularPortOrder embedding) f q
          · have hffirst := kwOrderedInternalDart_eq_of_fst_eq_of_faces G
                (kwAngularPortOrder embedding)
                (hfconnect.symm.trans hconnect) hffaces hfaces
            exact (hne hffirst).elim
          · rw [kwAngularInternalExitSolution_of_not_faces
                embedding f e (by simpa [q] using hffaces), mul_zero]
        · rw [kwAngularSplitBlocks_enter_apply_of_not_connect
              embedding weight d f (by simpa [p] using hfconnect), zero_mul]
      _ = weight d.edge * embedding.turnPhase d e := by
        rw [kwAngularSplitBlocks_enter_apply_of_connect
            embedding weight d first (by simpa [p] using hconnect),
          kwAngularInternalExitSolution_of_faces
            embedding first e (by simpa [q] using hfaces)]
        have hphase := kwAngularSplitPhase_endpointProduct_of_rank_lt
          embedding d e hde (by simpa [p, q] using hrank) first first
          (by simpa [p] using hconnect.symm)
          (by simp [first])
        rw [kwAngularSplitPhase_internal_external] at hphase
        rw [← hphase]
        ring
  · have hbound : 0 <
        kwOrderedPortRank (kwAngularPortOrder embedding) p := by omega
    let first := kwOrderedDecreasingInternalDartFrom G
      (kwAngularPortOrder embedding) p hbound
    have hfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) first q :=
      kwOrderedDecreasingInternalDartFrom_faces G
        (kwAngularPortOrder embedding) p q hpqfirst hrank hbound
    have hconnect : p = first.1.fst := by simp [first]
    calc
      ∑ f, (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d f *
          kwAngularInternalExitSolution embedding f e =
          (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d first *
            kwAngularInternalExitSolution embedding first e := by
        apply Fintype.sum_eq_single first
        intro f hne
        by_cases hfconnect : p = f.1.fst
        · by_cases hffaces : KWOrderedInternalDartFacesPort
              (kwAngularPortOrder embedding) f q
          · have hffirst := kwOrderedInternalDart_eq_of_fst_eq_of_faces G
                (kwAngularPortOrder embedding)
                (hfconnect.symm.trans hconnect) hffaces hfaces
            exact (hne hffirst).elim
          · rw [kwAngularInternalExitSolution_of_not_faces
                embedding f e (by simpa [q] using hffaces), mul_zero]
        · rw [kwAngularSplitBlocks_enter_apply_of_not_connect
              embedding weight d f (by simpa [p] using hfconnect), zero_mul]
      _ = weight d.edge * embedding.turnPhase d e := by
        rw [kwAngularSplitBlocks_enter_apply_of_connect
            embedding weight d first (by simpa [p] using hconnect),
          kwAngularInternalExitSolution_of_faces
            embedding first e (by simpa [q] using hfaces)]
        have hphase := kwAngularSplitPhase_endpointProduct_of_rank_gt
          embedding d e hde (by simpa [p, q] using hrank) first first
          (by simpa [p] using hconnect.symm)
          (by
            have hs := kwOrderedDecreasingInternalDartFrom_rank_snd G
              (kwAngularPortOrder embedding) p hbound
            change kwOrderedPortRank (kwAngularPortOrder embedding) first.1.snd <
              kwOrderedPortRank (kwAngularPortOrder embedding) first.1.fst
            simp only [first, kwOrderedDecreasingInternalDartFrom_fst]
            omega)
        rw [kwAngularSplitPhase_internal_external] at hphase
        rw [← hphase]
        ring



theorem kwAngularSplit_enter_mul_exitSolution_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : G.Dart) (hstep : ¬(d.snd = e.fst ∧ d.edge ≠ e.edge)) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₁₂ *
      kwAngularInternalExitSolution embedding) d e = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro f _
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  by_cases hconnect : p = f.1.fst
  · by_cases hfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) f q
    · exfalso
      apply hstep
      have hpfirst : p.1 = d.snd := by
        have h := kwDartOfPort_fst G p
        simpa [p] using h.symm
      have hqfirst : q.1 = e.fst := by
        have h := kwDartOfPort_fst G q
        simpa [q] using h.symm
      have hfdata := kwOrderedInternalSplitDart_adj_data G
        (kwAngularPortOrder embedding) f
      have hde : d.snd = e.fst := by
        rw [← hpfirst, ← hqfirst, hconnect]
        exact hfdata.1.trans hfaces.1
      refine ⟨hde, ?_⟩
      intro hedge
      rw [SimpleGraph.dart_edge_eq_iff] at hedge
      rcases hedge with hedge | hedge
      · rw [hedge] at hde
        exact e.fst_ne_snd hde.symm
      · have hpq : p = q := by
          apply kwDartOfPort_injective G
          simp [p, q, hedge]
        apply kwOrderedInternalDart_not_faces_fst G
          (kwAngularPortOrder embedding) f
        have htarget : q = f.1.fst := hpq.symm.trans hconnect
        rwa [← htarget]
    · rw [kwAngularInternalExitSolution_of_not_faces
          embedding f e (by simpa [q] using hfaces), mul_zero]
  · rw [kwAngularSplitBlocks_enter_apply_of_not_connect
        embedding weight d f (by simpa [p] using hconnect), zero_mul]



theorem kwAngularSplit_enter_mul_exitSolution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ) :
    (kwAngularSplitBlocks embedding weight).toBlocks₁₂ *
        kwAngularInternalExitSolution embedding =
      kwGraphTransition G weight embedding.turnPhase := by
  ext d e
  unfold kwGraphTransition
  by_cases hstep : d.snd = e.fst ∧ d.edge ≠ e.edge
  · rw [if_pos hstep,
      kwAngularSplit_enter_mul_exitSolution_of_step
        embedding weight d e hstep.1 hstep.2]
  · rw [if_neg hstep,
      kwAngularSplit_enter_mul_exitSolution_of_not_step
        embedding weight d e hstep]



theorem kwAngularSplit_pathEffective_eq_original
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (n : ℕ)
    (hpow : (kwAngularSplitBlocks embedding weight).toBlocks₂₂ ^ n = 0) :
    (kwAngularSplitBlocks embedding weight).toBlocks₁₂ *
        kwNilpotentResolvent
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
        (kwAngularSplitBlocks embedding weight).toBlocks₂₁ =
      kwGraphTransition G weight embedding.turnPhase := by
  rw [Matrix.mul_assoc,
    kwAngularSplit_resolvent_mul_exit_eq_solution
      embedding weight n hpow,
    kwAngularSplit_enter_mul_exitSolution]





theorem kwAngularSplit_det_eq_original
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)).det =
      (1 - kwGraphTransition G weight embedding.turnPhase).det := by
  classical
  let M := kwGraphTransition
    (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
    (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)
  let R := kwAngularSplitBlocks embedding weight
  obtain ⟨n, hn⟩ := kwOrderedSplitInternalBlock_isNilpotent G
    (kwAngularPortOrder embedding) (kwOrderedSplitWeight G weight)
    (kwAngularSplitPhase embedding)
  change R.toBlocks₂₂ ^ n = 0 at hn
  have hzero : R.toBlocks₁₁ = 0 := by
    exact kwOrderedSplit_externalBlock_eq_zero G
      (kwAngularPortOrder embedding) (kwOrderedSplitWeight G weight)
      (kwAngularSplitPhase embedding)
  have hpath : R.toBlocks₁₂ * kwNilpotentResolvent R.toBlocks₂₂ n *
      R.toBlocks₂₁ = kwGraphTransition G weight embedding.turnPhase := by
    exact kwAngularSplit_pathEffective_eq_original embedding weight n hn
  have hsub : kwOrderedSplitTransitionInBlocks G
      (kwAngularPortOrder embedding) (1 - M) = 1 - R := by
    ext i j
    simp [kwOrderedSplitTransitionInBlocks, Matrix.reindex_apply,
      Matrix.one_apply, R, M, kwAngularSplitBlocks]
  change (1 - M).det = (1 - kwGraphTransition G weight embedding.turnPhase).det
  calc
    (1 - M).det =
        (kwOrderedSplitTransitionInBlocks G
          (kwAngularPortOrder embedding) (1 - M)).det :=
      (kwOrderedSplitTransitionInBlocks_det G
        (kwAngularPortOrder embedding) (1 - M)).symm
    _ = (1 - R).det := by rw [hsub]
    _ = (1 - Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂).det := by
      rw [Matrix.fromBlocks_toBlocks]
    _ = (1 - kwInternalGadgetTransition 0 R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂).det := by
      rw [hzero]
      rfl
    _ = (1 - kwEliminateAcyclicInternal 0 R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n).det :=
      kw_det_eliminateAcyclicInternal 0 R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n hn
    _ = (1 - kwGraphTransition G weight embedding.turnPhase).det := by
      unfold kwEliminateAcyclicInternal
      rw [zero_add, hpath]


theorem kwOrderedDartPortSplitGraph_degree_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) :
    (kwOrderedDartPortSplitGraph G order).degree p ≤ 3 := by
  classical
  let code : (kwOrderedDartPortSplitGraph G order).neighborSet p →
      Fin 3 := fun q ↦
    if kwDartOfPort G q.1 = (kwDartOfPort G p).symm then 0
    else if kwOrderedPortRank order q.1 + 1 =
        kwOrderedPortRank order p then 1
    else 2
  have hcode : Function.Injective code := by
    intro q r hqr
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    simp only [code] at hqr
    rw [SimpleGraph.mem_neighborSet,
      kwOrderedDartPortSplitGraph_adj] at hq hr
    by_cases hqext : kwDartOfPort G q = (kwDartOfPort G p).symm
    · have hrext : kwDartOfPort G r = (kwDartOfPort G p).symm := by
        by_contra hne
        simp only [hqext, ↓reduceIte, hne] at hqr
        split at hqr <;> omega
      apply Subtype.ext
      exact kwDartOfPort_injective G (hqext.trans hrext.symm)
    · by_cases hrext : kwDartOfPort G r = (kwDartOfPort G p).symm
      · simp only [hqext, hrext, ↓reduceIte] at hqr
        split at hqr <;> omega
      · have hqdata := hq.resolve_left hqext
        have hrdata := hr.resolve_left hrext
        by_cases hqpred : kwOrderedPortRank order q + 1 =
            kwOrderedPortRank order p
        · have hrpred : kwOrderedPortRank order r + 1 =
              kwOrderedPortRank order p := by
            by_contra hne
            simp [hqext, hrext, hqpred, hne] at hqr
          apply Subtype.ext
          apply kwDartPort_eq_of_fst_of_orderRank order
              (hqdata.1.symm.trans hrdata.1)
          omega
        · have hrpred : ¬(kwOrderedPortRank order r + 1 =
              kwOrderedPortRank order p) := by
            intro hp
            simp [hqext, hrext, hqpred, hp] at hqr
          have hqsucc : kwOrderedPortRank order p + 1 =
              kwOrderedPortRank order q := hqdata.2.resolve_right hqpred
          have hrsucc : kwOrderedPortRank order p + 1 =
              kwOrderedPortRank order r := hrdata.2.resolve_right hrpred
          apply Subtype.ext
          apply kwDartPort_eq_of_fst_of_orderRank order
              (hqdata.1.symm.trans hrdata.1)
          omega
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective code hcode

theorem kwOrderedDartPortSplitGraph_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    kwOrderedDartPortSplitGraph G (kwIdentityPortOrder G) =
      kwDartPortSplitGraph G := by
  ext p q
  rfl





def KWDartEdgeBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {b : G.Dart → Fin 2 // ∀ d, b d.symm = b d}

noncomputable instance KWDartEdgeBits_fintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (KWDartEdgeBits G) := by
  classical
  change Fintype {b : G.Dart → Fin 2 // ∀ d, b d.symm = b d}
  infer_instance


noncomputable def kwExternalPortBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (p : KWDartPort G) : Fin 2 :=
  b.1 (kwDartOfPort G p)

theorem kwExternalPortBits_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (p : KWDartPort G) :
    kwExternalPortBits G b (kwPortOfDart G (kwDartOfPort G p).symm) =
      kwExternalPortBits G b p := by
  simp only [kwExternalPortBits, kwDartOfPort_portOfDart]
  exact b.2 _



def KWOriginalPortEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) : Prop :=
  ∀ v, (∑ i : Fin (Fintype.card (KWOutgoingDart (G := G) v)),
    kwExternalPortBits G b ⟨v, i⟩) = 0



def KWPortChainField
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (v : V) → Fin (Fintype.card (KWOutgoingDart (G := G) v) + 1) → Fin 2

noncomputable instance KWPortChainField_fintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (KWPortChainField G) := by
  classical
  change Fintype ((v : V) →
    Fin (Fintype.card (KWOutgoingDart (G := G) v) + 1) → Fin 2)
  infer_instance



def KWGlobalPortChainEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (y : KWPortChainField G) : Prop :=
  ∀ v, KWPortChainEven
    (fun i ↦ kwExternalPortBits G b ⟨v, i⟩) (y v)


def kwPortAtOrderedRank
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v))) : KWDartPort G :=
  ⟨v, (order v).symm i⟩


def KWOrderedGlobalPortChainEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) : Prop :=
  ∀ v, KWPortChainEven
    (fun i ↦ kwExternalPortBits G b (kwPortAtOrderedRank order v i))
    (y v)

theorem kwOrderedExternalPortBits_sum_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G) (v : V) :
    (∑ i, kwExternalPortBits G b (kwPortAtOrderedRank order v i)) =
      ∑ i, kwExternalPortBits G b ⟨v, i⟩ := by
  exact Equiv.sum_comp (order v).symm
    (fun i ↦ kwExternalPortBits G b ⟨v, i⟩)



theorem kwOrderedDartPortSplit_existsUnique_internal_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G) :
    KWOriginalPortEven G b ↔ ∃! y : KWPortChainField G,
      KWOrderedGlobalPortChainEven G order b y := by
  constructor
  · intro hb
    let y : KWPortChainField G := fun v ↦ kwPortChainState
      (fun i ↦ kwExternalPortBits G b (kwPortAtOrderedRank order v i))
    refine ⟨y, ?_, ?_⟩
    · intro v
      refine ⟨kwPortChainState_zero _, kwPortChainState_succ _, ?_⟩
      apply (kwPortChainState_last_eq_zero_iff _).2
      rw [kwOrderedExternalPortBits_sum_eq G order b v, hb v]
    · intro z hz
      funext v
      exact kwPortChainState_unique _ (z v) (hz v).1 (hz v).2.1
  · rintro ⟨y, hy, -⟩
    intro v
    have hsum := kwPortChain_sum_eq_endpoints
      (fun i ↦ kwExternalPortBits G b (kwPortAtOrderedRank order v i))
      (y v) (hy v).2.1
    rw [(hy v).1, (hy v).2.2, add_zero] at hsum
    rw [← kwOrderedExternalPortBits_sum_eq G order b v]
    exact hsum


noncomputable def kwOrderedPortSplitAdjBit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (p q : KWDartPort G) : Fin 2 :=
  if kwDartOfPort G q = (kwDartOfPort G p).symm then
    kwExternalPortBits G b p
  else if kwOrderedPortRank order q + 1 = kwOrderedPortRank order p then
    y p.1 (order p.1 p.2).castSucc
  else
    y p.1 (order p.1 p.2).succ

theorem kwOrderedPortSplitAdjBit_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) {p q : KWDartPort G}
    (hpq : (kwOrderedDartPortSplitGraph G order).Adj p q) :
    kwOrderedPortSplitAdjBit G order b y p q =
      kwOrderedPortSplitAdjBit G order b y q p := by
  rw [kwOrderedDartPortSplitGraph_adj] at hpq
  by_cases hext : kwDartOfPort G q = (kwDartOfPort G p).symm
  · have hrev : kwDartOfPort G p = (kwDartOfPort G q).symm := by
      rw [hext]
      exact (kwDartOfPort G p).symm_symm.symm
    rw [kwOrderedPortSplitAdjBit, if_pos hext,
      kwOrderedPortSplitAdjBit, if_pos hrev]
    unfold kwExternalPortBits
    rw [hext, b.2]
  · have hrev : ¬kwDartOfPort G p = (kwDartOfPort G q).symm := by
      intro h
      apply hext
      rw [h]
      exact (kwDartOfPort G q).symm_symm.symm
    rcases hpq.resolve_left hext with ⟨hfst, hidx⟩
    rcases p with ⟨v, i⟩
    rcases q with ⟨w, j⟩
    dsimp only at hfst hidx ⊢
    subst w
    by_cases hpred : (order v j).val + 1 = (order v i).val
    · have hnotSucc : ¬((order v i).val + 1 = (order v j).val) := by
        omega
      have hpred' : kwOrderedPortRank order ⟨v, j⟩ + 1 =
          kwOrderedPortRank order ⟨v, i⟩ := hpred
      have hnotSucc' : ¬(kwOrderedPortRank order ⟨v, i⟩ + 1 =
          kwOrderedPortRank order ⟨v, j⟩) := hnotSucc
      rw [kwOrderedPortSplitAdjBit, if_neg hext, if_pos hpred',
        kwOrderedPortSplitAdjBit, if_neg hrev, if_neg hnotSucc']
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.succ]
      exact hpred.symm
    · have hsucc : (order v i).val + 1 = (order v j).val :=
        hidx.resolve_right hpred
      have hpred' : ¬(kwOrderedPortRank order ⟨v, j⟩ + 1 =
          kwOrderedPortRank order ⟨v, i⟩) := hpred
      have hsucc' : kwOrderedPortRank order ⟨v, i⟩ + 1 =
          kwOrderedPortRank order ⟨v, j⟩ := hsucc
      rw [kwOrderedPortSplitAdjBit, if_neg hext, if_neg hpred',
        kwOrderedPortSplitAdjBit, if_neg hrev, if_pos hsucc']
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.succ]
      exact hsucc


noncomputable def kwOrderedPortSplitIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (p : KWDartPort G) : Fin 2 :=
  kwExternalPortBits G b p +
    (if kwOrderedPortRank order p = 0 then 0
      else y p.1 (order p.1 p.2).castSucc) +
    (if kwOrderedPortRank order p + 1 =
        Fintype.card (KWOutgoingDart (G := G) p.1) then 0
      else y p.1 (order p.1 p.2).succ)

theorem kwOrderedPortSplitIncidence_eq_zero_of_globalEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G)
    (hy : KWOrderedGlobalPortChainEven G order b y) (p : KWDartPort G) :
    kwOrderedPortSplitIncidence G order b y p = 0 := by
  let i := order p.1 p.2
  have hp := hy p.1
  have hbit : kwExternalPortBits G b p =
      kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i) := by
    have heq : kwPortAtOrderedRank order p.1 i = p := by
      rcases p with ⟨v, j⟩
      simp [kwPortAtOrderedRank, i]
    rw [heq]
  have hleft :
      (if kwOrderedPortRank order p = 0 then 0
        else y p.1 i.castSucc) = y p.1 i.castSucc := by
    by_cases hzero : kwOrderedPortRank order p = 0
    · rw [if_pos hzero]
      symm
      rw [← hp.1]
      congr 1
      apply Fin.ext
      exact hzero
    · rw [if_neg hzero]
  have hright :
      (if kwOrderedPortRank order p + 1 =
          Fintype.card (KWOutgoingDart (G := G) p.1) then 0
        else y p.1 i.succ) = y p.1 i.succ := by
    by_cases hlast : kwOrderedPortRank order p + 1 =
        Fintype.card (KWOutgoingDart (G := G) p.1)
    · rw [if_pos hlast]
      symm
      rw [← hp.2.2]
      congr 1
      apply Fin.ext
      exact hlast
    · rw [if_neg hlast]
  unfold kwOrderedPortSplitIncidence
  rw [hbit, hleft, hright, hp.2.1 i]
  calc
    kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i) +
        y p.1 i.castSucc +
        (y p.1 i.castSucc +
          kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i)) =
      (kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i) +
          kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i)) +
        (y p.1 i.castSucc + y p.1 i.castSucc) := by ac_rfl
    _ = 0 := by rw [kw_fin_two_self_add, kw_fin_two_self_add, add_zero]




noncomputable def kwPortSplitAdjBit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (y : KWPortChainField G)
    (p q : KWDartPort G) : Fin 2 :=
  if kwDartOfPort G q = (kwDartOfPort G p).symm then
    kwExternalPortBits G b p
  else if q.2.val + 1 = p.2.val then
    y p.1 p.2.castSucc
  else
    y p.1 p.2.succ

theorem kwPortSplitAdjBit_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (y : KWPortChainField G)
    {p q : KWDartPort G} (hpq : (kwDartPortSplitGraph G).Adj p q) :
    kwPortSplitAdjBit G b y p q = kwPortSplitAdjBit G b y q p := by
  rw [kwDartPortSplitGraph_adj] at hpq
  by_cases hext : kwDartOfPort G q = (kwDartOfPort G p).symm
  · have hrev : kwDartOfPort G p = (kwDartOfPort G q).symm := by
      rw [hext]
      exact (kwDartOfPort G p).symm_symm.symm
    rw [kwPortSplitAdjBit, if_pos hext, kwPortSplitAdjBit, if_pos hrev]
    unfold kwExternalPortBits
    rw [hext, b.2]
  · have hrev : ¬kwDartOfPort G p = (kwDartOfPort G q).symm := by
      intro h
      apply hext
      rw [h]
      exact (kwDartOfPort G q).symm_symm.symm
    rcases hpq.resolve_left hext with ⟨hfst, hidx⟩
    rcases p with ⟨v, i⟩
    rcases q with ⟨w, j⟩
    dsimp only at hfst hidx ⊢
    subst w
    by_cases hpred : j.val + 1 = i.val
    · have hnotSucc : ¬(i.val + 1 = j.val) := by omega
      simp only [kwPortSplitAdjBit, hext, hrev, hpred, hnotSucc,
        ↓reduceIte]
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.succ]
      omega
    · have hsucc : i.val + 1 = j.val := hidx.resolve_right hpred
      simp only [kwPortSplitAdjBit, hext, hrev, hpred, hsucc,
        ↓reduceIte]
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.succ]
      exact hsucc



noncomputable def kwPortSplitIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (y : KWPortChainField G)
    (p : KWDartPort G) : Fin 2 :=
  kwExternalPortBits G b p +
    (if p.2.val = 0 then 0 else y p.1 p.2.castSucc) +
    (if p.2.val + 1 = Fintype.card (KWOutgoingDart (G := G) p.1)
      then 0 else y p.1 p.2.succ)



theorem kwPortSplitIncidence_eq_zero_of_globalEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (y : KWPortChainField G)
    (hy : KWGlobalPortChainEven G b y) (p : KWDartPort G) :
    kwPortSplitIncidence G b y p = 0 := by
  let n := Fintype.card (KWOutgoingDart (G := G) p.1)
  let bit : Fin n → Fin 2 := fun i ↦ kwExternalPortBits G b ⟨p.1, i⟩
  have hp := hy p.1
  have hleft :
      (if p.2.val = 0 then 0 else y p.1 p.2.castSucc) =
        y p.1 p.2.castSucc := by
    by_cases hzero : p.2.val = 0
    · rw [if_pos hzero]
      symm
      rw [← hp.1]
      congr 1
      apply Fin.ext
      simpa using hzero
    · rw [if_neg hzero]
  have hright :
      (if p.2.val + 1 = n then 0 else y p.1 p.2.succ) =
        y p.1 p.2.succ := by
    by_cases hlast : p.2.val + 1 = n
    · rw [if_pos hlast]
      symm
      rw [← hp.2.2]
      congr 1
      apply Fin.ext
      simpa [n] using hlast
    · rw [if_neg hlast]
  change bit p.2 +
      (if p.2.val = 0 then 0 else y p.1 p.2.castSucc) +
      (if p.2.val + 1 = n then 0 else y p.1 p.2.succ) = 0
  rw [hleft, hright, hp.2.1 p.2]
  calc
    bit p.2 + y p.1 p.2.castSucc +
        (y p.1 p.2.castSucc + bit p.2) =
      (bit p.2 + bit p.2) +
        (y p.1 p.2.castSucc + y p.1 p.2.castSucc) := by ac_rfl
    _ = 0 := by rw [kw_fin_two_self_add, kw_fin_two_self_add, add_zero]




theorem kwDartPortSplit_existsUnique_internal_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : KWDartEdgeBits G) :
    KWOriginalPortEven G b ↔ ∃! y : KWPortChainField G,
      KWGlobalPortChainEven G b y := by
  constructor
  · intro hb
    let y : KWPortChainField G := fun v ↦
      kwPortChainState (fun i ↦ kwExternalPortBits G b ⟨v, i⟩)
    refine ⟨y, ?_, ?_⟩
    · intro v
      exact ⟨kwPortChainState_zero _, kwPortChainState_succ _,
        (kwPortChainState_last_eq_zero_iff _).2 (hb v)⟩
    · intro z hz
      funext v
      exact kwPortChainState_unique _ (z v) (hz v).1 (hz v).2.1
  · rintro ⟨y, hy, -⟩
    intro v
    have hsum := kwPortChain_sum_eq_endpoints
      (fun i ↦ kwExternalPortBits G b ⟨v, i⟩) (y v) (hy v).2.1
    rw [(hy v).1, (hy v).2.2, add_zero] at hsum
    exact hsum



noncomputable def kwCanonicalPortChainField
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : KWDartEdgeBits G) :
    KWPortChainField G := fun v ↦
  kwPortChainState (fun i ↦ kwExternalPortBits G b ⟨v, i⟩)

theorem kwCanonicalPortChainField_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : KWDartEdgeBits G)
    (hb : KWOriginalPortEven G b) :
    KWGlobalPortChainEven G b (kwCanonicalPortChainField G b) := by
  intro v
  exact ⟨kwPortChainState_zero _, kwPortChainState_succ _,
    (kwPortChainState_last_eq_zero_iff _).2 (hb v)⟩

theorem kwPortChainField_eq_canonical
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (hy : KWGlobalPortChainEven G b y) :
    y = kwCanonicalPortChainField G b := by
  funext v
  exact kwPortChainState_unique _ (y v) (hy v).1 (hy v).2.1

theorem kwOriginalPortEven_of_globalPortChainEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (hy : KWGlobalPortChainEven G b y) :
    KWOriginalPortEven G b := by
  intro v
  have hsum := kwPortChain_sum_eq_endpoints
    (fun i ↦ kwExternalPortBits G b ⟨v, i⟩) (y v) (hy v).2.1
  rw [(hy v).1, (hy v).2.2, add_zero] at hsum
  exact hsum


def KWOriginalEvenBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {b : KWDartEdgeBits G // KWOriginalPortEven G b}

noncomputable instance KWOriginalEvenBits_fintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (KWOriginalEvenBits G) := by
  classical
  change Fintype {b : KWDartEdgeBits G // KWOriginalPortEven G b}
  infer_instance



def KWSplitEvenBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {p : KWDartEdgeBits G × KWPortChainField G //
    KWGlobalPortChainEven G p.1 p.2}

noncomputable instance KWSplitEvenBits_fintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (KWSplitEvenBits G) := by
  classical
  change Fintype {p : KWDartEdgeBits G × KWPortChainField G //
    KWGlobalPortChainEven G p.1 p.2}
  infer_instance



noncomputable def kwDartPortSplitEvenEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    KWOriginalEvenBits G ≃ KWSplitEvenBits G where
  toFun b := ⟨⟨b.1, kwCanonicalPortChainField G b.1⟩,
    kwCanonicalPortChainField_even G b.1 b.2⟩
  invFun p := ⟨p.1.1,
    kwOriginalPortEven_of_globalPortChainEven G p.1.1 p.1.2 p.2⟩
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (kwPortChainField_eq_canonical G p.1.1 p.1.2 p.2).symm




theorem kwDartPortSplit_weightedEnumerator_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : KWDartEdgeBits G → ℂ) :
    (∑ b : KWOriginalEvenBits G, W b.1) =
      ∑ p : KWSplitEvenBits G, W p.1.1 := by
  classical
  apply Fintype.sum_equiv (kwDartPortSplitEvenEquiv G)
  intro b
  rfl








theorem kw_det_portSplit_of_effective_gauge
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (original external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ)
    (nilpotenceIndex : ℕ) (hpow : internal ^ nilpotenceIndex = 0)
    (gauge : External → ℂ) (hgauge : ∀ i, gauge i ≠ 0)
    (heffective :
      kwEliminateAcyclicInternal external enter exit internal
          nilpotenceIndex = kwGaugeConjugate gauge original) :
    (1 - kwInternalGadgetTransition external enter exit internal).det =
      (1 - original).det := by
  rw [kw_det_eliminateAcyclicInternal external enter exit internal
      nilpotenceIndex hpow,
    heffective, kw_det_one_sub_gaugeConjugate gauge original hgauge]

end StatMech.FrontierA
