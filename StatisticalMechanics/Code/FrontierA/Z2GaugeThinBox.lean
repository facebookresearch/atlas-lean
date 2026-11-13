/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.Z2GaugeIsingAdapter
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section



section TreeCutSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



theorem cutSpace_eq_edgePowerset_of_isTree [Nonempty V] (hG : G.IsTree) :
    cutSpace G = G.edgeFinset.powerset := by
  have hmaps :
      ((Finset.univ : Finset (ConfigSpace V)) : Set (ConfigSpace V)).MapsTo
        (cutEdges G) (cutSpace G) := by
    intro s _
    change cutEdges G s ∈ cutSpace G
    rw [cutSpace, Finset.mem_image]
    exact ⟨s, Finset.mem_univ s, rfl⟩
  have hfiber : ∀ delta ∈ cutSpace G,
      ((Finset.univ.filter
        (fun s : ConfigSpace V => cutEdges G s = delta)).card) = 2 := by
    intro delta hdelta
    rw [cutSpace, Finset.mem_image] at hdelta
    obtain ⟨s, _, hs⟩ := hdelta
    exact fiber_card_eq_two G hG.preconnected hs
  have hcutCard : 2 * (cutSpace G).card =
      Fintype.card (ConfigSpace V) := by
    have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_univ] at hpartition
    calc
      2 * (cutSpace G).card =
          ∑ delta ∈ cutSpace G, 2 := by
            simp [mul_comm]
      _ = ∑ delta ∈ cutSpace G,
          (Finset.univ.filter
            (fun s : ConfigSpace V => cutEdges G s = delta)).card := by
            apply Finset.sum_congr rfl
            intro delta hdelta
            exact (hfiber delta hdelta).symm
      _ = Fintype.card (ConfigSpace V) := hpartition.symm
  have hpowerCard : 2 * G.edgeFinset.powerset.card =
      Fintype.card (ConfigSpace V) := by
    rw [Finset.card_powerset, Fintype.card_fun, Fintype.card_bool]
    rw [← hG.card_edgeFinset]
    simp [pow_succ']
  have hcard : (cutSpace G).card = G.edgeFinset.powerset.card := by
    omega
  apply Finset.eq_of_subset_of_card_le
  · intro delta hdelta
    rw [Finset.mem_powerset]
    rw [cutSpace, Finset.mem_image] at hdelta
    obtain ⟨s, _, rfl⟩ := hdelta
    exact Finset.filter_subset _ _
  · exact hcard.ge

end TreeCutSpace



local instance thinBoxPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p


abbrev thinBoxDualGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.pathGraph (n + 1)

local instance thinBoxAdjDecidable (n : ℕ) :
    DecidableRel (thinBoxDualGraph n).Adj := Classical.decRel _


abbrev thinBoxPlaquette (n : ℕ) := Fin n



abbrev thinBoxGaugeEdge := Fin 0


def thinBoxIncidence (n : ℕ) :
    thinBoxPlaquette n → Finset thinBoxGaugeEdge :=
  fun _ => ∅


def thinBoxPlaquetteEdge (n : ℕ) (i : thinBoxPlaquette n) :
    (thinBoxDualGraph n).edgeFinset :=
  ⟨s(i.castSucc, i.succ), by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.pathGraph_adj]
    left
    simp⟩

theorem thinBoxPlaquetteEdge_injective (n : ℕ) :
    Function.Injective (thinBoxPlaquetteEdge n) := by
  intro i j hij
  have hedge : s(i.castSucc, i.succ) = s(j.castSucc, j.succ) :=
    congrArg Subtype.val hij
  rcases Sym2.eq_iff.mp hedge with h | h
  · exact Fin.ext (by simpa using congrArg Fin.val h.1)
  · have hleft := congrArg Fin.val h.1
    have hright := congrArg Fin.val h.2
    simp only [Fin.val_castSucc, Fin.val_succ] at hleft hright
    omega

theorem thinBoxPlaquetteEdge_surjective (n : ℕ) :
    Function.Surjective (thinBoxPlaquetteEdge n) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj : u.val + 1 = v.val ∨ v.val + 1 = u.val := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.pathGraph_adj] using he
      rcases hadj with huv | hvu
      · let i : Fin n := ⟨u.val, by omega⟩
        refine ⟨i, ?_⟩
        apply Subtype.ext
        change s(i.castSucc, i.succ) = s(u, v)
        apply Sym2.eq_iff.mpr
        left
        constructor <;> apply Fin.ext <;> simp [i, huv]
      · let i : Fin n := ⟨v.val, by omega⟩
        refine ⟨i, ?_⟩
        apply Subtype.ext
        change s(i.castSucc, i.succ) = s(u, v)
        apply Sym2.eq_iff.mpr
        right
        constructor <;> apply Fin.ext <;> simp [i, hvu]


def thinBoxDualEdge (n : ℕ) :
    thinBoxPlaquette n ≃ (thinBoxDualGraph n).edgeFinset :=
  Equiv.ofBijective (thinBoxPlaquetteEdge n)
    ⟨thinBoxPlaquetteEdge_injective n, thinBoxPlaquetteEdge_surjective n⟩


theorem thinBoxDualGraph_isTree (n : ℕ) :
    (thinBoxDualGraph n).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · simpa [thinBoxDualGraph] using SimpleGraph.pathGraph_connected n
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      Nat.card_eq_fintype_card]
    have hcard := Fintype.card_congr (thinBoxDualEdge n)
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      congrArg (fun k => k + 1) hcard.symm


theorem thinBox_isClosed (n : ℕ) (A : Finset (thinBoxPlaquette n)) :
    IsClosedPlaquetteSet (thinBoxIncidence n) A := by
  intro e
  exact Fin.elim0 e


def thinBoxPlaquettePreimage (n : ℕ)
    (delta : Finset (Sym2 (Fin (n + 1)))) :
    Finset (thinBoxPlaquette n) :=
  ((thinBoxDualGraph n).edgeFinset.attach.filter
      (fun e => e.1 ∈ delta)).map (thinBoxDualEdge n).symm.toEmbedding

@[simp] theorem mem_thinBoxPlaquettePreimage (n : ℕ)
    (delta : Finset (Sym2 (Fin (n + 1)))) (p : thinBoxPlaquette n) :
    p ∈ thinBoxPlaquettePreimage n delta ↔
      (thinBoxDualEdge n p).1 ∈ delta := by
  simp [thinBoxPlaquettePreimage]



def thinBoxSurfaceEquiv (n : ℕ) :
    {A : Finset (thinBoxPlaquette n) //
        A ∈ gaugeClosedSurfaceFamily (thinBoxIncidence n)} ≃
      {delta : Finset (Sym2 (Fin (n + 1))) //
        delta ∈ cutSpace (thinBoxDualGraph n)} where
  toFun A := ⟨A.1.map (dualPlaquetteEmbedding (thinBoxDualEdge n)), by
    rw [cutSpace_eq_edgePowerset_of_isTree _ (thinBoxDualGraph_isTree n),
      Finset.mem_powerset]
    intro e he
    rw [Finset.mem_map] at he
    obtain ⟨p, _, rfl⟩ := he
    exact (thinBoxDualEdge n p).2⟩
  invFun delta := ⟨thinBoxPlaquettePreimage n delta.1, by
    rw [gaugeClosedSurfaceFamily, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), thinBox_isClosed n _⟩⟩
  left_inv A := by
    apply Subtype.ext
    ext p
    rw [mem_thinBoxPlaquettePreimage, Finset.mem_map]
    constructor
    · rintro ⟨q, hq, hqp⟩
      have hedge : thinBoxDualEdge n q = thinBoxDualEdge n p := by
        apply Subtype.ext
        exact hqp
      have hpq : q = p := (thinBoxDualEdge n).injective hedge
      simpa [hpq] using hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  right_inv delta := by
    apply Subtype.ext
    ext e
    constructor
    · intro he
      rw [Finset.mem_map] at he
      obtain ⟨p, hp, rfl⟩ := he
      exact (mem_thinBoxPlaquettePreimage n delta.1 p).mp hp
    · intro he
      have hsubset : delta.1 ⊆ (thinBoxDualGraph n).edgeFinset := by
        have hpow : delta.1 ∈ (thinBoxDualGraph n).edgeFinset.powerset := by
          rw [← cutSpace_eq_edgePowerset_of_isTree _ (thinBoxDualGraph_isTree n)]
          exact delta.2
        exact Finset.mem_powerset.mp hpow
      let p := (thinBoxDualEdge n).symm ⟨e, hsubset he⟩
      rw [Finset.mem_map]
      refine ⟨p, (mem_thinBoxPlaquettePreimage n delta.1 p).mpr ?_, ?_⟩
      · simpa [p]
      · change (thinBoxDualEdge n p).1 = e
        simp [p]

@[simp] theorem thinBoxSurfaceEquiv_apply (n : ℕ)
    (A : {A : Finset (thinBoxPlaquette n) //
      A ∈ gaugeClosedSurfaceFamily (thinBoxIncidence n)}) :
    (thinBoxSurfaceEquiv n A).1 =
      A.1.map (dualPlaquetteEmbedding (thinBoxDualEdge n)) :=
  rfl



theorem thinBox_gaugePartition_isingDuality (n : ℕ)
    (K : thinBoxPlaquette n → ℝ) (hK : ∀ p, 0 < K p) :
    (Real.exp (∑ e ∈ (thinBoxDualGraph n).edgeFinset,
          dualIsingCoupling (thinBoxDualEdge n) K e) * 2) *
        gaugePartition (thinBoxIncidence n) K =
      ((2 : ℝ) ^ Fintype.card thinBoxGaugeEdge *
          ∏ p : thinBoxPlaquette n, Real.cosh (K p)) *
        ZJ (thinBoxDualGraph n).edgeFinset
          (dualIsingCoupling (thinBoxDualEdge n) K) (fun _ => 0) := by
  exact gaugePartition_isingDuality
    (SimpleGraph.pathGraph_preconnected (n + 1))
    (thinBoxIncidence n) K hK (thinBoxDualEdge n)
    (thinBoxSurfaceEquiv n) (thinBoxSurfaceEquiv_apply n)

end

end StatMech.FrontierA
