/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.FK.TriHexPeriodicDual
import Code.BeffaraDC.Duality

open Finset Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

abbrev TorusSite (L : ℕ) := ZMod L × ZMod L
abbrev TriHexTorusEdgeIndex (L : ℕ) := TorusSite L × Fin 3
abbrev HexTorusVertex (L : ℕ) := TorusSite L × Bool

instance triHexTorusNeZero (L : ℕ) [Fact (2 < L)] : NeZero L :=
  ⟨by have := (Fact.out : 2 < L); omega⟩

private theorem zmod_one_ne_zero (L : ℕ) [Fact (2 < L)] :
    (1 : ZMod L) ≠ 0 := by
  have h : ((1 : ℕ) : ZMod L) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd
    have := (Fact.out : 2 < L)
    omega
  simpa using h

private theorem zmod_two_ne_zero (L : ℕ) [Fact (2 < L)] :
    (2 : ZMod L) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod L) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    have := (Fact.out : 2 < L)
    omega
  simpa using h


def triangularTorusStep (L : ℕ) (i : Fin 3) : TorusSite L :=
  ![(1, 0), (0, 1), (-1, 1)] i


def hexagonalTorusStep (L : ℕ) (i : Fin 3) : TorusSite L :=
  ![(1, 0), (0, 1), (1, 1)] i

theorem triangularTorusStep_ne_zero (L : ℕ) [Fact (2 < L)] (i : Fin 3) :
    triangularTorusStep L i ≠ 0 := by
  fin_cases i <;> intro h
  · exact zmod_one_ne_zero L (congrArg Prod.fst h)
  · exact zmod_one_ne_zero L (congrArg Prod.snd h)
  · exact zmod_one_ne_zero L (by
      have hs := congrArg Prod.snd h
      simpa [triangularTorusStep] using hs)

theorem triangularTorusStep_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (triangularTorusStep L) := by
  have h1 := zmod_one_ne_zero L
  have h2 := zmod_two_ne_zero L
  have hm : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangularTorusStep]

theorem triangularTorusStep_add_ne_zero (L : ℕ) [Fact (2 < L)]
    (i j : Fin 3) :
    triangularTorusStep L i + triangularTorusStep L j ≠ 0 := by
  have h1 := zmod_one_ne_zero L
  have h2 := zmod_two_ne_zero L
  fin_cases i <;> fin_cases j <;> intro h <;>
    simp only [triangularTorusStep, Nat.succ_eq_add_one, Nat.reduceAdd,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Prod.mk_add_mk, Prod.mk_eq_zero, add_zero, zero_add, add_neg_cancel,
      neg_add_cancel, and_true, true_and, and_self, neg_eq_zero] at h
  all_goals first
    | exact h2 (by linear_combination h)
    | exact h2 (by linear_combination -h.1)
    | exact h2 (by linear_combination -h.2)
    | exact h1 (by linear_combination h)
    | exact h2 h.1
    | exact h2 h.2
    | exact h1 h.1

theorem hexagonalTorusStep_ne_zero (L : ℕ) [Fact (2 < L)] (i : Fin 3) :
    hexagonalTorusStep L i ≠ 0 := by
  fin_cases i <;> intro h
  · exact zmod_one_ne_zero L (congrArg Prod.fst h)
  · exact zmod_one_ne_zero L (congrArg Prod.snd h)
  · exact zmod_one_ne_zero L (congrArg Prod.fst h)

theorem hexagonalTorusStep_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (hexagonalTorusStep L) := by
  have h1 := zmod_one_ne_zero L
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [hexagonalTorusStep]


def triangularTorusIndexedEdge (L : ℕ) (a : TriHexTorusEdgeIndex L) :
    Sym2 (TorusSite L) :=
  s(a.1, a.1 + triangularTorusStep L a.2)


def triangularTorusGraph (L : ℕ) [Fact (2 < L)] : SimpleGraph (TorusSite L) where
  Adj x y := ∃ a : TriHexTorusEdgeIndex L,
    triangularTorusIndexedEdge L a = s(x, y)
  symm := by
    rintro x y ⟨a, h⟩
    exact ⟨a, h.trans Sym2.eq_swap⟩
  loopless := ⟨by
    rintro x ⟨⟨z, i⟩, h⟩
    rw [triangularTorusIndexedEdge, Sym2.eq_iff] at h
    rcases h with h | h
    · obtain ⟨hleft, hright⟩ := h
      apply triangularTorusStep_ne_zero L i
      have hz : z + triangularTorusStep L i = z + 0 := by
        rw [hleft] at hright
        simpa using hright
      exact add_left_cancel hz
    · obtain ⟨hleft, hright⟩ := h
      apply triangularTorusStep_ne_zero L i
      have hz : z + triangularTorusStep L i = z + 0 := by
        rw [hleft] at hright
        simpa using hright
      exact add_left_cancel hz⟩

noncomputable instance (L : ℕ) [Fact (2 < L)] :
    DecidableRel (triangularTorusGraph L).Adj := Classical.decRel _

theorem triangularTorusIndexedEdge_mem (L : ℕ) [Fact (2 < L)]
    (a : TriHexTorusEdgeIndex L) :
    triangularTorusIndexedEdge L a ∈ (triangularTorusGraph L).edgeSet := by
  change (triangularTorusGraph L).Adj a.1
    (a.1 + triangularTorusStep L a.2)
  exact ⟨a, rfl⟩

def triangularTorusEdgeChart (L : ℕ) [Fact (2 < L)]
    (a : TriHexTorusEdgeIndex L) : (triangularTorusGraph L).edgeSet :=
  ⟨triangularTorusIndexedEdge L a, triangularTorusIndexedEdge_mem L a⟩

theorem triangularTorusEdgeChart_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (triangularTorusEdgeChart L) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have he : s(x, x + triangularTorusStep L i) =
      s(y, y + triangularTorusStep L j) := congrArg Subtype.val h
  rw [Sym2.eq_iff] at he
  rcases he with hdir | hswap
  · have hxy : x = y := hdir.1
    subst y
    have hs : triangularTorusStep L i = triangularTorusStep L j :=
      add_left_cancel hdir.2
    exact Prod.ext rfl (triangularTorusStep_injective L hs)
  · have hsecond := hswap.2
    rw [hswap.1] at hsecond
    have hzero : triangularTorusStep L j + triangularTorusStep L i = 0 := by
      apply add_left_cancel (a := y)
      simpa [add_assoc] using hsecond
    exact (triangularTorusStep_add_ne_zero L j i hzero).elim

theorem triangularTorusEdgeChart_surjective (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (triangularTorusEdgeChart L) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨a, ha⟩ := he
      exact ⟨a, Subtype.ext ha⟩


noncomputable def triangularTorusEdgeChartEquiv (L : ℕ) [Fact (2 < L)] :
    TriHexTorusEdgeIndex L ≃ (triangularTorusGraph L).edgeSet :=
  Equiv.ofBijective (triangularTorusEdgeChart L)
    ⟨triangularTorusEdgeChart_injective L, triangularTorusEdgeChart_surjective L⟩


def hexagonalTorusIndexedEdge (L : ℕ) (a : TriHexTorusEdgeIndex L) :
    Sym2 (HexTorusVertex L) :=
  s((a.1, false), (a.1 + hexagonalTorusStep L a.2, true))


def hexagonalTorusGraph (L : ℕ) [Fact (2 < L)] :
    SimpleGraph (HexTorusVertex L) where
  Adj u v := ∃ a : TriHexTorusEdgeIndex L,
    hexagonalTorusIndexedEdge L a = s(u, v)
  symm := by
    rintro u v ⟨a, h⟩
    exact ⟨a, h.trans Sym2.eq_swap⟩
  loopless := ⟨by
    rintro u ⟨a, h⟩
    rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at h
    rcases h with h | h
    · have hb : (false : Bool) = true := congrArg Prod.snd (h.1.trans h.2.symm)
      simp at hb
    · have hb : (false : Bool) = true := congrArg Prod.snd (h.1.trans h.2.symm)
      simp at hb⟩

noncomputable instance (L : ℕ) [Fact (2 < L)] :
    DecidableRel (hexagonalTorusGraph L).Adj := Classical.decRel _

theorem hexagonalTorusIndexedEdge_mem (L : ℕ) [Fact (2 < L)]
    (a : TriHexTorusEdgeIndex L) :
    hexagonalTorusIndexedEdge L a ∈ (hexagonalTorusGraph L).edgeSet := by
  change (hexagonalTorusGraph L).Adj (a.1, false)
    (a.1 + hexagonalTorusStep L a.2, true)
  exact ⟨a, rfl⟩

def hexagonalTorusEdgeChart (L : ℕ) [Fact (2 < L)]
    (a : TriHexTorusEdgeIndex L) : (hexagonalTorusGraph L).edgeSet :=
  ⟨hexagonalTorusIndexedEdge L a, hexagonalTorusIndexedEdge_mem L a⟩

theorem hexagonalTorusEdgeChart_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (hexagonalTorusEdgeChart L) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have he : s((x, false), (x + hexagonalTorusStep L i, true)) =
      s((y, false), (y + hexagonalTorusStep L j, true)) :=
    congrArg Subtype.val h
  rw [Sym2.eq_iff] at he
  rcases he with hdir | hswap
  · have hxy : x = y := congrArg Prod.fst hdir.1
    subst y
    have hs0 : x + hexagonalTorusStep L i =
        x + hexagonalTorusStep L j := congrArg Prod.fst hdir.2
    exact Prod.ext rfl (hexagonalTorusStep_injective L (add_left_cancel hs0))
  · have hb : (false : Bool) = true := congrArg Prod.snd hswap.1
    simp at hb

theorem hexagonalTorusEdgeChart_surjective (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (hexagonalTorusEdgeChart L) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨a, ha⟩ := he
      exact ⟨a, Subtype.ext ha⟩


noncomputable def hexagonalTorusEdgeChartEquiv (L : ℕ) [Fact (2 < L)] :
    TriHexTorusEdgeIndex L ≃ (hexagonalTorusGraph L).edgeSet :=
  Equiv.ofBijective (hexagonalTorusEdgeChart L)
    ⟨hexagonalTorusEdgeChart_injective L, hexagonalTorusEdgeChart_surjective L⟩


def triHexTorusIndexEquiv (L : ℕ) :
    TriHexTorusEdgeIndex L ≃ TriHexTorusEdgeIndex L where
  toFun a := (if a.2 = 2 then a.1 - (1, 0) else a.1, a.2)
  invFun a := (if a.2 = 2 then a.1 + (1, 0) else a.1, a.2)
  left_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp
  right_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp


noncomputable def triHexTorusDualEdgeEquiv (L : ℕ) [Fact (2 < L)] :
    (triangularTorusGraph L).edgeSet ≃ (hexagonalTorusGraph L).edgeSet :=
  (triangularTorusEdgeChartEquiv L).symm.trans
    ((triHexTorusIndexEquiv L).trans (hexagonalTorusEdgeChartEquiv L))


noncomputable def triHexTorusPrimalOfDualEdge (L : ℕ) [Fact (2 < L)]
    (e : Sym2 (HexTorusVertex L)) : Sym2 (TorusSite L) :=
  if he : e ∈ (hexagonalTorusGraph L).edgeSet then
    ((triHexTorusDualEdgeEquiv L).symm ⟨e, he⟩ :
      (triangularTorusGraph L).edgeSet)
  else s((0, 0), (0, 0))

theorem triHexTorusPrimalOfDualEdge_mem (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (HexTorusVertex L)}
    (he : e ∈ (hexagonalTorusGraph L).edgeFinset) :
    triHexTorusPrimalOfDualEdge L e ∈
      (triangularTorusGraph L).edgeFinset := by
  have heSet : e ∈ (hexagonalTorusGraph L).edgeSet := by
    simpa [SimpleGraph.edgeFinset] using he
  simp only [triHexTorusPrimalOfDualEdge, dif_pos heSet]
  change (((triHexTorusDualEdgeEquiv L).symm ⟨e, heSet⟩ :
    (triangularTorusGraph L).edgeSet) : Sym2 (TorusSite L)) ∈
      (triangularTorusGraph L).edgeSet.toFinset
  rw [Set.mem_toFinset]
  exact ((triHexTorusDualEdgeEquiv L).symm ⟨e, heSet⟩).2

theorem triHexTorusPrimalOfDualEdge_injOn (L : ℕ) [Fact (2 < L)] :
    Set.InjOn (triHexTorusPrimalOfDualEdge L)
      (↑(hexagonalTorusGraph L).edgeFinset :
        Set (Sym2 (HexTorusVertex L))) := by
  intro e he e' he' h
  have heSet : e ∈ (hexagonalTorusGraph L).edgeSet := by
    simpa [SimpleGraph.edgeFinset] using he
  have heSet' : e' ∈ (hexagonalTorusGraph L).edgeSet := by
    simpa [SimpleGraph.edgeFinset] using he'
  simp only [triHexTorusPrimalOfDualEdge, dif_pos heSet, dif_pos heSet'] at h
  exact congrArg Subtype.val ((triHexTorusDualEdgeEquiv L).symm.injective
    (Subtype.ext h))


noncomputable def triHexTorusDualConfig (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L))) :
    ConfigSpace (Sym2 (HexTorusVertex L)) := fun e =>
  if _ : e ∈ (hexagonalTorusGraph L).edgeSet then
    !(omega (triHexTorusPrimalOfDualEdge L e))
  else false


theorem triHexTorus_dual_openCount (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L))) :
    FK.openCount (hexagonalTorusGraph L) (triHexTorusDualConfig L omega) =
      (hexagonalTorusGraph L).edgeFinset.card -
        FK.openCount (triangularTorusGraph L) omega := by
  classical
  unfold FK.openCount
  let EH := (hexagonalTorusGraph L).edgeFinset
  let ET := (triangularTorusGraph L).edgeFinset
  have hcardE : EH.card = ET.card := by
    simpa [EH, ET, SimpleGraph.edgeFinset] using
      (Fintype.card_congr (triHexTorusDualEdgeEquiv L)).symm
  have hopen : EH.filter (fun e => triHexTorusDualConfig L omega e = true) =
      EH.filter (fun e => omega (triHexTorusPrimalOfDualEdge L e) = false) := by
    ext e
    simp only [Finset.mem_filter]
    by_cases he : e ∈ EH
    · have heSet : e ∈ (hexagonalTorusGraph L).edgeSet := by
        simpa [EH, SimpleGraph.edgeFinset] using he
      simp only [he, true_and, triHexTorusDualConfig, dif_pos heSet]
      cases omega (triHexTorusPrimalOfDualEdge L e) <;> simp
    · simp [he]
  rw [hopen]
  have hclosed :
      (EH.filter (fun e => omega (triHexTorusPrimalOfDualEdge L e) = false)).card =
        (ET.filter (fun e => omega e = false)).card := by
    apply Finset.card_bij
        (fun e (_ : e ∈ EH.filter
          (fun e => omega (triHexTorusPrimalOfDualEdge L e) = false)) =>
            triHexTorusPrimalOfDualEdge L e)
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨triHexTorusPrimalOfDualEdge_mem L he.1, he.2⟩
    · intro a ha b hb hab
      simp only [Finset.mem_filter] at ha hb
      exact triHexTorusPrimalOfDualEdge_injOn L ha.1 hb.1 hab
    · intro b hb
      simp only [Finset.mem_filter] at hb
      have hbSet : b ∈ (triangularTorusGraph L).edgeSet := by
        simpa [ET, SimpleGraph.edgeFinset] using hb.1
      let tb : (triangularTorusGraph L).edgeSet := ⟨b, hbSet⟩
      let d : Sym2 (HexTorusVertex L) :=
        (triHexTorusDualEdgeEquiv L tb :
          (hexagonalTorusGraph L).edgeSet)
      have hdSet : d ∈ (hexagonalTorusGraph L).edgeSet :=
        (triHexTorusDualEdgeEquiv L tb).2
      have hd : d ∈ EH := by
        simpa [EH, SimpleGraph.edgeFinset] using hdSet
      have hdb : triHexTorusPrimalOfDualEdge L d = b := by
        simp only [triHexTorusPrimalOfDualEdge, dif_pos hdSet]
        exact congrArg Subtype.val ((triHexTorusDualEdgeEquiv L).symm_apply_apply tb)
      refine ⟨d, ?_, hdb⟩
      simp only [Finset.mem_filter]
      exact ⟨hd, hdb ▸ hb.2⟩
  rw [hclosed, hcardE]
  have hc := Finset.card_filter_add_card_filter_not
    (s := ET) (fun e => omega e = true)
  have hnot : ET.filter (fun e => ¬ omega e = true) =
      ET.filter (fun e => omega e = false) := by
    ext e
    simp only [Finset.mem_filter]
    cases omega e <;> simp
  rw [hnot] at hc
  have hopen_le : (ET.filter (fun e => omega e = true)).card ≤ ET.card :=
    Finset.card_filter_le _ _
  change (ET.filter (fun e => omega e = false)).card =
    ET.card - (ET.filter (fun e => omega e = true)).card
  omega


noncomputable def graphEdgeConfig {V : Type*} (K : SimpleGraph V) :
    ConfigSpace (Sym2 V) := by
  classical
  exact fun e => decide (e ∈ K.edgeSet)


noncomputable def triHexTorusFaceCount (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (TorusSite L)) : ℕ := by
  exact Nat.card (FK.openSub (hexagonalTorusGraph L)
    (triHexTorusDualConfig L (graphEdgeConfig K))).ConnectedComponent


noncomputable def triHexTorusDefect (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (TorusSite L)) : ℤ :=
  (K.edgeSet.ncard : ℤ) - Nat.card (TorusSite L) +
    Nat.card K.ConnectedComponent + 1 - triHexTorusFaceCount L K

theorem triHexTorus_euler (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (TorusSite L)) :
    (Nat.card (TorusSite L) : ℤ) - K.edgeSet.ncard +
        triHexTorusFaceCount L K =
      Nat.card K.ConnectedComponent + 1 - triHexTorusDefect L K := by
  unfold triHexTorusDefect
  ring

private theorem mem_openSub_edgeSet_iff
    {V : Type*} (G : SimpleGraph V) (omega : ConfigSpace (Sym2 V))
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    e ∈ (FK.openSub G omega).edgeSet ↔ omega e = true := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      simpa only [SimpleGraph.mem_edgeSet] using and_iff_right he

theorem triHexTorusFaceCount_openSub (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L))) :
    triHexTorusFaceCount L (FK.openSub (triangularTorusGraph L) omega) =
      FK.numClusters (hexagonalTorusGraph L) (triHexTorusDualConfig L omega) := by
  classical
  have hcfg : triHexTorusDualConfig L
        (graphEdgeConfig (FK.openSub (triangularTorusGraph L) omega)) =
      triHexTorusDualConfig L omega := by
    funext e
    by_cases he : e ∈ (hexagonalTorusGraph L).edgeSet
    · have hpSet : triHexTorusPrimalOfDualEdge L e ∈
          (triangularTorusGraph L).edgeSet := by
        simp only [triHexTorusPrimalOfDualEdge, dif_pos he]
        exact ((triHexTorusDualEdgeEquiv L).symm ⟨e, he⟩).2
      have hopen : triHexTorusPrimalOfDualEdge L e ∈
            (FK.openSub (triangularTorusGraph L) omega).edgeSet ↔
          omega (triHexTorusPrimalOfDualEdge L e) = true := by
        exact mem_openSub_edgeSet_iff (triangularTorusGraph L) omega hpSet
      unfold triHexTorusDualConfig
      simp only [dif_pos he]
      cases homega : omega (triHexTorusPrimalOfDualEdge L e)
      · have hclosed : triHexTorusPrimalOfDualEdge L e ∉
            (FK.openSub (triangularTorusGraph L) omega).edgeSet := by
          rw [hopen, homega]
          simp
        simp [graphEdgeConfig, hclosed]
      · have hopen' : triHexTorusPrimalOfDualEdge L e ∈
            (FK.openSub (triangularTorusGraph L) omega).edgeSet := by
          rw [hopen, homega]
        simp [graphEdgeConfig, hopen']
    · unfold triHexTorusDualConfig
      simp [he]
  unfold triHexTorusFaceCount FK.numClusters
  have hg := congrArg (FK.openSub (hexagonalTorusGraph L)) hcfg
  calc
    Nat.card (FK.openSub (hexagonalTorusGraph L)
        (triHexTorusDualConfig L
          (graphEdgeConfig (FK.openSub (triangularTorusGraph L) omega)))).ConnectedComponent =
        Nat.card (FK.openSub (hexagonalTorusGraph L)
          (triHexTorusDualConfig L omega)).ConnectedComponent := by
      exact congrArg (fun G : SimpleGraph (HexTorusVertex L) =>
        Nat.card G.ConnectedComponent) hg
    _ = Fintype.card (FK.openSub (hexagonalTorusGraph L)
        (triHexTorusDualConfig L omega)).ConnectedComponent :=
      Nat.card_eq_fintype_card

private theorem triHexTorus_openSub_edge_ncard
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) :
    (FK.openSub G omega).edgeSet.ncard = FK.openCount G omega := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  unfold FK.openCount
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Set.mem_toFinset, SimpleGraph.mem_edgeSet, FK.openSub_adj,
        Finset.mem_filter, SimpleGraph.mem_edgeFinset]

theorem triHexTorus_edge_card (L : ℕ) [Fact (2 < L)] :
    (triangularTorusGraph L).edgeFinset.card =
      (hexagonalTorusGraph L).edgeFinset.card := by
  simpa [SimpleGraph.edgeFinset] using
    Fintype.card_congr (triHexTorusDualEdgeEquiv L)



theorem triHexTorus_fkWeight_duality_signed (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L)))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkWeight (triangularTorusGraph L) p q omega *
        q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        FK.fkWeight (hexagonalTorusGraph L)
          (BeffaraDC.dualParam p q) q (triHexTorusDualConfig L omega) *
        q ^ triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) omega) := by
  let m := (triangularTorusGraph L).edgeFinset.card
  let o := FK.openCount (triangularTorusGraph L) omega
  let k := Nat.card (FK.openSub (triangularTorusGraph L) omega).ConnectedComponent
  let kd := Nat.card (FK.openSub (hexagonalTorusGraph L)
    (triHexTorusDualConfig L omega)).ConnectedComponent
  let v := Nat.card (TorusSite L)
  let d := triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega)
  have hom : o ≤ m := Finset.card_filter_le _ _
  have hedge := BeffaraDC.dlt_edgeProduct_duality hp hp1 hq m o hom
  have heuler : ((o + k + 1 : ℕ) : ℤ) = ((v + kd : ℕ) : ℤ) + d := by
    have h := triHexTorus_euler L (FK.openSub (triangularTorusGraph L) omega)
    rw [triHexTorus_openSub_edge_ncard,
      triHexTorusFaceCount_openSub] at h
    unfold FK.numClusters at h
    rw [← Nat.card_eq_fintype_card] at h
    push_cast at h ⊢
    dsimp only [o, k, kd, v, d]
    linarith
  have hqne : q ≠ 0 := ne_of_gt hq
  have hpow : q ^ (o + k + 1) = q ^ (v + kd) * q ^ d := by
    rw [← zpow_natCast, ← zpow_natCast, heuler, zpow_add₀ hqne]
  unfold FK.fkWeight
  unfold FK.numClusters
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  rw [BeffaraDC.dlt_edgeProduct_eq_count,
    BeffaraDC.dlt_edgeProduct_eq_count]
  change BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
      (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q)
        (hexagonalTorusGraph L).edgeFinset.card
        (FK.openCount (hexagonalTorusGraph L) (triHexTorusDualConfig L omega)) *
          q ^ kd) * q ^ d
  rw [← triHexTorus_edge_card L, triHexTorus_dual_openCount,
    ← triHexTorus_edge_card L]
  change BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
      (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
        q ^ kd) * q ^ d
  calc
    BeffaraDC.edgeProductCount p m o * q ^ k * q ^ (m + 1) =
        (BeffaraDC.edgeProductCount p m o * q ^ m) * (q ^ k * q) := by
      rw [pow_succ]
      ring
    _ = ((p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ o *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o)) *
          (q ^ k * q) := by rw [hedge]
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
          q ^ (o + k + 1) := by
      rw [pow_add, pow_succ]
      ring
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m *
          BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
          (q ^ (v + kd) * q ^ d) := by rw [hpow]
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^ m * q ^ v *
          (BeffaraDC.edgeProductCount (BeffaraDC.dualParam p q) m (m - o) *
            q ^ kd) * q ^ d := by
      rw [pow_add]
      ring





noncomputable def triHexTorusPrimalSectorSum
    (L : ℕ) [Fact (2 < L)] (r : ℤ) (p q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    if triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega) = r then
      F (triHexTorusDualConfig L omega) *
        FK.fkWeight (triangularTorusGraph L) p q omega
    else 0



noncomputable def triHexTorusDualSectorSum
    (L : ℕ) [Fact (2 < L)] (r : ℤ) (pDual q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    if triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega) = r then
      F (triHexTorusDualConfig L omega) *
        FK.fkWeight (hexagonalTorusGraph L) pDual q
          (triHexTorusDualConfig L omega)
    else 0



theorem triHexTorus_sectorSum_duality (L : ℕ) [Fact (2 < L)]
    (r : ℤ) (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triHexTorusPrimalSectorSum L r p q F *
        q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F * q ^ r := by
  classical
  unfold triHexTorusPrimalSectorSum triHexTorusDualSectorSum
  rw [Finset.sum_mul]
  calc
    ∑ omega, (if triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) omega) = r then
        F (triHexTorusDualConfig L omega) *
          FK.fkWeight (triangularTorusGraph L) p q omega
      else 0) * q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
        ∑ omega,
          (p / (1 - BeffaraDC.dualParam p q)) ^
              (triangularTorusGraph L).edgeFinset.card *
            q ^ Nat.card (TorusSite L) *
            (if triHexTorusDefect L
                (FK.openSub (triangularTorusGraph L) omega) = r then
              F (triHexTorusDualConfig L omega) *
                FK.fkWeight (hexagonalTorusGraph L)
                  (BeffaraDC.dualParam p q) q
                  (triHexTorusDualConfig L omega)
            else 0) * q ^ r := by
      apply Finset.sum_congr rfl
      intro omega homega
      by_cases hsector : triHexTorusDefect L
          (FK.openSub (triangularTorusGraph L) omega) = r
      · simp only [hsector, if_true]
        have hweight := triHexTorus_fkWeight_duality_signed L omega hp hp1 hq
        rw [hsector] at hweight
        calc
          (F (triHexTorusDualConfig L omega) *
              FK.fkWeight (triangularTorusGraph L) p q omega) *
              q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
              F (triHexTorusDualConfig L omega) *
                (FK.fkWeight (triangularTorusGraph L) p q omega *
                  q ^ ((triangularTorusGraph L).edgeFinset.card + 1)) := by ring
          _ = F (triHexTorusDualConfig L omega) *
              ((p / (1 - BeffaraDC.dualParam p q)) ^
                  (triangularTorusGraph L).edgeFinset.card *
                q ^ Nat.card (TorusSite L) *
                FK.fkWeight (hexagonalTorusGraph L)
                  (BeffaraDC.dualParam p q) q
                  (triHexTorusDualConfig L omega) * q ^ r) := by rw [hweight]
          _ = (p / (1 - BeffaraDC.dualParam p q)) ^
                  (triangularTorusGraph L).edgeFinset.card *
                q ^ Nat.card (TorusSite L) *
                (F (triHexTorusDualConfig L omega) *
                  FK.fkWeight (hexagonalTorusGraph L)
                    (BeffaraDC.dualParam p q) q
                    (triHexTorusDualConfig L omega)) * q ^ r := by ring
      · simp [hsector]
    _ = (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        (∑ omega, if triHexTorusDefect L
              (FK.openSub (triangularTorusGraph L) omega) = r then
            F (triHexTorusDualConfig L omega) *
              FK.fkWeight (hexagonalTorusGraph L)
                (BeffaraDC.dualParam p q) q
                (triHexTorusDualConfig L omega)
          else 0) * q ^ r := by
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]


theorem triHexTorus_sectorPartition_duality (L : ℕ) [Fact (2 < L)]
    (r : ℤ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triHexTorusPrimalSectorSum L r p q (fun _ => 1) *
        q ^ ((triangularTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^
          (triangularTorusGraph L).edgeFinset.card *
        q ^ Nat.card (TorusSite L) *
        triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
          (fun _ => 1) * q ^ r :=
  triHexTorus_sectorSum_duality L r (fun _ => 1) hp hp1 hq



theorem triHexTorus_sectorNormalized_duality (L : ℕ) [Fact (2 < L)]
    (r : ℤ) (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hprimal : triHexTorusPrimalSectorSum L r p q (fun _ => 1) ≠ 0)
    (hdual : triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
      (fun _ => 1) ≠ 0) :
    triHexTorusPrimalSectorSum L r p q F /
        triHexTorusPrimalSectorSum L r p q (fun _ => 1) =
      triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F /
        triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
          (fun _ => 1) := by
  let A := q ^ ((triangularTorusGraph L).edgeFinset.card + 1)
  let B := (p / (1 - BeffaraDC.dualParam p q)) ^
      (triangularTorusGraph L).edgeFinset.card *
    q ^ Nat.card (TorusSite L) * q ^ r
  have hA : A ≠ 0 := by
    exact pow_ne_zero _ (ne_of_gt hq)
  have hnum := triHexTorus_sectorSum_duality L r F hp hp1 hq
  have hpart := triHexTorus_sectorPartition_duality L r hp hp1 hq
  have hnum' : triHexTorusPrimalSectorSum L r p q F * A =
      B * triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F := by
    dsimp only [A, B]
    linarith
  have hpart' : triHexTorusPrimalSectorSum L r p q (fun _ => 1) * A =
      B * triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
        (fun _ => 1) := by
    dsimp only [A, B]
    linarith
  apply (div_eq_div_iff hprimal hdual).2
  apply mul_right_cancel₀ hA
  calc
    (triHexTorusPrimalSectorSum L r p q F *
          triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
            (fun _ => 1)) * A =
        (triHexTorusPrimalSectorSum L r p q F * A) *
          triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
            (fun _ => 1) := by ring
    _ = (B * triHexTorusDualSectorSum L r
          (BeffaraDC.dualParam p q) q F) *
        triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
          (fun _ => 1) := by rw [hnum']
    _ = triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F *
        (B * triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q
          (fun _ => 1)) := by ring
    _ = triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F *
        (triHexTorusPrimalSectorSum L r p q (fun _ => 1) * A) := by
      rw [hpart']
    _ = (triHexTorusDualSectorSum L r (BeffaraDC.dualParam p q) q F *
          triHexTorusPrimalSectorSum L r p q (fun _ => 1)) * A := by
      ring

end PeriodicPlanar
end FK
end StatMech
