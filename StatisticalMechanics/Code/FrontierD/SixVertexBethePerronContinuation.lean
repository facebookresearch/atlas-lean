/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheZeroPhaseSingle
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexSectorTransferInfinity (N n : Nat) :
    Matrix (SixVertexSector N n) (SixVertexSector N n) Real := by
  classical
  exact fun x y =>
    if x ≠ y ∧ SixVertexInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y) ∧
        sixVertexRowDistance (sixVertexSectorRow x)
          (sixVertexSectorRow y) = 2 * n then 1 else 0

theorem sixVertexSectorTransferInfinity_apply (N n : Nat)
    (x y : SixVertexSector N n) :
    sixVertexSectorTransferInfinity N n x y =
      if x ≠ y ∧ SixVertexInterlaced (sixVertexSectorRow x)
          (sixVertexSectorRow y) ∧
          sixVertexRowDistance (sixVertexSectorRow x)
            (sixVertexSectorRow y) = 2 * n then 1 else 0 :=
  rfl

theorem sixVertexSectorTransferInfinity_nonneg (N n : Nat)
    (x y : SixVertexSector N n) :
    0 ≤ sixVertexSectorTransferInfinity N n x y := by
  rw [sixVertexSectorTransferInfinity_apply]
  split_ifs <;> norm_num

theorem sixVertexSectorTransferInfinity_symmetric (N n : Nat)
    (x y : SixVertexSector N n) :
    sixVertexSectorTransferInfinity N n x y =
      sixVertexSectorTransferInfinity N n y x := by
  rw [sixVertexSectorTransferInfinity_apply,
    sixVertexSectorTransferInfinity_apply]
  apply if_congr
  · constructor
    · rintro ⟨hxy, hinter, hdist⟩
      exact ⟨Ne.symm hxy, (sixVertexInterlaced_comm _ _).mp hinter,
        (sixVertexRowDistance_comm _ _).symm.trans hdist⟩
    · rintro ⟨hyx, hinter, hdist⟩
      exact ⟨Ne.symm hyx, (sixVertexInterlaced_comm _ _).mp hinter,
        (sixVertexRowDistance_comm _ _).trans hdist⟩
  · rfl
  · rfl



theorem sixVertexSectorRowDistance_le_twice (N n : Nat)
    (x y : SixVertexSector N n) :
    sixVertexRowDistance (sixVertexSectorRow x)
        (sixVertexSectorRow y) ≤ 2 * n := by
  let D : Finset (Fin N) :=
    {i | sixVertexSectorRow x i ≠ sixVertexSectorRow y i}
  have hsub : D ⊆ (x : Finset (Fin N)) ∪ (y : Finset (Fin N)) := by
    intro i hi
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and,
      sixVertexSectorRow_apply] at hi
    simp only [Finset.mem_union]
    by_cases hix : i ∈ (x : Finset (Fin N))
    · exact Or.inl hix
    · right
      by_contra hiy
      simp [hix, hiy] at hi
  calc
    sixVertexRowDistance (sixVertexSectorRow x)
        (sixVertexSectorRow y) = D.card := rfl
    _ ≤ ((x : Finset (Fin N)) ∪ (y : Finset (Fin N))).card :=
      Finset.card_le_card hsub
    _ ≤ (x : Finset (Fin N)).card + (y : Finset (Fin N)).card :=
      Finset.card_union_le _ _
    _ = 2 * n := by rw [x.prop, y.prop]; omega



theorem sixVertexSectorRowDistance_eq_twice_iff_disjoint
    (N n : Nat) (x y : SixVertexSector N n) :
    sixVertexRowDistance (sixVertexSectorRow x)
        (sixVertexSectorRow y) = 2 * n ↔
      Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)) := by
  let D : Finset (Fin N) :=
    {i | sixVertexSectorRow x i ≠ sixVertexSectorRow y i}
  have hD : D = ((x : Finset (Fin N)) \ (y : Finset (Fin N))) ∪
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))) := by
    ext i
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and,
      sixVertexSectorRow_apply, Finset.mem_union, Finset.mem_sdiff]
    by_cases hix : i ∈ (x : Finset (Fin N)) <;>
      by_cases hiy : i ∈ (y : Finset (Fin N)) <;> simp [hix, hiy]
  have hparts : Disjoint
      ((x : Finset (Fin N)) \ (y : Finset (Fin N)))
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))) := by
    rw [Finset.disjoint_left]
    intro i hix hiy
    exact (Finset.mem_sdiff.mp hix).2 (Finset.mem_sdiff.mp hiy).1
  change D.card = 2 * n ↔ _
  rw [hD, Finset.card_union_of_disjoint hparts,
    Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop]
  constructor
  · intro hcard
    have hinterle : ((x : Finset (Fin N)) ∩ (y : Finset (Fin N))).card ≤ n := by
      calc
        ((x : Finset (Fin N)) ∩ (y : Finset (Fin N))).card ≤
            (x : Finset (Fin N)).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = n := x.prop
    rw [Finset.inter_comm (y : Finset (Fin N)) (x : Finset (Fin N))]
      at hcard
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.card_eq_zero.mp
    omega
  · intro hdisj
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    rw [Finset.inter_comm (y : Finset (Fin N)) (x : Finset (Fin N)),
      hdisj]
    simp
    omega



def SixVertexSectorNoAdjacent {N n : Nat} (x : SixVertexSector N n) : Prop :=
  (∀ (k : Nat) (hk : k + 1 < n),
      (sixVertexSectorPosition x ⟨k, by omega⟩).val + 1 <
        (sixVertexSectorPosition x ⟨k + 1, hk⟩).val) ∧
    ∀ hn : 0 < n,
      (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val + 1 <
        N + (sixVertexSectorPosition x ⟨0, hn⟩).val

private theorem sixVertexSectorNoAdjacent_pair_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) :
    SixVertexSectorNoAdjacent x ∧ SixVertexSectorNoAdjacent y := by
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hforward
  have hne (i j : Fin n) :
      sixVertexSectorPosition x i ≠ sixVertexSectorPosition y j := by
    intro heq
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (sixVertexSectorPosition_mem x i)
      (heq ▸ sixVertexSectorPosition_mem y j)
  constructor
  · constructor
    · intro k hk
      let i : Fin n := ⟨k, by omega⟩
      let j : Fin n := ⟨k + 1, hk⟩
      have hleft := hpos.1 i
      have hright := hpos.2 k hk
      have hleft' : (sixVertexSectorPosition x i).val <
          (sixVertexSectorPosition y i).val := by
        exact_mod_cast lt_of_le_of_ne hleft (hne i i)
      have hright' : (sixVertexSectorPosition y i).val <
          (sixVertexSectorPosition x j).val := by
        exact_mod_cast lt_of_le_of_ne hright (Ne.symm (hne j i))
      change (sixVertexSectorPosition x i).val + 1 <
        (sixVertexSectorPosition x j).val
      omega
    · intro hn
      let last : Fin n := ⟨n - 1, by omega⟩
      have hlast := hpos.1 last
      have hlast' : (sixVertexSectorPosition x last).val <
          (sixVertexSectorPosition y last).val := by
        exact_mod_cast lt_of_le_of_ne hlast (hne last last)
      have hyN := (sixVertexSectorPosition y last).isLt
      change (sixVertexSectorPosition x last).val + 1 <
        N + (sixVertexSectorPosition x ⟨0, hn⟩).val
      exact lt_of_lt_of_le
        (lt_of_le_of_lt (Nat.succ_le_of_lt hlast') hyN)
        (Nat.le_add_right N _)
  · constructor
    · intro k hk
      let i : Fin n := ⟨k, by omega⟩
      let j : Fin n := ⟨k + 1, hk⟩
      have hleft := hpos.2 k hk
      have hright := hpos.1 j
      have hleft' : (sixVertexSectorPosition y i).val <
          (sixVertexSectorPosition x j).val := by
        exact_mod_cast lt_of_le_of_ne hleft (Ne.symm (hne j i))
      have hright' : (sixVertexSectorPosition x j).val <
          (sixVertexSectorPosition y j).val := by
        exact_mod_cast lt_of_le_of_ne hright (hne j j)
      change (sixVertexSectorPosition y i).val + 1 <
        (sixVertexSectorPosition y j).val
      omega
    · intro hn
      let first : Fin n := ⟨0, hn⟩
      have hfirst := hpos.1 first
      have hfirst' : (sixVertexSectorPosition x first).val <
          (sixVertexSectorPosition y first).val := by
        exact_mod_cast lt_of_le_of_ne hfirst (hne first first)
      have hlastN := (sixVertexSectorPosition y
        ⟨n - 1, by omega⟩).isLt
      have hyfirst : 0 < (sixVertexSectorPosition y first).val :=
        lt_of_le_of_lt (Nat.zero_le _) hfirst'
      change (sixVertexSectorPosition y ⟨n - 1, by omega⟩).val + 1 <
        N + (sixVertexSectorPosition y first).val
      exact lt_of_le_of_lt (Nat.succ_le_of_lt hlastN)
        (Nat.lt_add_of_pos_right hyfirst)

private theorem tendsto_sixVertexAnisotropyDenominator :
    Tendsto (fun c : Real => c ^ 2 - 2) atTop atTop := by
  have hsq : Tendsto (fun c : Real => c * c) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
    have hc1 : 1 ≤ c := le_trans (le_max_left _ _) hc
    have hcb : b ≤ c := le_trans (le_max_right _ _) hc
    nlinarith
  simpa only [pow_two, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-2) hsq)

private theorem tendsto_sixVertexAnisotropyCorrection :
    Tendsto (fun c : Real => c ^ 2 / (c ^ 2 - 2)) atTop (nhds 1) := by
  have hzero : Tendsto (fun c : Real => 2 / (c ^ 2 - 2)) atTop (nhds 0) :=
    tendsto_sixVertexAnisotropyDenominator.const_div_atTop 2
  have hone : Tendsto (fun c : Real => 1 + 2 / (c ^ 2 - 2))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  apply hone.congr'
  filter_upwards
    [tendsto_sixVertexAnisotropyDenominator.eventually
      (eventually_gt_atTop (0 : Real))] with c hc
  field_simp [hc.ne']
  ring



theorem tendsto_sixVertexAnisotropyPowerRatio
    {d n : Nat} (hd : d ≤ 2 * n) :
    Tendsto (fun c : Real => c ^ d / (c ^ 2 - 2) ^ n) atTop
      (nhds (if d = 2 * n then 1 else 0)) := by
  have hcorrection :
      Tendsto (fun c : Real => c ^ (2 * n) / (c ^ 2 - 2) ^ n)
        atTop (nhds 1) := by
    simpa only [pow_mul, div_pow, one_pow] using
      tendsto_sixVertexAnisotropyCorrection.pow n
  by_cases hmax : d = 2 * n
  · subst d
    simpa using hcorrection
  · have hdlt : d < 2 * n := lt_of_le_of_ne hd hmax
    have hsmall : Tendsto (fun c : Real => c ^ d / c ^ (2 * n))
        atTop (nhds 0) :=
      tendsto_pow_div_pow_atTop_zero hdlt
    have hmul := hsmall.mul hcorrection
    have hmul' : Tendsto
        (fun c : Real => (c ^ d / c ^ (2 * n)) *
          (c ^ (2 * n) / (c ^ 2 - 2) ^ n)) atTop (nhds 0) := by
      simpa using hmul
    simp only [hmax, if_false]
    apply hmul'.congr'
    filter_upwards
      [eventually_gt_atTop (0 : Real),
        tendsto_sixVertexAnisotropyDenominator.eventually
          (eventually_gt_atTop (0 : Real))] with c hc hcden
    field_simp [hc.ne', hcden.ne']



theorem tendsto_sixVertexSectorTransfer_normalized_atTop
    {N n : Nat} (hn : 0 < n) (x y : SixVertexSector N n) :
    Tendsto (fun c : Real =>
        sixVertexSectorTransfer N n c x y / (c ^ 2 - 2) ^ n)
      atTop (nhds (sixVertexSectorTransferInfinity N n x y)) := by
  rw [sixVertexSectorTransferInfinity_apply]
  by_cases hxy : x = y
  · subst y
    have hratio := tendsto_sixVertexAnisotropyPowerRatio
      (d := 0) (n := n) (by omega)
    have hconst : Tendsto (fun _ : Real => (2 : Real)) atTop (nhds 2) :=
      tendsto_const_nhds
    have hscaled := hconst.mul hratio
    simpa [sixVertexSectorTransfer, sixVertexTransfer, hn.ne'] using hscaled
  · have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
      fun h => hxy (sixVertexSectorRow_injective h)
    by_cases hinter : SixVertexInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y)
    · have hratio := tendsto_sixVertexAnisotropyPowerRatio
        (sixVertexSectorRowDistance_le_twice N n x y)
      simpa [sixVertexSectorTransfer, sixVertexTransfer, hxy, hrow,
        hinter] using hratio
    · simp [sixVertexSectorTransfer, sixVertexTransfer, hxy, hrow,
        hinter, tendsto_const_nhds]



def sixVertexInfinityGraph (N n : Nat) : SimpleGraph (SixVertexSector N n) where
  Adj x y := x ≠ y ∧
    SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ∧
    sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) = 2 * n
  symm := by
    rintro x y ⟨hxy, hinter, hdist⟩
    exact ⟨Ne.symm hxy, (sixVertexInterlaced_comm _ _).mp hinter,
      (sixVertexRowDistance_comm _ _).symm.trans hdist⟩
  loopless := ⟨by
    intro x hx
    exact hx.1 rfl⟩

noncomputable instance sixVertexInfinityGraph_adjDecidable (N n : Nat) :
    DecidableRel (sixVertexInfinityGraph N n).Adj :=
  Classical.decRel _



theorem sixVertexInfinityGraph_adj_noAdjacent
    {N n : Nat} {x y : SixVertexSector N n}
    (hxy : (sixVertexInfinityGraph N n).Adj x y) :
    SixVertexSectorNoAdjacent x ∧ SixVertexSectorNoAdjacent y := by
  have hdisj :=
    (sixVertexSectorRowDistance_eq_twice_iff_disjoint N n x y).mp hxy.2.2
  rcases hxy.2.1 with hforward | hforward
  · exact sixVertexSectorNoAdjacent_pair_of_forward_disjoint
      x y hforward hdisj
  · have h := sixVertexSectorNoAdjacent_pair_of_forward_disjoint
      y x hforward hdisj.symm
    exact ⟨h.2, h.1⟩


abbrev SixVertexNoAdjacentSector (N n : Nat) :=
  {x : SixVertexSector N n // SixVertexSectorNoAdjacent x}


def sixVertexNoAdjacentTransferInfinity (N n : Nat) :
    Matrix (SixVertexNoAdjacentSector N n)
      (SixVertexNoAdjacentSector N n) Real :=
  fun x y => sixVertexSectorTransferInfinity N n x.1 y.1

theorem sixVertexNoAdjacentTransferInfinity_nonneg (N n : Nat)
    (x y : SixVertexNoAdjacentSector N n) :
    0 ≤ sixVertexNoAdjacentTransferInfinity N n x y :=
  sixVertexSectorTransferInfinity_nonneg N n x.1 y.1

theorem sixVertexNoAdjacentTransferInfinity_symmetric (N n : Nat)
    (x y : SixVertexNoAdjacentSector N n) :
    sixVertexNoAdjacentTransferInfinity N n x y =
      sixVertexNoAdjacentTransferInfinity N n y x :=
  sixVertexSectorTransferInfinity_symmetric N n x.1 y.1



theorem sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left
    {N n : Nat} {x : SixVertexSector N n}
    (hx : ¬ SixVertexSectorNoAdjacent x) (y : SixVertexSector N n) :
    sixVertexSectorTransferInfinity N n x y = 0 := by
  rw [sixVertexSectorTransferInfinity_apply]
  split_ifs with h
  · exact False.elim (hx (sixVertexInfinityGraph_adj_noAdjacent h).1)
  · rfl

theorem sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_right
    {N n : Nat} (x : SixVertexSector N n) {y : SixVertexSector N n}
    (hy : ¬ SixVertexSectorNoAdjacent y) :
    sixVertexSectorTransferInfinity N n x y = 0 := by
  rw [sixVertexSectorTransferInfinity_symmetric]
  exact sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left hy x


def sixVertexNoAdjacentInfinityGraph (N n : Nat) :
    SimpleGraph (SixVertexNoAdjacentSector N n) :=
  (sixVertexInfinityGraph N n).induce
    {x | SixVertexSectorNoAdjacent x}

noncomputable instance sixVertexNoAdjacentInfinityGraph_adjDecidable
    (N n : Nat) : DecidableRel (sixVertexNoAdjacentInfinityGraph N n).Adj :=
  Classical.decRel _

theorem sixVertexNoAdjacentInfinityGraph_adjMatrix :
    (sixVertexNoAdjacentInfinityGraph N n).adjMatrix Real =
      sixVertexNoAdjacentTransferInfinity N n := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [sixVertexNoAdjacentInfinityGraph, SimpleGraph.induce,
      sixVertexInfinityGraph, sixVertexNoAdjacentTransferInfinity,
      sixVertexSectorTransferInfinity]
  · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    simp [sixVertexNoAdjacentInfinityGraph, SimpleGraph.induce,
      sixVertexInfinityGraph, sixVertexNoAdjacentTransferInfinity,
      sixVertexSectorTransferInfinity, hxy, hval]
    rfl

private def sixVertexAlternatingEvenEmbedding
    {N n : Nat} (hhalf : 2 * n ≤ N) : Fin n ↪o Fin N := by
  let f : Fin n → Fin N := fun i =>
    ⟨2 * i.val, lt_of_lt_of_le (by omega) hhalf⟩
  exact OrderEmbedding.ofStrictMono f (by
    intro i j hij
    change 2 * i.val < 2 * j.val
    omega)

private def sixVertexAlternatingOddEmbedding
    {N n : Nat} (hhalf : 2 * n ≤ N) : Fin n ↪o Fin N := by
  let f : Fin n → Fin N := fun i =>
    ⟨2 * i.val + 1, lt_of_lt_of_le (by omega) hhalf⟩
  exact OrderEmbedding.ofStrictMono f (by
    intro i j hij
    change 2 * i.val + 1 < 2 * j.val + 1
    omega)


def sixVertexAlternatingEvenSector
    (N n : Nat) (hhalf : 2 * n ≤ N) : SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv (sixVertexAlternatingEvenEmbedding hhalf)


def sixVertexAlternatingOddSector
    (N n : Nat) (hhalf : 2 * n ≤ N) : SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv (sixVertexAlternatingOddEmbedding hhalf)

@[simp] theorem sixVertexSectorPosition_alternatingEven
    (N n : Nat) (hhalf : 2 * n ≤ N) :
    sixVertexSectorPosition (sixVertexAlternatingEvenSector N n hhalf) =
      sixVertexAlternatingEvenEmbedding hhalf := by
  change Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv (sixVertexAlternatingEvenEmbedding hhalf)) = _
  exact Equiv.symm_apply_apply _ _

@[simp] theorem sixVertexSectorPosition_alternatingOdd
    (N n : Nat) (hhalf : 2 * n ≤ N) :
    sixVertexSectorPosition (sixVertexAlternatingOddSector N n hhalf) =
      sixVertexAlternatingOddEmbedding hhalf := by
  change Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv (sixVertexAlternatingOddEmbedding hhalf)) = _
  exact Equiv.symm_apply_apply _ _

@[simp] theorem sixVertexSectorPosition_alternatingEven_apply_val
    (N n : Nat) (hhalf : 2 * n ≤ N) (k : Fin n) :
    (sixVertexSectorPosition
      (sixVertexAlternatingEvenSector N n hhalf) k).val = 2 * k.val := by
  rw [sixVertexSectorPosition_alternatingEven]
  rfl

@[simp] theorem sixVertexSectorPosition_alternatingOdd_apply_val
    (N n : Nat) (hhalf : 2 * n ≤ N) (k : Fin n) :
    (sixVertexSectorPosition
      (sixVertexAlternatingOddSector N n hhalf) k).val = 2 * k.val + 1 := by
  rw [sixVertexSectorPosition_alternatingOdd]
  rfl

theorem sixVertexAlternatingEvenSector_noAdjacent
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    SixVertexSectorNoAdjacent
      (sixVertexAlternatingEvenSector N n hhalf) := by
  constructor
  · intro k hk
    simp only [sixVertexSectorPosition_alternatingEven,
      sixVertexAlternatingEvenEmbedding, OrderEmbedding.coe_ofStrictMono,
      Fin.val_mk]
    omega
  · intro hn'
    simp only [sixVertexSectorPosition_alternatingEven,
      sixVertexAlternatingEvenEmbedding, OrderEmbedding.coe_ofStrictMono,
      Fin.val_mk]
    omega

theorem sixVertexAlternatingOddSector_noAdjacent
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    SixVertexSectorNoAdjacent
      (sixVertexAlternatingOddSector N n hhalf) := by
  constructor
  · intro k hk
    simp only [sixVertexSectorPosition_alternatingOdd,
      sixVertexAlternatingOddEmbedding, OrderEmbedding.coe_ofStrictMono,
      Fin.val_mk]
    omega
  · intro hn'
    simp only [sixVertexSectorPosition_alternatingOdd,
      sixVertexAlternatingOddEmbedding, OrderEmbedding.coe_ofStrictMono,
      Fin.val_mk]
    omega

theorem sixVertexAlternatingEven_disjoint_odd
    {N n : Nat} (hhalf : 2 * n ≤ N) :
    Disjoint
      ((sixVertexAlternatingEvenSector N n hhalf : SixVertexSector N n) :
        Finset (Fin N))
      ((sixVertexAlternatingOddSector N n hhalf : SixVertexSector N n) :
        Finset (Fin N)) := by
  rw [Finset.disjoint_left]
  intro z hzEven hzOdd
  have hzEven' : z ∈ Set.range (sixVertexAlternatingEvenEmbedding hhalf) := by
    exact (Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range
      (sixVertexAlternatingEvenEmbedding hhalf) z).mp hzEven
  have hzOdd' : z ∈ Set.range (sixVertexAlternatingOddEmbedding hhalf) := by
    exact (Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range
      (sixVertexAlternatingOddEmbedding hhalf) z).mp hzOdd
  obtain ⟨i, hi⟩ := hzEven'
  obtain ⟨j, hj⟩ := hzOdd'
  have hval := congrArg Fin.val (hi.trans hj.symm)
  simp only [sixVertexAlternatingEvenEmbedding,
    sixVertexAlternatingOddEmbedding, OrderEmbedding.coe_ofStrictMono,
    Fin.val_mk] at hval
  omega



theorem sixVertexInfinityGraph_adj_alternating
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    (sixVertexInfinityGraph N n).Adj
      (sixVertexAlternatingEvenSector N n hhalf)
      (sixVertexAlternatingOddSector N n hhalf) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hpos := congrArg
      (fun x : SixVertexSector N n => (sixVertexSectorPosition x ⟨0, hn⟩).val)
      heq
    simp only [sixVertexSectorPosition_alternatingEven,
      sixVertexSectorPosition_alternatingOdd,
      sixVertexAlternatingEvenEmbedding, sixVertexAlternatingOddEmbedding,
      OrderEmbedding.coe_ofStrictMono, Fin.val_mk] at hpos
    omega
  · left
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro i
      rw [sixVertexSectorPosition_alternatingEven,
        sixVertexSectorPosition_alternatingOdd]
      change (2 * i.val : Nat) ≤ 2 * i.val + 1
      omega
    · intro k hk
      rw [sixVertexSectorPosition_alternatingEven,
        sixVertexSectorPosition_alternatingOdd]
      change (2 * k + 1 : Nat) ≤ 2 * (k + 1)
      omega
  · exact (sixVertexSectorRowDistance_eq_twice_iff_disjoint N n _ _).mpr
      (sixVertexAlternatingEven_disjoint_odd hhalf)

def sixVertexNoAdjacentAlternatingEven
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    SixVertexNoAdjacentSector N n :=
  ⟨sixVertexAlternatingEvenSector N n hhalf,
    sixVertexAlternatingEvenSector_noAdjacent hn hhalf⟩

def sixVertexNoAdjacentAlternatingOdd
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    SixVertexNoAdjacentSector N n :=
  ⟨sixVertexAlternatingOddSector N n hhalf,
    sixVertexAlternatingOddSector_noAdjacent hn hhalf⟩

theorem sixVertexNoAdjacentInfinityGraph_adj_alternating
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    (sixVertexNoAdjacentInfinityGraph N n).Adj
      (sixVertexNoAdjacentAlternatingEven N n hn hhalf)
      (sixVertexNoAdjacentAlternatingOdd N n hn hhalf) :=
  sixVertexInfinityGraph_adj_alternating hn hhalf


noncomputable def sixVertexCyclicSuccEquiv
    {N : Nat} (hN : 0 < N) : Equiv.Perm (Fin N) := by
  letI : NeZero N := ⟨hN.ne'⟩
  exact Equiv.addRight 1

@[simp] theorem sixVertexCyclicSuccEquiv_val
    {N : Nat} (hN : 0 < N) (i : Fin N) :
    (sixVertexCyclicSuccEquiv hN i).val = (i.val + 1) % N := by
  simp [sixVertexCyclicSuccEquiv, Equiv.addRight, Fin.add_def]



theorem sixVertexSector_disjoint_cyclicSucc_of_noAdjacent
    {N n : Nat} (hN : 0 < N) (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) :
    Disjoint (x : Finset (Fin N))
      ((x : Finset (Fin N)).map (sixVertexCyclicSuccEquiv hN).toEmbedding) := by
  rw [Finset.disjoint_left]
  intro z hzx hzsucc
  rw [Finset.mem_map] at hzsucc
  obtain ⟨w, hwx, hwz⟩ := hzsucc
  have hzi : z ∈ Set.range (sixVertexSectorPosition x) :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem x z).mpr hzx
  have hwj : w ∈ Set.range (sixVertexSectorPosition x) :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem x w).mpr hwx
  obtain ⟨i, hi⟩ := hzi
  obtain ⟨j, hj⟩ := hwj
  have heq : sixVertexSectorPosition x i =
      sixVertexCyclicSuccEquiv hN (sixVertexSectorPosition x j) := by
    calc
      sixVertexSectorPosition x i = z := hi
      _ = sixVertexCyclicSuccEquiv hN w := hwz.symm
      _ = sixVertexCyclicSuccEquiv hN (sixVertexSectorPosition x j) := by
        rw [hj]
  have hval := congrArg Fin.val heq
  rw [sixVertexCyclicSuccEquiv_val] at hval
  by_cases hjlast : (sixVertexSectorPosition x j).val + 1 < N
  · rw [Nat.mod_eq_of_lt hjlast] at hval
    have hji : j < i := by
      apply (sixVertexSectorPosition x).lt_iff_lt.mp
      exact_mod_cast (show (sixVertexSectorPosition x j).val <
        (sixVertexSectorPosition x i).val by omega)
    have hijval : i.val = j.val + 1 := by
      by_contra hne
      have hskip : j.val + 1 < i.val := by omega
      let j' : Fin n := ⟨j.val + 1, lt_of_lt_of_le hskip i.isLt.le⟩
      have hjj' : j < j' := by
        change j.val < (j' : Fin n).val
        simp only [j', Fin.val_mk]
        omega
      have hj'i : j' < i := by
        change (j' : Fin n).val < i.val
        simpa only [j', Fin.val_mk] using hskip
      have hpos1 := (sixVertexSectorPosition x).strictMono hjj'
      have hpos2 := (sixVertexSectorPosition x).strictMono hj'i
      have hpos1' : (sixVertexSectorPosition x j).val <
          (sixVertexSectorPosition x j').val := by exact_mod_cast hpos1
      have hpos2' : (sixVertexSectorPosition x j').val <
          (sixVertexSectorPosition x i).val := by exact_mod_cast hpos2
      omega
    have hgap := hx.1 j.val (by omega)
    have hindex : (⟨j.val + 1, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simpa using hijval.symm
    have hgap' : (sixVertexSectorPosition x j).val + 1 <
        (sixVertexSectorPosition x i).val := by
      have hjindex : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
      rw [hjindex, hindex] at hgap
      exact hgap
    omega
  · have hjval : (sixVertexSectorPosition x j).val = N - 1 := by
      have hjle := (sixVertexSectorPosition x j).isLt
      omega
    have hval0 : (sixVertexSectorPosition x i).val = 0 := by
      rw [hjval] at hval
      have hpred : N - 1 + 1 = N := by omega
      rw [hpred, Nat.mod_self] at hval
      exact hval
    have hival : i.val = 0 := by
      by_contra hi0
      let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (fun hn0 => by
        subst n
        exact Fin.elim0 i)⟩
      have hi0lt : i0 < i := by
        change (i0 : Fin n).val < i.val
        simpa only [i0, Fin.val_mk] using Nat.pos_of_ne_zero hi0
      have hpos := (sixVertexSectorPosition x).strictMono hi0lt
      have hpos' : (sixVertexSectorPosition x i0).val <
          (sixVertexSectorPosition x i).val := by exact_mod_cast hpos
      omega
    have hjindex : j.val = n - 1 := by
      by_contra hjne
      have hjsucc : j.val + 1 < n := by omega
      let j' : Fin n := ⟨j.val + 1, hjsucc⟩
      have hpos := (sixVertexSectorPosition x).strictMono
        (show j < j' by
          change j.val < (j' : Fin n).val
          simp only [j', Fin.val_mk]
          omega)
      have hpos' : (sixVertexSectorPosition x j).val <
          (sixVertexSectorPosition x j').val := by exact_mod_cast hpos
      have hj'N := (sixVertexSectorPosition x j').isLt
      omega
    have hn : 0 < n := Nat.pos_of_ne_zero (fun hn0 => by
      subst n
      exact Fin.elim0 i)
    have hwrap := hx.2 hn
    have hiindex : (⟨0, hn⟩ : Fin n) = i := by
      apply Fin.ext
      simpa using hival.symm
    have hjindex' : (⟨n - 1, by omega⟩ : Fin n) = j := by
      apply Fin.ext
      simpa using hjindex.symm
    rw [hiindex, hjindex', hval0, hjval] at hwrap
    omega



noncomputable def sixVertexDefectSet
    {N n : Nat} (hN : 0 < N) (x : SixVertexSector N n) : Finset (Fin N) :=
  Finset.univ \ ((x : Finset (Fin N)) ∪
    (x : Finset (Fin N)).map (sixVertexCyclicSuccEquiv hN).toEmbedding)

theorem card_sixVertexDefectSet
    {N n : Nat} (hN : 0 < N) (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) :
    (sixVertexDefectSet hN x).card = N - 2 * n := by
  rw [sixVertexDefectSet,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rw [Finset.card_union_of_disjoint
    (sixVertexSector_disjoint_cyclicSucc_of_noAdjacent hN x hx),
    Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hxcard : (x : Finset (Fin N)).card = n := x.prop
  omega

theorem card_sixVertexFixedChargeDefectSet
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    (sixVertexDefectSet (sixVertexFourWidth_pos r k) x).card = 2 * r := by
  rw [card_sixVertexDefectSet (sixVertexFourWidth_pos r k) x hx,
    sixVertexFourWidth, sixVertexFixedChargeBetheParticleCount_eq]
  omega


def sixVertexSectorGap {N n : Nat} (x : SixVertexSector N n)
    (i : Fin n) : Nat :=
  if hnext : i.val + 1 < n then
    (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val -
      (sixVertexSectorPosition x i).val - 1
  else
    N + (sixVertexSectorPosition x ⟨0, Nat.pos_of_ne_zero
        (fun hn => by subst n; exact Fin.elim0 i)⟩).val -
      (sixVertexSectorPosition x i).val - 1

theorem sixVertexSectorGap_pos_of_noAdjacent
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (i : Fin n) :
    0 < sixVertexSectorGap x i := by
  rw [sixVertexSectorGap]
  split_ifs with hnext
  · have hgap := hx.1 i.val hnext
    have hi : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
    rw [hi] at hgap
    omega
  · have hn : 0 < n := Nat.pos_of_ne_zero
      (fun hn => by subst n; exact Fin.elim0 i)
    have hilast : i.val = n - 1 := by omega
    have hwrap := hx.2 hn
    have hi : (⟨n - 1, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simpa using hilast.symm
    rw [hi] at hwrap
    omega


def sixVertexSectorGapDefects {N n : Nat} (x : SixVertexSector N n)
    (i : Fin n) : Nat :=
  sixVertexSectorGap x i - 1

theorem sum_sixVertexSectorGap
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n) :
    ∑ i, sixVertexSectorGap x i = N - n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Fin.sum_univ_castSucc]
  simp only [sixVertexSectorGap]
  have hnext (i : Fin m) : i.castSucc.val + 1 < m + 1 := by
    simpa using i.isLt
  simp_rw [dif_pos (hnext _)]
  simp only [Fin.val_castSucc, Fin.val_last,
    show ¬(m + 1 < m + 1) by omega, ↓reduceDIte]
  have hcard : m + 1 ≤ N := by
    have hsub : (x : Finset (Fin N)).card ≤
        (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [x.prop] using hsub
  have hterm (i : Fin m) :
      (((sixVertexSectorPosition x ⟨i.val + 1, hnext i⟩).val -
          (sixVertexSectorPosition x i.castSucc).val - 1 : Nat) : Int) =
        (sixVertexSectorPosition x ⟨i.val + 1, hnext i⟩).val -
          (sixVertexSectorPosition x i.castSucc).val - 1 := by
    have hidx : (⟨i.val + 1, hnext i⟩ : Fin (m + 1)) = i.succ := Fin.ext rfl
    rw [hidx]
    have hlt := (sixVertexSectorPosition x).strictMono
      (Fin.castSucc_lt_succ (i := i))
    rw [Nat.cast_sub (by omega : 1 ≤
      (sixVertexSectorPosition x i.succ).val -
        (sixVertexSectorPosition x i.castSucc).val),
      Nat.cast_sub (by omega :
        (sixVertexSectorPosition x i.castSucc).val ≤
          (sixVertexSectorPosition x i.succ).val)]
    norm_num
  have hlast (z : Fin (m + 1)) (hz : z.val = 0) :
      ((N + (sixVertexSectorPosition x z).val -
          (sixVertexSectorPosition x (Fin.last m)).val - 1 : Nat) : Int) =
        N + (sixVertexSectorPosition x z).val -
          (sixVertexSectorPosition x (Fin.last m)).val - 1 := by
    have hp := (sixVertexSectorPosition x (Fin.last m)).isLt
    push_cast
    omega
  apply Int.ofNat_inj.mp
  push_cast
  simp_rw [hterm]
  simp_rw [hlast]
  let p : Nat → Int := fun k =>
    if hk : k < m + 1 then (sixVertexSectorPosition x ⟨k, hk⟩).val else 0
  let d : Nat → Int := fun k => p (k + 1) - p k - 1
  let g : Fin m → Int := fun i =>
    (sixVertexSectorPosition x i.succ).val -
      (sixVertexSectorPosition x i.castSucc).val - 1
  change (∑ i, g i) +
      ((N : Int) + (sixVertexSectorPosition x (0 : Fin (m + 1))).val -
        (sixVertexSectorPosition x (Fin.last m)).val - 1) =
    ((N - (m + 1) : Nat) : Int)
  have hsum : (∑ i, g i) = ∑ k ∈ Finset.range m, d k := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hinext : i.val + 1 < m + 1 := by omega
    have hicur : i.val < m + 1 := by omega
    simp only [g, d, p, dif_pos hinext, dif_pos hicur]
    congr 2 <;> apply congrArg Fin.val <;> rfl
  rw [hsum]
  have htel := Finset.sum_range_sub p m
  have hp0 : p 0 = (sixVertexSectorPosition x (0 : Fin (m + 1))).val := by
    simp [p]
  have hpm : p m = (sixVertexSectorPosition x (Fin.last m)).val := by
    simp only [p, dif_pos (show m < m + 1 by omega)]
    congr 2
  simp only [d]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [htel, hp0, hpm, Nat.cast_sub hcard]
  push_cast
  ring

theorem sum_sixVertexSectorGapDefects
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n) :
    ∑ i, sixVertexSectorGapDefects x i = N - 2 * n := by
  have hgap (i : Fin n) : sixVertexSectorGapDefects x i + 1 =
      sixVertexSectorGap x i := by
    rw [sixVertexSectorGapDefects, Nat.sub_add_cancel]
    exact sixVertexSectorGap_pos_of_noAdjacent x hx i
  have hcard : n ≤ N := by
    have hsub : (x : Finset (Fin N)).card ≤
        (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [x.prop] using hsub
  have hlower : n ≤ ∑ i, sixVertexSectorGap x i := by
    calc
      n = ∑ _i : Fin n, 1 := by simp
      _ ≤ ∑ i, sixVertexSectorGap x i := by
        apply Finset.sum_le_sum
        intro i _
        exact sixVertexSectorGap_pos_of_noAdjacent x hx i
  rw [sum_sixVertexSectorGap x hn] at hlower
  have hadd : (∑ i, sixVertexSectorGapDefects x i) + n =
      ∑ i, sixVertexSectorGap x i := by
    calc
      (∑ i, sixVertexSectorGapDefects x i) + n =
          ∑ i, (sixVertexSectorGapDefects x i + 1) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = ∑ i, sixVertexSectorGap x i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hgap i
  rw [sum_sixVertexSectorGap x hn] at hadd
  omega


def sixVertexSectorCyclicNext {n : Nat} (i : Fin n) : Fin n :=
  if hnext : i.val + 1 < n then ⟨i.val + 1, hnext⟩
  else ⟨0, Nat.pos_of_ne_zero (fun hn => by subst n; exact Fin.elim0 i)⟩


def sixVertexSectorAdvance {N n : Nat}
    (x y : SixVertexSector N n) (i : Fin n) : Nat :=
  (sixVertexSectorPosition y i).val - (sixVertexSectorPosition x i).val

theorem sixVertexSectorAdvance_pos_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    0 < sixVertexSectorAdvance x y i := by
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hforward
  have hne : sixVertexSectorPosition x i ≠ sixVertexSectorPosition y i := by
    intro heq
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (sixVertexSectorPosition_mem x i)
      (heq ▸ sixVertexSectorPosition_mem y i)
  rw [sixVertexSectorAdvance, Nat.sub_pos_iff_lt]
  exact_mod_cast lt_of_le_of_ne (hpos.1 i) hne

theorem sixVertexSectorAdvance_le_gap_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    sixVertexSectorAdvance x y i ≤ sixVertexSectorGap x i := by
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hforward
  have hne (a b : Fin n) :
      sixVertexSectorPosition x a ≠ sixVertexSectorPosition y b := by
    intro heq
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (sixVertexSectorPosition_mem x a)
      (heq ▸ sixVertexSectorPosition_mem y b)
  rw [sixVertexSectorAdvance, sixVertexSectorGap]
  split_ifs with hnext
  · have hle := hpos.2 i.val hnext
    have hlt : (sixVertexSectorPosition y i).val <
        (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val := by
      have hle' : sixVertexSectorPosition y i ≤
          sixVertexSectorPosition x ⟨i.val + 1, hnext⟩ := by
        simpa only using hle
      exact_mod_cast lt_of_le_of_ne hle' (Ne.symm (hne _ i))
    omega
  · have hyN := (sixVertexSectorPosition y i).isLt
    omega

theorem sixVertexSectorGap_transport_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    sixVertexSectorGap y i + sixVertexSectorAdvance x y i =
      sixVertexSectorGap x i +
        sixVertexSectorAdvance x y (sixVertexSectorCyclicNext i) := by
  have hsupport := sixVertexSectorNoAdjacent_pair_of_forward_disjoint
    x y hforward hdisj
  have hadv (j : Fin n) :=
    sixVertexSectorAdvance_pos_of_forward_disjoint x y hforward hdisj j
  rw [sixVertexSectorGap, sixVertexSectorGap,
    sixVertexSectorAdvance, sixVertexSectorAdvance,
    sixVertexSectorCyclicNext]
  split_ifs with hnext
  · have hxi := hsupport.1.1 i.val hnext
    have hyi := hsupport.2.1 i.val hnext
    have hi : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
    rw [hi] at hxi hyi
    have hai := hadv i
    have han := hadv (⟨i.val + 1, hnext⟩ : Fin n)
    rw [sixVertexSectorAdvance, Nat.sub_pos_iff_lt] at hai han
    have hgapx :
        (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val -
            (sixVertexSectorPosition x i).val - 1 +
            ((sixVertexSectorPosition x i).val + 1) =
          (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val := by omega
    have hgapy :
        (sixVertexSectorPosition y ⟨i.val + 1, hnext⟩).val -
            (sixVertexSectorPosition y i).val - 1 +
            ((sixVertexSectorPosition y i).val + 1) =
          (sixVertexSectorPosition y ⟨i.val + 1, hnext⟩).val := by omega
    have hadvi :
        (sixVertexSectorPosition y i).val -
            (sixVertexSectorPosition x i).val +
            (sixVertexSectorPosition x i).val =
          (sixVertexSectorPosition y i).val := by omega
    have hadvn :
        (sixVertexSectorPosition y ⟨i.val + 1, hnext⟩).val -
            (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val +
            (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val =
          (sixVertexSectorPosition y ⟨i.val + 1, hnext⟩).val := by omega
    omega

  · have hn : 0 < n := Nat.pos_of_ne_zero
      (fun hn => by subst n; exact Fin.elim0 i)
    have hilast : i.val = n - 1 := by omega
    have hxwrap := hsupport.1.2 hn
    have hywrap := hsupport.2.2 hn
    have hi : (⟨n - 1, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simpa using hilast.symm
    rw [hi] at hxwrap hywrap
    have hai := hadv i
    have ha0 := hadv (⟨0, hn⟩ : Fin n)
    rw [sixVertexSectorAdvance, Nat.sub_pos_iff_lt] at hai ha0
    have hgapx :
        N + (sixVertexSectorPosition x ⟨0, hn⟩).val -
            (sixVertexSectorPosition x i).val - 1 +
            ((sixVertexSectorPosition x i).val + 1) =
          N + (sixVertexSectorPosition x ⟨0, hn⟩).val := by omega
    have hgapy :
        N + (sixVertexSectorPosition y ⟨0, hn⟩).val -
            (sixVertexSectorPosition y i).val - 1 +
            ((sixVertexSectorPosition y i).val + 1) =
          N + (sixVertexSectorPosition y ⟨0, hn⟩).val := by omega
    have hadvi :
        (sixVertexSectorPosition y i).val -
            (sixVertexSectorPosition x i).val +
            (sixVertexSectorPosition x i).val =
          (sixVertexSectorPosition y i).val := by omega
    have hadv0 :
        (sixVertexSectorPosition y ⟨0, hn⟩).val -
            (sixVertexSectorPosition x ⟨0, hn⟩).val +
            (sixVertexSectorPosition x ⟨0, hn⟩).val =
          (sixVertexSectorPosition y ⟨0, hn⟩).val := by omega
    omega


def sixVertexSectorAdvanceDefects {N n : Nat}
    (x y : SixVertexSector N n) (i : Fin n) : Nat :=
  sixVertexSectorAdvance x y i - 1

theorem sixVertexSectorGapDefects_transport_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    sixVertexSectorGapDefects y i +
        sixVertexSectorAdvanceDefects x y i =
      sixVertexSectorGapDefects x i +
        sixVertexSectorAdvanceDefects x y (sixVertexSectorCyclicNext i) := by
  have hsupport := sixVertexSectorNoAdjacent_pair_of_forward_disjoint
    x y hforward hdisj
  have htransport := sixVertexSectorGap_transport_of_forward_disjoint
    x y hforward hdisj i
  have hgapx := sixVertexSectorGap_pos_of_noAdjacent x hsupport.1 i
  have hgapy := sixVertexSectorGap_pos_of_noAdjacent y hsupport.2 i
  have hadvi := sixVertexSectorAdvance_pos_of_forward_disjoint
    x y hforward hdisj i
  have hadvn := sixVertexSectorAdvance_pos_of_forward_disjoint
    x y hforward hdisj (sixVertexSectorCyclicNext i)
  rw [sixVertexSectorGapDefects, sixVertexSectorGapDefects,
    sixVertexSectorAdvanceDefects, sixVertexSectorAdvanceDefects]
  omega

theorem sixVertexSectorAdvanceDefects_le_gapDefects_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    sixVertexSectorAdvanceDefects x y i ≤
      sixVertexSectorGapDefects x i := by
  have hpos := sixVertexSectorAdvance_pos_of_forward_disjoint
    x y hforward hdisj i
  have hle := sixVertexSectorAdvance_le_gap_of_forward_disjoint
    x y hforward hdisj i
  rw [sixVertexSectorAdvanceDefects, sixVertexSectorGapDefects]
  omega

theorem sixVertexInfinityGraph_adj_iff_forward_disjoint
    {N n : Nat} (hn : 0 < n) (x y : SixVertexSector N n) :
    (sixVertexInfinityGraph N n).Adj x y ↔
      (SixVertexForwardInterlaced (sixVertexSectorRow x)
          (sixVertexSectorRow y) ∧
        Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) ∨
      (SixVertexForwardInterlaced (sixVertexSectorRow y)
          (sixVertexSectorRow x) ∧
        Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) := by
  change (x ≠ y ∧
      SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ∧
      sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) =
        2 * n) ↔ _
  rw [sixVertexSectorRowDistance_eq_twice_iff_disjoint]
  constructor
  · rintro ⟨_, hforward | hbackward, hdisj⟩
    · exact Or.inl ⟨hforward, hdisj⟩
    · exact Or.inr ⟨hbackward, hdisj⟩
  · rintro (⟨hforward, hdisj⟩ | ⟨hbackward, hdisj⟩)
    · refine ⟨?_, Or.inl hforward, hdisj⟩
      intro hxy
      subst y
      have hcard : (x : Finset (Fin N)).card = n := x.prop
      have : (x : Finset (Fin N)) = ∅ := disjoint_self.mp hdisj
      rw [this] at hcard
      simp at hcard
      omega
    · refine ⟨?_, Or.inr hbackward, hdisj⟩
      intro hxy
      subst y
      have hcard : (x : Finset (Fin N)).card = n := x.prop
      have : (x : Finset (Fin N)) = ∅ := disjoint_self.mp hdisj
      rw [this] at hcard
      simp at hcard
      omega

theorem sixVertexInfinityGraph_adj_defect_transport
    {N n : Nat} (hn : 0 < n) {x y : SixVertexSector N n}
    (hxy : (sixVertexInfinityGraph N n).Adj x y) :
    (∀ i,
      sixVertexSectorGapDefects y i +
          sixVertexSectorAdvanceDefects x y i =
        sixVertexSectorGapDefects x i +
          sixVertexSectorAdvanceDefects x y (sixVertexSectorCyclicNext i)) ∨
    (∀ i,
      sixVertexSectorGapDefects x i +
          sixVertexSectorAdvanceDefects y x i =
        sixVertexSectorGapDefects y i +
          sixVertexSectorAdvanceDefects y x (sixVertexSectorCyclicNext i)) := by
  rcases (sixVertexInfinityGraph_adj_iff_forward_disjoint hn x y).mp hxy with
      ⟨hforward, hdisj⟩ | ⟨hbackward, hdisj⟩
  · exact Or.inl (sixVertexSectorGapDefects_transport_of_forward_disjoint
      x y hforward hdisj)
  · exact Or.inr (sixVertexSectorGapDefects_transport_of_forward_disjoint
      y x hbackward hdisj.symm)

theorem sixVertexInfinityGraph_adj_iff (N n : Nat)
    (x y : SixVertexSector N n) :
    (sixVertexInfinityGraph N n).Adj x y ↔
      x ≠ y ∧ SixVertexInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y) ∧
        sixVertexRowDistance (sixVertexSectorRow x)
          (sixVertexSectorRow y) = 2 * n :=
  Iff.rfl

theorem sixVertexInfinityGraph_adjMatrix :
    (sixVertexInfinityGraph N n).adjMatrix Real =
      sixVertexSectorTransferInfinity N n := by
  classical
  ext x y
  simp [SimpleGraph.adjMatrix, sixVertexInfinityGraph,
    sixVertexSectorTransferInfinity]



theorem sixVertexSectorTransferInfinity_pow_apply_eq_card_walk
    (M N n : Nat) (x y : SixVertexSector N n) :
    (sixVertexSectorTransferInfinity N n ^ M) x y =
      Fintype.card {w : (sixVertexInfinityGraph N n).Walk x y |
        w.length = M} := by
  classical
  rw [← sixVertexInfinityGraph_adjMatrix]
  exact SimpleGraph.adjMatrix_pow_apply_eq_card_walk M x y



theorem trace_sixVertexSectorTransferInfinity_pow_eq_closedWalks
    (M N n : Nat) :
    Matrix.trace (sixVertexSectorTransferInfinity N n ^ M) =
      ∑ x : SixVertexSector N n,
        (Fintype.card {w : (sixVertexInfinityGraph N n).Walk x x |
          w.length = M} : Real) := by
  classical
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro x hx
  exact sixVertexSectorTransferInfinity_pow_apply_eq_card_walk M N n x x




theorem AnalyticOnNhd.eqOn_Ioi_of_eventuallyEq_atTop
    {f g : Real → Real} {a : Real}
    (hf : AnalyticOnNhd Real f (Set.Ioi a))
    (hg : AnalyticOnNhd Real g (Set.Ioi a))
    (hfg : f =ᶠ[atTop] g) : Set.EqOn f g (Set.Ioi a) := by
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp hfg
  let z0 := max (a + 1) (b + 1)
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_Ioi
      (z₀ := z0)
  · change a < z0
    dsimp [z0]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · filter_upwards [Ioi_mem_nhds (show b < z0 by
      dsimp [z0]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _))] with z hz
    exact hb z hz.le

end

end StatMech.FrontierD
