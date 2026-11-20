/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBethePerronContinuation








open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexSectorNoAdjacent_position_lower
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (k : Nat) (hk : k < n) :
    (sixVertexSectorPosition x ⟨0, by omega⟩).val + 2 * k ≤
      (sixVertexSectorPosition x ⟨k, hk⟩).val := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < n := by omega
      have hgap := hx.1 k (by omega)
      have hprev := ih hk'
      change (sixVertexSectorPosition x ⟨0, by omega⟩).val +
          2 * (k + 1) ≤
        (sixVertexSectorPosition x ⟨k + 1, by omega⟩).val
      omega


theorem sixVertexSectorNoAdjacent_position_add_lower
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (k m : Nat)
    (hkm : k + m < n) :
    (sixVertexSectorPosition x ⟨k, by omega⟩).val + 2 * m ≤
      (sixVertexSectorPosition x ⟨k + m, hkm⟩).val := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hprev : k + m < n := by omega
      have hind := ih hprev
      have hgap := hx.1 (k + m) (by omega)
      have hgap' :
          (sixVertexSectorPosition x ⟨k + m, hprev⟩).val + 1 <
            (sixVertexSectorPosition x ⟨k + m + 1, hkm⟩).val := by
        convert hgap using 1
      have hmain :
          (sixVertexSectorPosition x ⟨k, by omega⟩).val +
              2 * (m + 1) ≤
            (sixVertexSectorPosition x ⟨k + m + 1, hkm⟩).val := by
        omega
      convert hmain using 1



theorem sixVertexSectorNoAdjacent_twice_le
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) : 2 * n ≤ N := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let first := (sixVertexSectorPosition x ⟨0, hnpos⟩).val
  let last := (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val
  have hlower : first + 2 * (n - 1) ≤ last := by
    exact sixVertexSectorNoAdjacent_position_lower x hx (n - 1) (by omega)
  have hwrap := hx.2 hnpos
  change last + 1 < N + first at hwrap
  omega


theorem sixVertexSectorNoAdjacent_position_eq_of_half
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (hhalf : 2 * n = N) (k : Fin n) :
    (sixVertexSectorPosition x k).val =
      (sixVertexSectorPosition x ⟨0, hn⟩).val + 2 * k.val := by
  let first := (sixVertexSectorPosition x ⟨0, hn⟩).val
  let last := (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val
  have hlastLower : first + 2 * (n - 1) ≤ last :=
    sixVertexSectorNoAdjacent_position_lower x hx (n - 1) (by omega)
  have hwrap := hx.2 hn
  change last + 1 < N + first at hwrap
  have hlast : last = first + 2 * (n - 1) := by omega
  let m := n - 1 - k.val
  have hkm : k.val + m = n - 1 := by
    dsimp [m]
    omega
  have htail := sixVertexSectorNoAdjacent_position_add_lower
    x hx k.val m (by omega)
  have hlower := sixVertexSectorNoAdjacent_position_lower x hx k.val k.isLt
  change first + 2 * k.val ≤ (sixVertexSectorPosition x k).val at hlower
  have hkFin : (⟨k.val, by omega⟩ : Fin n) = k := Fin.ext rfl
  have hlastFin : (⟨k.val + m, by omega⟩ : Fin n) =
      ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    exact hkm
  rw [hkFin, hlastFin] at htail
  change (sixVertexSectorPosition x k).val + 2 * m ≤ last at htail
  omega



theorem sixVertexSectorNoAdjacent_eq_alternating_of_half
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (hhalf : 2 * n = N) :
    x = sixVertexAlternatingEvenSector N n hhalf.le ∨
      x = sixVertexAlternatingOddSector N n hhalf.le := by
  let first := (sixVertexSectorPosition x ⟨0, hn⟩).val
  have hfirstLt : first < 2 := by
    have hlastLower := sixVertexSectorNoAdjacent_position_lower
      x hx (n - 1) (by omega)
    have hlastN := (sixVertexSectorPosition x ⟨n - 1, by omega⟩).isLt
    change first + 2 * (n - 1) ≤ _ at hlastLower
    omega
  have hfirst : first = 0 ∨ first = 1 := by omega
  rcases hfirst with hzero | hone
  · left
    have hpos : sixVertexSectorPosition x =
        sixVertexSectorPosition
          (sixVertexAlternatingEvenSector N n hhalf.le) := by
      ext k
      rw [sixVertexSectorNoAdjacent_position_eq_of_half x hx hn hhalf]
      simp only [sixVertexSectorPosition_alternatingEven_apply_val]
      change first + 2 * k.val = 2 * k.val
      omega
    exact Set.powersetCard.ofFinEmbEquiv.symm.injective hpos
  · right
    have hpos : sixVertexSectorPosition x =
        sixVertexSectorPosition
          (sixVertexAlternatingOddSector N n hhalf.le) := by
      ext k
      rw [sixVertexSectorNoAdjacent_position_eq_of_half x hx hn hhalf]
      simp only [sixVertexSectorPosition_alternatingOdd_apply_val]
      change first + 2 * k.val = 2 * k.val + 1
      omega
    exact Set.powersetCard.ofFinEmbEquiv.symm.injective hpos



theorem sixVertexInfinityGraph_adj_twice_le
    {N n : Nat} {x y : SixVertexSector N n}
    (hxy : (sixVertexInfinityGraph N n).Adj x y) : 2 * n ≤ N :=
  sixVertexSectorNoAdjacent_twice_le x
    (sixVertexInfinityGraph_adj_noAdjacent hxy).1



theorem sixVertexInfinityGraph_adj_alternating_of_half
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N) :
    (sixVertexInfinityGraph N n).Adj
      (sixVertexAlternatingEvenSector N n hhalf.le)
      (sixVertexAlternatingOddSector N n hhalf.le) :=
  sixVertexInfinityGraph_adj_alternating hn hhalf.le



theorem sixVertexInfinityGraph_adj_iff_alternating_of_half
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N)
    (x y : SixVertexSector N n) :
    (sixVertexInfinityGraph N n).Adj x y ↔
      (x = sixVertexAlternatingEvenSector N n hhalf.le ∧
          y = sixVertexAlternatingOddSector N n hhalf.le) ∨
        (x = sixVertexAlternatingOddSector N n hhalf.le ∧
          y = sixVertexAlternatingEvenSector N n hhalf.le) := by
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  constructor
  · intro hxy
    have hsupport := sixVertexInfinityGraph_adj_noAdjacent hxy
    have hx := sixVertexSectorNoAdjacent_eq_alternating_of_half
      x hsupport.1 hn hhalf
    have hy := sixVertexSectorNoAdjacent_eq_alternating_of_half
      y hsupport.2 hn hhalf
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (hxy.1 rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact False.elim (hxy.1 rfl)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact sixVertexInfinityGraph_adj_alternating_of_half hn hhalf
    · exact (sixVertexInfinityGraph_adj_alternating_of_half hn hhalf).symm


theorem sixVertexSectorTransferInfinity_apply_half
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N)
    (x y : SixVertexSector N n) :
    sixVertexSectorTransferInfinity N n x y =
      if (x = sixVertexAlternatingEvenSector N n hhalf.le ∧
            y = sixVertexAlternatingOddSector N n hhalf.le) ∨
          (x = sixVertexAlternatingOddSector N n hhalf.le ∧
            y = sixVertexAlternatingEvenSector N n hhalf.le)
      then 1 else 0 := by
  rw [sixVertexSectorTransferInfinity_apply]
  apply if_congr
  · exact sixVertexInfinityGraph_adj_iff_alternating_of_half
      hn hhalf x y
  · rfl
  · rfl



theorem sixVertexSectorTransferInfinity_mulVec_half
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N)
    (v : SixVertexSector N n → Real) (x : SixVertexSector N n) :
    (sixVertexSectorTransferInfinity N n *ᵥ v) x =
      if x = sixVertexAlternatingEvenSector N n hhalf.le then
        v (sixVertexAlternatingOddSector N n hhalf.le)
      else if x = sixVertexAlternatingOddSector N n hhalf.le then
        v (sixVertexAlternatingEvenSector N n hhalf.le)
      else 0 := by
  classical
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  have hne : even ≠ odd :=
    (sixVertexInfinityGraph_adj_alternating_of_half hn hhalf).ne
  rw [Matrix.mulVec, dotProduct]
  by_cases hxe : x = even
  · subst x
    rw [Fintype.sum_eq_single odd]
    · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        even, odd, hne]
    · intro y hy
      simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        even, odd, hne, hy]
  · by_cases hxo : x = odd
    · subst x
      rw [Fintype.sum_eq_single even]
      · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
          even, odd, hne, Ne.symm hne]
      · intro y hy
        simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
          even, odd, hne, Ne.symm hne, hy]
    · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        even, odd, hxe, hxo]



def sixVertexHalfFilledTransferInfinityVector
    (N n : Nat) (hhalf : 2 * n = N) : SixVertexSector N n → Real :=
  fun x => if x = sixVertexAlternatingEvenSector N n hhalf.le ∨
      x = sixVertexAlternatingOddSector N n hhalf.le then 1 else 0


theorem sixVertexHalfFilledTransferInfinityVector_eigenrelation
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N) :
    sixVertexSectorTransferInfinity N n *ᵥ
        sixVertexHalfFilledTransferInfinityVector N n hhalf =
      sixVertexHalfFilledTransferInfinityVector N n hhalf := by
  classical
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  have hne : even ≠ odd :=
    (sixVertexInfinityGraph_adj_alternating_of_half hn hhalf).ne
  funext x
  rw [Matrix.mulVec, dotProduct]
  by_cases hxe : x = even
  · subst x
    rw [Fintype.sum_eq_single odd]
    · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        sixVertexHalfFilledTransferInfinityVector, even, odd, hne]
    · intro y hy
      simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        sixVertexHalfFilledTransferInfinityVector, even, odd, hne, hy]
  by_cases hxo : x = odd
  · subst x
    rw [Fintype.sum_eq_single even]
    · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        sixVertexHalfFilledTransferInfinityVector, even, odd, hne,
        Ne.symm hne]
    · intro y hy
      simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        sixVertexHalfFilledTransferInfinityVector, even, odd, hne,
        Ne.symm hne, hy]
  · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
      sixVertexHalfFilledTransferInfinityVector, even, odd, hxe, hxo]



theorem sixVertexSectorTransferInfinity_eigenvector_one_eq_smul
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N)
    (v : SixVertexSector N n → Real)
    (hv : sixVertexSectorTransferInfinity N n *ᵥ v = v) :
    v = v (sixVertexAlternatingEvenSector N n hhalf.le) •
      sixVertexHalfFilledTransferInfinityVector N n hhalf := by
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  have hne : even ≠ odd :=
    (sixVertexInfinityGraph_adj_alternating_of_half hn hhalf).ne
  funext x
  have hx := congrFun hv x
  rw [sixVertexSectorTransferInfinity_mulVec_half hn hhalf] at hx
  by_cases hxe : x = even
  · subst x
    simp [sixVertexHalfFilledTransferInfinityVector, even, odd]
  · by_cases hxo : x = odd
    · subst x
      simpa [sixVertexHalfFilledTransferInfinityVector, even, odd,
        hne, Ne.symm hne] using hx.symm
    · simpa [sixVertexHalfFilledTransferInfinityVector, even, odd,
        hxe, hxo] using hx.symm

end

end StatMech.FrontierD
