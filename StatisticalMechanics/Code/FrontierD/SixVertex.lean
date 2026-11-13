/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Hom.PowersetCard

open Finset Matrix

namespace StatMech.FrontierD




structure EvenTorus where
  width : ℕ
  height : ℕ
  width_pos : 0 < width
  height_pos : 0 < height
  width_even : Even width
  height_even : Even height


abbrev EvenTorus.Vertex (T : EvenTorus) := Fin T.width × Fin T.height



@[ext]
structure SixVertexArrows (T : EvenTorus) where
  horizontal : T.Vertex → Bool
  vertical : T.Vertex → Bool
deriving DecidableEq, Fintype

namespace SixVertexArrows

variable {T : EvenTorus}


def cyclicPred {N : ℕ} (hN : 0 < N) (i : Fin N) : Fin N :=
  ⟨(i.val + N - 1) % N, Nat.mod_lt _ hN⟩


def incomingCount (ω : SixVertexArrows T) (v : T.Vertex) : ℕ :=
  (ω.horizontal (cyclicPred T.width_pos v.1, v.2)).toNat + (!ω.horizontal v).toNat +
    (ω.vertical (v.1, cyclicPred T.height_pos v.2)).toNat + (!ω.vertical v).toNat


def IceRule (ω : SixVertexArrows T) : Prop :=
  ∀ v, ω.incomingCount v = 2




def IsCType (ω : SixVertexArrows T) (v : T.Vertex) : Prop :=
  ((ω.horizontal (cyclicPred T.width_pos v.1, v.2)).toNat +
      (!ω.horizontal v).toNat = 0) ∨
    ((ω.horizontal (cyclicPred T.width_pos v.1, v.2)).toNat +
      (!ω.horizontal v).toNat = 2)



noncomputable def localWeight (c : ℝ) (ω : SixVertexArrows T) (v : T.Vertex) : ℝ := by
  classical
  exact if ω.incomingCount v = 2 then if ω.IsCType v then c else 1 else 0


noncomputable def weight (c : ℝ) (ω : SixVertexArrows T) : ℝ :=
  ∏ v, ω.localWeight c v

end SixVertexArrows



abbrev SixVertexConfiguration (T : EvenTorus) :=
  {ω : SixVertexArrows T // ω.IceRule}




abbrev SixVertexRow (N : ℕ) := Fin N → Bool


def sixVertexUpCount {N : ℕ} (x : SixVertexRow N) : ℕ :=
  #{i | x i}


def sixVertexUpPositions {N : ℕ} (x : SixVertexRow N) : List (Fin N) :=
  ({i | x i} : Finset (Fin N)).sort (· ≤ ·)

@[simp] theorem sixVertexUpPositions_length {N : ℕ} (x : SixVertexRow N) :
    (sixVertexUpPositions x).length = sixVertexUpCount x := by
  simp [sixVertexUpPositions, sixVertexUpCount]



def sixVertexAlternating {N : ℕ} (x y : SixVertexRow N) : List (Fin N) :=
  (sixVertexUpPositions x).zip (sixVertexUpPositions y) |>.flatMap
    fun p => [p.1, p.2]



def SixVertexForwardInterlaced {N : ℕ} (x y : SixVertexRow N) : Prop :=
  sixVertexUpCount x = sixVertexUpCount y ∧
    (sixVertexAlternating x y).Pairwise (· ≤ ·)


def SixVertexInterlaced {N : ℕ} (x y : SixVertexRow N) : Prop :=
  SixVertexForwardInterlaced x y ∨ SixVertexForwardInterlaced y x

noncomputable instance sixVertexInterlacedDecidable {N : ℕ}
    (x y : SixVertexRow N) : Decidable (SixVertexInterlaced x y) :=
  Classical.propDecidable _

theorem sixVertexInterlaced_comm {N : ℕ} (x y : SixVertexRow N) :
    SixVertexInterlaced x y ↔ SixVertexInterlaced y x := by
  simp only [SixVertexInterlaced, or_comm]

theorem sixVertexInterlaced_upCount_eq {N : ℕ} {x y : SixVertexRow N}
    (h : SixVertexInterlaced x y) : sixVertexUpCount x = sixVertexUpCount y := by
  rcases h with h | h
  · exact h.1
  · exact h.1.symm


def sixVertexRowDistance {N : ℕ} (x y : SixVertexRow N) : ℕ :=
  #{i | x i ≠ y i}

theorem sixVertexRowDistance_comm {N : ℕ} (x y : SixVertexRow N) :
    sixVertexRowDistance x y = sixVertexRowDistance y x := by
  unfold sixVertexRowDistance
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm






noncomputable def sixVertexTransfer (N : ℕ) (c : ℝ) :
    Matrix (SixVertexRow N) (SixVertexRow N) ℝ := by
  classical
  exact fun x y => if x = y then 2
    else if SixVertexInterlaced x y then c ^ sixVertexRowDistance x y else 0

theorem sixVertexTransfer_apply (N : ℕ) (c : ℝ) (x y : SixVertexRow N) :
    sixVertexTransfer N c x y =
      if x = y then 2
      else if SixVertexInterlaced x y then c ^ sixVertexRowDistance x y else 0 :=
  rfl

theorem sixVertexTransfer_symmetric (N : ℕ) (c : ℝ) (x y : SixVertexRow N) :
    sixVertexTransfer N c x y = sixVertexTransfer N c y x := by
  classical
  by_cases hxy : x = y
  · subst y; rfl
  · have hyx : y ≠ x := Ne.symm hxy
    by_cases hi : SixVertexInterlaced x y
    · have hi' : SixVertexInterlaced y x := (sixVertexInterlaced_comm x y).1 hi
      simp [sixVertexTransfer, hxy, hyx, hi, hi', sixVertexRowDistance_comm]
    · have hi' : ¬ SixVertexInterlaced y x := by
        simpa only [sixVertexInterlaced_comm] using hi
      simp [sixVertexTransfer, hxy, hyx, hi, hi']



theorem sixVertexTransfer_eq_zero_of_upCount_ne {N : ℕ} (c : ℝ)
    {x y : SixVertexRow N} (hxy : sixVertexUpCount x ≠ sixVertexUpCount y) :
    sixVertexTransfer N c x y = 0 := by
  classical
  have hne : x ≠ y := fun h => hxy (h ▸ rfl)
  have hinter : ¬ SixVertexInterlaced x y :=
    fun h => hxy (sixVertexInterlaced_upCount_eq h)
  simp [sixVertexTransfer, hne, hinter]



theorem sixVertexTransfer_preserves_upCount {N : ℕ} (c : ℝ)
    {x y : SixVertexRow N} (h : sixVertexTransfer N c x y ≠ 0) :
    sixVertexUpCount x = sixVertexUpCount y := by
  by_contra hne
  exact h (sixVertexTransfer_eq_zero_of_upCount_ne c hne)

theorem sixVertexTransfer_nonneg {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (x y : SixVertexRow N) : 0 ≤ sixVertexTransfer N c x y := by
  classical
  simp only [sixVertexTransfer]
  split_ifs
  · norm_num
  · positivity
  · exact le_rfl



abbrev SixVertexSector (N n : ℕ) := Set.powersetCard (Fin N) n


def sixVertexSectorRow {N n : ℕ} (x : SixVertexSector N n) : SixVertexRow N :=
  fun i => decide (i ∈ (x : Finset (Fin N)))

@[simp] theorem sixVertexSectorRow_apply {N n : ℕ} (x : SixVertexSector N n)
    (i : Fin N) : sixVertexSectorRow x i = decide (i ∈ (x : Finset (Fin N))) :=
  rfl

@[simp] theorem sixVertexSectorRow_upCount {N n : ℕ} (x : SixVertexSector N n) :
    sixVertexUpCount (sixVertexSectorRow x) = n := by
  rw [sixVertexUpCount]
  have hx : ({i | sixVertexSectorRow x i} : Finset (Fin N)) = x := by
    ext i
    simp [sixVertexSectorRow]
  rw [hx]
  exact x.prop

@[simp] theorem sixVertexSectorRow_upPositions {N n : ℕ} (x : SixVertexSector N n) :
    sixVertexUpPositions (sixVertexSectorRow x) = (x : Finset (Fin N)).sort (· ≤ ·) := by
  unfold sixVertexUpPositions
  congr 1
  ext i
  simp [sixVertexSectorRow]


noncomputable def sixVertexSectorTransfer (N n : ℕ) (c : ℝ) :
    Matrix (SixVertexSector N n) (SixVertexSector N n) ℝ :=
  fun x y => sixVertexTransfer N c (sixVertexSectorRow x) (sixVertexSectorRow y)

theorem sixVertexSectorTransfer_isHermitian (N n : ℕ) (c : ℝ) :
    (sixVertexSectorTransfer N n c).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro x y
  simp only [star_id_of_comm]
  exact sixVertexTransfer_symmetric N c (sixVertexSectorRow y) (sixVertexSectorRow x)


theorem sixVertexSector_nonempty {N n : ℕ} (hn : n ≤ N) :
    Nonempty (SixVertexSector N n) := by
  let x : Finset (Fin N) := {i | i.val < n}
  have hcard : #{i : Fin N | i.val < n} = n := by
    rw [Fin.card_filter_val_lt, min_eq_right hn]
  exact ⟨⟨x, hcard⟩⟩


noncomputable def sixVertexSectorTopIndex (N n : ℕ) (hn : n ≤ N) :
    Fin (Fintype.card (SixVertexSector N n)) := by
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  exact ⟨0, Fintype.card_pos⟩





noncomputable def sixVertexSectorTopEigenvalue (N n : ℕ) (hn : n ≤ N)
    (c : ℝ) : ℝ :=
  (sixVertexSectorTransfer_isHermitian N n c).eigenvalues₀
    (sixVertexSectorTopIndex N n hn)



theorem sixVertexSectorTopEigenvalue_ge (N n : ℕ) (hn : n ≤ N) (c : ℝ)
    (i : Fin (Fintype.card (SixVertexSector N n))) :
    (sixVertexSectorTransfer_isHermitian N n c).eigenvalues₀ i ≤
      sixVertexSectorTopEigenvalue N n hn c := by
  apply (sixVertexSectorTransfer_isHermitian N n c).eigenvalues₀_antitone
  change (sixVertexSectorTopIndex N n hn).val ≤ i.val
  exact Nat.zero_le _



theorem sixVertexSectorTop_hasEigenvalue (N n : ℕ) (hn : n ≤ N) (c : ℝ) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c))
      (sixVertexSectorTopEigenvalue N n hn c) := by
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (sixVertexSectorTransfer_isHermitian N n c))
    finrank_euclideanSpace (sixVertexSectorTopIndex N n hn)




noncomputable def sixVertexLambda (N r : ℕ) (_hN : Even N) (_hr : r ≤ N / 2)
    (c : ℝ) : ℝ :=
  sixVertexSectorTopEigenvalue N (N / 2 - r)
    ((Nat.sub_le _ _).trans (Nat.div_le_self N 2)) c

end StatMech.FrontierD
