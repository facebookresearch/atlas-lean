/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusDevelopedWinding
import Code.FrontierD.FKRectTorusNetFull

namespace StatMech.FrontierD

noncomputable section




def fkRectSquareDevelopPoint (p : Int × Int) : Int × Int :=
  (p.1 + (p.2 + 1) / 2, p.1 - p.2 / 2)


theorem fkRectSquareDevelopPoint_fst_sub_snd (p : Int × Int) :
    (fkRectSquareDevelopPoint p).1 -
        (fkRectSquareDevelopPoint p).2 = p.2 := by
  simp [fkRectSquareDevelopPoint]
  omega



theorem fkRectSquareDevelopPoint_snd_add_rowHalf (p : Int × Int) :
    (fkRectSquareDevelopPoint p).2 + p.2 / 2 = p.1 := by
  simp [fkRectSquareDevelopPoint]


theorem fkRectSquareDevelopPoint_injective :
    Function.Injective fkRectSquareDevelopPoint := by
  intro p q hpq
  have hy : p.2 = q.2 := by
    rw [← fkRectSquareDevelopPoint_fst_sub_snd p,
      ← fkRectSquareDevelopPoint_fst_sub_snd q, hpq]
  have hx : p.1 = q.1 := by
    rw [← fkRectSquareDevelopPoint_snd_add_rowHalf p,
      ← fkRectSquareDevelopPoint_snd_add_rowHalf q, hpq, hy]
  exact Prod.ext hx hy


def fkRectSquareUndevelopPoint (p : Int × Int) : Int × Int :=
  (p.2 + (p.1 - p.2) / 2, p.1 - p.2)

@[simp] theorem fkRectSquareUndevelopPoint_developPoint
    (p : Int × Int) :
    fkRectSquareUndevelopPoint (fkRectSquareDevelopPoint p) = p := by
  apply Prod.ext
  · simp [fkRectSquareUndevelopPoint,
      fkRectSquareDevelopPoint_fst_sub_snd]
    exact fkRectSquareDevelopPoint_snd_add_rowHalf p
  · exact fkRectSquareDevelopPoint_fst_sub_snd p

@[simp] theorem fkRectSquareDevelopPoint_undevelopPoint
    (p : Int × Int) :
    fkRectSquareDevelopPoint (fkRectSquareUndevelopPoint p) = p := by
  apply Prod.ext <;>
    simp [fkRectSquareDevelopPoint, fkRectSquareUndevelopPoint] <;>
    omega



def fkRectSquareDevelopEquiv : (Int × Int) ≃ (Int × Int) where
  toFun := fkRectSquareDevelopPoint
  invFun := fkRectSquareUndevelopPoint
  left_inv := fkRectSquareUndevelopPoint_developPoint
  right_inv := fkRectSquareDevelopPoint_undevelopPoint




def fkRectLiftedIndexedEdgeEnds (R : FKRectTorus) (e : R.EdgeIndex) :
    (Int × Int) × (Int × Int) :=
  let X : Int := e.2.1.val
  let Y : Int := e.2.2.val
  if e.1 then
    ((X, Y), (X, Y - 1))
  else if Even e.2.2.val then
    ((X, Y), (X - 1, Y - 1))
  else
    ((X - 1, Y), (X, Y - 1))



theorem fkRectSquareDevelopPoint_even_vertical (X k : Int) :
    fkRectSquareDevelopPoint (X, 2 * k - 1) -
        fkRectSquareDevelopPoint (X, 2 * k) = (0, 1) := by
  apply Prod.ext <;> simp [fkRectSquareDevelopPoint] <;> omega



theorem fkRectSquareDevelopPoint_even_diagonal (X k : Int) :
    fkRectSquareDevelopPoint (X - 1, 2 * k - 1) -
        fkRectSquareDevelopPoint (X, 2 * k) = (-1, 0) := by
  apply Prod.ext <;> simp [fkRectSquareDevelopPoint] <;> omega



theorem fkRectSquareDevelopPoint_odd_vertical (X k : Int) :
    fkRectSquareDevelopPoint (X, 2 * k) -
        fkRectSquareDevelopPoint (X, 2 * k + 1) = (-1, 0) := by
  apply Prod.ext <;> simp [fkRectSquareDevelopPoint] <;> omega



theorem fkRectSquareDevelopPoint_odd_diagonal (X k : Int) :
    fkRectSquareDevelopPoint (X, 2 * k) -
        fkRectSquareDevelopPoint (X - 1, 2 * k + 1) = (0, 1) := by
  apply Prod.ext <;> simp [fkRectSquareDevelopPoint] <;> omega



theorem fkRectLiftedIndexedEdgeEnds_squareStep
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2 -
        fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 =
      (-1, 0) ∨
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2 -
        fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 =
      (0, 1) := by
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val
  · left
    have hyeven := hy
    obtain ⟨k, hk⟩ := hy
    have hk' : (y.val : Int) = (k : Int) + k := by
      exact_mod_cast hk
    simp only [fkRectLiftedIndexedEdgeEnds, Bool.false_eq_true,
      ↓reduceIte, hyeven]
    rw [show (y.val : Int) = 2 * (k : Int) by omega]
    exact fkRectSquareDevelopPoint_even_diagonal x.val k
  · right
    have hodd : Odd y.val := Nat.not_even_iff_odd.mp hy
    obtain ⟨k, hk⟩ := hodd
    have hk' : (y.val : Int) = 2 * (k : Int) + 1 := by
      exact_mod_cast hk
    simp only [fkRectLiftedIndexedEdgeEnds, Bool.false_eq_true,
      ↓reduceIte, hy]
    rw [hk']
    simpa using fkRectSquareDevelopPoint_odd_diagonal x.val k
  · right
    obtain ⟨k, hk⟩ := hy
    have hk' : (y.val : Int) = (k : Int) + k := by
      exact_mod_cast hk
    simp only [fkRectLiftedIndexedEdgeEnds, ↓reduceIte]
    rw [show (y.val : Int) = 2 * (k : Int) by omega]
    exact fkRectSquareDevelopPoint_even_vertical x.val k
  · left
    have hodd : Odd y.val := Nat.not_even_iff_odd.mp hy
    obtain ⟨k, hk⟩ := hodd
    have hk' : (y.val : Int) = 2 * (k : Int) + 1 := by
      exact_mod_cast hk
    simp only [fkRectLiftedIndexedEdgeEnds, ↓reduceIte]
    rw [hk']
    simpa using fkRectSquareDevelopPoint_odd_vertical x.val k




def fkRectSquareDeckTranslation (R : FKRectTorus) (u : Int × Int) :
    Int × Int :=
  ((R.width : Int) * u.1 + (R.height / 2 : Nat) * u.2,
    (R.width : Int) * u.1 - (R.height / 2 : Nat) * u.2)


def fkRectSquareDeckHom (R : FKRectTorus) :
    (Int × Int) →+ (Int × Int) where
  toFun := fkRectSquareDeckTranslation R
  map_zero' := by
    simp [fkRectSquareDeckTranslation]
  map_add' := by
    intro u v
    apply Prod.ext <;> simp [fkRectSquareDeckTranslation] <;> ring

theorem fkRectSquareDeckHom_injective (R : FKRectTorus) :
    Function.Injective (fkRectSquareDeckHom R) := by
  intro u v huv
  change fkRectSquareDeckTranslation R u =
    fkRectSquareDeckTranslation R v at huv
  have hp := congrArg Prod.fst huv
  have hq := congrArg Prod.snd huv
  simp only [fkRectSquareDeckTranslation] at hp hq
  have hw : (R.width : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.width_pos)
  have hhalfNat : R.height / 2 ≠ 0 := by
    exact ne_of_gt (Nat.div_pos R.height_gt_two.le (by norm_num))
  have hhalf : (R.height / 2 : Nat) ≠ (0 : Int) := by
    exact_mod_cast hhalfNat
  have hx2 : (2 : Int) * R.width * (u.1 - v.1) = 0 := by
    linear_combination hp + hq
  have hx : u.1 = v.1 := by
    have hcoefficient : (2 : Int) * R.width ≠ 0 :=
      mul_ne_zero (by norm_num) hw
    have : u.1 - v.1 = 0 :=
      (mul_eq_zero.mp hx2).resolve_left hcoefficient
    omega
  have hy2 : (2 : Int) * (R.height / 2 : Nat) *
      (u.2 - v.2) = 0 := by
    linear_combination hp - hq
  have hy : u.2 = v.2 := by
    have hcoefficient : (2 : Int) * (R.height / 2 : Nat) ≠ 0 :=
      mul_ne_zero (by norm_num) hhalf
    have : u.2 - v.2 = 0 :=
      (mul_eq_zero.mp hy2).resolve_left hcoefficient
    omega
  exact Prod.ext hx hy



def fkRectSquareDeckLattice (R : FKRectTorus) :
    AddSubgroup (Int × Int) :=
  (fkRectSquareDeckHom R).range

@[simp] theorem mem_fkRectSquareDeckLattice_iff
    (R : FKRectTorus) (z : Int × Int) :
    z ∈ fkRectSquareDeckLattice R ↔
      ∃ u : Int × Int, fkRectSquareDeckTranslation R u = z :=
  by
    change z ∈ (fkRectSquareDeckHom R).range ↔ _
    simpa [fkRectSquareDeckHom] using
      (AddMonoidHom.mem_range (f := fkRectSquareDeckHom R) (y := z))



theorem fkRectSquareDevelopPoint_add_period
    (R : FKRectTorus) (p u : Int × Int) :
    fkRectSquareDevelopPoint
          (p.1 + (R.width : Int) * u.1,
            p.2 + (R.height : Int) * u.2) -
        fkRectSquareDevelopPoint p =
      fkRectSquareDeckTranslation R u := by
  have hhNat : 2 * (R.height / 2) = R.height :=
    Nat.two_mul_div_two_of_even R.height_even
  have hh : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    exact_mod_cast hhNat
  have hhalf : ((R.height : Int) * u.2) / 2 =
      (R.height / 2 : Nat) * u.2 := by
    rw [← hh]
    rw [show (2 : Int) * (R.height / 2 : Nat) * u.2 =
      2 * ((R.height / 2 : Nat) * u.2) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hdiv : (2 : Int) ∣ (R.height : Int) * u.2 := by
    refine ⟨(R.height / 2 : Nat) * u.2, ?_⟩
    rw [← hh]
    ring
  have hceil :
      (p.2 + (R.height : Int) * u.2 + 1) / 2 =
        (p.2 + 1) / 2 + (R.height / 2 : Nat) * u.2 := by
    rw [show p.2 + (R.height : Int) * u.2 + 1 =
      (p.2 + 1) + (R.height : Int) * u.2 by ring]
    rw [Int.add_ediv_of_dvd_right hdiv, hhalf]
  have hfloor :
      (p.2 + (R.height : Int) * u.2) / 2 =
        p.2 / 2 + (R.height / 2 : Nat) * u.2 := by
    rw [Int.add_ediv_of_dvd_right hdiv, hhalf]
  apply Prod.ext <;>
    simp [fkRectSquareDevelopPoint, fkRectSquareDeckTranslation,
      hceil, hfloor] <;>
    ring



theorem fkRectSquareUndevelopPoint_add_deck
    (R : FKRectTorus) (p u : Int × Int) :
    fkRectSquareUndevelopPoint (p + fkRectSquareDeckTranslation R u) =
      ((fkRectSquareUndevelopPoint p).1 + (R.width : Int) * u.1,
        (fkRectSquareUndevelopPoint p).2 + (R.height : Int) * u.2) := by
  apply fkRectSquareDevelopPoint_injective
  rw [fkRectSquareDevelopPoint_undevelopPoint]
  have h := fkRectSquareDevelopPoint_add_period R
    (fkRectSquareUndevelopPoint p) u
  rw [fkRectSquareDevelopPoint_undevelopPoint] at h
  apply Prod.ext
  · have h' := congrArg Prod.fst h
    simp only [Prod.fst_sub, Prod.fst_add] at h' ⊢
    omega
  · have h' := congrArg Prod.snd h
    simp only [Prod.snd_sub, Prod.snd_add] at h' ⊢
    omega


abbrev FKRectSquareTorus (R : FKRectTorus) :=
  (Int × Int) ⧸ fkRectSquareDeckLattice R


def fkRectVertexSquarePoint (R : FKRectTorus) (x : R.Vertex) : Int × Int :=
  fkRectSquareDevelopPoint (x.1.val, x.2.val)


def fkRectVertexSquareClass (R : FKRectTorus) (x : R.Vertex) :
    FKRectSquareTorus R :=
  QuotientAddGroup.mk (fkRectVertexSquarePoint R x)



theorem fkRectVertexSquareClass_injective (R : FKRectTorus) :
    Function.Injective (fkRectVertexSquareClass R) := by
  intro x y hxy
  have hmem : fkRectVertexSquarePoint R x -
      fkRectVertexSquarePoint R y ∈ fkRectSquareDeckLattice R :=
    QuotientAddGroup.eq_iff_sub_mem.mp hxy
  obtain ⟨u, hu⟩ :=
    (mem_fkRectSquareDeckLattice_iff R _).mp hmem
  have hpoint : fkRectVertexSquarePoint R x =
      fkRectVertexSquarePoint R y + fkRectSquareDeckTranslation R u := by
    rw [hu]
    apply Prod.ext <;> simp <;> ring
  have htilt := congrArg fkRectSquareUndevelopPoint hpoint
  rw [fkRectSquareUndevelopPoint_add_deck] at htilt
  simp only [fkRectVertexSquarePoint,
    fkRectSquareUndevelopPoint_developPoint] at htilt
  have hxInt := congrArg Prod.fst htilt
  have hyInt := congrArg Prod.snd htilt
  simp only [Prod.fst, Prod.snd] at hxInt hyInt
  letI : NeZero R.width := ⟨ne_of_gt R.width_pos⟩
  letI : NeZero R.height := ⟨ne_of_gt R.height_pos⟩
  have hxMod : ((x.1.val : Int) : ZMod R.width) =
      ((y.1.val : Int) : ZMod R.width) := by
    have h := congrArg (fun z : Int => (z : ZMod R.width)) hxInt
    simpa using h
  have hyMod : ((x.2.val : Int) : ZMod R.height) =
      ((y.2.val : Int) : ZMod R.height) := by
    have h := congrArg (fun z : Int => (z : ZMod R.height)) hyInt
    simpa using h
  have hx : x.1 = y.1 := by
    apply Fin.ext
    have h := congrArg ZMod.val hxMod
    simpa only [Int.cast_natCast, ZMod.val_natCast_of_lt x.1.isLt,
      ZMod.val_natCast_of_lt y.1.isLt] using h
  have hy : x.2 = y.2 := by
    apply Fin.ext
    have h := congrArg ZMod.val hyMod
    simpa only [Int.cast_natCast, ZMod.val_natCast_of_lt x.2.isLt,
      ZMod.val_natCast_of_lt y.2.isLt] using h
  exact Prod.ext hx hy



def fkRectSquareRepresentativeVertex (R : FKRectTorus) (z : Int × Int) :
    R.Vertex :=
  let p := fkRectSquareUndevelopPoint z
  (⟨p.1.natMod R.width, Int.natMod_lt (ne_of_gt R.width_pos)⟩,
    ⟨p.2.natMod R.height, Int.natMod_lt (ne_of_gt R.height_pos)⟩)



def fkRectIntModFin {N : Nat} (hN : 0 < N) (z : Int) : Fin N :=
  ⟨z.natMod N, Int.natMod_lt (ne_of_gt hN)⟩

@[simp] theorem fkRectIntModFin_natCast {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    fkRectIntModFin hN (i.val : Int) = i := by
  apply Fin.ext
  simp [fkRectIntModFin, Int.natMod, Int.emod_eq_of_lt,
    Int.natCast_nonneg, i.isLt]

@[simp] theorem fkRectIntModFin_natCast_sub_one {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    fkRectIntModFin hN ((i.val : Int) - 1) =
      SixVertexArrows.cyclicPred hN i := by
  apply Fin.ext
  by_cases hi : i.val = 0
  · simp only [fkRectIntModFin, Fin.val_mk, Int.natMod,
      SixVertexArrows.cyclicPred, hi, Nat.zero_add]
    have hrepr : (-1 : Int) = ((N - 1 : Nat) : Int) + (N : Int) * (-1) := by
      omega
    have hnonneg : (0 : Int) ≤ ((N - 1 : Nat) : Int) := by omega
    have hlt : ((N - 1 : Nat) : Int) < N := by omega
    have hmod : (-1 : Int) % (N : Int) = (N - 1 : Nat) := by
      rw [hrepr, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt hnonneg hlt]
    change ((-1 : Int) % (N : Int)).toNat = (N - 1) % N
    rw [hmod, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]
  · have hiPos : (0 : Int) <= (i.val : Int) - 1 := by omega
    have hiLt : (i.val : Int) - 1 < N := by omega
    simp only [fkRectIntModFin, Fin.val_mk, Int.natMod,
      SixVertexArrows.cyclicPred]
    rw [Int.emod_eq_of_lt hiPos hiLt]
    have htoNat : ((i.val : Int) - 1).toNat = i.val - 1 := by
      rw [← Int.natCast_inj]
      rw [Int.natCast_toNat_eq_self.mpr hiPos]
      omega
    rw [htoNat]
    rw [show i.val + N - 1 = (i.val - 1) + N by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]


def fkRectLiftedVertex (R : FKRectTorus) (p : Int × Int) : R.Vertex :=
  (fkRectIntModFin R.width_pos p.1,
    fkRectIntModFin R.height_pos p.2)

@[simp] theorem fkRectSquareRepresentativeVertex_developPoint
    (R : FKRectTorus) (p : Int × Int) :
    fkRectSquareRepresentativeVertex R (fkRectSquareDevelopPoint p) =
      fkRectLiftedVertex R p := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [fkRectSquareRepresentativeVertex, fkRectLiftedVertex,
      fkRectIntModFin]


theorem fkRectVertexSquareClass_representative
    (R : FKRectTorus) (z : Int × Int) :
    fkRectVertexSquareClass R (fkRectSquareRepresentativeVertex R z) =
      QuotientAddGroup.mk z := by
      let p := fkRectSquareUndevelopPoint z
      let x := fkRectSquareRepresentativeVertex R z
      let u : Int × Int :=
        (p.1 / (R.width : Int), p.2 / (R.height : Int))
      have hw : (R.width : Int) ≠ 0 := by
        exact_mod_cast (ne_of_gt R.width_pos)
      have hh : (R.height : Int) ≠ 0 := by
        exact_mod_cast (ne_of_gt R.height_pos)
      have hremWidth : ((p.1.natMod R.width : Nat) : Int) =
          p.1 % (R.width : Int) := by
        rw [Int.natMod, Int.natCast_toNat_eq_self]
        exact Int.emod_nonneg _ hw
      have hremHeight : ((p.2.natMod R.height : Nat) : Int) =
          p.2 % (R.height : Int) := by
        rw [Int.natMod, Int.natCast_toNat_eq_self]
        exact Int.emod_nonneg _ hh
      have hp :
          ((x.1.val : Int) + (R.width : Int) * u.1,
            (x.2.val : Int) + (R.height : Int) * u.2) = p := by
        apply Prod.ext
        · dsimp [x, fkRectSquareRepresentativeVertex, p, u]
          rw [hremWidth]
          exact Int.emod_add_ediv _ _
        · dsimp [x, fkRectSquareRepresentativeVertex, p, u]
          rw [hremHeight]
          exact Int.emod_add_ediv _ _
      have hperiod := fkRectSquareDevelopPoint_add_period R
        ((x.1.val : Int), (x.2.val : Int)) u
      have hdevelop : fkRectVertexSquarePoint R x +
          fkRectSquareDeckTranslation R u = z := by
        have hz : fkRectSquareDevelopPoint p = z := by
          dsimp [p]
          exact fkRectSquareDevelopPoint_undevelopPoint z
        rw [← hz, ← hp]
        dsimp [fkRectVertexSquarePoint]
        apply Prod.ext
        · have h := congrArg Prod.fst hperiod
          simp only [Prod.fst_sub, Prod.fst_add] at h ⊢
          omega
        · have h := congrArg Prod.snd hperiod
          simp only [Prod.snd_sub, Prod.snd_add] at h ⊢
          omega
      change QuotientAddGroup.mk (fkRectVertexSquarePoint R x) =
        QuotientAddGroup.mk z
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      apply (mem_fkRectSquareDeckLattice_iff R _).mpr
      refine ⟨-u, ?_⟩
      have hmap : fkRectSquareDeckTranslation R (-u) =
          -fkRectSquareDeckTranslation R u :=
        map_neg (fkRectSquareDeckHom R) u
      rw [hmap, ← hdevelop]
      abel



theorem fkRectVertexSquareClass_liftedVertex
    (R : FKRectTorus) (p : Int × Int) :
    fkRectVertexSquareClass R (fkRectLiftedVertex R p) =
      QuotientAddGroup.mk (fkRectSquareDevelopPoint p) := by
  rw [← fkRectSquareRepresentativeVertex_developPoint]
  exact fkRectVertexSquareClass_representative R
    (fkRectSquareDevelopPoint p)



theorem fkRectLiftedIndexedEdgeEnds_project
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectTorusIndexedEdge R e =
      s(fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1,
        fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2) := by
  rcases e with ⟨b, x, y⟩
  cases b
  · by_cases hy : Even y.val
    · simp [fkRectTorusIndexedEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectLiftedVertex, hy]
    · simp [fkRectTorusIndexedEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectLiftedVertex, hy]
  · simp [fkRectTorusIndexedEdge, fkRectLiftedIndexedEdgeEnds,
      fkRectLiftedVertex]



theorem fkRectLiftedIndexedEdgeEnds_developedStep
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectDevelopedStep R
        (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1)
        (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2) =
      (fkRectLiftedIndexedEdgeEnds R e).2 -
        (fkRectLiftedIndexedEdgeEnds R e).1 := by
  rcases e with ⟨b, x, y⟩
  cases b
  · by_cases hy : Even y.val
    · simp only [fkRectLiftedIndexedEdgeEnds, Bool.false_eq_true,
        ↓reduceIte, hy, fkRectLiftedVertex, Prod.fst, Prod.snd,
        fkRectIntModFin_natCast, fkRectIntModFin_natCast_sub_one]
      rw [fkRectDevelopedStep, fkRectHorizontalSeamIncrement_pred,
        fkRectVerticalSeamIncrement_pred, fkRectCyclicPred_val,
        fkRectCyclicPred_val]
      by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0 <;>
        simp [hx0, hy0] <;> omega
    · simp only [fkRectLiftedIndexedEdgeEnds, Bool.false_eq_true,
        ↓reduceIte, hy, fkRectLiftedVertex, Prod.fst, Prod.snd,
        fkRectIntModFin_natCast, fkRectIntModFin_natCast_sub_one]
      rw [fkRectDevelopedStep, fkRectHorizontalSeamIncrement_swap,
        fkRectHorizontalSeamIncrement_pred,
        fkRectVerticalSeamIncrement_pred, fkRectCyclicPred_val,
        fkRectCyclicPred_val]
      by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0 <;>
        simp [hx0, hy0] <;> omega
  · simp only [fkRectLiftedIndexedEdgeEnds, ↓reduceIte,
      fkRectLiftedVertex, Prod.fst, Prod.snd,
      fkRectIntModFin_natCast, fkRectIntModFin_natCast_sub_one]
    rw [fkRectDevelopedStep, fkRectHorizontalSeamIncrement_same_fst,
      fkRectVerticalSeamIncrement_pred, fkRectCyclicPred_val]
    by_cases hy0 : y.val = 0 <;> simp [hy0] <;> omega




theorem fkRectIndexedEdge_squareLift
    (R : FKRectTorus) (e : R.EdgeIndex) :
    ∃ p q : Int × Int,
      fkRectTorusIndexedEdge R e =
        s(fkRectLiftedVertex R p, fkRectLiftedVertex R q) ∧
      fkRectVertexSquareClass R (fkRectLiftedVertex R p) =
        QuotientAddGroup.mk (fkRectSquareDevelopPoint p) ∧
      fkRectVertexSquareClass R (fkRectLiftedVertex R q) =
        QuotientAddGroup.mk (fkRectSquareDevelopPoint q) ∧
      fkRectDevelopedStep R (fkRectLiftedVertex R p)
          (fkRectLiftedVertex R q) = q - p ∧
      (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (-1, 0) ∨
        fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (0, 1)) := by
  refine ⟨(fkRectLiftedIndexedEdgeEnds R e).1,
    (fkRectLiftedIndexedEdgeEnds R e).2,
    fkRectLiftedIndexedEdgeEnds_project R e,
    fkRectVertexSquareClass_liftedVertex R _,
    fkRectVertexSquareClass_liftedVertex R _,
    fkRectLiftedIndexedEdgeEnds_developedStep R e, ?_⟩
  exact fkRectLiftedIndexedEdgeEnds_squareStep R e



theorem fkRectLiftedVertex_eq_iff_exists_period
    (R : FKRectTorus) (p q : Int × Int) :
    fkRectLiftedVertex R p = fkRectLiftedVertex R q ↔
      ∃ u : Int × Int,
        p = (q.1 + (R.width : Int) * u.1,
          q.2 + (R.height : Int) * u.2) := by
  constructor
  · intro hpq
    have hclass :
        (QuotientAddGroup.mk (fkRectSquareDevelopPoint p) :
            FKRectSquareTorus R) =
          QuotientAddGroup.mk (fkRectSquareDevelopPoint q) := by
      rw [← fkRectVertexSquareClass_liftedVertex R p,
        ← fkRectVertexSquareClass_liftedVertex R q, hpq]
    have hmem : fkRectSquareDevelopPoint p -
        fkRectSquareDevelopPoint q ∈ fkRectSquareDeckLattice R :=
      QuotientAddGroup.eq_iff_sub_mem.mp hclass
    obtain ⟨u, hu⟩ :=
      (mem_fkRectSquareDeckLattice_iff R _).mp hmem
    have hdevelop : fkRectSquareDevelopPoint p =
        fkRectSquareDevelopPoint q + fkRectSquareDeckTranslation R u := by
      rw [hu]
      apply Prod.ext <;> simp <;> ring
    have hundevelop := congrArg fkRectSquareUndevelopPoint hdevelop
    rw [fkRectSquareUndevelopPoint_developPoint,
      fkRectSquareUndevelopPoint_add_deck,
      fkRectSquareUndevelopPoint_developPoint] at hundevelop
    exact ⟨u, hundevelop⟩
  · rintro ⟨u, rfl⟩
    apply fkRectVertexSquareClass_injective R
    rw [fkRectVertexSquareClass_liftedVertex,
      fkRectVertexSquareClass_liftedVertex]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply (mem_fkRectSquareDeckLattice_iff R _).mpr
    refine ⟨u, ?_⟩
    exact (fkRectSquareDevelopPoint_add_period R q u).symm


def FKRectSquareAxisStep (p q : Int × Int) : Prop :=
  q - p = (-1, 0) ∨ q - p = (0, 1) ∨
    q - p = (1, 0) ∨ q - p = (0, -1)

theorem FKRectSquareAxisStep.symm {p q : Int × Int}
    (h : FKRectSquareAxisStep p q) :
    FKRectSquareAxisStep q p := by
  rcases h with h | h | h | h
  · right; right; left
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at * <;>
      omega
  · right; right; right
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at * <;>
      omega
  · left
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at * <;>
      omega
  · right; left
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at * <;>
      omega



theorem fkRectSquareDevelopPoint_sub_add_period
    (R : FKRectTorus) (p q u : Int × Int) :
    fkRectSquareDevelopPoint
          (q.1 + (R.width : Int) * u.1,
            q.2 + (R.height : Int) * u.2) -
        fkRectSquareDevelopPoint
          (p.1 + (R.width : Int) * u.1,
            p.2 + (R.height : Int) * u.2) =
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p := by
  have hp := fkRectSquareDevelopPoint_add_period R p u
  have hq := fkRectSquareDevelopPoint_add_period R q u
  apply Prod.ext
  · have hp' := congrArg Prod.fst hp
    have hq' := congrArg Prod.fst hq
    simp only [Prod.fst_sub] at hp' hq' ⊢
    omega
  · have hp' := congrArg Prod.snd hp
    have hq' := congrArg Prod.snd hq
    simp only [Prod.snd_sub] at hp' hq' ⊢
    omega




theorem fkRectTorusGraph_adj_squareLift
    (R : FKRectTorus) {x y : R.Vertex}
    (hxy : (fkRectTorusGraph R).Adj x y)
    (p : Int × Int) (hp : fkRectLiftedVertex R p = x) :
    ∃ q : Int × Int,
      fkRectLiftedVertex R q = y ∧
        q - p = fkRectDevelopedStep R x y ∧
        FKRectSquareAxisStep (fkRectSquareDevelopPoint p)
          (fkRectSquareDevelopPoint q) := by
  obtain ⟨e, he⟩ := hxy
  obtain ⟨a, b, hedge, ha, hb, hdeveloped, hstep⟩ :=
    fkRectIndexedEdge_squareLift R e
  have hpairs :
      s(fkRectLiftedVertex R a, fkRectLiftedVertex R b) = s(x, y) :=
    hedge.symm.trans he
  rcases Sym2.eq_iff.mp hpairs with horient | horient
  · have hpa : fkRectLiftedVertex R p = fkRectLiftedVertex R a :=
      hp.trans horient.1.symm
    obtain ⟨u, hu⟩ :=
      (fkRectLiftedVertex_eq_iff_exists_period R p a).mp hpa
    let q : Int × Int :=
      (b.1 + (R.width : Int) * u.1,
        b.2 + (R.height : Int) * u.2)
    refine ⟨q, ?_, ?_, ?_⟩
    · have hqb : fkRectLiftedVertex R q = fkRectLiftedVertex R b :=
        (fkRectLiftedVertex_eq_iff_exists_period R q b).mpr ⟨u, rfl⟩
      exact hqb.trans horient.2
    · rw [← horient.1, ← horient.2, hdeveloped]
      dsimp [q]
      rw [hu]
      apply Prod.ext <;> simp <;> ring
    · rw [hu]
      dsimp [q]
      unfold FKRectSquareAxisStep
      rw [fkRectSquareDevelopPoint_sub_add_period R a b u]
      exact hstep.elim Or.inl (fun h => Or.inr (Or.inl h))
  · have hpb : fkRectLiftedVertex R p = fkRectLiftedVertex R b :=
      hp.trans horient.2.symm
    obtain ⟨u, hu⟩ :=
      (fkRectLiftedVertex_eq_iff_exists_period R p b).mp hpb
    let q : Int × Int :=
      (a.1 + (R.width : Int) * u.1,
        a.2 + (R.height : Int) * u.2)
    refine ⟨q, ?_, ?_, ?_⟩
    · have hqa : fkRectLiftedVertex R q = fkRectLiftedVertex R a :=
        (fkRectLiftedVertex_eq_iff_exists_period R q a).mpr ⟨u, rfl⟩
      exact hqa.trans horient.1
    · rw [← horient.2, ← horient.1,
        fkRectDevelopedStep_swap, hdeveloped]
      dsimp [q]
      rw [hu]
      apply Prod.ext <;> simp <;> ring
    · rw [hu]
      dsimp [q]
      apply FKRectSquareAxisStep.symm
      unfold FKRectSquareAxisStep
      rw [fkRectSquareDevelopPoint_sub_add_period R a b u]
      exact hstep.elim Or.inl (fun h => Or.inr (Or.inl h))



inductive FKRectSquareWalkLift (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} :
    {x y : R.Vertex} → G.Walk x y →
      (Int × Int) → (Int × Int) → Prop
  | nil {x : R.Vertex} (p : Int × Int)
      (hp : fkRectLiftedVertex R p = x) :
      FKRectSquareWalkLift R (.nil : G.Walk x x) p p
  | cons {x y z : R.Vertex} {hxy : G.Adj x y}
      {w : G.Walk y z} {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep (fkRectSquareDevelopPoint p)
        (fkRectSquareDevelopPoint q))
      (tail : FKRectSquareWalkLift R w q r) :
      FKRectSquareWalkLift R (.cons hxy w) p r



theorem fkRectWalk_exists_squareLift
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    (hsub : G ≤ fkRectTorusGraph R) {x y : R.Vertex}
    (w : G.Walk x y) (p : Int × Int)
    (hp : fkRectLiftedVertex R p = x) :
    ∃ q : Int × Int, FKRectSquareWalkLift R w p q := by
  induction w generalizing p with
  | nil =>
      exact ⟨p, FKRectSquareWalkLift.nil p hp⟩
  | @cons x y z hxy w ih =>
      obtain ⟨q, hq, hdisp, haxis⟩ :=
        fkRectTorusGraph_adj_squareLift R (hsub hxy) p hp
      obtain ⟨r, htail⟩ := ih q hq
      exact ⟨r, FKRectSquareWalkLift.cons hp hq hdisp haxis htail⟩


theorem FKRectSquareWalkLift.end_project
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    fkRectLiftedVertex R q = y := by
  induction h with
  | nil p hp => exact hp
  | cons hp hq hdisp haxis tail ih => exact ih



theorem FKRectSquareWalkLift.sub_eq_developedDisplacement
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    q - p = fkRectWalkDevelopedDisplacement R w := by
  induction h with
  | nil p hp =>
      simp [fkRectWalkDevelopedDisplacement]
  | @cons x y z hxy w p q r hp hq hdisp haxis tail ih =>
      simp only [fkRectWalkDevelopedDisplacement]
      rw [← hdisp, ← ih]
      apply Prod.ext <;> simp <;> ring



theorem FKRectSquareWalkLift.closed_end_eq_period_winding
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    q = (p.1 + (R.width : Int) * (fkRectWalkWinding R w).1,
      p.2 + (R.height : Int) * (fkRectWalkWinding R w).2) := by
  have hdisp := h.sub_eq_developedDisplacement R
  rw [fkRectClosedWalkDevelopedDisplacement_eq_period_winding] at hdisp
  apply Prod.ext
  · have hx := congrArg Prod.fst hdisp
    simp only [Prod.fst_sub, Prod.fst] at hx ⊢
    omega
  · have hy := congrArg Prod.snd hdisp
    simp only [Prod.snd_sub, Prod.snd] at hy ⊢
    omega



theorem FKRectSquareWalkLift.closed_develop_sub_eq_deck_winding
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p =
      fkRectSquareDeckTranslation R (fkRectWalkWinding R w) := by
  rw [h.closed_end_eq_period_winding R]
  exact fkRectSquareDevelopPoint_add_period R p
    (fkRectWalkWinding R w)



theorem fkRectVertexSquareClass_surjective (R : FKRectTorus) :
    Function.Surjective (fkRectVertexSquareClass R) := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H z =>
      exact ⟨fkRectSquareRepresentativeVertex R z,
        fkRectVertexSquareClass_representative R z⟩



noncomputable def fkRectVertexSquareEquiv (R : FKRectTorus) :
    R.Vertex ≃ FKRectSquareTorus R :=
  Equiv.ofBijective (fkRectVertexSquareClass R)
    ⟨fkRectVertexSquareClass_injective R,
      fkRectVertexSquareClass_surjective R⟩



theorem fkRectSquareDeckTranslation_det
    (R : FKRectTorus) (u v : Int × Int) :
    (fkRectSquareDeckTranslation R u).1 *
          (fkRectSquareDeckTranslation R v).2 -
        (fkRectSquareDeckTranslation R u).2 *
          (fkRectSquareDeckTranslation R v).1 =
      -(R.width : Int) * R.height *
        (u.1 * v.2 - u.2 * v.1) := by
  have hhNat : 2 * (R.height / 2) = R.height :=
    Nat.two_mul_div_two_of_even R.height_even
  have hh : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    exact_mod_cast hhNat
  simp only [fkRectSquareDeckTranslation, Prod.fst, Prod.snd]
  linear_combination
    -(R.width : Int) * u.1 * v.2 * hh +
      (R.width : Int) * u.2 * v.1 * hh



theorem fkRectWindingIndependent_squareDeck_iff
    (R : FKRectTorus) (u v : Int × Int) :
    FKRectWindingIndependent (fkRectSquareDeckTranslation R u)
        (fkRectSquareDeckTranslation R v) ↔
      FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent
  rw [fkRectSquareDeckTranslation_det]
  have hw : (R.width : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.width_pos)
  have hh : (R.height : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.height_pos)
  constructor
  · intro h hzero
    apply h
    rw [hzero]
    ring
  · intro h hscaled
    apply h
    have hcoefficient : -(R.width : Int) * R.height ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hw) hh
    exact (mul_eq_zero.mp hscaled).resolve_left hcoefficient



theorem FKRectSquareWalkLift.closed_developedIndependent_iff
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (hz : FKRectSquareWalkLift R z a b) :
    FKRectWindingIndependent
        (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)
        (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a) ↔
      FKRectWindingIndependent
        (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  rw [hw.closed_develop_sub_eq_deck_winding R,
    hz.closed_develop_sub_eq_deck_winding R]
  exact fkRectWindingIndependent_squareDeck_iff R _ _


theorem fkRectOpenGraph_le_torusGraph
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenGraph R omega ≤ fkRectTorusGraph R := by
  intro x y hxy
  obtain ⟨e, _, he⟩ := hxy
  exact ⟨e, he⟩



def FKRectHasSquareLiftNet (R : FKRectTorus)
    (omega : R.Configuration) : Prop :=
  ∃ x : R.Vertex,
    ∃ w z : (fkRectOpenGraph R omega).Walk x x,
      ∃ p q a b : Int × Int,
        FKRectSquareWalkLift R w p q ∧
        FKRectSquareWalkLift R z a b ∧
        FKRectWindingIndependent
          (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)
          (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a)



theorem fkRectHasSquareLiftNet_iff
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectHasSquareLiftNet R omega ↔ FKRectHasNet R omega := by
  constructor
  · rintro ⟨x, w, z, p, q, a, b, hw, hz, hind⟩
    exact ⟨x, w, z,
      (hw.closed_developedIndependent_iff R hz).mp hind⟩
  · rintro ⟨x, w, z, hind⟩
    let p : Int × Int := ((x.1.val : Int), (x.2.val : Int))
    have hp : fkRectLiftedVertex R p = x := by
      apply Prod.ext <;>
        simp [p, fkRectLiftedVertex]
    obtain ⟨q, hw⟩ := fkRectWalk_exists_squareLift R
      (fkRectOpenGraph_le_torusGraph R omega) w p hp
    obtain ⟨b, hz⟩ := fkRectWalk_exists_squareLift R
      (fkRectOpenGraph_le_torusGraph R omega) z p hp
    exact ⟨x, w, z, p, q, p, b, hw, hz,
      (hw.closed_developedIndependent_iff R hz).mpr hind⟩

end

end StatMech.FrontierD
