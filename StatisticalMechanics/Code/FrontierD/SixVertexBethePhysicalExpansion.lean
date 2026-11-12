/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBethePhysicalReduction










open Finset Matrix

namespace StatMech.FrontierD

noncomputable section




def sixVertexBetheCyclicIntervalTuples {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) : Finset (Fin (n + 1) -> Int) :=
  Fintype.piFinset fun i =>
    Finset.Icc (sixVertexBetheShiftCoordinates N x i) (x i)

@[simp] theorem mem_sixVertexBetheCyclicIntervalTuples {n : Nat}
    (N : Nat) (x q : Fin (n + 1) -> Int) :
    q ∈ sixVertexBetheCyclicIntervalTuples N x ↔
      forall i, sixVertexBetheShiftCoordinates N x i <= q i /\ q i <= x i := by
  simp [sixVertexBetheCyclicIntervalTuples]



def sixVertexBetheCollision {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) (i : Fin (n + 1)) : Prop :=
  q i = x i /\
    q (finRotate (n + 1) i) =
      sixVertexBetheShiftCoordinates N x (finRotate (n + 1) i)


def sixVertexBetheCollisionSet {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (sixVertexBetheCollision N x q)

@[simp] theorem mem_sixVertexBetheCollisionSet {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) (i : Fin (n + 1)) :
    i ∈ sixVertexBetheCollisionSet N x q ↔
      sixVertexBetheCollision N x q i := by
  simp [sixVertexBetheCollisionSet]



def sixVertexBetheIntervalTupleWeight {n : Nat} (N : Nat) (c : Real)
    (z : Fin (n + 1) -> Complex) (x q : Fin (n + 1) -> Int) : Complex :=
  ∏ i, 
    (if q i = sixVertexBetheShiftCoordinates N x i \/ q i = x i
      then 1 else (c : Complex) ^ 2) * z i ^ q i


def sixVertexBetheCollisionFreeIntervalSum {n : Nat} (N : Nat) (c : Real)
    (z : Fin (n + 1) -> Complex) (x : Fin (n + 1) -> Int) : Complex := by
  classical
  exact ∑ q ∈ (sixVertexBetheCyclicIntervalTuples N x).filter
      (fun q => sixVertexBetheCollisionSet N x q = ∅),
    sixVertexBetheIntervalTupleWeight N c z x q


def sixVertexBetheCollisionConstrainedIntervalSum {n : Nat} (N : Nat)
    (c : Real) (z : Fin (n + 1) -> Complex) (x : Fin (n + 1) -> Int)
    (S : Finset (Fin (n + 1))) : Complex := by
  classical
  exact ∑ q ∈ (sixVertexBetheCyclicIntervalTuples N x).filter
      (fun q => S ⊆ sixVertexBetheCollisionSet N x q),
    sixVertexBetheIntervalTupleWeight N c z x q

private theorem sum_powerset_neg_one (s : Finset (Fin (n + 1))) :
    (∑ t ∈ s.powerset, (-1 : Complex) ^ t.card) =
      if s = ∅ then 1 else 0 := by
  calc
    (∑ t ∈ s.powerset, (-1 : Complex) ^ t.card) =
        ∑ t ∈ s.powerset, ∏ _i ∈ t, (-1 : Complex) := by simp
    _ = ∏ _i ∈ s, (1 + (-1 : Complex)) :=
      (Finset.prod_one_add s).symm
    _ = if s = ∅ then 1 else 0 := by
      by_cases hs : s = ∅
      · simp [hs]
      · rw [if_neg hs]
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        exact Finset.prod_eq_zero hi (by ring)



theorem sixVertexBetheCollisionFreeIntervalSum_inclusionExclusion
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) :
    sixVertexBetheCollisionFreeIntervalSum N c z x =
      ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
        (-1 : Complex) ^ S.card *
          sixVertexBetheCollisionConstrainedIntervalSum N c z x S := by
  classical
  unfold sixVertexBetheCollisionFreeIntervalSum
    sixVertexBetheCollisionConstrainedIntervalSum
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  have hfilter :
      ((Finset.univ : Finset (Fin (n + 1))).powerset.filter
          (fun S => S ⊆ sixVertexBetheCollisionSet N x q)) =
        (sixVertexBetheCollisionSet N x q).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ,
      true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Finset.Subset.trans h (Finset.subset_univ _), h⟩
  rw [hfilter, ← Finset.sum_mul, sum_powerset_neg_one]
  by_cases hfree : sixVertexBetheCollisionSet N x q = ∅ <;>
    simp [hfree]



def SixVertexBetheNoAdjacent {n : Nat}
    (S : Finset (Fin (n + 1))) : Prop :=
  ∀ i, i ∈ S -> finRotate (n + 1) i ∉ S




def sixVertexBetheConstrainedCoordinateSet {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Finset Int := by
  classical
  exact if i ∈ S then {x i}
    else if (finRotate (n + 1)).symm i ∈ S then
      {sixVertexBetheShiftCoordinates N x i}
    else Finset.Icc (sixVertexBetheShiftCoordinates N x i) (x i)

private theorem sixVertexBetheConstrainedTuples_eq_piFinset
    {n : Nat} (N : Nat) (x : Fin (n + 1) -> Int)
    (S : Finset (Fin (n + 1))) (hS : SixVertexBetheNoAdjacent S)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i ≤ x i) :
    (sixVertexBetheCyclicIntervalTuples N x).filter
        (fun q => S ⊆ sixVertexBetheCollisionSet N x q) =
      Fintype.piFinset (sixVertexBetheConstrainedCoordinateSet N x S) := by
  classical
  ext q
  simp only [Finset.mem_filter, mem_sixVertexBetheCyclicIntervalTuples,
    Fintype.mem_piFinset]
  constructor
  · rintro ⟨hq, hcollision⟩ i
    by_cases hi : i ∈ S
    · simp only [sixVertexBetheConstrainedCoordinateSet, hi, if_true,
        Finset.mem_singleton]
      exact (mem_sixVertexBetheCollisionSet N x q i).mp (hcollision hi) |>.1
    · by_cases hpred : (finRotate (n + 1)).symm i ∈ S
      · simp only [sixVertexBetheConstrainedCoordinateSet, hi, if_false,
          hpred, if_true, Finset.mem_singleton]
        have hmem := hcollision hpred
        have hcol := (mem_sixVertexBetheCollisionSet N x q _).mp hmem
        simpa using hcol.2
      · simp only [sixVertexBetheConstrainedCoordinateSet, hi, if_false,
          hpred, Finset.mem_Icc]
        exact hq i
  · intro hq
    constructor
    · intro i
      have hi := hq i
      by_cases his : i ∈ S
      · simp only [sixVertexBetheConstrainedCoordinateSet, his, if_true,
          Finset.mem_singleton] at hi
        rw [hi]
        exact ⟨hgap i, le_rfl⟩
      · by_cases hpred : (finRotate (n + 1)).symm i ∈ S
        · simp only [sixVertexBetheConstrainedCoordinateSet, his, if_false,
            hpred, if_true, Finset.mem_singleton] at hi
          rw [hi]
          exact ⟨le_rfl, hgap i⟩
        · unfold sixVertexBetheConstrainedCoordinateSet at hi
          rw [if_neg his, if_neg hpred] at hi
          simpa using hi
    · intro i hi
      rw [mem_sixVertexBetheCollisionSet]
      constructor
      · have hqi := hq i
        simpa [sixVertexBetheConstrainedCoordinateSet, hi] using hqi
      · have hnext_not : finRotate (n + 1) i ∉ S := hS i hi
        have hqnext := hq (finRotate (n + 1) i)
        simp only [sixVertexBetheConstrainedCoordinateSet, hnext_not,
          if_false] at hqnext
        have hpred :
            (finRotate (n + 1)).symm (finRotate (n + 1) i) ∈ S := by
          simpa using hi
        simp only [hpred, if_true, Finset.mem_singleton] at hqnext
        exact hqnext




theorem sixVertexBethe_geometricInterval_int
    (c : Real) {z : Complex} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    {a b : Int} (hab : a < b) :
    z ^ a + (c : Complex) ^ 2 * (∑ y ∈ Finset.Ioo a b, z ^ y) + z ^ b =
      sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b := by
  let motive : ∀ b : Int, a + 1 ≤ b -> Prop := fun b _ =>
    z ^ a + (c : Complex) ^ 2 * (∑ y ∈ Finset.Ioo a b, z ^ y) + z ^ b =
      sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b
  have hbase : motive (a + 1) le_rfl := by
    dsimp [motive]
    have hempty : Finset.Ioo a (a + 1) = ∅ := by
      rw [Finset.Ioo_add_one_right_eq_Ioc, Finset.Ioc_self]
    rw [hempty]
    simp only [Finset.sum_empty, mul_zero, add_zero]
    rw [zpow_add_one₀ hz0]
    unfold sixVertexBetheL sixVertexBetheM
    field_simp [sub_ne_zero.mpr (Ne.symm hz1)]
    ring
  have hstep : ∀ (b : Int) (hb : a + 1 ≤ b), motive b hb ->
      motive (b + 1) (by omega) := by
    intro b hb ih
    have hab' : a < b := by omega
    dsimp [motive] at ih ⊢
    rw [Finset.Ioo_add_one_right_eq_Ioc,
      ← Finset.Ioo_insert_right hab', Finset.sum_insert]
    · rw [zpow_add_one₀ hz0]
      calc
        z ^ a + (c : Complex) ^ 2 *
              (z ^ b + ∑ x ∈ Finset.Ioo a b, z ^ x) + z ^ b * z =
            (z ^ a + (c : Complex) ^ 2 *
              (∑ x ∈ Finset.Ioo a b, z ^ x) + z ^ b) +
              (c : Complex) ^ 2 * z ^ b - z ^ b + z ^ b * z := by ring
        _ = (sixVertexBetheL c z * z ^ a +
              sixVertexBetheM c z * z ^ b) +
              (c : Complex) ^ 2 * z ^ b - z ^ b + z ^ b * z := by rw [ih]
        _ = sixVertexBetheL c z * z ^ a +
              sixVertexBetheM c z * (z ^ b * z) := by
          unfold sixVertexBetheM
          field_simp [sub_ne_zero.mpr (Ne.symm hz1)]
          ring
    · simp
  exact Int.leInduction hbase hstep b (by omega)


theorem sixVertexBethe_intervalLocalSum
    (c : Real) {z : Complex} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    {a b : Int} (hab : a < b) :
    (∑ y ∈ Finset.Icc a b,
      (if y = a \/ y = b then 1 else (c : Complex) ^ 2) * z ^ y) =
      sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b := by
  have hIcc : Finset.Icc a b =
      insert a (insert b (Finset.Ioo a b)) := by
    ext y
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hIcc, Finset.sum_insert, Finset.sum_insert]
  · simp only [true_or, if_true, or_true]
    have hinter :
        (∑ y ∈ Finset.Ioo a b,
          (if y = a \/ y = b then 1 else (c : Complex) ^ 2) * z ^ y) =
          (c : Complex) ^ 2 * ∑ y ∈ Finset.Ioo a b, z ^ y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have hy' := Finset.mem_Ioo.mp hy
      rw [if_neg (by omega)]
    rw [hinter]
    convert sixVertexBethe_geometricInterval_int c hz0 hz1 hab using 1 <;> ring
  · simp
  · simp only [Finset.mem_insert, Finset.mem_Ioo, not_or]
    exact ⟨hab.ne, by omega⟩



theorem sixVertexBetheCollisionConstrainedIntervalSum_eq_prod
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hS : SixVertexBetheNoAdjacent S)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i ≤ x i) :
    sixVertexBetheCollisionConstrainedIntervalSum N c z x S =
      ∏ i, ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i,
        (if y = sixVertexBetheShiftCoordinates N x i \/ y = x i
          then 1 else (c : Complex) ^ 2) * z i ^ y := by
  classical
  unfold sixVertexBetheCollisionConstrainedIntervalSum
    sixVertexBetheIntervalTupleWeight
  rw [sixVertexBetheConstrainedTuples_eq_piFinset N x S hS hgap]
  exact (Finset.prod_univ_sum
    (sixVertexBetheConstrainedCoordinateSet N x S)
    (fun i y =>
      (if y = sixVertexBetheShiftCoordinates N x i \/ y = x i
        then 1 else (c : Complex) ^ 2) * z i ^ y)).symm



theorem sixVertexBetheCollisionConstrainedIntervalSum_eq_LMprod
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hS : SixVertexBetheNoAdjacent S)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i, z i ≠ 1) :
    sixVertexBetheCollisionConstrainedIntervalSum N c z x S =
      ∏ i, if i ∈ S then z i ^ x i
        else if (finRotate (n + 1)).symm i ∈ S then
          z i ^ (sixVertexBetheShiftCoordinates N x i)
        else
          sixVertexBetheL c (z i) *
              z i ^ (sixVertexBetheShiftCoordinates N x i) +
            sixVertexBetheM c (z i) * z i ^ x i := by
  rw [sixVertexBetheCollisionConstrainedIntervalSum_eq_prod N c z x S hS
    (fun i => (hgap i).le)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [sixVertexBetheConstrainedCoordinateSet, hi]
  · by_cases hpred : (finRotate (n + 1)).symm i ∈ S
    · have hpred' : i - 1 ∈ S := by simpa using hpred
      simp [sixVertexBetheConstrainedCoordinateSet, hi, hpred']
    · simp only [sixVertexBetheConstrainedCoordinateSet, hi, if_false,
        hpred]
      exact sixVertexBethe_intervalLocalSum c (hz0 i) (hz1 i) (hgap i)

private theorem sixVertexBetheCollisionConstrainedIntervalSum_eq_zero
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hS : ¬ SixVertexBetheNoAdjacent S) :
    sixVertexBetheCollisionConstrainedIntervalSum N c z x S = 0 := by
  classical
  simp only [SixVertexBetheNoAdjacent, not_forall] at hS
  obtain ⟨i, hi⟩ := hS
  simp only [Classical.not_imp, not_not] at hi
  unfold sixVertexBetheCollisionConstrainedIntervalSum
  apply Finset.sum_eq_zero
  intro q hq
  have hsubset := (Finset.mem_filter.mp hq).2
  have hcoli := (mem_sixVertexBetheCollisionSet N x q i).mp
    (hsubset hi.1)
  have hcolnext := (mem_sixVertexBetheCollisionSet N x q
    (finRotate (n + 1) i)).mp (hsubset hi.2)
  exfalso
  exact (hgap (finRotate (n + 1) i)).ne
    (hcoli.2.symm.trans hcolnext.1)



def sixVertexBetheIELowerCoefficient {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if (finRotate (n + 1)).symm i ∈ S then 1
  else if i ∈ S then 0 else sixVertexBetheL c (z i)



def sixVertexBetheIEUpperCoefficient {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if i ∈ S then 1
  else if (finRotate (n + 1)).symm i ∈ S then 0
  else sixVertexBetheM c (z i)



def sixVertexBetheRawIEWordCoefficient {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w : Finset (Fin (n + 1))) : Complex := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset.filter
      SixVertexBetheNoAdjacent,
    (-1 : Complex) ^ S.card *
      ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w),
          sixVertexBetheIEUpperCoefficient c z S i)

private theorem sixVertexBetheConstrainedLocal_eq_IE
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hS : SixVertexBetheNoAdjacent S) (i : Fin (n + 1)) :
    (if i ∈ S then z i ^ x i
      else if (finRotate (n + 1)).symm i ∈ S then
        z i ^ (sixVertexBetheShiftCoordinates N x i)
      else sixVertexBetheL c (z i) *
          z i ^ (sixVertexBetheShiftCoordinates N x i) +
        sixVertexBetheM c (z i) * z i ^ x i) =
      sixVertexBetheIELowerCoefficient c z S i *
          z i ^ (sixVertexBetheShiftCoordinates N x i) +
        sixVertexBetheIEUpperCoefficient c z S i * z i ^ x i := by
  by_cases hi : i ∈ S
  · have hpred : (finRotate (n + 1)).symm i ∉ S := by
      intro hpred
      apply hS ((finRotate (n + 1)).symm i) hpred
      simpa using hi
    have hpred' : i - 1 ∉ S := by simpa using hpred
    simp [sixVertexBetheIELowerCoefficient,
      sixVertexBetheIEUpperCoefficient, hi, hpred']
  · by_cases hpred : (finRotate (n + 1)).symm i ∈ S
    · have hpred' : i - 1 ∈ S := by simpa using hpred
      simp [sixVertexBetheIELowerCoefficient,
        sixVertexBetheIEUpperCoefficient, hi, hpred']
    · have hpred' : i - 1 ∉ S := by simpa using hpred
      simp [sixVertexBetheIELowerCoefficient,
        sixVertexBetheIEUpperCoefficient, hi, hpred']




theorem sixVertexBetheCollisionFreeIntervalSum_eq_rawWords
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i, z i ≠ 1) :
    sixVertexBetheCollisionFreeIntervalSum N c z x =
      ∑ w ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
        sixVertexBetheRawIEWordCoefficient c z w *
          ((∏ i ∈ w,
              z i ^ (sixVertexBetheShiftCoordinates N x i)) *
            ∏ i ∈ (Finset.univ \ w), z i ^ x i) := by
  classical
  rw [sixVertexBetheCollisionFreeIntervalSum_inclusionExclusion]
  let P := (Finset.univ : Finset (Fin (n + 1))).powerset
  let Q := P.filter SixVertexBetheNoAdjacent
  calc
    (∑ S ∈ P, (-1 : Complex) ^ S.card *
        sixVertexBetheCollisionConstrainedIntervalSum N c z x S) =
      ∑ S ∈ Q, (-1 : Complex) ^ S.card *
        sixVertexBetheCollisionConstrainedIntervalSum N c z x S := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro S hSP hSQ
        have hnmem : S ∉ Q := hSQ
        have hnS : ¬ SixVertexBetheNoAdjacent S := by
          simpa [Q, hSP] using hnmem
        rw [sixVertexBetheCollisionConstrainedIntervalSum_eq_zero
          N c z x S hgap hnS, mul_zero]
    _ = ∑ S ∈ Q, (-1 : Complex) ^ S.card *
        ∏ i, (sixVertexBetheIELowerCoefficient c z S i *
              z i ^ (sixVertexBetheShiftCoordinates N x i) +
            sixVertexBetheIEUpperCoefficient c z S i * z i ^ x i) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hno : SixVertexBetheNoAdjacent S := by
        exact (Finset.mem_filter.mp hS).2
      rw [sixVertexBetheCollisionConstrainedIntervalSum_eq_LMprod
        N c z x S hno hgap hz0 hz1]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact sixVertexBetheConstrainedLocal_eq_IE N c z x S hno i
    _ = ∑ w ∈ P,
        sixVertexBetheRawIEWordCoefficient c z w *
          ((∏ i ∈ w,
              z i ^ (sixVertexBetheShiftCoordinates N x i)) *
            ∏ i ∈ (Finset.univ \ w), z i ^ x i) := by
      simp_rw [Finset.prod_add, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      unfold sixVertexBetheRawIEWordCoefficient
      change (∑ S ∈ Q,
          (-1 : Complex) ^ S.card *
            ((∏ i ∈ w,
                sixVertexBetheIELowerCoefficient c z S i *
                  z i ^ (sixVertexBetheShiftCoordinates N x i)) *
              ∏ i ∈ (Finset.univ \ w),
                sixVertexBetheIEUpperCoefficient c z S i * z i ^ x i)) =
        (∑ S ∈ Q, (-1 : Complex) ^ S.card *
            ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
              ∏ i ∈ (Finset.univ \ w),
                sixVertexBetheIEUpperCoefficient c z S i)) *
          ((∏ i ∈ w,
              z i ^ (sixVertexBetheShiftCoordinates N x i)) *
            ∏ i ∈ (Finset.univ \ w), z i ^ x i)
      calc
        (∑ S ∈ Q,
            (-1 : Complex) ^ S.card *
              ((∏ i ∈ w,
                  sixVertexBetheIELowerCoefficient c z S i *
                    z i ^ (sixVertexBetheShiftCoordinates N x i)) *
                ∏ i ∈ (Finset.univ \ w),
                  sixVertexBetheIEUpperCoefficient c z S i * z i ^ x i)) =
          ∑ S ∈ Q,
            (((-1 : Complex) ^ S.card *
              ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
                ∏ i ∈ (Finset.univ \ w),
                  sixVertexBetheIEUpperCoefficient c z S i)) *
              ((∏ i ∈ w,
                  z i ^ (sixVertexBetheShiftCoordinates N x i)) *
                ∏ i ∈ (Finset.univ \ w), z i ^ x i)) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
            ring
        _ = _ := by rw [Finset.sum_mul]

private theorem sum_powerset_neg_one_mul_complement_prod
    {α : Type} [Fintype α] [DecidableEq α]
    (T : Finset α) (b : α -> Complex) :
    (∑ S ∈ T.powerset, (-1 : Complex) ^ S.card *
      ∏ i, if i ∈ S then 1 else b i) =
    ∏ i, if i ∈ T then b i - 1 else b i := by
  have hcomp (S : Finset α) (hS : S ⊆ T) :
      (Finset.univ \ S) = (T \ S) ∪ (Finset.univ \ T) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union]
    tauto
  calc
    (∑ S ∈ T.powerset, (-1 : Complex) ^ S.card *
      ∏ i, if i ∈ S then 1 else b i) =
      ∑ S ∈ T.powerset,
        ((-1 : Complex) ^ S.card * ∏ i ∈ T \ S, b i) *
          ∏ i ∈ Finset.univ \ T, b i := by
      apply Finset.sum_congr rfl
      intro S hS
      have hST : S ⊆ T := Finset.mem_powerset.mp hS
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, one_mul]
      have hfilter : (Finset.univ.filter fun i => i ∉ S) =
          Finset.univ \ S := by
        ext i
        simp
      rw [hfilter, hcomp S hST, Finset.prod_union]
      · ring
      · rw [Finset.disjoint_left]
        intro i hiT hiU
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hiT hiU
        exact hiU hiT.1
    _ = (∑ S ∈ T.powerset,
        (-1 : Complex) ^ S.card * ∏ i ∈ T \ S, b i) *
          ∏ i ∈ Finset.univ \ T, b i := by rw [Finset.sum_mul]
    _ = (∏ i ∈ T, (b i - 1)) *
          ∏ i ∈ Finset.univ \ T, b i := by
      rw [Finset.prod_sub]
      simp only [Finset.prod_const_one, mul_one]
    _ = ∏ i, if i ∈ T then b i - 1 else b i := by
      rw [Finset.prod_ite]
      congr 2 <;> ext i <;> simp


def sixVertexBetheWordMLSet {n : Nat}
    (w : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => i ∉ w ∧ finRotate (n + 1) i ∈ w

@[simp] theorem mem_sixVertexBetheWordMLSet {n : Nat}
    (w : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    i ∈ sixVertexBetheWordMLSet w ↔
      i ∉ w ∧ finRotate (n + 1) i ∈ w := by
  simp [sixVertexBetheWordMLSet]

theorem sixVertexBetheWordMLSet_noAdjacent {n : Nat}
    (w : Finset (Fin (n + 1))) :
    SixVertexBetheNoAdjacent (sixVertexBetheWordMLSet w) := by
  intro i hi hinext
  have hi' := (mem_sixVertexBetheWordMLSet w i).mp hi
  have hn' := (mem_sixVertexBetheWordMLSet w
    (finRotate (n + 1) i)).mp hinext
  exact hn'.1 hi'.2



def sixVertexBetheWordEdgeBase {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if i ∈ w then
    if finRotate (n + 1) i ∈ w then
      sixVertexBetheL c (z (finRotate (n + 1) i))
    else 1
  else if finRotate (n + 1) i ∈ w then
    sixVertexBetheM c (z i) *
      sixVertexBetheL c (z (finRotate (n + 1) i))
  else sixVertexBetheM c (z i)

private theorem sixVertexBetheWordCoefficient_eq_edgeBase_sub
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w : Finset (Fin (n + 1))) :
    sixVertexBetheWordCoefficient c z (Equiv.refl _) w =
      ∏ i, if i ∈ sixVertexBetheWordMLSet w then
        sixVertexBetheWordEdgeBase c z w i - 1
      else sixVertexBetheWordEdgeBase c z w i := by
  unfold sixVertexBetheWordCoefficient
  apply Finset.prod_congr rfl
  intro i _
  unfold sixVertexBetheWordEdgeFactor sixVertexBetheWordEdgeBase
  by_cases hi : i ∈ w
  · by_cases hn : finRotate (n + 1) i ∈ w
    · have hn' : i + 1 ∈ w := by simpa using hn
      simp [hi, hn']
    · have hn' : i + 1 ∉ w := by simpa using hn
      simp [hi, hn']
  · by_cases hn : finRotate (n + 1) i ∈ w
    · have hn' : i + 1 ∈ w := by simpa using hn
      simp [hi, hn']
    · have hn' : i + 1 ∉ w := by simpa using hn
      simp [hi, hn']

private def sixVertexBetheIEMPart {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if i ∈ w then 1 else if i ∈ S then 1 else sixVertexBetheM c (z i)

private def sixVertexBetheIEPrevLPart {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if i ∈ w then
    if (finRotate (n + 1)).symm i ∈ S then 1
    else sixVertexBetheL c (z i)
  else 1

private def sixVertexBetheIENextLPart {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if finRotate (n + 1) i ∈ w then
    if i ∈ S then 1
    else sixVertexBetheL c (z (finRotate (n + 1) i))
  else 1

private theorem sixVertexBetheIESlotFactor_eq_parts
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1)))
    (hST : S ⊆ sixVertexBetheWordMLSet w) (i : Fin (n + 1)) :
    (if i ∈ w then sixVertexBetheIELowerCoefficient c z S i
      else sixVertexBetheIEUpperCoefficient c z S i) =
      sixVertexBetheIEMPart c z w S i *
        sixVertexBetheIEPrevLPart c z w S i := by
  by_cases hi : i ∈ w
  · have hiS : i ∉ S := by
      intro hiS
      exact ((mem_sixVertexBetheWordMLSet w i).mp (hST hiS)).1 hi
    simp [sixVertexBetheIELowerCoefficient, sixVertexBetheIEMPart,
      sixVertexBetheIEPrevLPart, hi, hiS]
  · have hpred : (finRotate (n + 1)).symm i ∉ S := by
      intro hpred
      have hml := (mem_sixVertexBetheWordMLSet w _).mp (hST hpred)
      exact hi (by simpa using hml.2)
    have hpred' : i - 1 ∉ S := by simpa using hpred
    simp [sixVertexBetheIEUpperCoefficient, sixVertexBetheIEMPart,
      sixVertexBetheIEPrevLPart, hi, hpred']

private theorem sixVertexBetheIEPrevLPart_prod_eq_next
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1))) :
    (∏ i, sixVertexBetheIEPrevLPart c z w S i) =
      ∏ i, sixVertexBetheIENextLPart c z w S i := by
  calc
    (∏ i, sixVertexBetheIEPrevLPart c z w S i) =
        ∏ i, sixVertexBetheIEPrevLPart c z w S
          (finRotate (n + 1) i) :=
      (Equiv.prod_comp (finRotate (n + 1))
        (sixVertexBetheIEPrevLPart c z w S)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      unfold sixVertexBetheIEPrevLPart sixVertexBetheIENextLPart
      simp

private theorem sixVertexBetheIEEdgeFactor_eq_base
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1)))
    (hST : S ⊆ sixVertexBetheWordMLSet w) (i : Fin (n + 1)) :
    sixVertexBetheIEMPart c z w S i *
        sixVertexBetheIENextLPart c z w S i =
      if i ∈ S then 1 else sixVertexBetheWordEdgeBase c z w i := by
  by_cases hiS : i ∈ S
  · have hml := (mem_sixVertexBetheWordMLSet w i).mp (hST hiS)
    have hn' : i + 1 ∈ w := by simpa using hml.2
    simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
      hiS, hml.1, hn']
  · by_cases hi : i ∈ w
    · by_cases hn : finRotate (n + 1) i ∈ w
      · have hn' : i + 1 ∈ w := by simpa using hn
        simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
          sixVertexBetheWordEdgeBase, hiS, hi, hn']
      · have hn' : i + 1 ∉ w := by simpa using hn
        simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
          sixVertexBetheWordEdgeBase, hiS, hi, hn']
    · by_cases hn : finRotate (n + 1) i ∈ w
      · have hn' : i + 1 ∈ w := by simpa using hn
        simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
          sixVertexBetheWordEdgeBase, hiS, hi, hn']
      · have hn' : i + 1 ∉ w := by simpa using hn
        simp [sixVertexBetheIEMPart, sixVertexBetheIENextLPart,
          sixVertexBetheWordEdgeBase, hiS, hi, hn']

private theorem sixVertexBetheIESlotProduct_eq_edgeBase
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1)))
    (hST : S ⊆ sixVertexBetheWordMLSet w) :
    ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
      ∏ i ∈ (Finset.univ \ w), sixVertexBetheIEUpperCoefficient c z S i) =
      ∏ i, if i ∈ S then 1 else sixVertexBetheWordEdgeBase c z w i := by
  calc
    ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w), sixVertexBetheIEUpperCoefficient c z S i) =
      ∏ i, if i ∈ w then sixVertexBetheIELowerCoefficient c z S i
        else sixVertexBetheIEUpperCoefficient c z S i := by
          rw [Finset.prod_ite]
          congr 2 <;> ext i <;> simp
    _ =
      ∏ i, (sixVertexBetheIEMPart c z w S i *
        sixVertexBetheIEPrevLPart c z w S i) := by
          apply Finset.prod_congr rfl
          intro i _
          exact sixVertexBetheIESlotFactor_eq_parts c z w S hST i
    _ = (∏ i, sixVertexBetheIEMPart c z w S i) *
        ∏ i, sixVertexBetheIEPrevLPart c z w S i :=
      Finset.prod_mul_distrib
        (f := sixVertexBetheIEMPart c z w S)
        (g := sixVertexBetheIEPrevLPart c z w S)
    _ = (∏ i, sixVertexBetheIEMPart c z w S i) *
        ∏ i, sixVertexBetheIENextLPart c z w S i := by
      rw [sixVertexBetheIEPrevLPart_prod_eq_next]
    _ = ∏ i, (sixVertexBetheIEMPart c z w S i *
        sixVertexBetheIENextLPart c z w S i) :=
      Finset.prod_mul_distrib.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact sixVertexBetheIEEdgeFactor_eq_base c z w S hST i

private theorem sixVertexBetheIESlotProduct_eq_zero_of_not_subset
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w S : Finset (Fin (n + 1))) (hS : SixVertexBetheNoAdjacent S)
    (hnot : ¬ S ⊆ sixVertexBetheWordMLSet w) :
    ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
      ∏ i ∈ (Finset.univ \ w),
        sixVertexBetheIEUpperCoefficient c z S i) = 0 := by
  obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hnot
  by_cases hiw : i ∈ w
  · have hpred : (finRotate (n + 1)).symm i ∉ S := by
      intro hpred
      apply hS ((finRotate (n + 1)).symm i) hpred
      simpa using hiS
    have hpred' : i - 1 ∉ S := by simpa using hpred
    have hzero : sixVertexBetheIELowerCoefficient c z S i = 0 := by
      simp [sixVertexBetheIELowerCoefficient, hiS, hpred']
    rw [Finset.prod_eq_zero hiw hzero, zero_mul]
  · have hnext : finRotate (n + 1) i ∉ w := by
      intro hnext
      exact hiT ((mem_sixVertexBetheWordMLSet w i).mpr ⟨hiw, hnext⟩)
    let j := finRotate (n + 1) i
    have hnext' : i + 1 ∉ w := by simpa using hnext
    have hjcomp : j ∈ (Finset.univ \ w) := by
      simp [j, hnext']
    have hjS : j ∉ S := hS i hiS
    have hpred : (finRotate (n + 1)).symm j ∈ S := by
      simpa [j] using hiS
    have hpred' : j - 1 ∈ S := by simpa using hpred
    have hzero : sixVertexBetheIEUpperCoefficient c z S j = 0 := by
      simp [sixVertexBetheIEUpperCoefficient, hjS, hpred']
    rw [Finset.prod_eq_zero hjcomp hzero, mul_zero]



theorem sixVertexBetheRawIEWordCoefficient_eq_wordCoefficient
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w : Finset (Fin (n + 1))) :
    sixVertexBetheRawIEWordCoefficient c z w =
      sixVertexBetheWordCoefficient c z (Equiv.refl _) w := by
  classical
  let T := sixVertexBetheWordMLSet w
  let P := (Finset.univ : Finset (Fin (n + 1))).powerset
  let Q := P.filter SixVertexBetheNoAdjacent
  have hTno : SixVertexBetheNoAdjacent T :=
    sixVertexBetheWordMLSet_noAdjacent w
  have hTPQ : T.powerset ⊆ Q := by
    intro S hS
    have hST : S ⊆ T := Finset.mem_powerset.mp hS
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr (Finset.Subset.trans hST (Finset.subset_univ _))
    · intro i hiS hinext
      exact hTno i (hST hiS) (hST hinext)
  unfold sixVertexBetheRawIEWordCoefficient
  change (∑ S ∈ Q, (-1 : Complex) ^ S.card *
      ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w),
          sixVertexBetheIEUpperCoefficient c z S i)) = _
  calc
    (∑ S ∈ Q, (-1 : Complex) ^ S.card *
      ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w),
          sixVertexBetheIEUpperCoefficient c z S i)) =
      ∑ S ∈ T.powerset, (-1 : Complex) ^ S.card *
      ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w),
          sixVertexBetheIEUpperCoefficient c z S i) := by
      symm
      apply Finset.sum_subset hTPQ
      intro S hSQ hST
      have hno : SixVertexBetheNoAdjacent S :=
        (Finset.mem_filter.mp hSQ).2
      have hnsub : ¬ S ⊆ T := by
        intro hsub
        exact hST (Finset.mem_powerset.mpr hsub)
      rw [sixVertexBetheIESlotProduct_eq_zero_of_not_subset
        c z w S hno hnsub, mul_zero]
    _ = ∑ S ∈ T.powerset, (-1 : Complex) ^ S.card *
        ∏ i, if i ∈ S then 1 else sixVertexBetheWordEdgeBase c z w i := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [sixVertexBetheIESlotProduct_eq_edgeBase]
      exact Finset.mem_powerset.mp hS
    _ = ∏ i, if i ∈ T then sixVertexBetheWordEdgeBase c z w i - 1
        else sixVertexBetheWordEdgeBase c z w i :=
      sum_powerset_neg_one_mul_complement_prod T
        (sixVertexBetheWordEdgeBase c z w)
    _ = _ := by
      rw [sixVertexBetheWordCoefficient_eq_edgeBase_sub]

private theorem sixVertexBetheWordMonomial_refl_eq_endpoints
    {n : Nat} (N : Nat) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (w : Finset (Fin (n + 1))) :
    sixVertexBetheWordMonomial N z (Equiv.refl _) x w =
      ((∏ i ∈ w, z i ^ (sixVertexBetheShiftCoordinates N x i)) *
        ∏ i ∈ (Finset.univ \ w), z i ^ x i) := by
  unfold sixVertexBetheWordMonomial
  rw [Finset.prod_ite]
  congr 2 <;> ext i <;> simp



theorem sixVertexBetheCollisionFreeIntervalSum_eq_words
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i, z i ≠ 1) :
    sixVertexBetheCollisionFreeIntervalSum N c z x =
      ∑ w : Finset (Fin (n + 1)),
        sixVertexBetheWordCoefficient c z (Equiv.refl _) w *
          sixVertexBetheWordMonomial N z (Equiv.refl _) x w := by
  rw [sixVertexBetheCollisionFreeIntervalSum_eq_rawWords
    N c z x hgap hz0 hz1, Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro w _
  rw [sixVertexBetheRawIEWordCoefficient_eq_wordCoefficient,
    sixVertexBetheWordMonomial_refl_eq_endpoints]

private theorem sixVertexBetheCollisionFreeTuple_strictMono
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) :
    StrictMono q := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  let a : Fin (n + 1) := i.castSucc
  let b : Fin (n + 1) := i.succ
  have hab : finRotate (n + 1) a = b := by
    apply Fin.ext
    simp [a, b]
  have hqa := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq a
  have hqb := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq b
  have hshift : sixVertexBetheShiftCoordinates N
      (sixVertexSectorIntCoordinates x) b =
      sixVertexSectorIntCoordinates x a := by
    simp [a, b, sixVertexBetheShiftCoordinates]
  have hle : q a ≤ q b := hqa.2.trans (hshift ▸ hqb.1)
  apply lt_of_le_of_ne hle
  intro heq
  have hqa_eq : q a = sixVertexSectorIntCoordinates x a :=
    le_antisymm hqa.2 ((hshift ▸ hqb.1).trans heq.ge)
  have hqb_eq : q b = sixVertexBetheShiftCoordinates N
      (sixVertexSectorIntCoordinates x) b :=
    le_antisymm (heq.ge.trans (hshift ▸ hqa.2)) hqb.1
  have hmem : a ∈ sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q := by
    rw [mem_sixVertexBetheCollisionSet]
    exact ⟨hqa_eq, by simpa [hab] using hqb_eq⟩
  rw [hfree] at hmem
  simp at hmem

private theorem sixVertexBetheCollisionFreeTuple_wrap_lt
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) :
    q (Fin.last n) < q 0 + N := by
  have hlast := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq
    (Fin.last n)
  have hzero := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq 0
  have hle : q (Fin.last n) ≤ q 0 + N := by
    have ha : sixVertexSectorIntCoordinates x (Fin.last n) - N ≤ q 0 := by
      simpa [sixVertexBetheShiftCoordinates] using hzero.1
    omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hlast_eq : q (Fin.last n) = sixVertexSectorIntCoordinates x
        (Fin.last n) := by
      have ha : sixVertexSectorIntCoordinates x (Fin.last n) - N ≤ q 0 := by
        simpa [sixVertexBetheShiftCoordinates] using hzero.1
      apply le_antisymm hlast.2
      omega
    have hzero_eq : q 0 = sixVertexBetheShiftCoordinates N
        (sixVertexSectorIntCoordinates x) 0 := by
      apply le_antisymm
      · have := hlast.2
        simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero]
        omega
      · exact hzero.1
    have hmem : Fin.last n ∈ sixVertexBetheCollisionSet N
        (sixVertexSectorIntCoordinates x) q := by
      rw [mem_sixVertexBetheCollisionSet]
      constructor
      · exact hlast_eq
      · simpa [sixVertexBetheShiftCoordinates] using hzero_eq
    rw [hfree] at hmem
    simp at hmem

private theorem sixVertexBetheTuple_nonnegative
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x)) (hq0 : 0 ≤ q 0) :
    ∀ i, 0 ≤ q i := by
  intro i
  induction i using Fin.cases with
  | zero => exact hq0
  | succ i =>
      have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
      have hx : 0 ≤ sixVertexSectorIntCoordinates x i.castSucc := by
        simp [sixVertexSectorIntCoordinates]
      simpa [sixVertexBetheShiftCoordinates] using hx.trans hi.1


noncomputable def sixVertexBetheDirectTupleEmbedding
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    Fin (n + 1) ↪o Fin N := by
  have hnonneg := sixVertexBetheTuple_nonnegative x q hq hq0
  let f : Fin (n + 1) -> Fin N := fun i =>
    ⟨(q i).toNat, by
      rw [Int.toNat_lt (hnonneg i)]
      have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i
      have hxlt : sixVertexSectorIntCoordinates x i < (N : Int) := by
        unfold sixVertexSectorIntCoordinates
        exact_mod_cast (sixVertexSectorPosition x i).prop
      exact hi.2.trans_lt hxlt⟩
  refine OrderEmbedding.ofStrictMono f ?_
  intro i j hij
  have hqij := sixVertexBetheCollisionFreeTuple_strictMono x q hq hfree hij
  change (q i).toNat < (q j).toNat
  rw [← Int.ofNat_lt]
  simpa [Int.toNat_of_nonneg (hnonneg i), Int.toNat_of_nonneg (hnonneg j)]
    using hqij



noncomputable def sixVertexBetheDirectTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    SixVertexSector N (n + 1) :=
  Set.powersetCard.ofFinEmbEquiv
    (sixVertexBetheDirectTupleEmbedding x q hq hfree hq0)

@[simp] private theorem sixVertexSectorPosition_directTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    sixVertexSectorPosition
      (sixVertexBetheDirectTupleSector x q hq hfree hq0) =
      sixVertexBetheDirectTupleEmbedding x q hq hfree hq0 := by
  change Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv
      (sixVertexBetheDirectTupleEmbedding x q hq hfree hq0)) = _
  exact Equiv.symm_apply_apply _ _

private theorem sixVertexSectorIntCoordinates_directTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    sixVertexSectorIntCoordinates
      (sixVertexBetheDirectTupleSector x q hq hfree hq0) = q := by
  funext i
  unfold sixVertexSectorIntCoordinates
  rw [sixVertexSectorPosition_directTupleSector]
  change ((q i).toNat : Int) = q i
  exact Int.toNat_of_nonneg
    (sixVertexBetheTuple_nonnegative x q hq hq0 i)

private theorem sixVertexBetheDirectTupleSector_forward
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    SixVertexForwardInterlaced
      (sixVertexSectorRow (sixVertexBetheDirectTupleSector x q hq hfree hq0))
      (sixVertexSectorRow x) := by
  apply sixVertexForwardInterlaced_of_positions
  constructor
  · intro i
    have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i
    have hcoord := congrFun
      (sixVertexSectorIntCoordinates_directTupleSector x q hq hfree hq0) i
    have hle : ((sixVertexSectorPosition
        (sixVertexBetheDirectTupleSector x q hq hfree hq0) i).val : Int) ≤
        (sixVertexSectorPosition x i).val := by
      simpa [sixVertexSectorIntCoordinates] using hcoord.le.trans hi.2
    exact_mod_cast hle
  · intro k hk
    let i : Fin n := ⟨k, by omega⟩
    have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
    have hshift : sixVertexBetheShiftCoordinates N
        (sixVertexSectorIntCoordinates x) i.succ =
        sixVertexSectorIntCoordinates x i.castSucc := by
      simp [sixVertexBetheShiftCoordinates]
    have hcoord := congrFun
      (sixVertexSectorIntCoordinates_directTupleSector x q hq hfree hq0) i.succ
    have hcoord' : ((sixVertexSectorPosition
        (sixVertexBetheDirectTupleSector x q hq hfree hq0) i.succ).val : Int) =
        q i.succ := by
      simpa only [sixVertexSectorIntCoordinates] using hcoord
    have hle : ((sixVertexSectorPosition x i.castSucc).val : Int) ≤
        (sixVertexSectorPosition
          (sixVertexBetheDirectTupleSector x q hq hfree hq0) i.succ).val := by
      have hbase : sixVertexSectorIntCoordinates x i.castSucc ≤ q i.succ :=
        hshift ▸ hi.1
      simpa only [sixVertexSectorIntCoordinates] using hbase.trans hcoord'.ge
    exact_mod_cast hle

private theorem sixVertexForwardTuple_mem
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    sixVertexSectorIntCoordinates y ∈
      sixVertexBetheCyclicIntervalTuples N
        (sixVertexSectorIntCoordinates x) := by
  rw [mem_sixVertexBetheCyclicIntervalTuples]
  have hpos := (sixVertexForwardInterlaced_iff_positions y x).mp hyx
  intro i
  constructor
  · induction i using Fin.cases with
    | zero =>
        simp only [sixVertexBetheShiftCoordinates, sixVertexSectorIntCoordinates,
          Fin.cases_zero]
        have hxlast := (sixVertexSectorPosition x (Fin.last n)).prop
        have hyzero : 0 ≤ (sixVertexSectorPosition y 0).val := Nat.zero_le _
        omega
    | succ i =>
        simp only [sixVertexBetheShiftCoordinates, sixVertexSectorIntCoordinates,
          Fin.cases_succ]
        exact_mod_cast hpos.2 i.val (by omega)
  · unfold sixVertexSectorIntCoordinates
    exact_mod_cast hpos.1 i

private theorem sixVertexForwardTuple_collisionFree
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    sixVertexBetheCollisionSet N (sixVertexSectorIntCoordinates x)
      (sixVertexSectorIntCoordinates y) = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨i, hi⟩
  have hcol := (mem_sixVertexBetheCollisionSet N _ _ i).mp hi
  induction i using Fin.lastCases with
  | last =>
      have hrot : finRotate (n + 1) (Fin.last n) = 0 := by
        apply Fin.ext
        simp
      have hyzero : 0 ≤ sixVertexSectorIntCoordinates y 0 := by
        simp [sixVertexSectorIntCoordinates]
      have hxlast : sixVertexSectorIntCoordinates x (Fin.last n) < N := by
        unfold sixVertexSectorIntCoordinates
        exact_mod_cast (sixVertexSectorPosition x (Fin.last n)).prop
      have hthis := hcol.2
      rw [hrot] at hthis
      simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at hthis
      omega
  | cast i =>
      have hnext : finRotate (n + 1) i.castSucc = i.succ := by
        apply Fin.ext
        simp
      have hystrict := (sixVertexSectorPosition y).strictMono
        (Fin.castSucc_lt_succ (i := i))
      have heq : sixVertexSectorIntCoordinates y i.castSucc =
          sixVertexSectorIntCoordinates y i.succ := by
        calc
          _ = sixVertexSectorIntCoordinates x i.castSucc := hcol.1
          _ = sixVertexBetheShiftCoordinates N
              (sixVertexSectorIntCoordinates x) i.succ := by
                simp [sixVertexBetheShiftCoordinates]
          _ = sixVertexSectorIntCoordinates y i.succ := by
                simpa [hnext] using hcol.2.symm
      have hystrictInt : sixVertexSectorIntCoordinates y i.castSucc <
          sixVertexSectorIntCoordinates y i.succ := by
        unfold sixVertexSectorIntCoordinates
        exact_mod_cast hystrict
      exact hystrictInt.ne heq

private theorem sixVertexDirectTupleSector_forwardTuple
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    sixVertexBetheDirectTupleSector x (sixVertexSectorIntCoordinates y)
      (sixVertexForwardTuple_mem x y hyx)
      (sixVertexForwardTuple_collisionFree x y hyx)
      (by simp [sixVertexSectorIntCoordinates]) = y := by
  apply (Set.powersetCard.ofFinEmbEquiv
    (n := n + 1) (I := Fin N)).symm.injective
  change sixVertexSectorPosition _ = sixVertexSectorPosition y
  rw [sixVertexSectorPosition_directTupleSector]
  ext i
  change (sixVertexSectorIntCoordinates y i).toNat =
    (sixVertexSectorPosition y i).val
  simp [sixVertexSectorIntCoordinates]



def sixVertexBetheUnshiftCoordinates {n : Nat} (N : Nat)
    (q : Fin (n + 1) -> Int) : Fin (n + 1) -> Int :=
  Fin.lastCases (q 0 + N) (fun i => q i.succ)

@[simp] theorem sixVertexBetheShiftCoordinates_unshift
    {n : Nat} (N : Nat) (q : Fin (n + 1) -> Int) :
    sixVertexBetheShiftCoordinates N
      (sixVertexBetheUnshiftCoordinates N q) = q := by
  funext i
  induction i using Fin.cases with
  | zero => simp [sixVertexBetheShiftCoordinates,
      sixVertexBetheUnshiftCoordinates]
  | succ i => simp [sixVertexBetheShiftCoordinates,
      sixVertexBetheUnshiftCoordinates]

@[simp] theorem sixVertexBetheUnshiftCoordinates_shift
    {n : Nat} (N : Nat) (r : Fin (n + 1) -> Int) :
    sixVertexBetheUnshiftCoordinates N
      (sixVertexBetheShiftCoordinates N r) = r := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [sixVertexBetheUnshiftCoordinates,
      sixVertexBetheShiftCoordinates]
  | cast i => simp [sixVertexBetheUnshiftCoordinates,
      sixVertexBetheShiftCoordinates]

private theorem sixVertexBetheUnshiftCoordinates_nonnegative
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x)) :
    ∀ i, 0 ≤ sixVertexBetheUnshiftCoordinates N q i := by
  intro i
  induction i using Fin.lastCases with
  | last =>
      have hq0 := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq 0
      have hxlast : 0 ≤ sixVertexSectorIntCoordinates x (Fin.last n) := by
        simp [sixVertexSectorIntCoordinates]
      simp only [sixVertexBetheUnshiftCoordinates, Fin.lastCases_last]
      have : sixVertexSectorIntCoordinates x (Fin.last n) - N ≤ q 0 := by
        simpa [sixVertexBetheShiftCoordinates] using hq0.1
      omega
  | cast i =>
      have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
      have hx : 0 ≤ sixVertexSectorIntCoordinates x i.castSucc := by
        simp [sixVertexSectorIntCoordinates]
      simp only [sixVertexBetheUnshiftCoordinates, Fin.lastCases_castSucc]
      simpa [sixVertexBetheShiftCoordinates] using hx.trans hi.1

private theorem sixVertexBetheUnshiftCoordinates_strictMono
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) :
    StrictMono (sixVertexBetheUnshiftCoordinates N q) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  induction n with
  | zero => exact Fin.elim0 i
  | succ k =>
      induction i using Fin.lastCases with
      | last =>
          simpa [sixVertexBetheUnshiftCoordinates] using
            sixVertexBetheCollisionFreeTuple_wrap_lt x q hq hfree
      | cast j =>
          have hstrict := sixVertexBetheCollisionFreeTuple_strictMono
            x q hq hfree (Fin.castSucc_lt_succ (i := j.succ))
          have heq : j.castSucc.succ = j.succ.castSucc := by
            apply Fin.ext
            rfl
          rw [heq]
          simp only [sixVertexBetheUnshiftCoordinates, Fin.lastCases_castSucc]
          change q j.castSucc.succ < q j.succ.succ
          exact hstrict



noncomputable def sixVertexBetheRotatedTupleEmbedding
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    Fin (n + 1) ↪o Fin N := by
  have hnonneg := sixVertexBetheUnshiftCoordinates_nonnegative x q hq
  let r := sixVertexBetheUnshiftCoordinates N q
  let f : Fin (n + 1) -> Fin N := fun i =>
    ⟨(r i).toNat, by
      rw [Int.toNat_lt (hnonneg i)]
      induction i using Fin.lastCases with
      | last =>
          simp only [r, sixVertexBetheUnshiftCoordinates, Fin.lastCases_last]
          omega
      | cast i =>
          have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
          have hxlt : sixVertexSectorIntCoordinates x i.succ < (N : Int) := by
            unfold sixVertexSectorIntCoordinates
            exact_mod_cast (sixVertexSectorPosition x i.succ).prop
          simp only [r, sixVertexBetheUnshiftCoordinates,
            Fin.lastCases_castSucc]
          exact hi.2.trans_lt hxlt⟩
  refine OrderEmbedding.ofStrictMono f ?_
  intro i j hij
  have hrij := sixVertexBetheUnshiftCoordinates_strictMono x q hq hfree hij
  change (r i).toNat < (r j).toNat
  have hrjpos : 0 < r j := (hnonneg i).trans_lt hrij
  exact (Int.toNat_lt_toNat hrjpos).mpr hrij

noncomputable def sixVertexBetheRotatedTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    SixVertexSector N (n + 1) :=
  Set.powersetCard.ofFinEmbEquiv
    (sixVertexBetheRotatedTupleEmbedding x q hq hfree hq0)

@[simp] private theorem sixVertexSectorPosition_rotatedTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    sixVertexSectorPosition
      (sixVertexBetheRotatedTupleSector x q hq hfree hq0) =
      sixVertexBetheRotatedTupleEmbedding x q hq hfree hq0 := by
  change Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv
      (sixVertexBetheRotatedTupleEmbedding x q hq hfree hq0)) = _
  exact Equiv.symm_apply_apply _ _

private theorem sixVertexSectorIntCoordinates_rotatedTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    sixVertexSectorIntCoordinates
      (sixVertexBetheRotatedTupleSector x q hq hfree hq0) =
      sixVertexBetheUnshiftCoordinates N q := by
  funext i
  unfold sixVertexSectorIntCoordinates
  rw [sixVertexSectorPosition_rotatedTupleSector]
  unfold sixVertexBetheRotatedTupleEmbedding
  simp only [OrderEmbedding.coe_ofStrictMono]
  change ((sixVertexBetheUnshiftCoordinates N q i).toNat : Int) = _
  exact Int.toNat_of_nonneg
    (sixVertexBetheUnshiftCoordinates_nonnegative x q hq i)

private theorem sixVertexBetheRotatedTupleSector_forward
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow (sixVertexBetheRotatedTupleSector x q hq hfree hq0)) := by
  apply sixVertexForwardInterlaced_of_positions
  constructor
  · intro i
    have hcoord := sixVertexSectorIntCoordinates_rotatedTupleSector
      x q hq hfree hq0
    induction i using Fin.lastCases with
    | last =>
        have hqzero := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq 0
        have hle : sixVertexSectorIntCoordinates x (Fin.last n) ≤ q 0 + N := by
          have := hqzero.1
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at this
          omega
        have hlast := congrFun hcoord (Fin.last n)
        simp only [sixVertexBetheUnshiftCoordinates, Fin.lastCases_last] at hlast
        have hle' : sixVertexSectorIntCoordinates x (Fin.last n) ≤
            sixVertexSectorIntCoordinates
              (sixVertexBetheRotatedTupleSector x q hq hfree hq0)
                (Fin.last n) := hle.trans hlast.ge
        unfold sixVertexSectorIntCoordinates at hle'
        exact_mod_cast hle'
    | cast i =>
        have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
        have hshift : sixVertexBetheShiftCoordinates N
            (sixVertexSectorIntCoordinates x) i.succ =
            sixVertexSectorIntCoordinates x i.castSucc := by
          simp [sixVertexBetheShiftCoordinates]
        have hri := congrFun hcoord i.castSucc
        simp only [sixVertexBetheUnshiftCoordinates,
          Fin.lastCases_castSucc] at hri
        have hle : sixVertexSectorIntCoordinates x i.castSucc ≤
            sixVertexSectorIntCoordinates
              (sixVertexBetheRotatedTupleSector x q hq hfree hq0)
                i.castSucc := (hshift ▸ hi.1).trans hri.ge
        unfold sixVertexSectorIntCoordinates at hle
        exact_mod_cast hle
  · intro k hk
    let i : Fin n := ⟨k, by omega⟩
    have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
    have hcoord := congrFun
      (sixVertexSectorIntCoordinates_rotatedTupleSector x q hq hfree hq0)
      i.castSucc
    simp only [sixVertexBetheUnshiftCoordinates,
      Fin.lastCases_castSucc] at hcoord
    have hle : sixVertexSectorIntCoordinates
        (sixVertexBetheRotatedTupleSector x q hq hfree hq0) i.castSucc ≤
        sixVertexSectorIntCoordinates x i.succ := hcoord.le.trans hi.2
    unfold sixVertexSectorIntCoordinates at hle
    exact_mod_cast hle

private theorem sixVertexReverseTuple_mem
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) ∈
      sixVertexBetheCyclicIntervalTuples N
        (sixVertexSectorIntCoordinates x) := by
  rw [mem_sixVertexBetheCyclicIntervalTuples]
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hxy
  intro i
  induction i using Fin.cases with
  | zero =>
      simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero]
      constructor
      · have hle : sixVertexSectorIntCoordinates x (Fin.last n) ≤
            sixVertexSectorIntCoordinates y (Fin.last n) := by
          unfold sixVertexSectorIntCoordinates
          exact_mod_cast hpos.1 (Fin.last n)
        exact sub_le_sub_right hle (N : Int)
      · have hylt : sixVertexSectorIntCoordinates y (Fin.last n) < N := by
          unfold sixVertexSectorIntCoordinates
          exact_mod_cast (sixVertexSectorPosition y (Fin.last n)).prop
        have hxzero : 0 ≤ sixVertexSectorIntCoordinates x 0 := by
          simp [sixVertexSectorIntCoordinates]
        omega
  | succ i =>
      simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ]
      constructor
      · unfold sixVertexSectorIntCoordinates
        exact_mod_cast hpos.1 i.castSucc
      · unfold sixVertexSectorIntCoordinates
        exact_mod_cast hpos.2 i.val (by omega)

private theorem sixVertexReverseTuple_first_neg
    {N n : Nat} (y : SixVertexSector N (n + 1)) :
    sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) 0 < 0 := by
  simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero]
  unfold sixVertexSectorIntCoordinates
  have := (sixVertexSectorPosition y (Fin.last n)).prop
  omega

private theorem sixVertexReverseTuple_collisionFree
    {N n : Nat} (x y : SixVertexSector N (n + 1)) :
    sixVertexBetheCollisionSet N (sixVertexSectorIntCoordinates x)
      (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y)) = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨i, hi⟩
  have hcol := (mem_sixVertexBetheCollisionSet N _ _ i).mp hi
  induction i using Fin.cases with
  | zero =>
      have hneg := sixVertexReverseTuple_first_neg y
      have hxzero : 0 ≤ sixVertexSectorIntCoordinates x 0 := by
        simp [sixVertexSectorIntCoordinates]
      exact (not_lt_of_ge hxzero) (hcol.1 ▸ hneg)
  | succ i =>
      have hfirst : sixVertexSectorIntCoordinates y i.castSucc =
          sixVertexSectorIntCoordinates x i.succ := by
        simpa [sixVertexBetheShiftCoordinates] using hcol.1
      by_cases hwrap : finRotate (n + 1) i.succ = 0
      · have hilast : i.succ = Fin.last n := by
          apply (finRotate (n + 1)).injective
          simpa using hwrap
        have hsecond : sixVertexSectorIntCoordinates y (Fin.last n) =
            sixVertexSectorIntCoordinates x (Fin.last n) := by
          have h := hcol.2
          rw [hwrap] at h
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at h
          have h' : sixVertexSectorIntCoordinates y (Fin.last n) - N =
              sixVertexSectorIntCoordinates x (Fin.last n) - N := by
            simpa [hilast] using h
          omega
        have hilt : i.castSucc < Fin.last n := by
          exact_mod_cast i.prop
        have hystrict := (sixVertexSectorPosition y).strictMono hilt
        have heq : sixVertexSectorIntCoordinates y i.castSucc =
            sixVertexSectorIntCoordinates y (Fin.last n) := by
          calc
            _ = sixVertexSectorIntCoordinates x i.succ := hfirst
            _ = sixVertexSectorIntCoordinates x (Fin.last n) := by rw [hilast]
            _ = sixVertexSectorIntCoordinates y (Fin.last n) := hsecond.symm
        have hystrictInt : sixVertexSectorIntCoordinates y i.castSucc <
            sixVertexSectorIntCoordinates y (Fin.last n) := by
          unfold sixVertexSectorIntCoordinates
          exact_mod_cast hystrict
        exact hystrictInt.ne heq
      · obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hwrap
        have hjval : j.castSucc = i.succ := by
          apply Fin.ext
          have hval : (finRotate (n + 1) i.succ).val = j.val + 1 := by
            simpa using congrArg Fin.val hj
          have hilast : i.succ ≠ Fin.last n := by
            intro hilast
            apply hwrap
            rw [hilast]
            apply Fin.ext
            simp
          have hrotval : (finRotate (n + 1) i.succ).val = i.succ.val + 1 :=
            coe_finRotate_of_ne_last hilast
          exact Nat.add_right_cancel (hval.symm.trans hrotval)
        have hsecond : sixVertexSectorIntCoordinates y j.castSucc =
            sixVertexSectorIntCoordinates x i.succ := by
          have h := hcol.2
          rw [hj] at h
          simpa [sixVertexBetheShiftCoordinates, hjval] using h
        have hystrict := (sixVertexSectorPosition y).strictMono
          (show i.castSucc < j.castSucc by
            rw [hjval]
            exact Fin.castSucc_lt_succ)
        have heq : sixVertexSectorIntCoordinates y i.castSucc =
            sixVertexSectorIntCoordinates y j.castSucc :=
          hfirst.trans hsecond.symm
        have hystrictInt : sixVertexSectorIntCoordinates y i.castSucc <
            sixVertexSectorIntCoordinates y j.castSucc := by
          unfold sixVertexSectorIntCoordinates
          exact_mod_cast hystrict
        exact hystrictInt.ne heq

private theorem sixVertexRotatedTupleSector_reverseTuple
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    sixVertexBetheRotatedTupleSector x
      (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
      (sixVertexReverseTuple_mem x y hxy)
      (sixVertexReverseTuple_collisionFree x y)
      (sixVertexReverseTuple_first_neg y) = y := by
  apply (Set.powersetCard.ofFinEmbEquiv
    (n := n + 1) (I := Fin N)).symm.injective
  change sixVertexSectorPosition _ = sixVertexSectorPosition y
  ext i
  have hcoord := congrFun (sixVertexSectorIntCoordinates_rotatedTupleSector
    x (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
      (sixVertexReverseTuple_mem x y hxy)
      (sixVertexReverseTuple_collisionFree x y)
      (sixVertexReverseTuple_first_neg y)) i
  have hcoord' : sixVertexSectorIntCoordinates
      (sixVertexBetheRotatedTupleSector x
        (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
        (sixVertexReverseTuple_mem x y hxy)
        (sixVertexReverseTuple_collisionFree x y)
        (sixVertexReverseTuple_first_neg y)) i =
      sixVertexSectorIntCoordinates y i := by
    calc
      _ = sixVertexBetheUnshiftCoordinates N
          (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y)) i :=
        hcoord
      _ = _ := congrFun (sixVertexBetheUnshiftCoordinates_shift N
        (sixVertexSectorIntCoordinates y)) i
  unfold sixVertexSectorIntCoordinates at hcoord'
  exact_mod_cast hcoord'



def sixVertexBetheInteriorSet {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i =>
    q i ≠ sixVertexBetheShiftCoordinates N x i ∧ q i ≠ x i

@[simp] theorem mem_sixVertexBetheInteriorSet {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) (i : Fin (n + 1)) :
    i ∈ sixVertexBetheInteriorSet N x q ↔
      q i ≠ sixVertexBetheShiftCoordinates N x i ∧ q i ≠ x i := by
  simp [sixVertexBetheInteriorSet]

private theorem sixVertexBetheIntervalTupleWeight_eq_interior
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x q : Fin (n + 1) -> Int) :
    sixVertexBetheIntervalTupleWeight N c z x q =
      ((c : Complex) ^ 2) ^ (sixVertexBetheInteriorSet N x q).card *
        ∏ i, z i ^ q i := by
  unfold sixVertexBetheIntervalTupleWeight
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 2
  ext i
  simp [sixVertexBetheInteriorSet]

private theorem sixVertexSector_mem_iff_exists_position
    {N m : Nat} (x : SixVertexSector N m) (v : Fin N) :
    v ∈ (x : Finset (Fin N)) ↔ ∃ i, sixVertexSectorPosition x i = v := by
  constructor
  · intro hv
    have hrange : v ∈ Set.range (sixVertexSectorPosition x) := by
      unfold sixVertexSectorPosition
      rw [Finset.range_orderEmbOfFin (x : Finset (Fin N)) x.prop]
      exact hv
    exact hrange
  · rintro ⟨i, rfl⟩
    exact sixVertexSectorPosition_mem x i

private theorem sixVertexForward_endpoint_iff_mem
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x))
    (i : Fin (n + 1)) :
    (sixVertexSectorIntCoordinates y i =
        sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates x) i \/
      sixVertexSectorIntCoordinates y i = sixVertexSectorIntCoordinates x i) ↔
      sixVertexSectorPosition y i ∈ (x : Finset (Fin N)) := by
  have hpos := (sixVertexForwardInterlaced_iff_positions y x).mp hyx
  constructor
  · intro hend
    induction i using Fin.cases with
    | zero =>
        rcases hend with hlo | hhi
        · have hyzero : 0 ≤ sixVertexSectorIntCoordinates y 0 := by
            simp [sixVertexSectorIntCoordinates]
          have hxlast : sixVertexSectorIntCoordinates x (Fin.last n) < N := by
            unfold sixVertexSectorIntCoordinates
            exact_mod_cast (sixVertexSectorPosition x (Fin.last n)).prop
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at hlo
          omega
        · rw [sixVertexSector_mem_iff_exists_position]
          refine ⟨0, ?_⟩
          apply Fin.ext
          unfold sixVertexSectorIntCoordinates at hhi
          exact_mod_cast hhi.symm
    | succ k =>
        rw [sixVertexSector_mem_iff_exists_position]
        rcases hend with hlo | hhi
        · refine ⟨k.castSucc, ?_⟩
          apply Fin.ext
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ] at hlo
          unfold sixVertexSectorIntCoordinates at hlo
          exact_mod_cast hlo.symm
        · refine ⟨k.succ, ?_⟩
          apply Fin.ext
          unfold sixVertexSectorIntCoordinates at hhi
          exact_mod_cast hhi.symm
  · intro hmem
    obtain ⟨j, hj⟩ := (sixVertexSector_mem_iff_exists_position x _).mp hmem
    induction i using Fin.cases with
    | zero =>
        have hy_le_x : sixVertexSectorPosition y 0 ≤
            sixVertexSectorPosition x 0 := hpos.1 0
        have hjzero : j = 0 := by
          by_contra hne
          have hjpos : (0 : Fin (n + 1)) < j := by
            exact Fin.pos_iff_ne_zero.mpr hne
          have hxlt := (sixVertexSectorPosition x).strictMono hjpos
          rw [hj] at hxlt
          exact (not_lt_of_ge hy_le_x) hxlt
        right
        unfold sixVertexSectorIntCoordinates
        rw [hjzero] at hj
        exact_mod_cast congrArg Fin.val hj.symm
    | succ k =>
        have hlo : sixVertexSectorPosition x k.castSucc ≤
            sixVertexSectorPosition y k.succ := by
          exact hpos.2 k.val (by omega)
        have hhi : sixVertexSectorPosition y k.succ ≤
            sixVertexSectorPosition x k.succ := hpos.1 k.succ
        have hjlo : k.castSucc ≤ j := by
          by_contra h
          have hjlt : j < k.castSucc := lt_of_not_ge h
          have hxlt := (sixVertexSectorPosition x).strictMono hjlt
          rw [hj] at hxlt
          exact (not_lt_of_ge hlo) hxlt
        have hjhi : j ≤ k.succ := by
          by_contra h
          have hjgt : k.succ < j := lt_of_not_ge h
          have hxlt := (sixVertexSectorPosition x).strictMono hjgt
          rw [hj] at hxlt
          exact (not_lt_of_ge hhi) hxlt
        have hjcases : j = k.castSucc ∨ j = k.succ := by
          change k.val ≤ j.val at hjlo
          change j.val ≤ k.val + 1 at hjhi
          by_cases hjv : j.val = k.val
          · left; apply Fin.ext; exact hjv
          · right
            apply Fin.ext
            have hlt : k.val < j.val :=
              lt_of_le_of_ne hjlo (Ne.symm hjv)
            exact Nat.le_antisymm hjhi (Nat.succ_le_iff.mpr hlt)
        rcases hjcases with rfl | rfl
        · left
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ]
          unfold sixVertexSectorIntCoordinates
          rw [hj]
        · right
          unfold sixVertexSectorIntCoordinates
          rw [hj]

private theorem sixVertexForward_interior_card
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    (sixVertexBetheInteriorSet N (sixVertexSectorIntCoordinates x)
      (sixVertexSectorIntCoordinates y)).card =
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card := by
  let I := sixVertexBetheInteriorSet N (sixVertexSectorIntCoordinates x)
    (sixVertexSectorIntCoordinates y)
  have hmap : Finset.map (sixVertexSectorPosition y).toEmbedding I =
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))) := by
    ext v
    constructor
    · intro hv
      simp only [Finset.mem_map] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      have hi' := (mem_sixVertexBetheInteriorSet N _ _ i).mp hi
      simp only [Finset.mem_sdiff]
      constructor
      · exact sixVertexSectorPosition_mem y i
      · intro hix
        have hend := (sixVertexForward_endpoint_iff_mem x y hyx i).mpr hix
        exact hend.elim hi'.1 hi'.2
    · intro hv
      simp only [Finset.mem_sdiff] at hv
      have hv' := hv
      obtain ⟨i, rfl⟩ := (sixVertexSector_mem_iff_exists_position y v).mp hv'.1
      simp only [Finset.mem_map]
      refine ⟨i, ?_, rfl⟩
      rw [mem_sixVertexBetheInteriorSet]
      have hnend := fun hend => hv'.2
        ((sixVertexForward_endpoint_iff_mem x y hyx i).mp hend)
      tauto
  rw [← hmap, Finset.card_map]

private theorem sixVertexReverse_endpoint_iff_mem
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y))
    (i : Fin (n + 1)) :
    (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i =
        sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates x) i \/
      sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i =
        sixVertexSectorIntCoordinates x i) ↔
      sixVertexSectorPosition y ((finRotate (n + 1)).symm i) ∈
        (x : Finset (Fin N)) := by
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hxy
  have hsymm0 : (finRotate (n + 1)).symm 0 = Fin.last n := by
    apply Fin.ext
    simp [finRotate_symm_apply]
  have hsymmsucc (k : Fin n) :
      (finRotate (n + 1)).symm k.succ = k.castSucc := by
    apply Fin.ext
    simp [finRotate_symm_apply, Fin.coe_sub_one]
  constructor
  · intro hend
    induction i using Fin.cases with
    | zero =>
        rw [hsymm0]
        rw [sixVertexSector_mem_iff_exists_position]
        rcases hend with hlo | hhi
        · refine ⟨Fin.last n, ?_⟩
          apply Fin.ext
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at hlo
          unfold sixVertexSectorIntCoordinates at hlo
          omega
        · have hneg := sixVertexReverseTuple_first_neg y
          have hxzero : 0 ≤ sixVertexSectorIntCoordinates x 0 := by
            simp [sixVertexSectorIntCoordinates]
          exfalso
          exact (not_lt_of_ge hxzero) (hhi ▸ hneg)
    | succ k =>
        rw [hsymmsucc k]
        rw [sixVertexSector_mem_iff_exists_position]
        rcases hend with hlo | hhi
        · refine ⟨k.castSucc, ?_⟩
          apply Fin.ext
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ] at hlo
          unfold sixVertexSectorIntCoordinates at hlo
          exact_mod_cast hlo.symm
        · refine ⟨k.succ, ?_⟩
          apply Fin.ext
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ] at hhi
          unfold sixVertexSectorIntCoordinates at hhi
          exact_mod_cast hhi.symm
  · intro hmem
    obtain ⟨j, hj⟩ := (sixVertexSector_mem_iff_exists_position x _).mp hmem
    induction i using Fin.cases with
    | zero =>
        rw [hsymm0] at hmem
        change sixVertexSectorPosition x j =
          sixVertexSectorPosition y (Fin.last n) at hj
        have hx_le_y : sixVertexSectorPosition x (Fin.last n) ≤
            sixVertexSectorPosition y (Fin.last n) := hpos.1 (Fin.last n)
        have hjlast : j = Fin.last n := by
          by_contra hne
          have hjlt : j < Fin.last n := Fin.lt_last_iff_ne_last.mpr hne
          have hxlt := (sixVertexSectorPosition x).strictMono hjlt
          rw [hj] at hxlt
          exact (not_lt_of_ge hx_le_y) hxlt
        left
        simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero]
        rw [hjlast] at hj
        unfold sixVertexSectorIntCoordinates
        have hcast : ((sixVertexSectorPosition y (Fin.last n)).val : Int) =
            (sixVertexSectorPosition x (Fin.last n)).val := by
          exact_mod_cast congrArg Fin.val hj.symm
        exact congrArg (fun t : Int => t - N) hcast
    | succ k =>
        rw [hsymmsucc k] at hmem
        replace hj : sixVertexSectorPosition x j =
            sixVertexSectorPosition y k.castSucc := by
          simpa [hsymmsucc k] using hj
        have hlo : sixVertexSectorPosition x k.castSucc ≤
            sixVertexSectorPosition y k.castSucc := hpos.1 k.castSucc
        have hhi : sixVertexSectorPosition y k.castSucc ≤
            sixVertexSectorPosition x k.succ := hpos.2 k.val (by omega)
        have hjlo : k.castSucc ≤ j := by
          by_contra h
          have hjlt : j < k.castSucc := lt_of_not_ge h
          have hxlt := (sixVertexSectorPosition x).strictMono hjlt
          rw [hj] at hxlt
          exact (not_lt_of_ge hlo) hxlt
        have hjhi : j ≤ k.succ := by
          by_contra h
          have hjgt : k.succ < j := lt_of_not_ge h
          have hxlt := (sixVertexSectorPosition x).strictMono hjgt
          rw [hj] at hxlt
          exact (not_lt_of_ge hhi) hxlt
        have hjcases : j = k.castSucc ∨ j = k.succ := by
          change k.val ≤ j.val at hjlo
          change j.val ≤ k.val + 1 at hjhi
          by_cases hjv : j.val = k.val
          · left; apply Fin.ext; exact hjv
          · right
            apply Fin.ext
            have hlt : k.val < j.val :=
              lt_of_le_of_ne hjlo (Ne.symm hjv)
            exact Nat.le_antisymm hjhi (Nat.succ_le_iff.mpr hlt)
        rcases hjcases with rfl | rfl
        · left
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ]
          unfold sixVertexSectorIntCoordinates
          rw [hj]
        · right
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ]
          unfold sixVertexSectorIntCoordinates
          rw [hj]

private theorem sixVertexReverse_interior_card
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    (sixVertexBetheInteriorSet N (sixVertexSectorIntCoordinates x)
      (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))).card =
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card := by
  let I := sixVertexBetheInteriorSet N (sixVertexSectorIntCoordinates x)
    (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
  let e : Fin (n + 1) ↪ Fin N :=
    (finRotate (n + 1)).symm.toEmbedding.trans
      (sixVertexSectorPosition y).toEmbedding
  have hmap : Finset.map e I =
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))) := by
    ext v
    constructor
    · intro hv
      simp only [Finset.mem_map] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      have hi' := (mem_sixVertexBetheInteriorSet N _ _ i).mp hi
      simp only [Finset.mem_sdiff]
      constructor
      · exact sixVertexSectorPosition_mem y _
      · intro hix
        have hend := (sixVertexReverse_endpoint_iff_mem x y hxy i).mpr hix
        exact hend.elim hi'.1 hi'.2
    · intro hv
      simp only [Finset.mem_sdiff] at hv
      obtain ⟨j, hj⟩ := (sixVertexSector_mem_iff_exists_position y v).mp hv.1
      let i := finRotate (n + 1) j
      have heq : (finRotate (n + 1)).symm i = j := by
        simp [i]
      simp only [Finset.mem_map]
      refine ⟨i, ?_, ?_⟩
      · rw [mem_sixVertexBetheInteriorSet]
        have hnend : ¬(
            sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i =
                sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates x) i \/
              sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i =
                sixVertexSectorIntCoordinates x i) := by
          intro hend
          have hmemx := (sixVertexReverse_endpoint_iff_mem x y hxy i).mp hend
          rw [heq, hj] at hmemx
          exact hv.2 hmemx
        tauto
      · dsimp [e]
        rw [heq, hj]
  rw [← hmap, Finset.card_map]

private theorem sixVertexBetheIntervalTupleWeight_forward
    {N n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    sixVertexBetheIntervalTupleWeight N c z
        (sixVertexSectorIntCoordinates x) (sixVertexSectorIntCoordinates y) =
      (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) *
        ∏ i, z i ^ sixVertexSectorIntCoordinates y i := by
  have hcard : ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card =
      ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop,
      Finset.inter_comm]
  rw [sixVertexBetheIntervalTupleWeight_eq_interior,
    sixVertexForward_interior_card x y hyx,
    hcard, sixVertexSectorRowDistance_eq_two_mul_sdiff]
  rw [pow_mul]

private theorem sixVertexBetheIntervalTupleWeight_reverse
    {N n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    sixVertexBetheIntervalTupleWeight N c z
        (sixVertexSectorIntCoordinates x)
        (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y)) =
      (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) *
        ∏ i, z i ^
          (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) i) := by
  have hcard : ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card =
      ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop,
      Finset.inter_comm]
  rw [sixVertexBetheIntervalTupleWeight_eq_interior,
    sixVertexReverse_interior_card x y hxy,
    hcard, sixVertexSectorRowDistance_eq_two_mul_sdiff]
  rw [pow_mul]

private theorem sixVertexForwardInterlaced_refl {N m : Nat}
    (x : SixVertexSector N m) :
    SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow x) := by
  apply sixVertexForwardInterlaced_of_positions
  constructor
  · exact fun _ => le_rfl
  · intro k hk
    exact (sixVertexSectorPosition x).monotone (by
      apply Fin.mk_le_mk.mpr
      omega)

private theorem sixVertexForwardInterlaced_antisymm
    {N m : Nat} (x y : SixVertexSector N m)
    (hxy : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hyx : SixVertexForwardInterlaced (sixVertexSectorRow y)
      (sixVertexSectorRow x)) : x = y := by
  have hpXY := (sixVertexForwardInterlaced_iff_positions x y).mp hxy
  have hpYX := (sixVertexForwardInterlaced_iff_positions y x).mp hyx
  apply (Set.powersetCard.ofFinEmbEquiv (n := m) (I := Fin N)).symm.injective
  change sixVertexSectorPosition x = sixVertexSectorPosition y
  ext i
  exact le_antisymm (hpXY.1 i) (hpYX.1 i)

local instance sixVertexForwardInterlacedDecidable {N : Nat}
    (x y : SixVertexRow N) : Decidable (SixVertexForwardInterlaced x y) :=
  Classical.propDecidable _

private theorem sixVertexSectorTransferComplex_eq_oriented
    (N m : Nat) (c : Real) (x y : SixVertexSector N m) :
    sixVertexSectorTransferComplex N m c x y =
      (if SixVertexForwardInterlaced (sixVertexSectorRow y)
          (sixVertexSectorRow x) then
        (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) else 0) +
      (if SixVertexForwardInterlaced (sixVertexSectorRow x)
          (sixVertexSectorRow y) then
        (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) else 0) := by
  classical
  by_cases hyx : SixVertexForwardInterlaced (sixVertexSectorRow y)
      (sixVertexSectorRow x)
  · by_cases hxy : SixVertexForwardInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y)
    · have heq := sixVertexForwardInterlaced_antisymm x y hxy hyx
      subst y
      simp [sixVertexSectorTransferComplex, sixVertexSectorTransfer,
        sixVertexTransfer, sixVertexForwardInterlaced_refl,
        sixVertexRowDistance]
      norm_num
    · have hne : x ≠ y := by
        intro heq
        subst y
        exact hxy (sixVertexForwardInterlaced_refl x)
      have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
        fun h => hne (sixVertexSectorRow_injective h)
      simp [sixVertexSectorTransferComplex, sixVertexSectorTransfer,
        sixVertexTransfer, hyx, hxy, hrow, SixVertexInterlaced]
  · by_cases hxy : SixVertexForwardInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y)
    · have hne : x ≠ y := by
        intro heq
        subst y
        exact hyx (sixVertexForwardInterlaced_refl x)
      have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
        fun h => hne (sixVertexSectorRow_injective h)
      simp [sixVertexSectorTransferComplex, sixVertexSectorTransfer,
        sixVertexTransfer, hyx, hxy, hrow, SixVertexInterlaced]
    · have hne : x ≠ y := by
        intro heq
        subst y
        exact hyx (sixVertexForwardInterlaced_refl x)
      have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
        fun h => hne (sixVertexSectorRow_injective h)
      simp [sixVertexSectorTransferComplex, sixVertexSectorTransfer,
        sixVertexTransfer, hyx, hxy, hrow, SixVertexInterlaced]

private theorem sixVertexSectorTransferComplex_mulVec_oriented
    (N m : Nat) (c : Real) (v : SixVertexSector N m -> Complex)
    (x : SixVertexSector N m) :
    (sixVertexSectorTransferComplex N m c).mulVec v x =
      (∑ y ∈ (Finset.univ : Finset (SixVertexSector N m)).filter
          (fun y => SixVertexForwardInterlaced
            (sixVertexSectorRow y) (sixVertexSectorRow x)),
        (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) * v y) +
      (∑ y ∈ (Finset.univ : Finset (SixVertexSector N m)).filter
          (fun y => SixVertexForwardInterlaced
            (sixVertexSectorRow x) (sixVertexSectorRow y)),
        (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) * v y) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  simp_rw [sixVertexSectorTransferComplex_eq_oriented, add_mul]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hyx : SixVertexForwardInterlaced
        (sixVertexSectorRow y) (sixVertexSectorRow x) <;>
      simp [hyx, add_mul]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hxy : SixVertexForwardInterlaced
        (sixVertexSectorRow x) (sixVertexSectorRow y) <;>
      simp [hxy, add_mul]

def sixVertexBetheCollisionFreeTuples {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) : Finset (Fin (n + 1) -> Int) := by
  classical
  exact (sixVertexBetheCyclicIntervalTuples N x).filter
    (fun q => sixVertexBetheCollisionSet N x q = ∅)

def sixVertexBetheNonnegativeTuples {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) : Finset (Fin (n + 1) -> Int) := by
  classical
  exact (sixVertexBetheCollisionFreeTuples N x).filter (fun q => 0 ≤ q 0)

def sixVertexBetheNegativeTuples {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) : Finset (Fin (n + 1) -> Int) := by
  classical
  exact (sixVertexBetheCollisionFreeTuples N x).filter (fun q => q 0 < 0)

@[simp] theorem mem_sixVertexBetheNonnegativeTuples {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) :
    q ∈ sixVertexBetheNonnegativeTuples N x ↔
      q ∈ sixVertexBetheCyclicIntervalTuples N x ∧
        sixVertexBetheCollisionSet N x q = ∅ ∧ 0 ≤ q 0 := by
  unfold sixVertexBetheNonnegativeTuples sixVertexBetheCollisionFreeTuples
  simp only [Finset.mem_filter]
  tauto

@[simp] theorem mem_sixVertexBetheNegativeTuples {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) :
    q ∈ sixVertexBetheNegativeTuples N x ↔
      q ∈ sixVertexBetheCyclicIntervalTuples N x ∧
        sixVertexBetheCollisionSet N x q = ∅ ∧ q 0 < 0 := by
  unfold sixVertexBetheNegativeTuples sixVertexBetheCollisionFreeTuples
  simp only [Finset.mem_filter]
  tauto

def sixVertexBetheTupleBoltzmann {n : Nat} (N : Nat) (c : Real)
    (x q : Fin (n + 1) -> Int) : Complex :=
  ((c : Complex) ^ 2) ^ (sixVertexBetheInteriorSet N x q).card

def sixVertexBetheTupleWaveWeight {n : Nat} (N : Nat) (c : Real)
    (p : Fin (n + 1) -> Real) (x q : Fin (n + 1) -> Int) : Complex :=
  sixVertexBetheTupleBoltzmann N c x q *
    sixVertexCoordinateBetheIntWave c p q

private theorem sixVertexForward_orientedSum_eq_nonnegativeTuples
    {N n : Nat} (c : Real) (p : Fin (n + 1) -> Real)
    (x : SixVertexSector N (n + 1)) :
    (∑ y ∈ (Finset.univ : Finset (SixVertexSector N (n + 1))).filter
        (fun y => SixVertexForwardInterlaced
          (sixVertexSectorRow y) (sixVertexSectorRow x)),
      (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) *
        sixVertexCoordinateBetheWave c p y) =
      ∑ q ∈ sixVertexBetheNonnegativeTuples N
          (sixVertexSectorIntCoordinates x),
        sixVertexBetheTupleWaveWeight N c p
          (sixVertexSectorIntCoordinates x) q := by
  classical
  apply Finset.sum_bij (fun y _ => sixVertexSectorIntCoordinates y)
  · intro y hy
    have hyx := (Finset.mem_filter.mp hy).2
    rw [mem_sixVertexBetheNonnegativeTuples]
    exact ⟨sixVertexForwardTuple_mem x y hyx,
      sixVertexForwardTuple_collisionFree x y hyx,
      by simp [sixVertexSectorIntCoordinates]⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    apply (Set.powersetCard.ofFinEmbEquiv
      (n := n + 1) (I := Fin N)).symm.injective
    change sixVertexSectorPosition y₁ = sixVertexSectorPosition y₂
    ext i
    have hi := congrFun heq i
    unfold sixVertexSectorIntCoordinates at hi
    exact_mod_cast hi
  · intro q hq
    have hparts := (mem_sixVertexBetheNonnegativeTuples N _ q).mp hq
    let y := sixVertexBetheDirectTupleSector x q hparts.1 hparts.2.1 hparts.2.2
    have hyx := sixVertexBetheDirectTupleSector_forward x q
      hparts.1 hparts.2.1 hparts.2.2
    refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyx⟩, ?_⟩
    exact sixVertexSectorIntCoordinates_directTupleSector x q
      hparts.1 hparts.2.1 hparts.2.2
  · intro y hy
    have hyx := (Finset.mem_filter.mp hy).2
    unfold sixVertexBetheTupleWaveWeight sixVertexBetheTupleBoltzmann
    rw [sixVertexCoordinateBetheWave_eq_intWave,
      sixVertexForward_interior_card x y hyx,
      sixVertexSectorRowDistance_eq_two_mul_sdiff]
    have hcard : ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card =
        ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
      rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop,
        Finset.inter_comm]
    rw [hcard, pow_mul]

private theorem SixVertexSatisfiesMultiplicativeBetheEquations.reverse_orientedSum_eq_negativeTuples
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : SixVertexSector N (n + 1)) :
    (∑ y ∈ (Finset.univ : Finset (SixVertexSector N (n + 1))).filter
        (fun y => SixVertexForwardInterlaced
          (sixVertexSectorRow x) (sixVertexSectorRow y)),
      (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) *
        sixVertexCoordinateBetheWave c p y) =
      ∑ q ∈ sixVertexBetheNegativeTuples N
          (sixVertexSectorIntCoordinates x),
        sixVertexBetheTupleWaveWeight N c p
          (sixVertexSectorIntCoordinates x) q := by
  classical
  apply Finset.sum_bij (fun y _ =>
    sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
  · intro y hy
    have hxy := (Finset.mem_filter.mp hy).2
    rw [mem_sixVertexBetheNegativeTuples]
    exact ⟨sixVertexReverseTuple_mem x y hxy,
      sixVertexReverseTuple_collisionFree x y,
      sixVertexReverseTuple_first_neg y⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    have heq' := congrArg (sixVertexBetheUnshiftCoordinates N) heq
    simp only [sixVertexBetheUnshiftCoordinates_shift] at heq'
    apply (Set.powersetCard.ofFinEmbEquiv
      (n := n + 1) (I := Fin N)).symm.injective
    change sixVertexSectorPosition y₁ = sixVertexSectorPosition y₂
    ext i
    have hi := congrFun heq' i
    unfold sixVertexSectorIntCoordinates at hi
    exact_mod_cast hi
  · intro q hq
    have hparts := (mem_sixVertexBetheNegativeTuples N _ q).mp hq
    let y := sixVertexBetheRotatedTupleSector x q
      hparts.1 hparts.2.1 hparts.2.2
    have hxy := sixVertexBetheRotatedTupleSector_forward x q
      hparts.1 hparts.2.1 hparts.2.2
    refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, ?_⟩
    have hcoord := sixVertexSectorIntCoordinates_rotatedTupleSector x q
      hparts.1 hparts.2.1 hparts.2.2
    rw [hcoord, sixVertexBetheShiftCoordinates_unshift]
  · intro y hy
    have hxy := (Finset.mem_filter.mp hy).2
    unfold sixVertexBetheTupleWaveWeight sixVertexBetheTupleBoltzmann
    rw [sixVertexCoordinateBetheWave_eq_intWave,
      sixVertexReverse_interior_card x y hxy,
      sixVertexSectorRowDistance_eq_two_mul_sdiff]
    have hcard : ((y : Finset (Fin N)) \ (x : Finset (Fin N))).card =
        ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
      rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop,
        Finset.inter_comm]
    rw [hcard, pow_mul]
    rw [← hp.intWave_shift hc (sixVertexSectorIntCoordinates y)]

private theorem sixVertexBetheCollisionFreeTuples_sum_split
    {n : Nat} (N : Nat) (x : Fin (n + 1) -> Int)
    (f : (Fin (n + 1) -> Int) -> Complex) :
    (∑ q ∈ sixVertexBetheCollisionFreeTuples N x, f q) =
      (∑ q ∈ sixVertexBetheNonnegativeTuples N x, f q) +
        ∑ q ∈ sixVertexBetheNegativeTuples N x, f q := by
  classical
  let A := sixVertexBetheNonnegativeTuples N x
  let B := sixVertexBetheNegativeTuples N x
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro q hA hB
    have hA' := (mem_sixVertexBetheNonnegativeTuples N x q).mp hA
    have hB' := (mem_sixVertexBetheNegativeTuples N x q).mp hB
    omega
  have hunion : A ∪ B = sixVertexBetheCollisionFreeTuples N x := by
    ext q
    simp only [Finset.mem_union]
    constructor
    · rintro (hA | hB)
      · have hp := (mem_sixVertexBetheNonnegativeTuples N x q).mp hA
        unfold sixVertexBetheCollisionFreeTuples
        exact Finset.mem_filter.mpr ⟨hp.1, hp.2.1⟩
      · have hp := (mem_sixVertexBetheNegativeTuples N x q).mp hB
        unfold sixVertexBetheCollisionFreeTuples
        exact Finset.mem_filter.mpr ⟨hp.1, hp.2.1⟩
    · intro hq
      have hbase := Finset.mem_filter.mp hq
      by_cases hq0 : 0 ≤ q 0
      · left
        rw [mem_sixVertexBetheNonnegativeTuples]
        exact ⟨hbase.1, hbase.2, hq0⟩
      · right
        rw [mem_sixVertexBetheNegativeTuples]
        exact ⟨hbase.1, hbase.2, lt_of_not_ge hq0⟩
  rw [← hunion, Finset.sum_union hdis]

private theorem sixVertexBethe_sum_intervalTupleWeight
    {N n : Nat} (c : Real) (p : Fin (n + 1) -> Real)
    (x q : Fin (n + 1) -> Int) :
    (∑ sigma : Equiv.Perm (Fin (n + 1)),
      sixVertexBetheAmplitude c p sigma *
        sixVertexBetheIntervalTupleWeight N c
          (fun i => sixVertexBethePhase (p (sigma i))) x q) =
      sixVertexBetheTupleWaveWeight N c p x q := by
  rw [show (∑ sigma : Equiv.Perm (Fin (n + 1)),
      sixVertexBetheAmplitude c p sigma *
        sixVertexBetheIntervalTupleWeight N c
          (fun i => sixVertexBethePhase (p (sigma i))) x q) =
      sixVertexBetheTupleBoltzmann N c x q *
        ∑ sigma, sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntMonomial p sigma q by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sigma _
    rw [sixVertexBetheIntervalTupleWeight_eq_interior]
    unfold sixVertexBetheTupleBoltzmann sixVertexBetheIntMonomial
    ring]
  rfl

theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalCyclicIntervalExpansion
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : SixVertexSector N (n + 1)) :
    (sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x =
      ∑ q ∈ sixVertexBetheCollisionFreeTuples N
          (sixVertexSectorIntCoordinates x),
        sixVertexBetheTupleWaveWeight N c p
          (sixVertexSectorIntCoordinates x) q := by
  rw [sixVertexSectorTransferComplex_mulVec_oriented,
    sixVertexForward_orientedSum_eq_nonnegativeTuples,
    hp.reverse_orientedSum_eq_negativeTuples hc,
    ← sixVertexBetheCollisionFreeTuples_sum_split]

private theorem sixVertexBetheCollisionFreeIntervalSum_eq_tupleSum
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) :
    sixVertexBetheCollisionFreeIntervalSum N c z x =
      ∑ q ∈ sixVertexBetheCollisionFreeTuples N x,
        sixVertexBetheIntervalTupleWeight N c z x q := by
  rfl



theorem sixVertexBetheShiftCoordinates_lt_sector {N n : Nat}
    (x : SixVertexSector N (n + 1)) (i : Fin (n + 1)) :
    sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates x) i <
      sixVertexSectorIntCoordinates x i := by
  induction i using Fin.cases with
  | zero =>
      simp only [sixVertexBetheShiftCoordinates, sixVertexSectorIntCoordinates,
        Fin.cases_zero]
      have hlast : (sixVertexSectorPosition x (Fin.last n)).val < N :=
        (sixVertexSectorPosition x (Fin.last n)).prop
      have hzero : 0 <= (sixVertexSectorPosition x 0).val := Nat.zero_le _
      omega
  | succ i =>
      simp only [sixVertexBetheShiftCoordinates, sixVertexSectorIntCoordinates,
        Fin.cases_succ]
      exact_mod_cast (sixVertexSectorPosition x).strictMono
        (Fin.castSucc_lt_succ (i := i))





theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalWordExpansion
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    SixVertexPhysicalWordExpansion (N := N) c p := by
  intro x
  rw [hp.physicalCyclicIntervalExpansion hc p x]
  let Q := sixVertexBetheCollisionFreeTuples N
    (sixVertexSectorIntCoordinates x)
  calc
    (∑ q ∈ Q, sixVertexBetheTupleWaveWeight N c p
        (sixVertexSectorIntCoordinates x) q) =
      ∑ q ∈ Q, ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntervalTupleWeight N c
            (fun i => sixVertexBethePhase (p (sigma i)))
            (sixVertexSectorIntCoordinates x) q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (sixVertexBethe_sum_intervalTupleWeight c p
        (sixVertexSectorIntCoordinates x) q).symm
    _ = ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheCollisionFreeIntervalSum N c
            (fun i => sixVertexBethePhase (p (sigma i)))
            (sixVertexSectorIntCoordinates x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sigma _
      rw [sixVertexBetheCollisionFreeIntervalSum_eq_tupleSum,
        Finset.mul_sum]
    _ = ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          ∑ w : Finset (Fin (n + 1)),
            sixVertexBetheWordCoefficient c
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _) w *
            sixVertexBetheWordMonomial N
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _)
              (sixVertexSectorIntCoordinates x) w := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [sixVertexBetheCollisionFreeIntervalSum_eq_words]
      · exact fun i => sixVertexBetheShiftCoordinates_lt_sector x i
      · exact fun i => Complex.exp_ne_zero _
      · exact fun i => hphase (sigma i)
    _ = ∑ w : Finset (Fin (n + 1)),
        ∑ sigma, sixVertexBetheAmplitude c p sigma *
          sixVertexBetheWordCoefficient c
            (fun j => sixVertexBethePhase (p j)) sigma w *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase (p j)) sigma
            (sixVertexSectorIntCoordinates x) w := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro sigma _
      change sixVertexBetheAmplitude c p sigma *
          (sixVertexBetheWordCoefficient c
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _) w *
            sixVertexBetheWordMonomial N
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _)
              (sixVertexSectorIntCoordinates x) w) = _
      have hcoeff :
          sixVertexBetheWordCoefficient c
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _) w =
            sixVertexBetheWordCoefficient c
              (fun j => sixVertexBethePhase (p j)) sigma w := by
        unfold sixVertexBetheWordCoefficient
        apply Finset.prod_congr rfl
        intro i _
        simp [sixVertexBetheWordEdgeFactor]
      have hmono :
          sixVertexBetheWordMonomial N
              (fun i => sixVertexBethePhase (p (sigma i))) (Equiv.refl _)
              (sixVertexSectorIntCoordinates x) w =
            sixVertexBetheWordMonomial N
              (fun j => sixVertexBethePhase (p j)) sigma
              (sixVertexSectorIntCoordinates x) w := by
        unfold sixVertexBetheWordMonomial
        apply Finset.prod_congr rfl
        intro i _
        simp
      rw [hcoeff, hmono]
      ring



theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p :=
  sixVertexCoordinateBetheEigenrelation_of_physicalWordExpansion
    hc p hp hphase (hp.physicalWordExpansion hc p hphase)

end

end StatMech.FrontierD
