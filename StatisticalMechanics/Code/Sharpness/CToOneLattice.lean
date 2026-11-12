/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Sharpness.CToOne
import Code.Ising.FiniteVolumeDomain

open Filter Topology

namespace StatMech

namespace Sharpness

open Ising Lattice


abbrev sctBox (d n : ℕ) := {x : Site d // x ∈ box d n}

noncomputable instance sctBoxFintype (d n : ℕ) : Fintype (sctBox d n) :=
  (box_finite d n).fintype


def sctBoxGraph (d n : ℕ) : SimpleGraph (sctBox d n) :=
  (hypercubicLattice d).induce (box d n)

noncomputable instance sctBoxGraphDecidableAdj (d n : ℕ) :
    DecidableRel (sctBoxGraph d n).Adj := Classical.decRel _



def sctBoxInLarger (d n m : ℕ) (z : sctBox d m) : Prop := z.1 ∈ box d n

noncomputable instance sctBoxInLargerDecidable (d n m : ℕ) :
    DecidablePred (sctBoxInLarger d n m) := Classical.decPred _



noncomputable def sctBoxInclusionEquiv (d : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    sctBox d n ≃ {z : sctBox d m // sctBoxInLarger d n m z} where
  toFun z := ⟨⟨z.1, fun i => le_trans (z.2 i) hnm⟩, z.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv z := by ext i; rfl
  right_inv z := by ext i; rfl


theorem sctBoxInclusionEquiv_adj (d : ℕ) {n m : ℕ} (hnm : n ≤ m)
    (a b : sctBox d n) :
    (sctBoxGraph d n).Adj a b ↔
      ((sctBoxGraph d m).comap
        (Subtype.val : {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m)).Adj
        (sctBoxInclusionEquiv d hnm a) (sctBoxInclusionEquiv d hnm b) := by
  simp [sctBoxGraph, sctBoxInclusionEquiv, SimpleGraph.comap_adj]


def sctBoxOrigin (d n : ℕ) : sctBox d n :=
  ⟨fun _ => 0, by intro i; simp⟩


def sctTranslatedBox (d n : ℕ) (y : Site d) : Set (Site d) :=
  (fun z : Site d => z - y) '' box d n


noncomputable def sctTranslateEquiv (d n : ℕ) (y : Site d) :
    sctBox d n ≃ {z : Site d // z ∈ sctTranslatedBox d n y} where
  toFun z := ⟨z.1 - y, ⟨z.1, z.2, rfl⟩⟩
  invFun w := ⟨w.1 + y, by
    rcases w.2 with ⟨z, hz, hzy⟩
    have hw : w.1 + y = z := by
      rw [← hzy]
      funext i
      dsimp
      ring
    rwa [hw]⟩
  left_inv z := by ext i; simp
  right_inv w := by ext i; simp


def sctTranslatedBoxGraph (d n : ℕ) (y : Site d) :
    SimpleGraph {z : Site d // z ∈ sctTranslatedBox d n y} :=
  (hypercubicLattice d).induce (sctTranslatedBox d n y)

noncomputable instance sctTranslatedBoxFintype (d n : ℕ) (y : Site d) :
    Fintype {z : Site d // z ∈ sctTranslatedBox d n y} :=
  ((box_finite d n).image (fun z : Site d => z - y)).fintype

noncomputable instance sctTranslatedBoxGraphDecidableAdj (d n : ℕ) (y : Site d) :
    DecidableRel (sctTranslatedBoxGraph d n y).Adj := Classical.decRel _


def sctTranslatedInDouble (d n : ℕ) (y : sctBox d n) (z : sctBox d (2 * n)) : Prop :=
  z.1 ∈ sctTranslatedBox d n y.1

noncomputable instance sctTranslatedInDoubleDecidable (d n : ℕ) (y : sctBox d n) :
    DecidablePred (sctTranslatedInDouble d n y) := Classical.decPred _



noncomputable def sctTranslatedInDoubleEquiv (d n : ℕ) (y : sctBox d n) :
    {z : Site d // z ∈ sctTranslatedBox d n y.1} ≃
      {z : sctBox d (2 * n) // sctTranslatedInDouble d n y z} where
  toFun z := ⟨⟨z.1, sct_translate_box_subset_double y.2 z.2⟩, z.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv z := by ext i; rfl
  right_inv z := by ext i; rfl



theorem sctTranslatedInDoubleEquiv_adj (d n : ℕ) (y : sctBox d n)
    (a b : {z : Site d // z ∈ sctTranslatedBox d n y.1}) :
    (sctTranslatedBoxGraph d n y.1).Adj a b ↔
      ((sctBoxGraph d (2 * n)).comap
        (Subtype.val :
          {z : sctBox d (2 * n) // sctTranslatedInDouble d n y z} → sctBox d (2 * n))).Adj
        (sctTranslatedInDoubleEquiv d n y a)
        (sctTranslatedInDoubleEquiv d n y b) := by
  simp [sctTranslatedBoxGraph, sctBoxGraph, sctTranslatedInDoubleEquiv,
    SimpleGraph.comap_adj]


theorem sctTranslateEquiv_adj (d n : ℕ) (y : Site d) (a b : sctBox d n) :
    (sctBoxGraph d n).Adj a b ↔
      (sctTranslatedBoxGraph d n y).Adj
        (sctTranslateEquiv d n y a) (sctTranslateEquiv d n y b) := by
  simp only [sctBoxGraph, sctTranslatedBoxGraph, SimpleGraph.induce_adj,
    hypercubicLattice_adj]
  have hs : (∑ i, (a.1 i - b.1 i).natAbs) =
      ∑ i, (((sctTranslateEquiv d n y a).1 i) -
        ((sctTranslateEquiv d n y b).1 i)).natAbs := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change a.1 i - b.1 i = (a.1 i - y i) - (b.1 i - y i)
    ring
  rw [hs]


noncomputable def sctBoxMag (d : ℕ) (β h : ℝ) (n : ℕ) (x : sctBox d n) : ℝ :=
  isingExpectation (sctBoxGraph d n) β h (fun s => spin s x)


noncomputable def sctOriginMag (d : ℕ) (β h : ℝ) (n : ℕ) : ℝ :=
  sctBoxMag d β h n (sctBoxOrigin d n)


noncomputable def sctBoxSites (d n : ℕ) : Finset (sctBox d n) := Finset.univ

theorem sctBoxSites_nonempty (d n : ℕ) : (sctBoxSites d n).Nonempty := by
  exact ⟨sctBoxOrigin d n, Finset.mem_univ _⟩



noncomputable def sctLatticeC (d : ℕ) (β h : ℝ) (n : ℕ) : ℝ :=
  sct_cInfDep (sctBox d) (sctOriginMag d β h) (sctBoxSites d)
    (sctBoxMag d β h) (sctBoxSites_nonempty d) n

@[simp]
theorem sctBoxMag_origin (d : ℕ) (β h : ℝ) (n : ℕ) :
    sctBoxMag d β h n (sctBoxOrigin d n) = sctOriginMag d β h n := rfl




theorem sctBoxMag_eq_translated_origin (d : ℕ) (β h : ℝ) (n : ℕ)
    (x : sctBox d n) :
    sctBoxMag d β h n x =
      isingExpectation (sctTranslatedBoxGraph d n x.1) β h
        (fun s => spin s (sctTranslateEquiv d n x.1 x)) := by
  exact isingExpectation_spin_relabel (sctBoxGraph d n)
    (sctTranslatedBoxGraph d n x.1) (sctTranslateEquiv d n x.1)
    (sctTranslateEquiv_adj d n x.1) β h x


theorem sctTranslateEquiv_self (d : ℕ) (n : ℕ) (x : sctBox d n) :
    (sctTranslateEquiv d n x.1 x).1 = (fun _ => 0 : Site d) := by
  funext i
  simp [sctTranslateEquiv]



theorem sctBoxMag_pos (d : ℕ) (β h : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (n : ℕ) (x : sctBox d n) :
    0 < sctBoxMag d β h n x :=
  sct_expectation_spin_pos (sctBoxGraph d n) β h hβ hh x


theorem sctOriginMag_pos (d : ℕ) (β h : ℝ) (hβ : 0 < β) (hh : 0 < h) (n : ℕ) :
    0 < sctOriginMag d β h n :=
  sctBoxMag_pos d β h hβ hh n (sctBoxOrigin d n)


theorem sctOriginMag_le_one (d : ℕ) (β h : ℝ) (n : ℕ) :
    sctOriginMag d β h n ≤ 1 :=
  expectation_spin_le_one (sctBoxGraph d n) β h (sctBoxOrigin d n)


theorem sctOriginMag_monotone (d : ℕ) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) : Monotone (sctOriginMag d β h) := by
  intro n m hnm
  let e := sctBoxInclusionEquiv d hnm
  calc
    sctOriginMag d β h n =
        isingExpectation
          ((sctBoxGraph d m).comap
            (Subtype.val :
              {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m)) β h
          (fun s => spin s (e (sctBoxOrigin d n))) := by
            exact isingExpectation_spin_relabel (sctBoxGraph d n)
              ((sctBoxGraph d m).comap
                (Subtype.val :
                  {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m))
              e (sctBoxInclusionEquiv_adj d hnm) β h (sctBoxOrigin d n)
    _ ≤ isingExpectation (sctBoxGraph d m) β h
          (fun s => spin s (e (sctBoxOrigin d n)).1) :=
      isingExpectation_spin_induce_le (sctBoxGraph d m)
        (sctBoxInLarger d n m) β h hβ hh (e (sctBoxOrigin d n))
    _ = sctOriginMag d β h m := by
      congr 2



theorem sctBoxMag_le_double (d : ℕ) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (n : ℕ) (x : sctBox d n) :
    sctBoxMag d β h n x ≤ sctOriginMag d β h (2 * n) := by
  let o := sctTranslateEquiv d n x.1 x
  let e := sctTranslatedInDoubleEquiv d n x
  calc
    sctBoxMag d β h n x =
        isingExpectation (sctTranslatedBoxGraph d n x.1) β h
          (fun s => spin s o) := sctBoxMag_eq_translated_origin d β h n x
    _ = isingExpectation
          ((sctBoxGraph d (2 * n)).comap
            (Subtype.val :
              {z : sctBox d (2 * n) // sctTranslatedInDouble d n x z} →
                sctBox d (2 * n))) β h
          (fun s => spin s (e o)) := by
            exact isingExpectation_spin_relabel (sctTranslatedBoxGraph d n x.1)
              ((sctBoxGraph d (2 * n)).comap
                (Subtype.val :
                  {z : sctBox d (2 * n) // sctTranslatedInDouble d n x z} →
                    sctBox d (2 * n)))
              e (sctTranslatedInDoubleEquiv_adj d n x) β h o
    _ ≤ isingExpectation (sctBoxGraph d (2 * n)) β h
          (fun s => spin s (e o).1) :=
      isingExpectation_spin_induce_le (sctBoxGraph d (2 * n))
        (sctTranslatedInDouble d n x) β h hβ hh (e o)
    _ = sctOriginMag d β h (2 * n) := by
      have hsite : (e o).1 = sctBoxOrigin d (2 * n) := by
        ext i
        exact congrFun (sctTranslateEquiv_self d n x) i
      rw [hsite]
      rfl



theorem sctLatticeC_le_one (d : ℕ) (β h : ℝ) (hβ : 0 < β) (hh : 0 < h) (n : ℕ) :
    sctLatticeC d β h n ≤ 1 := by
  unfold sctLatticeC
  exact sct_cInfDep_le_one (sctBox d) (sctOriginMag d β h) (sctBoxSites d)
    (sctBoxMag d β h) (sctBoxSites_nonempty d) (sctBoxOrigin d)
    (fun k => Finset.mem_univ _) (sctBoxMag_origin d β h)
    (fun k => (sctOriginMag_pos d β h hβ hh k).ne') n





theorem sctLatticeC_tendsto_one (d : ℕ) (β h : ℝ) (hβ : 0 < β) (hh : 0 < h)
    :
    Tendsto (sctLatticeC d β h) atTop (𝓝 1) := by
  exact sct_cInfDep_to_one_of_monotone (sctBox d) (sctOriginMag d β h)
    (sctBoxSites d) (sctBoxMag d β h) (sctBoxSites_nonempty d)
    (sctOriginMag_monotone d β h hβ.le hh.le)
    (sctOriginMag_le_one d β h) (sctOriginMag_pos d β h hβ hh 0)
    (fun n x _ => sctBoxMag_pos d β h hβ hh n x) (sctBoxOrigin d)
    (fun n => Finset.mem_univ _) (sctBoxMag_origin d β h)
    (fun n x _ => sctBoxMag_le_double d β h hβ.le hh.le n x)

end Sharpness

end StatMech
