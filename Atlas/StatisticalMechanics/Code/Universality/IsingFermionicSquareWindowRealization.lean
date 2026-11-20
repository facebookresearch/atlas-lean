/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalAverageAnchor
import Code.Universality.IsingFermionicCaratheodoryHolderAnchor





namespace StatMech.Universality

open Finset

noncomputable section


theorem fkIsingSquareRadialPatchEdge_injective
    (n m : Nat) (hm : m ≤ n) :
    Function.Injective
      (fun p : Fin m × Fin m ↦
        fkIsingSquareRadialPatchEdge n m hm p.1 p.2) := by
  intro p q hpq
  let up := fkIsingSquareRadialPatchVertex n m hm p.1 p.2
  let uq := fkIsingSquareRadialPatchVertex n m hm q.1 q.2
  let dp := fkIsingSquareRadialPatchDirection p.1.1 p.2.1
  let dq := fkIsingSquareRadialPatchDirection q.1.1 q.2.1
  let vp := fkIsingSquareNeighbor n up dp
    (fkIsingSquareRadialPatchDirection_available n m hm p.1 p.2)
  let vq := fkIsingSquareNeighbor n uq dq
    (fkIsingSquareRadialPatchDirection_available n m hm q.1 q.2)
  have hs : s(up, vp) = s(uq, vq) := by
    exact congrArg Subtype.val hpq
  rcases Sym2.eq_iff.mp hs with hsame | hswap
  · have hx : up.1 0 + vp.1 0 = uq.1 0 + vq.1 0 := by
      rw [hsame.1, hsame.2]
    have hy : up.1 1 + vp.1 1 = uq.1 1 + vq.1 1 := by
      rw [hsame.1, hsame.2]
    by_cases hp : Even (p.1.1 + p.2.1) <;>
      by_cases hq : Even (q.1.1 + q.2.1)
    all_goals
      have hpmod := hp
      have hqmod := hq
      simp only [Nat.even_iff] at hpmod hqmod
      have hpcoord :
          2 * ((p.1.1 + p.2.1 + 1) / 2) =
            if Even (p.1.1 + p.2.1) then p.1.1 + p.2.1
            else p.1.1 + p.2.1 + 1 := by
        simp [hp]
        omega
      have hqcoord :
          2 * ((q.1.1 + q.2.1 + 1) / 2) =
            if Even (q.1.1 + q.2.1) then q.1.1 + q.2.1
            else q.1.1 + q.2.1 + 1 := by
        simp [hq]
        omega
      simp [hp, hq] at hpcoord hqcoord
      simp [up, uq, vp, vq, dp, dq, fkIsingSquareRadialPatchDirection,
        hp, hq, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareRadialPatchVertex] at hx hy
      simp_rw [fkIsingSquareRadialPatchHalf_eq] at hx hy
    all_goals
      apply Prod.ext <;> apply Fin.ext <;> omega
  · have hx : up.1 0 + vp.1 0 = uq.1 0 + vq.1 0 := by
      rw [hswap.1, hswap.2]
      ring
    have hy : up.1 1 + vp.1 1 = uq.1 1 + vq.1 1 := by
      rw [hswap.1, hswap.2]
      ring
    by_cases hp : Even (p.1.1 + p.2.1) <;>
      by_cases hq : Even (q.1.1 + q.2.1)
    all_goals
      have hpmod := hp
      have hqmod := hq
      simp only [Nat.even_iff] at hpmod hqmod
      have hpcoord :
          2 * ((p.1.1 + p.2.1 + 1) / 2) =
            if Even (p.1.1 + p.2.1) then p.1.1 + p.2.1
            else p.1.1 + p.2.1 + 1 := by
        simp [hp]
        omega
      have hqcoord :
          2 * ((q.1.1 + q.2.1 + 1) / 2) =
            if Even (q.1.1 + q.2.1) then q.1.1 + q.2.1
            else q.1.1 + q.2.1 + 1 := by
        simp [hq]
        omega
      simp [hp, hq] at hpcoord hqcoord
      simp [up, uq, vp, vq, dp, dq, fkIsingSquareRadialPatchDirection,
        hp, hq, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareRadialPatchVertex] at hx hy
      simp_rw [fkIsingSquareRadialPatchHalf_eq] at hx hy
    all_goals
      apply Prod.ext <;> apply Fin.ext <;> omega



def fkIsingSquareRadialPatchWindowCarrier
    (n m baseI baseJ R : Nat) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (p : IsingLeapfrogBox R) : FKIsingSquareWiredCarrier n :=
  .dart
    (fkIsingSquareRadialPatchEdge n m hm
      ⟨baseI + p.1.1, by have := p.1.2; omega⟩
      ⟨baseJ + p.2.1, by have := p.2.2; omega⟩, .west)

theorem fkIsingSquareRadialPatchWindowCarrier_injective
    (n m baseI baseJ R : Nat) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    Function.Injective
      (fkIsingSquareRadialPatchWindowCarrier
        n m baseI baseJ R hm hfitI hfitJ) := by
  intro p q hpq
  have hedge :
      fkIsingSquareRadialPatchEdge n m hm
          ⟨baseI + p.1.1, by have := p.1.2; omega⟩
          ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ =
        fkIsingSquareRadialPatchEdge n m hm
          ⟨baseI + q.1.1, by have := q.1.2; omega⟩
          ⟨baseJ + q.2.1, by have := q.2.2; omega⟩ := by
    simpa [fkIsingSquareRadialPatchWindowCarrier] using hpq
  have hcell := fkIsingSquareRadialPatchEdge_injective n m hm
    (a₁ :=
      (⟨baseI + p.1.1, by have := p.1.2; omega⟩,
        ⟨baseJ + p.2.1, by have := p.2.2; omega⟩))
    (a₂ :=
      (⟨baseI + q.1.1, by have := q.1.2; omega⟩,
        ⟨baseJ + q.2.1, by have := q.2.2; omega⟩)) hedge
  apply Prod.ext <;> apply Fin.ext
  · have := congrArg (fun x : Fin m × Fin m ↦ x.1.1) hcell
    change baseI + p.1.1 = baseI + q.1.1 at this
    omega
  · have := congrArg (fun x : Fin m × Fin m ↦ x.2.1) hcell
    change baseJ + p.2.1 = baseJ + q.2.1 at this
    omega



def fkIsingSquareRadialPatchWindowCarrierEmbedding
    (n m baseI baseJ R : Nat) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogBox R ↪ FKIsingSquareWiredCarrier n where
  toFun := fkIsingSquareRadialPatchWindowCarrier
    n m baseI baseJ R hm hfitI hfitJ
  inj' := fkIsingSquareRadialPatchWindowCarrier_injective
    n m baseI baseJ R hm hfitI hfitJ




theorem fkIsingSquareRadialPatchWindowCarrier_normalized_normSq_le
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (p : IsingLeapfrogBox R) :
    Complex.normSq
        ((fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable
          mesh (fkIsingSquareRadialPatchWindowCarrier
            n m baseI baseJ R hm hfitI hfitJ p)) ≤
      Complex.normSq
        (fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ p /
          (Real.sqrt (2 * mesh) : Complex)) := by
  let i : Fin m := ⟨baseI + p.1.1, by have := p.1.2; omega⟩
  let j : Fin m := ⟨baseJ + p.2.1, by have := p.2.2; omega⟩
  let e := fkIsingSquareWiredDirectedTangent n hn
    (.dart (fkIsingSquareRadialPatchEdge n m hm i j, .west))
  let F := fkIsingSquareRadialPatchFullObservable n m hn hm i j
  have he : Complex.normSq e = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [e, fkIsingSquareWiredDirectedTangent, Complex.norm_exp]
  have hproj : Complex.normSq (isingProj e F) ≤ Complex.normSq F := by
    have hpair := isingProj_normSq_add_neg e F he
    have hnonneg := Complex.normSq_nonneg (isingProj (-e) F)
    linarith
  have hobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, .west)) =
        isingProj e F := by
    exact (fkIsingSquareRadialPatchFullObservable_projection
      n m hn hm i j .west).symm
  have hsqrt : 0 < Real.sqrt (2 * mesh) := Real.sqrt_pos.2 (by positivity)
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt, Real.sq_sqrt (by positivity)]
  change Complex.normSq
      ((fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, .west)) /
        (Real.sqrt (2 * mesh) : Complex)) ≤
    Complex.normSq (F / (Real.sqrt (2 * mesh) : Complex))
  rw [hobs, hnorm, hnorm]
  exact div_le_div_of_nonneg_right hproj (by positivity)



theorem fkIsingSquareRadialPatchWindowCarrier_average_normSq_le
    (n m baseI baseJ R r : Nat) (K Q base : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hr : 0 < r)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hmr : (m : Real) ≤ K * (r : Real))
    (hmR : (m : Real) ≤ Q * (R + 1 : Nat))
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hprimalLower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
    (hdualUpper : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
    (∑ a ∈ Finset.univ.map
          (fkIsingSquareRadialPatchWindowCarrierEmbedding
            n m baseI baseJ R hm hfitI hfitJ),
        Complex.normSq
          ((fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable
            (1 / (m : Real)) a)) ≤
      ((Finset.univ.map
          (fkIsingSquareRadialPatchWindowCarrierEmbedding
            n m baseI baseJ R hm hfitI hfitJ)).card : Real) *
        (16 * K * Q ^ 2) := by
  let window := fkIsingSquareRadialPatchWindowCarrierEmbedding
    n m baseI baseJ R hm hfitI hfitJ
  let abstract := fun a : FKIsingSquareWiredCarrier n ↦
    (fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable
      (1 / (m : Real)) a
  let concrete := fun p : IsingLeapfrogBox R ↦ abstract (window p)
  have hmesh : 0 < 1 / (m : Real) := by positivity
  have hpointwise (p : IsingLeapfrogBox R) :
      Complex.normSq (concrete p) ≤
        Complex.normSq
          (fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * (1 / (m : Real))) : Complex)) := by
    exact fkIsingSquareRadialPatchWindowCarrier_normalized_normSq_le
      n m baseI baseJ R (1 / (m : Real)) hn hm hfitI hfitJ hmesh p
  have hfull :=
    fkIsingSquareRadialPatchPhysicalNormalizedWindow_average_normSq_le
      n m baseI baseJ R r K Q base hn hm hm2 hr hfitI hfitJ hK hQ
      hmr hmR hdeep hprimalLower hdualUpper
  have haverage :
      (∑ p : IsingLeapfrogBox R, Complex.normSq (concrete p)) ≤
        (Fintype.card (IsingLeapfrogBox R) : Real) * (16 * K * Q ^ 2) :=
    (Finset.sum_le_sum fun p _ ↦ hpointwise p).trans hfull
  exact finiteWindow_average_normSq_le_of_embedding
    window concrete abstract (16 * K * Q ^ 2) (fun _ ↦ rfl) haverage

end

end StatMech.Universality
