/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeMarginalRank
import Mathlib.Analysis.Matrix.PosDef










open Finset

namespace StatMech.Ising

open StatMech.FrontierA
open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 800000 in



theorem ghsiSubsetMarginalMass_logSupermodular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {M P Q : Finset V} (hPM : P ⊆ M) (hQM : Q ⊆ M) :
    ghsiSubsetMarginalMass G K hf M P *
        ghsiSubsetMarginalMass G K hf M Q <=
      ghsiSubsetMarginalMass G K hf M (P ∩ Q) *
        ghsiSubsetMarginalMass G K hf M (P ∪ Q) := by
  let U := Mᶜ
  let f1 : Finset V -> Real := fun S => ghsiSubsetMass G K hf (P ∪ S)
  let f2 : Finset V -> Real := fun S => ghsiSubsetMass G K hf (Q ∪ S)
  let f3 : Finset V -> Real := fun S =>
    ghsiSubsetMass G K hf ((P ∩ Q) ∪ S)
  let f4 : Finset V -> Real := fun S =>
    ghsiSubsetMass G K hf ((P ∪ Q) ∪ S)
  have hfour : ∀ A, A ⊆ U -> ∀ B, B ⊆ U ->
      f1 A * f2 B <= f3 (A ∩ B) * f4 (A ∪ B) := by
    intro A hA B hB
    have hPB : Disjoint P B := by
      rw [disjoint_left]
      intro x hxP hxB
      exact (mem_compl.mp (hB hxB)) (hPM hxP)
    have hQA : Disjoint Q A := by
      rw [disjoint_left]
      intro x hxQ hxA
      exact (mem_compl.mp (hA hxA)) (hQM hxQ)
    have hinter : (P ∪ A) ∩ (Q ∪ B) = (P ∩ Q) ∪ (A ∩ B) := by
      ext x
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hxP | hxA, hxQ | hxB⟩
        · exact Or.inl ⟨hxP, hxQ⟩
        · exact False.elim ((disjoint_left.mp hPB) hxP hxB)
        · exact False.elim ((disjoint_left.mp hQA) hxQ hxA)
        · exact Or.inr ⟨hxA, hxB⟩
      · rintro (⟨hxP, hxQ⟩ | ⟨hxA, hxB⟩)
        · exact ⟨Or.inl hxP, Or.inl hxQ⟩
        · exact ⟨Or.inr hxA, Or.inr hxB⟩
    have hunion : (P ∪ A) ∪ (Q ∪ B) = (P ∪ Q) ∪ (A ∪ B) := by
      ext x
      simp only [mem_union]
      tauto
    have hlog :=
      ghsiSubsetMass_logSupermodular G K hf hK hhf (P ∪ A) (Q ∪ B)
    rw [hinter, hunion] at hlog
    simpa only [f1, f2, f3, f4, mul_comm] using hlog
  have hff := U.four_functions_theorem
    (f₁ := f1) (f₂ := f2) (f₃ := f3) (f₄ := f4)
    (by intro S; exact ghsiSubsetMass_nonneg G K hf _)
    (by intro S; exact ghsiSubsetMass_nonneg G K hf _)
    (by intro S; exact ghsiSubsetMass_nonneg G K hf _)
    (by intro S; exact ghsiSubsetMass_nonneg G K hf _)
    hfour (show U.powerset ⊆ U.powerset from Subset.rfl)
    (show U.powerset ⊆ U.powerset from Subset.rfl)
  simp only [powerset_infs_powerset_self, powerset_sups_powerset_self] at hff
  simpa only [ghsiSubsetMarginalMass, U, f1, f2, f3, f4] using hff



theorem threePoint_strongGraham_sum
    {x y z p q s r : Real}
    (hx : 2 * x * p * q <= (1 - x ^ 2) * r)
    (hy : 2 * y * p * s <= (1 - y ^ 2) * r)
    (hz : 2 * z * q * s <= (1 - z ^ 2) * r) :
    2 * (x * p * q + y * p * s + z * q * s) <=
      (3 - x ^ 2 - y ^ 2 - z ^ 2) * r := by
  nlinarith




theorem threePoint_square_correction_le
    {x y z a b c r : Real}
    (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hr : 0 <= r)
    (hdelta : 0 <= x * y * z + x * c + y * b + z * a - r)
    (hstrong :
      2 * (x * a * b + y * a * c + z * b * c) <=
        (3 - x ^ 2 - y ^ 2 - z ^ 2) *
          (x * y * z + x * c + y * b + z * a - r)) :
    2 * (x * a * b * (x * y * z + y * b + z * a) +
        y * a * c * (x * y * z + x * c + z * a) +
        z * b * c * (x * y * z + x * c + y * b)) <=
      3 * ((x * y * z + x * c + y * b + z * a) ^ 2 - r ^ 2) := by
  let u := x * y * z + x * c + y * b + z * a
  let q := x * a * b + y * a * c + z * b * c
  have hu : 0 <= u := by dsimp [u]; positivity
  have hq : 0 <= q := by dsimp [q]; positivity
  have hD : 3 - x ^ 2 - y ^ 2 - z ^ 2 <= 3 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hDdelta :
      (3 - x ^ 2 - y ^ 2 - z ^ 2) * (u - r) <= 3 * (u - r) :=
    mul_le_mul_of_nonneg_right hD (by simpa [u] using hdelta)
  have hqu : 2 * q * u <= 3 * (u - r) * u := by
    have hqdelta : 2 * q <= 3 * (u - r) := by
      dsimp [q, u] at hstrong ⊢
      linarith
    exact mul_le_mul_of_nonneg_right hqdelta hu
  have hlow :
      x * a * b * (x * y * z + y * b + z * a) +
          y * a * c * (x * y * z + x * c + z * a) +
          z * b * c * (x * y * z + x * c + y * b) <= q * u := by
    have h0 : x * y * z + y * b + z * a <= u := by
      dsimp [u]
      nlinarith [mul_nonneg hx hc]
    have h1 : x * y * z + x * c + z * a <= u := by
      dsimp [u]
      nlinarith [mul_nonneg hy hb]
    have h2 : x * y * z + x * c + y * b <= u := by
      dsimp [u]
      nlinarith [mul_nonneg hz ha]
    have h0' := mul_le_mul_of_nonneg_left h0
      (mul_nonneg (mul_nonneg hx ha) hb)
    have h1' := mul_le_mul_of_nonneg_left h1
      (mul_nonneg (mul_nonneg hy ha) hc)
    have h2' := mul_le_mul_of_nonneg_left h2
      (mul_nonneg (mul_nonneg hz hb) hc)
    dsimp [q]
    nlinarith
  have hur : u <= u + r := by linarith
  have hlast : 3 * (u - r) * u <= 3 * (u - r) * (u + r) := by
    exact mul_le_mul_of_nonneg_left hur
      (mul_nonneg (by norm_num) (by simpa [u] using hdelta))
  dsimp [u, q] at hlow hqu hlast ⊢
  nlinarith

theorem ghsiCovariance_comm
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real) (i j : V) :
    ghsiCovariance G K hf i j = ghsiCovariance G K hf j i := by
  unfold ghsiCovariance
  rw [show (fun s => spin s i * spin s j) =
      (fun s => spin s j * spin s i) by funext s; ring]
  ring

theorem ghsiUrsell3_cyclic
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real) (i j k : V) :
    ghsiUrsell3 G K hf i j k = ghsiUrsell3 G K hf j k i := by
  unfold ghsiUrsell3
  rw [show (fun s => spin s i * (spin s j * spin s k)) =
      (fun s => spin s j * (spin s k * spin s i)) by funext s; ring,
    show (fun s => spin s j * spin s k) =
      (fun s => spin s k * spin s j) by funext s; ring,
    show (fun s => spin s i * spin s j) =
      (fun s => spin s j * spin s i) by funext s; ring,
    show (fun s => spin s i * spin s k) =
      (fun s => spin s k * spin s i) by funext s; ring]
  ring

theorem ghsiUrsell3_swap_last
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real) (i j k : V) :
    ghsiUrsell3 G K hf i j k = ghsiUrsell3 G K hf i k j := by
  unfold ghsiUrsell3
  rw [show (fun s => spin s i * (spin s j * spin s k)) =
      (fun s => spin s i * (spin s k * spin s j)) by funext s; ring,
    show (fun s => spin s j * spin s k) =
      (fun s => spin s k * spin s j) by funext s; ring]
  ring



theorem grahamInhomThreePoint_strong_symmetric
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (i j k : V) :
    2 * (grahamInhomOne G K hf i *
          ghsiCovariance G K hf i j * ghsiCovariance G K hf i k +
        grahamInhomOne G K hf j *
          ghsiCovariance G K hf i j * ghsiCovariance G K hf j k +
        grahamInhomOne G K hf k *
          ghsiCovariance G K hf i k * ghsiCovariance G K hf j k) <=
      (3 - grahamInhomOne G K hf i ^ 2 -
          grahamInhomOne G K hf j ^ 2 -
          grahamInhomOne G K hf k ^ 2) *
        (-ghsiUrsell3 G K hf i j k) := by
  let mi := grahamInhomOne G K hf i
  let mj := grahamInhomOne G K hf j
  let mk := grahamInhomOne G K hf k
  let cij := ghsiCovariance G K hf i j
  let cik := ghsiCovariance G K hf i k
  let cjk := ghsiCovariance G K hf j k
  let R := -ghsiUrsell3 G K hf i j k
  have hi0 := grahamImprovedGHS_inhomogeneous_strong
    G K hf hK hhf j k i
  have hj0 := grahamImprovedGHS_inhomogeneous_strong
    G K hf hK hhf i k j
  have hk0 := grahamImprovedGHS_inhomogeneous_strong
    G K hf hK hhf i j k
  rw [ghsiCovariance_comm G K hf j i,
    ghsiCovariance_comm G K hf k i,
    ← ghsiUrsell3_cyclic G K hf i j k] at hi0
  rw [ghsiCovariance_comm G K hf k j,
    ← ghsiUrsell3_swap_last G K hf i j k] at hj0
  have hi : 2 * mi * cij * cik <= (1 - mi ^ 2) * R := by
    simpa [mi, cij, cik, R] using hi0
  have hj : 2 * mj * cij * cjk <= (1 - mj ^ 2) * R := by
    simpa [mj, cij, cjk, R] using hj0
  have hk : 2 * mk * cik * cjk <= (1 - mk ^ 2) * R := by
    simpa [mk, cik, cjk, R] using hk0
  simpa [mi, mj, mk, cij, cik, cjk, R] using
    threePoint_strongGraham_sum hi hj hk




theorem grahamInhomThreePoint_square_correction_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let mi := grahamInhomOne G K hf i
    let mj := grahamInhomOne G K hf j
    let mk := grahamInhomOne G K hf k
    let cij := ghsiCovariance G K hf i j
    let cik := ghsiCovariance G K hf i k
    let cjk := ghsiCovariance G K hf j k
    let r := expJ G.edgeFinset K hf
      (fun s => spin s i * (spin s j * spin s k))
    let u := mi * mj * mk + mi * cjk + mj * cik + mk * cij
    2 * (mi * cij * cik * (mi * mj * mk + mj * cik + mk * cij) +
        mj * cij * cjk * (mi * mj * mk + mi * cjk + mk * cij) +
        mk * cik * cjk * (mi * mj * mk + mi * cjk + mj * cik)) <=
      3 * (u ^ 2 - r ^ 2) := by
  dsimp
  have hmi := grahamInhomOne_nonneg G K hf hK hhf i
  have hmj := grahamInhomOne_nonneg G K hf hK hhf j
  have hmk := grahamInhomOne_nonneg G K hf hK hhf k
  have hcij := grahamInhomCov_nonneg G K hf hK hhf i j
  have hcik := grahamInhomCov_nonneg G K hf hK hhf i k
  have hcjk := grahamInhomCov_nonneg G K hf hK hhf j k
  have hr := grahamInhomThreePoint_nonneg G K hf hK hhf hij hik hjk
  have hdelta : 0 <=
      grahamInhomOne G K hf i * grahamInhomOne G K hf j *
          grahamInhomOne G K hf k +
        grahamInhomOne G K hf i * ghsiCovariance G K hf j k +
        grahamInhomOne G K hf j * ghsiCovariance G K hf i k +
        grahamInhomOne G K hf k * ghsiCovariance G K hf i j -
        expJ G.edgeFinset K hf
          (fun s => spin s i * (spin s j * spin s k)) := by
    have hghs := ghsiUrsell3_nonpos G K hf hK hhf i j k hij
    unfold ghsiUrsell3 at hghs
    unfold ghsiCovariance grahamInhomOne
    linarith
  have hstrong := grahamInhomThreePoint_strong_symmetric
    G K hf hK hhf i j k
  have hstrong' :
      2 * (grahamInhomOne G K hf i *
            ghsiCovariance G K hf i j * ghsiCovariance G K hf i k +
          grahamInhomOne G K hf j *
            ghsiCovariance G K hf i j * ghsiCovariance G K hf j k +
          grahamInhomOne G K hf k *
            ghsiCovariance G K hf i k * ghsiCovariance G K hf j k) <=
        (3 - grahamInhomOne G K hf i ^ 2 -
            grahamInhomOne G K hf j ^ 2 -
            grahamInhomOne G K hf k ^ 2) *
          (grahamInhomOne G K hf i * grahamInhomOne G K hf j *
              grahamInhomOne G K hf k +
            grahamInhomOne G K hf i * ghsiCovariance G K hf j k +
            grahamInhomOne G K hf j * ghsiCovariance G K hf i k +
            grahamInhomOne G K hf k * ghsiCovariance G K hf i j -
            expJ G.edgeFinset K hf
              (fun s => spin s i * (spin s j * spin s k))) := by
    rw [show -ghsiUrsell3 G K hf i j k =
        grahamInhomOne G K hf i * grahamInhomOne G K hf j *
            grahamInhomOne G K hf k +
          grahamInhomOne G K hf i * ghsiCovariance G K hf j k +
          grahamInhomOne G K hf j * ghsiCovariance G K hf i k +
          grahamInhomOne G K hf k * ghsiCovariance G K hf i j -
          expJ G.edgeFinset K hf
            (fun s => spin s i * (spin s j * spin s k)) by
      unfold ghsiUrsell3 ghsiCovariance grahamInhomOne
      ring] at hstrong
    exact hstrong
  exact threePoint_square_correction_le hmi hmj hmk hcij hcik hcjk hr
    hdelta hstrong'




theorem grahamInhom_pair_covariance_square_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (i j : V) :
    grahamInhomOne G K hf i * ghsiCovariance G K hf i j ^ 2 <=
      (1 - grahamInhomOne G K hf i ^ 2) *
        grahamInhomOne G K hf j * ghsiCovariance G K hf i j := by
  have h := grahamImprovedGHS_inhomogeneous_strong
    G K hf hK hhf j j i
  rw [ghsiCovariance_comm G K hf j i] at h
  unfold ghsiUrsell3 at h
  rw [show (fun s => spin s j * (spin s j * spin s i)) =
      (fun s => spin s i) by
        funext s
        calc
          spin s j * (spin s j * spin s i) =
              (spin s j * spin s j) * spin s i := by ring
          _ = spin s i := by rw [spin_sq]; ring,
    show (fun s => spin s j * spin s j) =
      (fun _ => (1 : Real)) by funext s; rw [spin_sq],
    show (fun s => spin s j * spin s i) =
      (fun s => spin s i * spin s j) by funext s; ring,
    expJ_one G K hf] at h
  unfold grahamInhomOne ghsiCovariance at h
  unfold grahamInhomOne ghsiCovariance
  nlinarith


theorem expJ_variance_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (f : ConfigSpace V -> Real) :
    0 <= expJ G.edgeFinset K hf (fun s => f s ^ 2) -
      expJ G.edgeFinset K hf f ^ 2 := by
  let Z := ZJ G.edgeFinset K hf
  let A := ∑ s : ConfigSpace V, f s ^ 2 * wJ G.edgeFinset K hf s
  let B := ∑ s : ConfigSpace V, f s * wJ G.edgeFinset K hf s
  have hsum : 0 <= ∑ s : ConfigSpace V, ∑ t : ConfigSpace V,
      wJ G.edgeFinset K hf s * wJ G.edgeFinset K hf t *
        (f s - f t) ^ 2 := by
    apply Finset.sum_nonneg
    intro s _
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg
      (mul_nonneg (wJ_nonneg G.edgeFinset K hf s)
        (wJ_nonneg G.edgeFinset K hf t)) (sq_nonneg _)
  have hfirst : (∑ s : ConfigSpace V, ∑ t : ConfigSpace V,
      wJ G.edgeFinset K hf s * wJ G.edgeFinset K hf t * f s ^ 2) =
      A * Z := by
    dsimp [A, Z, ZJ]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hlast : (∑ s : ConfigSpace V, ∑ t : ConfigSpace V,
      wJ G.edgeFinset K hf s * wJ G.edgeFinset K hf t * f t ^ 2) =
      A * Z := by
    rw [Finset.sum_comm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfirst
  have hcross : (∑ s : ConfigSpace V, ∑ t : ConfigSpace V,
      wJ G.edgeFinset K hf s * wJ G.edgeFinset K hf t * f s * f t) =
      B ^ 2 := by
    dsimp [B]
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hcross2 : (∑ s : ConfigSpace V, ∑ t : ConfigSpace V,
      wJ G.edgeFinset K hf s * wJ G.edgeFinset K hf t *
        (2 * f s * f t)) = 2 * B ^ 2 := by
    calc
      _ = 2 * (∑ s : ConfigSpace V, ∑ t : ConfigSpace V,
          wJ G.edgeFinset K hf s * wJ G.edgeFinset K hf t * f s * f t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = 2 * B ^ 2 := by rw [hcross]
  have hid : (∑ s : ConfigSpace V, ∑ t : ConfigSpace V,
      wJ G.edgeFinset K hf s * wJ G.edgeFinset K hf t *
        (f s - f t) ^ 2) = 2 * (A * Z - B ^ 2) := by
    simp_rw [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [hfirst, hcross2, hlast]
    ring
  have hnum : 0 <= A * Z - B ^ 2 := by nlinarith
  have hZ : 0 < Z := ZJ_pos _ _ _
  unfold expJ
  change 0 <= A / Z - (B / Z) ^ 2
  rw [show A / Z - (B / Z) ^ 2 = (A * Z - B ^ 2) / Z ^ 2 by
    field_simp [hZ.ne']]
  exact div_nonneg hnum (sq_nonneg Z)



theorem ghsiCovariance_quadratic_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf dir : V -> Real) :
    0 <= ∑ i : V, ∑ j : V,
      dir i * dir j * ghsiCovariance G K hf i j := by
  have hvar := expJ_variance_nonneg G K hf (ghsiDirSpin dir)
  rw [show (fun s => ghsiDirSpin dir s ^ 2) =
      (fun s => (1 : Real) * ghsiDirSpin dir s * ghsiDirSpin dir s) by
    funext s
    ring] at hvar
  rw [ghsi_expJ_mul_dirSpin_sq G K hf dir (fun _ => (1 : Real)),
    ghsi_expJ_dirSpin G K hf dir] at hvar
  simp only [one_mul] at hvar
  rw [sq, Finset.sum_mul] at hvar
  simp_rw [Finset.mul_sum] at hvar
  unfold ghsiCovariance
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hsecond :
      (∑ i : V, ∑ j : V,
        dir i * dir j *
          (expJ G.edgeFinset K hf (fun s => spin s i) *
            expJ G.edgeFinset K hf (fun s => spin s j))) =
      ∑ i : V, ∑ j : V,
        (dir i * expJ G.edgeFinset K hf (fun s => spin s i)) *
          (dir j * expJ G.edgeFinset K hf (fun s => spin s j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsecond]
  exact hvar

set_option maxHeartbeats 800000 in



theorem fourBridge_zero_base_identity
    (m0 m1 m2 m3 c01 c02 c03 c12 c13 c23 : Real) :
    let p01 := m0 * m1 + c01
    let p02 := m0 * m2 + c02
    let p03 := m0 * m3 + c03
    let p12 := m1 * m2 + c12
    let p13 := m1 * m3 + c13
    let p23 := m2 * m3 + c23
    let u012 := m0 * p12 + m1 * p02 + m2 * p01 - 2 * m0 * m1 * m2
    let u013 := m0 * p13 + m1 * p03 + m3 * p01 - 2 * m0 * m1 * m3
    let u023 := m0 * p23 + m2 * p03 + m3 * p02 - 2 * m0 * m2 * m3
    let u123 := m1 * p23 + m2 * p13 + m3 * p12 - 2 * m1 * m2 * m3
    let a := m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2
    let b := p01 ^ 2 + p02 ^ 2 + p03 ^ 2 +
      p12 ^ 2 + p13 ^ 2 + p23 ^ 2
    a + 3 * a * b - a ^ 3 -
        3 * (u012 ^ 2 + u013 ^ 2 + u023 ^ 2 + u123 ^ 2) =
      m0 ^ 2 * (1 - m0 ^ 4) +
        6 * m0 ^ 3 * (c01 * m1 + c02 * m2 + c03 * m3) +
        6 * (c01 ^ 2 * m1 ^ 2 + c02 ^ 2 * m2 ^ 2 +
          c03 ^ 2 * m3 ^ 2) -
        3 * (c01 * m1 + c02 * m2 + c03 * m3) ^ 2 +
      m1 ^ 2 * (1 - m1 ^ 4) +
        6 * m1 ^ 3 * (c01 * m0 + c12 * m2 + c13 * m3) +
        6 * (c01 ^ 2 * m0 ^ 2 + c12 ^ 2 * m2 ^ 2 +
          c13 ^ 2 * m3 ^ 2) -
        3 * (c01 * m0 + c12 * m2 + c13 * m3) ^ 2 +
      m2 ^ 2 * (1 - m2 ^ 4) +
        6 * m2 ^ 3 * (c02 * m0 + c12 * m1 + c23 * m3) +
        6 * (c02 ^ 2 * m0 ^ 2 + c12 ^ 2 * m1 ^ 2 +
          c23 ^ 2 * m3 ^ 2) -
        3 * (c02 * m0 + c12 * m1 + c23 * m3) ^ 2 +
      m3 ^ 2 * (1 - m3 ^ 4) +
        6 * m3 ^ 3 * (c03 * m0 + c13 * m1 + c23 * m2) +
        6 * (c03 ^ 2 * m0 ^ 2 + c13 ^ 2 * m1 ^ 2 +
          c23 ^ 2 * m2 ^ 2) -
        3 * (c03 * m0 + c13 * m1 + c23 * m2) ^ 2 := by
  dsimp
  ring




theorem covariancePSD_row_contraction
    {m x y z a b c d e f : Real}
    (hpsd : forall q0 q1 q2 q3 : Real,
      0 <= (1 - m ^ 2) * q0 ^ 2 + (1 - x ^ 2) * q1 ^ 2 +
        (1 - y ^ 2) * q2 ^ 2 + (1 - z ^ 2) * q3 ^ 2 +
        2 * a * q0 * q1 + 2 * b * q0 * q2 + 2 * c * q0 * q3 +
        2 * d * q1 * q2 + 2 * e * q1 * q3 + 2 * f * q2 * q3) :
    let s := a * x + b * y + c * z
    (1 + m ^ 2) * s ^ 2 <=
      (1 - x ^ 2) * x ^ 2 + (1 - y ^ 2) * y ^ 2 +
        (1 - z ^ 2) * z ^ 2 + 2 * d * x * y +
        2 * e * x * z + 2 * f * y * z := by
  dsimp
  have h := hpsd (-(a * x + b * y + c * z)) x y z
  nlinarith




theorem covariancePSD_three_det_nonneg
    {x y z a b c : Real}
    (hpsd : forall q0 q1 q2 : Real,
      0 <= (1 - x ^ 2) * q0 ^ 2 + (1 - y ^ 2) * q1 ^ 2 +
        (1 - z ^ 2) * q2 ^ 2 + 2 * a * q0 * q1 +
        2 * b * q0 * q2 + 2 * c * q1 * q2) :
    0 <= (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) +
      2 * a * b * c - (1 - x ^ 2) * c ^ 2 -
      (1 - y ^ 2) * b ^ 2 - (1 - z ^ 2) * a ^ 2 := by
  let M : Matrix (Fin 3) (Fin 3) Real := !![
    1 - x ^ 2, a, b;
    a, 1 - y ^ 2, c;
    b, c, 1 - z ^ 2]
  have hM : M.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [M]
    · intro q
      have h := hpsd (q 0) (q 1) (q 2)
      simp [M, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      nlinarith
  have hdet := hM.det_nonneg
  simp [M, Matrix.det_fin_three] at hdet
  nlinarith



theorem twoVar_cubic_edge_nonneg
    {a b : Real} (ha0 : 0 <= a) (hb0 : 0 <= b) :
    0 <= 1 + 6 * a * b * (a + b) - 9 * a * b := by
  by_cases hs : 3 / 2 <= a + b
  · have hab : 0 <= a * b := mul_nonneg ha0 hb0
    have hk : 0 <= 6 * (a + b) - 9 := by linarith
    nlinarith [mul_nonneg hab hk]
  · have hs0 : 0 <= a + b := by linarith
    have hs1 : a + b <= 3 / 2 := le_of_not_ge hs
    have hab : 4 * a * b <= (a + b) ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    have hk : 6 * (a + b) - 9 <= 0 := by linarith
    have hmul :
        (6 * (a + b) - 9) * (a + b) ^ 2 <=
          (6 * (a + b) - 9) * (4 * a * b) :=
      mul_le_mul_of_nonpos_left hab hk
    have hfactor : 0 <=
        (a + b - 1) ^ 2 * (6 * (a + b) + 3) := by positivity
    nlinarith [show
      4 + (6 * (a + b) - 9) * (a + b) ^ 2 =
        1 + (a + b - 1) ^ 2 * (6 * (a + b) + 3) by ring]


theorem twoVar_cubic_edge_linear_nonneg
    {a b : Real} (ha0 : 0 <= a) (hb0 : 0 <= b) :
    0 <= a + b + 6 * a * b * (a + b) - 9 * a * b := by
  have hs0 : 0 <= a + b := by linarith
  have hab : 4 * a * b <= (a + b) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  by_cases hs : 3 / 2 <= a + b
  · have hk : 0 <= 6 * (a + b) - 9 := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha0 hb0) hk]
  · have hs1 : a + b <= 3 / 2 := le_of_not_ge hs
    have hk : 6 * (a + b) - 9 <= 0 := by linarith
    have hmul :
        (6 * (a + b) - 9) * (a + b) ^ 2 <=
          (6 * (a + b) - 9) * (4 * a * b) :=
      mul_le_mul_of_nonpos_left hab hk
    have hquad : 0 <= 6 * (a + b - 3 / 4) ^ 2 + 5 / 8 := by positivity
    nlinarith [show
      6 * (a + b) ^ 2 - 9 * (a + b) + 4 =
        6 * (a + b - 3 / 4) ^ 2 + 5 / 8 by ring,
      mul_nonneg hs0 hquad]


theorem twoVar_cubic_edge_three_quarters_nonneg
    {a b : Real} (ha0 : 0 <= a) (hb0 : 0 <= b) :
    0 <= 3 / 4 + 6 * a * b * (a + b) - 9 * a * b := by
  have hab : 4 * a * b <= (a + b) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  by_cases hs : 3 / 2 <= a + b
  · have hk : 0 <= 6 * (a + b) - 9 := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha0 hb0) hk]
  · have hk : 6 * (a + b) - 9 <= 0 := by linarith
    have hmul :
        (6 * (a + b) - 9) * (a + b) ^ 2 <=
          (6 * (a + b) - 9) * (4 * a * b) :=
      mul_le_mul_of_nonpos_left hab hk
    have hfactor : 0 <=
        (a + b - 1) ^ 2 * (6 * (a + b) + 3) := by positivity
    nlinarith [show
      3 + (6 * (a + b) - 9) * (a + b) ^ 2 =
        (a + b - 1) ^ 2 * (6 * (a + b) + 3) by ring]


theorem twoVar_cubic_edge_left_linear_nonneg
    {a b : Real} (ha0 : 0 <= a) (hb0 : 0 <= b) :
    0 <= 27 / 8 * a + 6 * a * b * (a + b) - 9 * a * b := by
  have hquad : 0 <= 6 * (b - 3 / 4) ^ 2 := by positivity
  nlinarith [mul_nonneg ha0 hquad, mul_nonneg (mul_nonneg ha0 hb0) ha0]


theorem twoVar_cubic_edge_sum_linear_nonneg
    {a b : Real} (ha0 : 0 <= a) (hb0 : 0 <= b) :
    0 <= 27 / 32 * (a + b) + 6 * a * b * (a + b) - 9 * a * b := by
  have hs0 : 0 <= a + b := by linarith
  have hab : 4 * a * b <= (a + b) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  by_cases hs : 3 / 2 <= a + b
  · have hk : 0 <= 6 * (a + b) - 9 := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha0 hb0) hk]
  · have hk : 6 * (a + b) - 9 <= 0 := by linarith
    have hmul :
        (6 * (a + b) - 9) * (a + b) ^ 2 <=
          (6 * (a + b) - 9) * (4 * a * b) :=
      mul_le_mul_of_nonpos_left hab hk
    have hfactor : 0 <= 48 * (a + b - 3 / 4) ^ 2 := by positivity
    nlinarith [show
      27 + 8 * (6 * (a + b) - 9) * (a + b) =
        48 * (a + b - 3 / 4) ^ 2 by ring,
      mul_nonneg hs0 hfactor]



theorem twoVar_cubic_edge_min_cost
    {a b : Real} (ha0 : 0 <= a) (hb0 : 0 <= b) :
    -(min (3 / 4)
        (min (27 / 8 * min a b) (27 / 32 * (a + b)))) <=
      6 * a * b * (a + b) - 9 * a * b := by
  have hconst := twoVar_cubic_edge_three_quarters_nonneg ha0 hb0
  have hleft := twoVar_cubic_edge_left_linear_nonneg ha0 hb0
  have hright := twoVar_cubic_edge_left_linear_nonneg hb0 ha0
  have hsum := twoVar_cubic_edge_sum_linear_nonneg ha0 hb0
  have hminSide :
      -(27 / 8 * min a b) <= 6 * a * b * (a + b) - 9 * a * b := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab]
      nlinarith [hleft]
    · rw [min_eq_right hba]
      nlinarith [hright]
  let c0 : Real := 3 / 4
  let c1 : Real := 27 / 8 * min a b
  let c2 : Real := 27 / 32 * (a + b)
  by_cases h0 : c0 <= min c1 c2
  · rw [min_eq_left h0]
    dsimp [c0]
    nlinarith [hconst]
  · have h10 : min c1 c2 <= c0 := le_of_not_ge h0
    rw [min_eq_right h10]
    rcases le_total c1 c2 with h12 | h21
    · rw [min_eq_left h12]
      dsimp [c1]
      nlinarith [hminSide]
    · rw [min_eq_right h21]
      dsimp [c2]
      nlinarith [hsum]



theorem pair_covariance_square_bound_cancel
    {x y a : Real} (hx0 : 0 <= x) (hy0 : 0 <= y)
    (hx1 : x <= 1) (ha : 0 <= a)
    (h : x * a ^ 2 <= (1 - x ^ 2) * y * a) :
    x * a <= (1 - x ^ 2) * y := by
  have hv : 0 <= 1 - x ^ 2 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  by_cases ha0 : a = 0
  · subst a
    simpa using mul_nonneg hv hy0
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h' : a * (x * a) <= a * ((1 - x ^ 2) * y) := by
      nlinarith
    exact le_of_mul_le_mul_left h' hap

set_option maxHeartbeats 800000 in



theorem fourBridge_triangle_cross_remainder_nonneg_of_sqsum_ge_one
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
    (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
    (hS : 1 <= x ^ 2 + y ^ 2 + z ^ 2) :
    9 * (a * b * y * z + a * c * x * z + b * c * x * y) <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      6 * x * a * b * (x * y * z + y * b + z * a) +
      6 * y * a * c * (x * y * z + x * c + z * a) +
      6 * z * b * c * (x * y * z + x * c + y * b) := by
  have gxa := pair_covariance_square_bound_cancel hx0 hy0 hx1 ha hxa
  have gya := pair_covariance_square_bound_cancel hy0 hx0 hy1 ha hya
  have gxb := pair_covariance_square_bound_cancel hx0 hz0 hx1 hb hxb
  have gzb := pair_covariance_square_bound_cancel hz0 hx0 hz1 hb hzb
  have gyc := pair_covariance_square_bound_cancel hy0 hz0 hy1 hc hyc
  have gzc := pair_covariance_square_bound_cancel hz0 hy0 hz1 hc hzc
  have hconstraint : 0 <=
      9 / 2 * (b * z * ((1 - y ^ 2) * x - y * a) +
        a * y * ((1 - z ^ 2) * x - z * b)) +
      9 / 2 * (c * z * ((1 - x ^ 2) * y - x * a) +
        a * x * ((1 - z ^ 2) * y - z * c)) +
      9 / 2 * (c * y * ((1 - x ^ 2) * z - x * b) +
        b * x * ((1 - y ^ 2) * z - y * c)) := by
    positivity
  have hx4 : 0 <= 1 - x ^ 4 := by
    have hx2 : x ^ 2 <= 1 := by
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2)
      (add_nonneg (sq_nonneg x) zero_le_one)]
  have hy4 : 0 <= 1 - y ^ 4 := by
    have hy2 : y ^ 2 <= 1 := by
      nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hy2)
      (add_nonneg (sq_nonneg y) zero_le_one)]
  have hz4 : 0 <= 1 - z ^ 4 := by
    have hz2 : z ^ 2 <= 1 := by
      nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hz2)
      (add_nonneg (sq_nonneg z) zero_le_one)]
  have hvertex : 0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) := by positivity
  have hlinear : 0 <=
      9 * (x ^ 2 + y ^ 2 + z ^ 2 - 1) *
        (a * x * y + b * x * z + c * y * z) := by positivity
  have hcorrection : 0 <=
      6 * x * a * b * (x * y * z + y * b + z * a) +
        6 * y * a * c * (x * y * z + x * c + z * a) +
        6 * z * b * c * (x * y * z + x * c + y * b) := by
    positivity
  have hid :
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
          z ^ 2 * (1 - z ^ 4) +
        9 * (a * x * y * (x ^ 2 + y ^ 2) +
          b * x * z * (x ^ 2 + z ^ 2) +
          c * y * z * (y ^ 2 + z ^ 2)) +
        6 * x * a * b * (x * y * z + y * b + z * a) +
        6 * y * a * c * (x * y * z + x * c + z * a) +
        6 * z * b * c * (x * y * z + x * c + y * b) -
        9 * (a * b * y * z + a * c * x * z + b * c * x * y) =
      (9 / 2 * (b * z * ((1 - y ^ 2) * x - y * a) +
          a * y * ((1 - z ^ 2) * x - z * b)) +
        9 / 2 * (c * z * ((1 - x ^ 2) * y - x * a) +
          a * x * ((1 - z ^ 2) * y - z * c)) +
        9 / 2 * (c * y * ((1 - x ^ 2) * z - x * b) +
          b * x * ((1 - y ^ 2) * z - y * c))) +
      (x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4)) +
      9 * (x ^ 2 + y ^ 2 + z ^ 2 - 1) *
        (a * x * y + b * x * z + c * y * z) +
      (6 * x * a * b * (x * y * z + y * b + z * a) +
        6 * y * a * c * (x * y * z + x * c + z * a) +
        6 * z * b * c * (x * y * z + x * c + y * b)) := by
    ring
  nlinarith [hid]



theorem fourBridge_triangle_correct_nonneg_of_sqsum_ge_one
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
    (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
    (hS : 1 <= x ^ 2 + y ^ 2 + z ^ 2) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) +
        b ^ 2 * (x ^ 2 + z ^ 2) +
        c ^ 2 * (y ^ 2 + z ^ 2)) +
      (-18 * a * b * y * z +
        6 * x * a * b * (x * y * z + y * b + z * a)) +
      (-18 * a * c * x * z +
        6 * y * a * c * (x * y * z + x * c + z * a)) +
      (-18 * b * c * x * y +
        6 * z * b * c * (x * y * z + x * c + y * b)) := by
  have hcross :=
    fourBridge_triangle_cross_remainder_nonneg_of_sqsum_ge_one
      hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc
      hxa hya hxb hzb hyc hzc hS
  have hsquares : 0 <=
      9 / 2 * ((y * a - z * b) ^ 2 + (x * a - z * c) ^ 2 +
        (x * b - y * c) ^ 2) := by positivity
  have hid :
      a ^ 2 * (x ^ 2 + y ^ 2) +
          b ^ 2 * (x ^ 2 + z ^ 2) +
          c ^ 2 * (y ^ 2 + z ^ 2) -
          2 * (a * b * y * z + a * c * x * z + b * c * x * y) =
        (y * a - z * b) ^ 2 + (x * a - z * c) ^ 2 +
          (x * b - y * c) ^ 2 := by
    ring
  nlinarith [hid]



theorem fourBridge_triangle_correct_nonneg_of_first_eq_zero
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hx : x = 0) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) +
        b ^ 2 * (x ^ 2 + z ^ 2) +
        c ^ 2 * (y ^ 2 + z ^ 2)) +
      (-18 * a * b * y * z +
        6 * x * a * b * (x * y * z + y * b + z * a)) +
      (-18 * a * c * x * z +
        6 * y * a * c * (x * y * z + x * c + z * a)) +
      (-18 * b * c * x * y +
        6 * z * b * c * (x * y * z + x * c + y * b)) := by
  subst x
  have hya0 : y * a ^ 2 = 0 := by
    apply le_antisymm
    · simpa using hya
    · positivity
  have hzb0 : z * b ^ 2 = 0 := by
    apply le_antisymm
    · simpa using hzb
    · positivity
  rcases mul_eq_zero.mp hya0 with hy | ha2
  · subst y
    rcases mul_eq_zero.mp hzb0 with hz | hb2
    · subst z
      norm_num
    · have hb0 : b = 0 := (sq_eq_zero_iff).mp hb2
      subst b
      have hz4 : 0 <= 1 - z ^ 4 := by
        nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1),
          mul_nonneg (sub_nonneg.mpr (show z ^ 2 <= 1 by
            nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]))
            (add_nonneg (sq_nonneg z) zero_le_one)]
      nlinarith [mul_nonneg (sq_nonneg z) hz4,
        mul_nonneg (sq_nonneg c) (sq_nonneg z)]
  · have ha0 : a = 0 := (sq_eq_zero_iff).mp ha2
    subst a
    rcases mul_eq_zero.mp hzb0 with hz | hb2
    · subst z
      have hy4 : 0 <= 1 - y ^ 4 := by
        have hy2 : y ^ 2 <= 1 := by
          nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hy2)
          (add_nonneg (sq_nonneg y) zero_le_one)]
      nlinarith [mul_nonneg (sq_nonneg y) hy4,
        mul_nonneg (sq_nonneg c) (sq_nonneg y)]
    · have hb0 : b = 0 := (sq_eq_zero_iff).mp hb2
      subst b
      have hy2 : y ^ 2 <= 1 := by
        nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
      have hz2 : z ^ 2 <= 1 := by
        nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
      have hy4 : 0 <= 1 - y ^ 4 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hy2)
          (add_nonneg (sq_nonneg y) zero_le_one)]
      have hz4 : 0 <= 1 - z ^ 4 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hz2)
          (add_nonneg (sq_nonneg z) zero_le_one)]
      positivity



theorem fourBridge_triangle_correct_nonneg_of_any_eq_zero
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
    (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
    (hzero : x = 0 ∨ y = 0 ∨ z = 0) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) +
        b ^ 2 * (x ^ 2 + z ^ 2) +
        c ^ 2 * (y ^ 2 + z ^ 2)) +
      (-18 * a * b * y * z +
        6 * x * a * b * (x * y * z + y * b + z * a)) +
      (-18 * a * c * x * z +
        6 * y * a * c * (x * y * z + x * c + z * a)) +
      (-18 * b * c * x * y +
        6 * z * b * c * (x * y * z + x * c + y * b)) := by
  rcases hzero with hx | hy | hz
  · exact fourBridge_triangle_correct_nonneg_of_first_eq_zero
      hx0 hy0 hz0 hy1 hz1 ha hb hc hya hzb hx
  · have h := fourBridge_triangle_correct_nonneg_of_first_eq_zero
      hy0 hx0 hz0 hx1 hz1 ha hc hb hxa hzc hy
    convert h using 1 <;> ring
  · have h := fourBridge_triangle_correct_nonneg_of_first_eq_zero
      hz0 hx0 hy0 hx1 hy1 hb hc ha hxb hyc hz
    convert h using 1 <;> ring


set_option maxHeartbeats 800000 in




theorem fourBridge_triangle_nonneg
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      9 * (a ^ 2 * (x ^ 2 + y ^ 2) +
        b ^ 2 * (x ^ 2 + z ^ 2) +
        c ^ 2 * (y ^ 2 + z ^ 2)) +
      (-18 * a * b * y * z +
        6 * x * a * b * (x * y * z + y * b + z * a)) +
      (-18 * a * c * x * z +
        6 * y * a * c * (x * y * z + x * c + z * a)) +
      (-18 * b * c * x * y +
        6 * z * b * c * (x * y * z + x * c + y * b)) := by
  have hx2 : x ^ 2 <= 1 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hy2 : y ^ 2 <= 1 := by
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  have hz2 : z ^ 2 <= 1 := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  have hx4 : 0 <= 1 - x ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2)
      (add_nonneg (sq_nonneg x) zero_le_one)]
  have hy4 : 0 <= 1 - y ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy2)
      (add_nonneg (sq_nonneg y) zero_le_one)]
  have hz4 : 0 <= 1 - z ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz2)
      (add_nonneg (sq_nonneg z) zero_le_one)]
  have hvertex : 0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) := by positivity
  have hedge_id :
      a ^ 2 * (x ^ 2 + y ^ 2) +
          b ^ 2 * (x ^ 2 + z ^ 2) +
          c ^ 2 * (y ^ 2 + z ^ 2) -
          2 * (a * b * y * z + a * c * x * z + b * c * x * y) =
        (y * a - z * b) ^ 2 + (x * a - z * c) ^ 2 +
          (x * b - y * c) ^ 2 := by
    ring
  have hlinear : 0 <=
      a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2) := by
    positivity
  have hsquares : 0 <=
      (y * a - z * b) ^ 2 + (x * a - z * c) ^ 2 +
        (x * b - y * c) ^ 2 := by positivity
  have hedge : 0 <=
      a * x * y * (x ^ 2 + y ^ 2) +
          b * x * z * (x ^ 2 + z ^ 2) +
          c * y * z * (y ^ 2 + z ^ 2) +
        (a ^ 2 * (x ^ 2 + y ^ 2) +
          b ^ 2 * (x ^ 2 + z ^ 2) +
          c ^ 2 * (y ^ 2 + z ^ 2)) -
        2 * (a * b * y * z + a * c * x * z + b * c * x * y) := by
    nlinarith [hedge_id]
  have hcorrection : 0 <=
      6 * x * a * b * (x * y * z + y * b + z * a) +
        6 * y * a * c * (x * y * z + x * c + z * a) +
        6 * z * b * c * (x * y * z + x * c + y * b) := by
    positivity
  nlinarith

set_option maxHeartbeats 1600000 in



theorem fourBridge_Ursell_correction_nonneg_of_face_sqsum_ge_one
    {m0 m1 m2 m3 c01 c02 c03 c12 c13 c23 : Real}
    (hm00 : 0 <= m0) (hm10 : 0 <= m1) (hm20 : 0 <= m2) (hm30 : 0 <= m3)
    (hm01 : m0 <= 1) (hm11 : m1 <= 1) (hm21 : m2 <= 1) (hm31 : m3 <= 1)
    (hc01 : 0 <= c01) (hc02 : 0 <= c02) (hc03 : 0 <= c03)
    (hc12 : 0 <= c12) (hc13 : 0 <= c13) (hc23 : 0 <= c23)
    (h001 : m0 * c01 ^ 2 <= (1 - m0 ^ 2) * m1 * c01)
    (h101 : m1 * c01 ^ 2 <= (1 - m1 ^ 2) * m0 * c01)
    (h002 : m0 * c02 ^ 2 <= (1 - m0 ^ 2) * m2 * c02)
    (h202 : m2 * c02 ^ 2 <= (1 - m2 ^ 2) * m0 * c02)
    (h003 : m0 * c03 ^ 2 <= (1 - m0 ^ 2) * m3 * c03)
    (h303 : m3 * c03 ^ 2 <= (1 - m3 ^ 2) * m0 * c03)
    (h112 : m1 * c12 ^ 2 <= (1 - m1 ^ 2) * m2 * c12)
    (h212 : m2 * c12 ^ 2 <= (1 - m2 ^ 2) * m1 * c12)
    (h113 : m1 * c13 ^ 2 <= (1 - m1 ^ 2) * m3 * c13)
    (h313 : m3 * c13 ^ 2 <= (1 - m3 ^ 2) * m1 * c13)
    (h223 : m2 * c23 ^ 2 <= (1 - m2 ^ 2) * m3 * c23)
    (h323 : m3 * c23 ^ 2 <= (1 - m3 ^ 2) * m2 * c23)
    (h012S : 1 <= m0 ^ 2 + m1 ^ 2 + m2 ^ 2)
    (h013S : 1 <= m0 ^ 2 + m1 ^ 2 + m3 ^ 2)
    (h023S : 1 <= m0 ^ 2 + m2 ^ 2 + m3 ^ 2)
    (h123S : 1 <= m1 ^ 2 + m2 ^ 2 + m3 ^ 2) :
    let p01 := m0 * m1 + c01
    let p02 := m0 * m2 + c02
    let p03 := m0 * m3 + c03
    let p12 := m1 * m2 + c12
    let p13 := m1 * m3 + c13
    let p23 := m2 * m3 + c23
    let u012 := m0 * p12 + m1 * p02 + m2 * p01 - 2 * m0 * m1 * m2
    let u013 := m0 * p13 + m1 * p03 + m3 * p01 - 2 * m0 * m1 * m3
    let u023 := m0 * p23 + m2 * p03 + m3 * p02 - 2 * m0 * m2 * m3
    let u123 := m1 * p23 + m2 * p13 + m3 * p12 - 2 * m1 * m2 * m3
    let aa := m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2
    let bb := p01 ^ 2 + p02 ^ 2 + p03 ^ 2 +
      p12 ^ 2 + p13 ^ 2 + p23 ^ 2
    0 <= aa + 3 * aa * bb - aa ^ 3 -
        3 * (u012 ^ 2 + u013 ^ 2 + u023 ^ 2 + u123 ^ 2) +
      2 * (m0 * c01 * c02 *
          (m0 * m1 * m2 + m1 * c02 + m2 * c01) +
        m1 * c01 * c12 *
          (m0 * m1 * m2 + m0 * c12 + m2 * c01) +
        m2 * c02 * c12 *
          (m0 * m1 * m2 + m0 * c12 + m1 * c02)) +
      2 * (m0 * c01 * c03 *
          (m0 * m1 * m3 + m1 * c03 + m3 * c01) +
        m1 * c01 * c13 *
          (m0 * m1 * m3 + m0 * c13 + m3 * c01) +
        m3 * c03 * c13 *
          (m0 * m1 * m3 + m0 * c13 + m1 * c03)) +
      2 * (m0 * c02 * c03 *
          (m0 * m2 * m3 + m2 * c03 + m3 * c02) +
        m2 * c02 * c23 *
          (m0 * m2 * m3 + m0 * c23 + m3 * c02) +
        m3 * c03 * c23 *
          (m0 * m2 * m3 + m0 * c23 + m2 * c03)) +
      2 * (m1 * c12 * c13 *
          (m1 * m2 * m3 + m2 * c13 + m3 * c12) +
        m2 * c12 * c23 *
          (m1 * m2 * m3 + m1 * c23 + m3 * c12) +
        m3 * c13 * c23 *
          (m1 * m2 * m3 + m1 * c23 + m2 * c13)) := by
  have h012 := fourBridge_triangle_correct_nonneg_of_sqsum_ge_one
    hm00 hm10 hm20 hm01 hm11 hm21 hc01 hc02 hc12
    h001 h101 h002 h202 h112 h212 h012S
  have h013 := fourBridge_triangle_correct_nonneg_of_sqsum_ge_one
    hm00 hm10 hm30 hm01 hm11 hm31 hc01 hc03 hc13
    h001 h101 h003 h303 h113 h313 h013S
  have h023 := fourBridge_triangle_correct_nonneg_of_sqsum_ge_one
    hm00 hm20 hm30 hm01 hm21 hm31 hc02 hc03 hc23
    h002 h202 h003 h303 h223 h323 h023S
  have h123 := fourBridge_triangle_correct_nonneg_of_sqsum_ge_one
    hm10 hm20 hm30 hm11 hm21 hm31 hc12 hc13 hc23
    h112 h212 h113 h313 h223 h323 h123S
  have hbase := fourBridge_zero_base_identity
    m0 m1 m2 m3 c01 c02 c03 c12 c13 c23
  dsimp at hbase ⊢
  rw [hbase]
  nlinarith

set_option maxHeartbeats 6000000 in




theorem fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos_of_face_sqsum_ge_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h012S : 1 <= grahamInhomOne G K hf w ^ 2 +
      grahamInhomOne G K hf x ^ 2 + grahamInhomOne G K hf y ^ 2)
    (h013S : 1 <= grahamInhomOne G K hf w ^ 2 +
      grahamInhomOne G K hf x ^ 2 + grahamInhomOne G K hf z ^ 2)
    (h023S : 1 <= grahamInhomOne G K hf w ^ 2 +
      grahamInhomOne G K hf y ^ 2 + grahamInhomOne G K hf z ^ 2)
    (h123S : 1 <= grahamInhomOne G K hf x ^ 2 +
      grahamInhomOne G K hf y ^ 2 + grahamInhomOne G K hf z ^ 2) :
    fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G K hf w x y z)
        (fourBridgeTwoCoeff G K hf w x y z)
        (fourBridgeThreeCoeff G K hf w x y z)
        (fourBridgeFourCoeff G K hf w x y z) 0 <= 0 := by
  let m0 := grahamInhomOne G K hf w
  let m1 := grahamInhomOne G K hf x
  let m2 := grahamInhomOne G K hf y
  let m3 := grahamInhomOne G K hf z
  let c01 := ghsiCovariance G K hf w x
  let c02 := ghsiCovariance G K hf w y
  let c03 := ghsiCovariance G K hf w z
  let c12 := ghsiCovariance G K hf x y
  let c13 := ghsiCovariance G K hf x z
  let c23 := ghsiCovariance G K hf y z
  have hm00 := grahamInhomOne_nonneg G K hf hK hhf w
  have hm10 := grahamInhomOne_nonneg G K hf hK hhf x
  have hm20 := grahamInhomOne_nonneg G K hf hK hhf y
  have hm30 := grahamInhomOne_nonneg G K hf hK hhf z
  have hm01 := grahamInhomOne_le_one G K hf w
  have hm11 := grahamInhomOne_le_one G K hf x
  have hm21 := grahamInhomOne_le_one G K hf y
  have hm31 := grahamInhomOne_le_one G K hf z
  have hc01 := grahamInhomCov_nonneg G K hf hK hhf w x
  have hc02 := grahamInhomCov_nonneg G K hf hK hhf w y
  have hc03 := grahamInhomCov_nonneg G K hf hK hhf w z
  have hc12 := grahamInhomCov_nonneg G K hf hK hhf x y
  have hc13 := grahamInhomCov_nonneg G K hf hK hhf x z
  have hc23 := grahamInhomCov_nonneg G K hf hK hhf y z
  have h001 := grahamInhom_pair_covariance_square_le G K hf hK hhf w x
  have h101 := grahamInhom_pair_covariance_square_le G K hf hK hhf x w
  have h002 := grahamInhom_pair_covariance_square_le G K hf hK hhf w y
  have h202 := grahamInhom_pair_covariance_square_le G K hf hK hhf y w
  have h003 := grahamInhom_pair_covariance_square_le G K hf hK hhf w z
  have h303 := grahamInhom_pair_covariance_square_le G K hf hK hhf z w
  have h112 := grahamInhom_pair_covariance_square_le G K hf hK hhf x y
  have h212 := grahamInhom_pair_covariance_square_le G K hf hK hhf y x
  have h113 := grahamInhom_pair_covariance_square_le G K hf hK hhf x z
  have h313 := grahamInhom_pair_covariance_square_le G K hf hK hhf z x
  have h223 := grahamInhom_pair_covariance_square_le G K hf hK hhf y z
  have h323 := grahamInhom_pair_covariance_square_le G K hf hK hhf z y
  rw [ghsiCovariance_comm G K hf x w] at h101
  rw [ghsiCovariance_comm G K hf y w] at h202
  rw [ghsiCovariance_comm G K hf z w] at h303
  rw [ghsiCovariance_comm G K hf y x] at h212
  rw [ghsiCovariance_comm G K hf z x] at h313
  rw [ghsiCovariance_comm G K hf z y] at h323
  have hscalar :=
    fourBridge_Ursell_correction_nonneg_of_face_sqsum_ge_one
      (m0 := m0) (m1 := m1) (m2 := m2) (m3 := m3)
      (c01 := c01) (c02 := c02) (c03 := c03)
      (c12 := c12) (c13 := c13) (c23 := c23)
      hm00 hm10 hm20 hm30 hm01 hm11 hm21 hm31
      hc01 hc02 hc03 hc12 hc13 hc23
      h001 h101 h002 h202 h003 h303 h112 h212 h113 h313 h223 h323
      h012S h013S h023S h123S
  have hcorr012 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hwx hwy hxy
  have hcorr013 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hwx hwz hxz
  have hcorr023 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hwy hwz hyz
  have hcorr123 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hxy hxz hyz
  have hp01 : expJ G.edgeFinset K hf (fun s => spin s w * spin s x) =
      m0 * m1 + c01 := by
    dsimp [m0, m1, c01]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp02 : expJ G.edgeFinset K hf (fun s => spin s w * spin s y) =
      m0 * m2 + c02 := by
    dsimp [m0, m2, c02]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp03 : expJ G.edgeFinset K hf (fun s => spin s w * spin s z) =
      m0 * m3 + c03 := by
    dsimp [m0, m3, c03]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp12 : expJ G.edgeFinset K hf (fun s => spin s x * spin s y) =
      m1 * m2 + c12 := by
    dsimp [m1, m2, c12]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp13 : expJ G.edgeFinset K hf (fun s => spin s x * spin s z) =
      m1 * m3 + c13 := by
    dsimp [m1, m3, c13]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp23 : expJ G.edgeFinset K hf (fun s => spin s y * spin s z) =
      m2 * m3 + c23 := by
    dsimp [m2, m3, c23]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hone : fourBridgeOneCoeff G K hf w x y z =
      m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 := by
    unfold fourBridgeOneCoeff
    dsimp [m0, m1, m2, m3, grahamInhomOne]
  have htwo : fourBridgeTwoCoeff G K hf w x y z =
      (m0 * m1 + c01) ^ 2 + (m0 * m2 + c02) ^ 2 +
        (m0 * m3 + c03) ^ 2 + (m1 * m2 + c12) ^ 2 +
        (m1 * m3 + c13) ^ 2 + (m2 * m3 + c23) ^ 2 := by
    unfold fourBridgeTwoCoeff
    rw [hp01, hp02, hp03, hp12, hp13, hp23]
  have hthree : fourBridgeThreeCoeff G K hf w x y z =
      (expJ G.edgeFinset K hf
          (fun s => spin s w * (spin s x * spin s y))) ^ 2 +
        (expJ G.edgeFinset K hf
          (fun s => spin s w * (spin s x * spin s z))) ^ 2 +
        (expJ G.edgeFinset K hf
          (fun s => spin s w * (spin s y * spin s z))) ^ 2 +
        (expJ G.edgeFinset K hf
          (fun s => spin s x * (spin s y * spin s z))) ^ 2 := by
    rfl
  dsimp at hscalar hcorr012 hcorr013 hcorr023 hcorr123
  simp only [fourBridgeVarianceSkewBernsteinCoeff]
  rw [hone, htwo, hthree]
  dsimp [m0, m1, m2, m3, c01, c02, c03, c12, c13, c23]
  clear hm00 hm10 hm20 hm30 hm01 hm11 hm21 hm31
  clear hc01 hc02 hc03 hc12 hc13 hc23
  clear h001 h101 h002 h202 h003 h303 h112 h212 h113 h313 h223 h323
  clear h012S h013S h023S h123S hp01 hp02 hp03 hp12 hp13 hp23
    hone htwo hthree
  linarith [hscalar, hcorr012, hcorr013, hcorr023, hcorr123]

set_option maxHeartbeats 1600000 in



theorem fourBridge_Ursell_correction_with_edgeSlack_nonneg
    {m0 m1 m2 m3 c01 c02 c03 c12 c13 c23 : Real}
    (hm00 : 0 <= m0) (hm10 : 0 <= m1) (hm20 : 0 <= m2) (hm30 : 0 <= m3)
    (hm01 : m0 <= 1) (hm11 : m1 <= 1) (hm21 : m2 <= 1) (hm31 : m3 <= 1)
    (hc01 : 0 <= c01) (hc02 : 0 <= c02) (hc03 : 0 <= c03)
    (hc12 : 0 <= c12) (hc13 : 0 <= c13) (hc23 : 0 <= c23) :
    let p01 := m0 * m1 + c01
    let p02 := m0 * m2 + c02
    let p03 := m0 * m3 + c03
    let p12 := m1 * m2 + c12
    let p13 := m1 * m3 + c13
    let p23 := m2 * m3 + c23
    let u012 := m0 * p12 + m1 * p02 + m2 * p01 - 2 * m0 * m1 * m2
    let u013 := m0 * p13 + m1 * p03 + m3 * p01 - 2 * m0 * m1 * m3
    let u023 := m0 * p23 + m2 * p03 + m3 * p02 - 2 * m0 * m2 * m3
    let u123 := m1 * p23 + m2 * p13 + m3 * p12 - 2 * m1 * m2 * m3
    let aa := m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2
    let bb := p01 ^ 2 + p02 ^ 2 + p03 ^ 2 +
      p12 ^ 2 + p13 ^ 2 + p23 ^ 2
    0 <= aa + 3 * aa * bb - aa ^ 3 -
        3 * (u012 ^ 2 + u013 ^ 2 + u023 ^ 2 + u123 ^ 2) +
      2 * (m0 * c01 * c02 *
          (m0 * m1 * m2 + m1 * c02 + m2 * c01) +
        m1 * c01 * c12 *
          (m0 * m1 * m2 + m0 * c12 + m2 * c01) +
        m2 * c02 * c12 *
          (m0 * m1 * m2 + m0 * c12 + m1 * c02)) +
      2 * (m0 * c01 * c03 *
          (m0 * m1 * m3 + m1 * c03 + m3 * c01) +
        m1 * c01 * c13 *
          (m0 * m1 * m3 + m0 * c13 + m3 * c01) +
        m3 * c03 * c13 *
          (m0 * m1 * m3 + m0 * c13 + m1 * c03)) +
      2 * (m0 * c02 * c03 *
          (m0 * m2 * m3 + m2 * c03 + m3 * c02) +
        m2 * c02 * c23 *
          (m0 * m2 * m3 + m0 * c23 + m3 * c02) +
        m3 * c03 * c23 *
          (m0 * m2 * m3 + m0 * c23 + m2 * c03)) +
      2 * (m1 * c12 * c13 *
          (m1 * m2 * m3 + m2 * c13 + m3 * c12) +
        m2 * c12 * c23 *
          (m1 * m2 * m3 + m1 * c23 + m3 * c12) +
        m3 * c13 * c23 *
          (m1 * m2 * m3 + m1 * c23 + m2 * c13)) +
      3 * (c01 ^ 2 * (m0 ^ 2 + m1 ^ 2) +
        c02 ^ 2 * (m0 ^ 2 + m2 ^ 2) +
        c03 ^ 2 * (m0 ^ 2 + m3 ^ 2) +
        c12 ^ 2 * (m1 ^ 2 + m2 ^ 2) +
        c13 ^ 2 * (m1 ^ 2 + m3 ^ 2) +
        c23 ^ 2 * (m2 ^ 2 + m3 ^ 2)) := by
  have h012 := fourBridge_triangle_nonneg hm00 hm10 hm20 hm01 hm11 hm21
    hc01 hc02 hc12
  have h013 := fourBridge_triangle_nonneg hm00 hm10 hm30 hm01 hm11 hm31
    hc01 hc03 hc13
  have h023 := fourBridge_triangle_nonneg hm00 hm20 hm30 hm01 hm21 hm31
    hc02 hc03 hc23
  have h123 := fourBridge_triangle_nonneg hm10 hm20 hm30 hm11 hm21 hm31
    hc12 hc13 hc23
  have hbase := fourBridge_zero_base_identity
    m0 m1 m2 m3 c01 c02 c03 c12 c13 c23
  dsimp at hbase ⊢
  rw [hbase]
  nlinarith

end

end StatMech.Ising
