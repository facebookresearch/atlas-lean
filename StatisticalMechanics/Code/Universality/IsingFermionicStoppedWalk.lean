/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRegularity










namespace StatMech.Universality

open Finset

noncomputable section


abbrev IsingLeapfrogBox (R : Nat) := Fin (R + 1) × Fin (R + 1)

def isingLeapfrogBoxBoundary (R : Nat) (p : IsingLeapfrogBox R) : Prop :=
  p.1.1 = 0 ∨ p.1.1 + 1 = R + 1 ∨
    p.2.1 = 0 ∨ p.2.1 + 1 = R + 1

private noncomputable instance isingLeapfrogBoxBoundary_decidable
    (R : Nat) (p : IsingLeapfrogBox R) :
    Decidable (isingLeapfrogBoxBoundary R p) := Classical.propDecidable _

def isingLeapfrogWest (R : Nat) (p : IsingLeapfrogBox R) : Fin (R + 1) :=
  ⟨p.1.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) p.1.2⟩

def isingLeapfrogSouth (R : Nat) (p : IsingLeapfrogBox R) : Fin (R + 1) :=
  ⟨p.2.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) p.2.2⟩

def isingLeapfrogEast (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : Fin (R + 1) :=
  ⟨p.1.1 + 1, by
    have hle := p.1.2
    unfold isingLeapfrogBoxBoundary at hp
    omega⟩

def isingLeapfrogNorth (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : Fin (R + 1) :=
  ⟨p.2.1 + 1, by
    have hle := p.2.2
    unfold isingLeapfrogBoxBoundary at hp
    omega⟩

def isingLeapfrogSW (R : Nat) (p : IsingLeapfrogBox R) :
    IsingLeapfrogBox R :=
  (isingLeapfrogWest R p, isingLeapfrogSouth R p)

def isingLeapfrogSE (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : IsingLeapfrogBox R :=
  (isingLeapfrogEast R p hp, isingLeapfrogSouth R p)

def isingLeapfrogNW (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : IsingLeapfrogBox R :=
  (isingLeapfrogWest R p, isingLeapfrogNorth R p hp)

def isingLeapfrogNE (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : IsingLeapfrogBox R :=
  (isingLeapfrogEast R p hp, isingLeapfrogNorth R p hp)



def IsingLeapfrogHarmonicOnBox (R : Nat)
    (f : IsingLeapfrogBox R → Complex) : Prop :=
  ∀ p (hp : ¬ isingLeapfrogBoxBoundary R p),
    f (isingLeapfrogSW R p) + f (isingLeapfrogNW R p hp) +
        f (isingLeapfrogSE R p hp) + f (isingLeapfrogNE R p hp) =
      4 * f p


noncomputable def isingLeapfrogStoppedKernel (R : Nat) :
    Nat → IsingLeapfrogBox R → IsingLeapfrogBox R → Real
  | 0, p, q => if p = q then 1 else 0
  | t + 1, p, q =>
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogStoppedKernel R t p q
      else
        (isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p hp) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p hp) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p hp) q) / 4

theorem isingLeapfrogStoppedKernel_succ (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R (t + 1) p q =
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogStoppedKernel R t p q
      else
        (isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p hp) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p hp) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p hp) q) / 4 := by
  rfl


noncomputable def isingLeapfrogStoppedMean (R t : Nat)
    (f : IsingLeapfrogBox R → Complex) (p : IsingLeapfrogBox R) : Complex :=
  ∑ q, (isingLeapfrogStoppedKernel R t p q : Complex) * f q

@[simp] theorem isingLeapfrogStoppedMean_zero (R : Nat)
    (f : IsingLeapfrogBox R → Complex) (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedMean R 0 f p = f p := by
  classical
  unfold isingLeapfrogStoppedMean isingLeapfrogStoppedKernel
  have hcast (q : IsingLeapfrogBox R) :
      ((if p = q then 1 else 0 : Real) : Complex) =
        if p = q then 1 else 0 := by
    split_ifs <;> simp_all
  simp_rw [hcast]
  simp

theorem isingLeapfrogStoppedMean_succ (R t : Nat)
    (f : IsingLeapfrogBox R → Complex) (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedMean R (t + 1) f p =
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogStoppedMean R t f p
      else
        (isingLeapfrogStoppedMean R t f (isingLeapfrogSW R p) +
          isingLeapfrogStoppedMean R t f (isingLeapfrogSE R p hp) +
          isingLeapfrogStoppedMean R t f (isingLeapfrogNW R p hp) +
          isingLeapfrogStoppedMean R t f (isingLeapfrogNE R p hp)) / 4 := by
  classical
  unfold isingLeapfrogStoppedMean
  by_cases hp : isingLeapfrogBoxBoundary R p
  · simp [isingLeapfrogStoppedKernel, hp]
  · simp only [isingLeapfrogStoppedKernel, dif_neg hp]
    push_cast
    have hdist (a b c d z : Complex) :
        ((a + b + c + d) / 4) * z =
          (a * z + b * z + c * z + d * z) / 4 := by ring
    simp_rw [hdist]
    rw [← Finset.sum_div]
    repeat' rw [Finset.sum_add_distrib]


theorem isingLeapfrogStoppedKernel_nonneg (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    0 ≤ isingLeapfrogStoppedKernel R t p q := by
  induction t generalizing p with
  | zero =>
      unfold isingLeapfrogStoppedKernel
      split_ifs <;> norm_num
  | succ t ih =>
      simp only [isingLeapfrogStoppedKernel]
      split_ifs with hp
      · exact ih p
      · have hSW := ih (isingLeapfrogSW R p)
        have hSE := ih (isingLeapfrogSE R p hp)
        have hNW := ih (isingLeapfrogNW R p hp)
        have hNE := ih (isingLeapfrogNE R p hp)
        positivity


theorem isingLeapfrogStoppedKernel_sum_eq_one (R t : Nat)
    (p : IsingLeapfrogBox R) :
    ∑ q, isingLeapfrogStoppedKernel R t p q = 1 := by
  induction t generalizing p with
  | zero =>
      unfold isingLeapfrogStoppedKernel
      simp
  | succ t ih =>
      simp only [isingLeapfrogStoppedKernel]
      split_ifs with hp
      · exact ih p
      · rw [← Finset.sum_div]
        repeat' rw [Finset.sum_add_distrib]
        rw [ih, ih, ih, ih]
        norm_num

theorem isingLeapfrogStoppedKernel_le_one (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R t p q ≤ 1 := by
  classical
  calc
    isingLeapfrogStoppedKernel R t p q ≤
        ∑ x, isingLeapfrogStoppedKernel R t p x := by
      exact Finset.single_le_sum
        (fun x _ ↦ isingLeapfrogStoppedKernel_nonneg R t p x)
        (Finset.mem_univ q)
    _ = 1 := isingLeapfrogStoppedKernel_sum_eq_one R t p


theorem isingLeapfrogStoppedKernel_add (R t s : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R (t + s) p q =
      ∑ r, isingLeapfrogStoppedKernel R t p r *
        isingLeapfrogStoppedKernel R s r q := by
  classical
  induction t generalizing p with
  | zero =>
      simp [isingLeapfrogStoppedKernel]
  | succ t ih =>
      rw [Nat.succ_add]
      simp only [isingLeapfrogStoppedKernel]
      by_cases hp : isingLeapfrogBoxBoundary R p
      · simp only [dif_pos hp]
        exact ih p
      · simp only [dif_neg hp]
        rw [ih, ih, ih, ih]
        repeat' rw [← Finset.sum_add_distrib]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r hr
        ring



theorem isingLeapfrogStoppedKernel_l1_add_le
    (R t t' s : Nat) (p p' : IsingLeapfrogBox R) :
    (∑ q, |isingLeapfrogStoppedKernel R (t + s) p q -
        isingLeapfrogStoppedKernel R (t' + s) p' q|) ≤
      ∑ r, |isingLeapfrogStoppedKernel R t p r -
        isingLeapfrogStoppedKernel R t' p' r| := by
  classical
  simp_rw [isingLeapfrogStoppedKernel_add R t s p,
    isingLeapfrogStoppedKernel_add R t' s p']
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ q, ∑ r, |isingLeapfrogStoppedKernel R t p r -
          isingLeapfrogStoppedKernel R t' p' r| *
        isingLeapfrogStoppedKernel R s r q := by
      apply Finset.sum_le_sum
      intro q hq
      refine le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ) ?_
      apply Finset.sum_le_sum
      intro r hr
      rw [abs_mul, abs_of_nonneg
        (isingLeapfrogStoppedKernel_nonneg R s r q)]
    _ = ∑ r, ∑ q, |isingLeapfrogStoppedKernel R t p r -
          isingLeapfrogStoppedKernel R t' p' r| *
        isingLeapfrogStoppedKernel R s r q := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.mul_sum, isingLeapfrogStoppedKernel_sum_eq_one,
        mul_one]


theorem isingLeapfrogStoppedKernel_of_boundary (R t : Nat)
    (p q : IsingLeapfrogBox R) (hp : isingLeapfrogBoxBoundary R p) :
    isingLeapfrogStoppedKernel R t p q = if p = q then 1 else 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [isingLeapfrogStoppedKernel, dif_pos hp]
      exact ih


theorem isingLeapfrogStoppedKernel_boundary_mono (R t : Nat)
    (p q : IsingLeapfrogBox R) (hq : isingLeapfrogBoxBoundary R q) :
    isingLeapfrogStoppedKernel R t p q ≤
      isingLeapfrogStoppedKernel R (t + 1) p q := by
  induction t generalizing p with
  | zero =>
      by_cases hp : isingLeapfrogBoxBoundary R p
      · rw [isingLeapfrogStoppedKernel_of_boundary R 0 p q hp,
          isingLeapfrogStoppedKernel_of_boundary R 1 p q hp]
      · have hpq : p ≠ q := fun hpq ↦ hp (hpq ▸ hq)
        rw [isingLeapfrogStoppedKernel_succ R 0 p q]
        simp only [isingLeapfrogStoppedKernel, hpq, if_false, dif_neg hp]
        have hSW := isingLeapfrogStoppedKernel_nonneg R 0
          (isingLeapfrogSW R p) q
        have hSE := isingLeapfrogStoppedKernel_nonneg R 0
          (isingLeapfrogSE R p hp) q
        have hNW := isingLeapfrogStoppedKernel_nonneg R 0
          (isingLeapfrogNW R p hp) q
        have hNE := isingLeapfrogStoppedKernel_nonneg R 0
          (isingLeapfrogNE R p hp) q
        positivity
  | succ t ih =>
      rw [isingLeapfrogStoppedKernel_succ R t p q,
        isingLeapfrogStoppedKernel_succ R (t + 1) p q]
      by_cases hp : isingLeapfrogBoxBoundary R p
      · simp only [dif_pos hp]
        exact ih p
      · simp only [dif_neg hp]
        have hSW := ih (isingLeapfrogSW R p)
        have hSE := ih (isingLeapfrogSE R p hp)
        have hNW := ih (isingLeapfrogNW R p hp)
        have hNE := ih (isingLeapfrogNE R p hp)
        linarith


noncomputable def isingLeapfrogStoppedBoundaryMass (R t : Nat)
    (p : IsingLeapfrogBox R) : Real :=
  ∑ q with isingLeapfrogBoxBoundary R q,
    isingLeapfrogStoppedKernel R t p q

theorem isingLeapfrogStoppedBoundaryMass_nonneg (R t : Nat)
    (p : IsingLeapfrogBox R) :
    0 ≤ isingLeapfrogStoppedBoundaryMass R t p := by
  classical
  unfold isingLeapfrogStoppedBoundaryMass
  exact Finset.sum_nonneg fun q _ ↦
    isingLeapfrogStoppedKernel_nonneg R t p q

@[simp] theorem isingLeapfrogStoppedBoundaryMass_zero (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedBoundaryMass R 0 p =
      if isingLeapfrogBoxBoundary R p then 1 else 0 := by
  classical
  unfold isingLeapfrogStoppedBoundaryMass isingLeapfrogStoppedKernel
  by_cases hp : isingLeapfrogBoxBoundary R p
  · simp [hp]
  · simp [hp]

theorem isingLeapfrogStoppedBoundaryMass_succ (R t : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedBoundaryMass R (t + 1) p =
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogStoppedBoundaryMass R t p
      else
        (isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogSW R p) +
          isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogSE R p hp) +
          isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogNW R p hp) +
          isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogNE R p hp)) / 4 := by
  classical
  unfold isingLeapfrogStoppedBoundaryMass
  by_cases hp : isingLeapfrogBoxBoundary R p
  · simp [isingLeapfrogStoppedKernel, hp]
  · simp only [isingLeapfrogStoppedKernel, dif_neg hp]
    rw [← Finset.sum_div]
    repeat' rw [Finset.sum_add_distrib]


theorem isingLeapfrogStoppedBoundaryMass_mono (R t : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedBoundaryMass R t p ≤
      isingLeapfrogStoppedBoundaryMass R (t + 1) p := by
  induction t generalizing p with
  | zero =>
      rw [isingLeapfrogStoppedBoundaryMass_succ]
      split_ifs with hp
      · exact le_rfl
      · simp [hp]
        positivity
  | succ t ih =>
      rw [isingLeapfrogStoppedBoundaryMass_succ,
        isingLeapfrogStoppedBoundaryMass_succ]
      split_ifs with hp
      · exact ih p
      · have hSW := ih (isingLeapfrogSW R p)
        have hSE := ih (isingLeapfrogSE R p hp)
        have hNW := ih (isingLeapfrogNW R p hp)
        have hNE := ih (isingLeapfrogNE R p hp)
        linarith



theorem IsingLeapfrogHarmonicOnBox.stoppedMean_eq
    {R : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f) (t : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedMean R t f p = f p := by
  induction t generalizing p with
  | zero => exact isingLeapfrogStoppedMean_zero R f p
  | succ t ih =>
      rw [isingLeapfrogStoppedMean_succ]
      split_ifs with hp
      · exact ih p
      · rw [ih, ih, ih, ih]
        have h := hf p hp
        apply (div_eq_iff (by norm_num : (4 : Complex) ≠ 0)).2
        linear_combination h


noncomputable def isingLeapfrogStoppedKernelGradientSq
    (R t : Nat) (p p' : IsingLeapfrogBox R) : Real :=
  ∑ q, (isingLeapfrogStoppedKernel R t p q -
    isingLeapfrogStoppedKernel R t p' q) ^ 2




noncomputable def isingLeapfrogStoppedKernelTimeGradientSq
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) : Real :=
  ∑ q, (isingLeapfrogStoppedKernel R t p q -
    isingLeapfrogStoppedKernel R t' p' q) ^ 2

@[simp] theorem isingLeapfrogStoppedKernelTimeGradientSq_sameTime
    (R t : Nat) (p p' : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernelTimeGradientSq R t t p p' =
      isingLeapfrogStoppedKernelGradientSq R t p p' := rfl




theorem isingLeapfrogStoppedKernelTimeGradientSq_le_two
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' ≤ 2 := by
  classical
  unfold isingLeapfrogStoppedKernelTimeGradientSq
  calc
    _ ≤ ∑ q, (isingLeapfrogStoppedKernel R t p q +
        isingLeapfrogStoppedKernel R t' p' q) := by
      apply Finset.sum_le_sum
      intro q hq
      have ha0 := isingLeapfrogStoppedKernel_nonneg R t p q
      have ha1 := isingLeapfrogStoppedKernel_le_one R t p q
      have hb0 := isingLeapfrogStoppedKernel_nonneg R t' p' q
      have hb1 := isingLeapfrogStoppedKernel_le_one R t' p' q
      nlinarith [mul_nonneg ha0 hb0]
    _ = (∑ q, isingLeapfrogStoppedKernel R t p q) +
        ∑ q, isingLeapfrogStoppedKernel R t' p' q := by
      rw [Finset.sum_add_distrib]
    _ = 2 := by
      rw [isingLeapfrogStoppedKernel_sum_eq_one,
        isingLeapfrogStoppedKernel_sum_eq_one]
      norm_num



theorem isingLeapfrogStoppedKernelTimeGradientSq_le_mul_l1
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) (A : Real)
    (hpoint : ∀ q, |isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R t' p' q| ≤ A) :
    isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' ≤
      A * ∑ q, |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t' p' q| := by
  classical
  unfold isingLeapfrogStoppedKernelTimeGradientSq
  calc
    _ ≤ ∑ q, A * |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t' p' q| := by
      apply Finset.sum_le_sum
      intro q hq
      rw [← sq_abs, pow_two]
      exact mul_le_mul_of_nonneg_right (hpoint q) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]



theorem IsingLeapfrogHarmonicOnBox.normSq_sub_le_kernelGradient
    {R : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f) (t : Nat)
    (p p' : IsingLeapfrogBox R) :
    Complex.normSq (f p - f p') ≤
      isingLeapfrogStoppedKernelGradientSq R t p p' *
        ∑ q, Complex.normSq (f q) := by
  classical
  rw [← hf.stoppedMean_eq t p, ← hf.stoppedMean_eq t p']
  unfold isingLeapfrogStoppedMean isingLeapfrogStoppedKernelGradientSq
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  have hcs := isingComplex_normSq_sum_mul_le Finset.univ
    (fun q ↦ isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R t p' q) f
  convert hcs using 1 <;> simp


theorem IsingLeapfrogHarmonicOnBox.normSq_sub_le_kernelTimeGradient
    {R : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f) (t t' : Nat)
    (p p' : IsingLeapfrogBox R) :
    Complex.normSq (f p - f p') ≤
      isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' *
        ∑ q, Complex.normSq (f q) := by
  classical
  rw [← hf.stoppedMean_eq t p, ← hf.stoppedMean_eq t' p']
  unfold isingLeapfrogStoppedMean isingLeapfrogStoppedKernelTimeGradientSq
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  have hcs := isingComplex_normSq_sum_mul_le Finset.univ
    (fun q ↦ isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R t' p' q) f
  convert hcs using 1 <;> simp




def IsingLeapfrogInteriorMargin (R ρ : Nat) (p : IsingLeapfrogBox R) : Prop :=
  ρ ≤ p.1.1 ∧ p.1.1 + ρ ≤ R ∧
    ρ ≤ p.2.1 ∧ p.2.1 + ρ ≤ R


def IsingLeapfrogDiagonalAdjacent {R : Nat}
    (p p' : IsingLeapfrogBox R) : Prop :=
  Nat.dist p.1.1 p'.1.1 = 1 ∧ Nat.dist p.2.1 p'.2.1 = 1








def IsingLeapfrogDiffusiveGradientBound (C : Real) : Prop :=
  0 ≤ C ∧
    ∀ (R ρ : Nat) (p p' : IsingLeapfrogBox R),
      0 < ρ →
      IsingLeapfrogInteriorMargin R ρ p →
      IsingLeapfrogInteriorMargin R ρ p' →
      IsingLeapfrogDiagonalAdjacent p p' →
      isingLeapfrogStoppedKernelTimeGradientSq R
          (ρ * ρ) (ρ * ρ + 1) p p' ≤
        C / (ρ : Real) ^ 3




def IsingLeapfrogDiffusiveKernelInputs (A B : Real) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧
    ∀ (R ρ : Nat) (p p' : IsingLeapfrogBox R),
      0 < ρ →
      IsingLeapfrogInteriorMargin R ρ p →
      IsingLeapfrogInteriorMargin R ρ p' →
      IsingLeapfrogDiagonalAdjacent p p' →
      (∀ q, |isingLeapfrogStoppedKernel R (ρ * ρ) p q -
          isingLeapfrogStoppedKernel R (ρ * ρ + 1) p' q| ≤
        A / (ρ : Real) ^ 2) ∧
      (∑ q, |isingLeapfrogStoppedKernel R (ρ * ρ) p q -
          isingLeapfrogStoppedKernel R (ρ * ρ + 1) p' q|) ≤
        B / (ρ : Real)

theorem IsingLeapfrogDiffusiveKernelInputs.gradientBound
    {A B : Real} (hAB : IsingLeapfrogDiffusiveKernelInputs A B) :
    IsingLeapfrogDiffusiveGradientBound (A * B) := by
  refine ⟨mul_nonneg hAB.1 hAB.2.1, ?_⟩
  intro R ρ p p' hρ hp hp' hpp'
  have hinputs := hAB.2.2 R ρ p p' hρ hp hp' hpp'
  calc
    isingLeapfrogStoppedKernelTimeGradientSq R
        (ρ * ρ) (ρ * ρ + 1) p p' ≤
        (A / (ρ : Real) ^ 2) *
          ∑ q, |isingLeapfrogStoppedKernel R (ρ * ρ) p q -
            isingLeapfrogStoppedKernel R (ρ * ρ + 1) p' q| :=
      isingLeapfrogStoppedKernelTimeGradientSq_le_mul_l1
        R (ρ * ρ) (ρ * ρ + 1) p p'
        (A / (ρ : Real) ^ 2) hinputs.1
    _ ≤ (A / (ρ : Real) ^ 2) * (B / (ρ : Real)) := by
      exact mul_le_mul_of_nonneg_left hinputs.2 (div_nonneg hAB.1 (by positivity))
    _ = A * B / (ρ : Real) ^ 3 := by
      have hρR : (ρ : Real) ≠ 0 := by positivity
      field_simp



theorem isingLeapfrogDiffusiveGradientBound_unitMargin
    (R : Nat) (p p' : IsingLeapfrogBox R)
    (_hp : IsingLeapfrogInteriorMargin R 1 p)
    (_hp' : IsingLeapfrogInteriorMargin R 1 p')
    (_hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    isingLeapfrogStoppedKernelTimeGradientSq R 1 2 p p' ≤
      (2 : Real) / (1 : Real) ^ 3 := by
  simpa using isingLeapfrogStoppedKernelTimeGradientSq_le_two R 1 2 p p'




theorem IsingLeapfrogHarmonicOnBox.normSq_sub_le_of_diffusiveGradient
    {C : Real} (hC : IsingLeapfrogDiffusiveGradientBound C)
    {R ρ : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f)
    (p p' : IsingLeapfrogBox R) (hρ : 0 < ρ)
    (hp : IsingLeapfrogInteriorMargin R ρ p)
    (hp' : IsingLeapfrogInteriorMargin R ρ p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    Complex.normSq (f p - f p') ≤
      (C / (ρ : Real) ^ 3) * ∑ q, Complex.normSq (f q) := by
  refine le_trans (hf.normSq_sub_le_kernelTimeGradient
    (ρ * ρ) (ρ * ρ + 1) p p') ?_
  exact mul_le_mul_of_nonneg_right
    (hC.2 R ρ p p' hρ hp hp' hpp')
    (Finset.sum_nonneg fun q _ ↦ Complex.normSq_nonneg (f q))





noncomputable def fkIsingSquareRadialPatchFullObservableWindow
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogBox R → Complex :=
  fun p ↦ fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨baseI + p.1.1, by have := p.1.2; omega⟩
    ⟨baseJ + p.2.1, by have := p.2.2; omega⟩



theorem fkIsingSquareRadialPatchFullObservableWindow_harmonic
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogHarmonicOnBox R
      (fkIsingSquareRadialPatchFullObservableWindow
        n m baseI baseJ R hn hm hfitI hfitJ) := by
  intro p hp
  have hx0 : 0 < p.1.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hy0 : 0 < p.2.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hxR : p.1.1 + 1 < R + 1 := by
    have hxle := p.1.2
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hyR : p.2.1 + 1 < R + 1 := by
    have hyle := p.2.2
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hphysical :=
    fkIsingSquareRadialPatchFullObservable_leapfrog_harmonic
      n m (baseI + p.1.1 - 1) (baseJ + p.2.1 - 1) hn hm
      (by omega) (by omega)
  have hSW :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogSW R p) =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
      isingLeapfrogSW isingLeapfrogWest isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNW :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogNW R p hp) =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
      isingLeapfrogNW isingLeapfrogWest isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hSE :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogSE R p hp) =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
      isingLeapfrogSE isingLeapfrogEast isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNE :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogNE R p hp) =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
      isingLeapfrogNE isingLeapfrogEast isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hC :
      fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p =
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 1, by omega⟩ := by
    unfold fkIsingSquareRadialPatchFullObservableWindow
    congr 2 <;> omega
  rw [hSW, hNW, hSE, hNE, hC]
  exact hphysical




theorem fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (t : Nat) (p p' : IsingLeapfrogBox R) :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ p -
          fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ p') ≤
      isingLeapfrogStoppedKernelGradientSq R t p p' *
        ∑ q, Complex.normSq
          (fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ q) := by
  exact (fkIsingSquareRadialPatchFullObservableWindow_harmonic
    n m baseI baseJ R hn hm hfitI hfitJ).normSq_sub_le_kernelGradient t p p'

end

end StatMech.Universality
