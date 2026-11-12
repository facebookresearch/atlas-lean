/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointRace
import Code.Universality.IsingFermionicReflectionEstimates








namespace StatMech.Universality

open Finset
open IsingDiagonalWalkHitSplit

noncomputable section

private def isingLineFarFifth (m : Nat) (q : IsingLineBox m) : Real :=
  ((m : Real) - (q.1 : Real)) ^ 5

private theorem isingLineFarFifth_step
    (m : Nat) (p : IsingLineBox m)
    (hp : ¬ isingLineBoxBoundary m p) :
    isingLineFarFifth m (isingLineWest m p) +
        isingLineFarFifth m (isingLineEast m p hp) =
      2 * isingLineFarFifth m p +
        20 * ((m : Real) - (p.1 : Real)) ^ 3 +
          10 * ((m : Real) - (p.1 : Real)) := by
  unfold isingLineFarFifth isingLineWest isingLineEast
  have hp0 : 0 < p.1 := by
    unfold isingLineBoxBoundary at hp
    omega
  have hpR : p.1 < m := by
    unfold isingLineBoxBoundary at hp
    have hle := p.2
    omega
  push_cast
  rw [Nat.cast_sub hp0]
  ring

private theorem isingLineFarThird_step
    (m : Nat) (p : IsingLineBox m)
    (hp : ¬ isingLineBoxBoundary m p) :
    ((m : Real) - ((isingLineWest m p).1 : Real)) ^ 3 +
        ((m : Real) - ((isingLineEast m p hp).1 : Real)) ^ 3 =
      2 * ((m : Real) - (p.1 : Real)) ^ 3 +
        6 * ((m : Real) - (p.1 : Real)) := by
  unfold isingLineWest isingLineEast
  have hp0 : 0 < p.1 := by
    unfold isingLineBoxBoundary at hp
    omega
  have hpR : p.1 < m := by
    unfold isingLineBoxBoundary at hp
    have hle := p.2
    omega
  push_cast
  rw [Nat.cast_sub hp0]
  ring

private theorem isingLineFarFirst_step
    (m : Nat) (p : IsingLineBox m)
    (hp : ¬ isingLineBoxBoundary m p) :
    ((m : Real) - ((isingLineWest m p).1 : Real)) +
        ((m : Real) - ((isingLineEast m p hp).1 : Real)) =
      2 * ((m : Real) - (p.1 : Real)) := by
  unfold isingLineWest isingLineEast
  have hp0 : 0 < p.1 := by
    unfold isingLineBoxBoundary at hp
    omega
  have hpR : p.1 < m := by
    unfold isingLineBoxBoundary at hp
    have hle := p.2
    omega
  push_cast
  rw [Nat.cast_sub hp0]
  ring



theorem isingLineStoppedMean_farFifth_le
    (m t : Nat) (p : IsingLineBox m) :
    isingLineStoppedMean m t (isingLineFarFifth m) p ≤
      ((m : Real) - (p.1 : Real)) ^ 5 +
        10 * (t : Real) * ((m : Real) - (p.1 : Real)) ^ 3 +
          15 * (t : Real) ^ 2 * ((m : Real) - (p.1 : Real)) := by
  induction t generalizing p with
  | zero =>
      simp [isingLineStoppedMean, isingLineStoppedKernel,
        isingLineFarFifth]
  | succ t ih =>
      rw [isingLineStoppedMean_succ]
      by_cases hp : isingLineBoxBoundary m p
      · rw [dif_pos hp]
        have h := ih p
        have hy : 0 ≤ (m : Real) - (p.1 : Real) := by
          have hpLe : p.1 ≤ m := by omega
          have hpLeReal : (p.1 : Real) ≤ (m : Real) := by exact_mod_cast hpLe
          linarith
        have hy3 : 0 ≤ ((m : Real) - (p.1 : Real)) ^ 3 :=
          pow_nonneg hy _
        have hty : 0 ≤ (2 * (t : Real) + 1) *
            ((m : Real) - (p.1 : Real)) :=
          mul_nonneg (by positivity) hy
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith
      · rw [dif_neg hp]
        have hw := ih (isingLineWest m p)
        have he := ih (isingLineEast m p hp)
        have h5 := isingLineFarFifth_step m p hp
        have h3 := isingLineFarThird_step m p hp
        have h1 := isingLineFarFirst_step m p hp
        have hy : 0 ≤ (m : Real) - (p.1 : Real) := by
          have hpLe : p.1 ≤ m := by omega
          have hpLeReal : (p.1 : Real) ≤ (m : Real) := by exact_mod_cast hpLe
          linarith
        unfold isingLineFarFifth at hw he h5 ⊢
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith [sq_nonneg (t : Real)]



theorem isingLineStoppedKernel_far_boundary_le_fifth
    (m t : Nat) (hm : 0 < m) :
    isingLineStoppedKernel m t ⟨m - 1, by omega⟩ ⟨0, by omega⟩ ≤
      26 * (t + 1 : Real) ^ 2 / (m : Real) ^ 5 := by
  have hmean := isingLineStoppedMean_farFifth_le m t
    (⟨m - 1, by omega⟩ : IsingLineBox m)
  have hm5 : 0 < (m : Real) ^ 5 := by positivity
  apply (le_div_iff₀ hm5).2
  let start : IsingLineBox m := ⟨m - 1, by omega⟩
  let far : IsingLineBox m := ⟨0, by omega⟩
  have hboundary :
      (m : Real) ^ 5 * isingLineStoppedKernel m t start far ≤
        isingLineStoppedMean m t (isingLineFarFifth m) start := by
    calc
      _ = isingLineStoppedKernel m t start far *
          isingLineFarFifth m far := by
        simp [isingLineFarFifth, far]
        ring
      _ ≤ ∑ q, isingLineStoppedKernel m t start q *
          isingLineFarFifth m q := by
        refine Finset.single_le_sum (s := Finset.univ)
          (f := fun q : IsingLineBox m =>
            isingLineStoppedKernel m t start q * isingLineFarFifth m q) ?_
          (Finset.mem_univ far)
        intro q hq
        exact mul_nonneg (isingLineStoppedKernel_nonneg _ _ _ _)
          (by
            unfold isingLineFarFifth
            have hqLe : q.1 ≤ m := by omega
            have hqLeReal : (q.1 : Real) ≤ (m : Real) := by exact_mod_cast hqLe
            exact pow_nonneg (sub_nonneg.mpr hqLeReal) _)
      _ = _ := rfl
  have hmean' :
      isingLineStoppedMean m t (isingLineFarFifth m) start ≤
        26 * (t + 1 : Real) ^ 2 := by
    have hcast : ((m - 1 : Nat) : Real) = (m : Real) - 1 := by
      rw [Nat.cast_sub hm]
      norm_num
    dsimp [start] at hmean
    rw [hcast] at hmean
    norm_num at hmean ⊢
    nlinarith [sq_nonneg (t : Real)]
  change isingLineStoppedKernel m t start far * (m : Real) ^ 5 ≤
    26 * (t + 1 : Real) ^ 2
  calc
    _ = (m : Real) ^ 5 * isingLineStoppedKernel m t start far := by ring
    _ ≤ isingLineStoppedMean m t (isingLineFarFifth m) start := hboundary
    _ ≤ 26 * (t + 1 : Real) ^ 2 := hmean'



def IsingLineFarFirstBoundaryFamily (m k : Nat) :=
  {ys : List Bool // ys.length = k ∧
    isingLineChoiceRun m ⟨m - 1, by omega⟩ ys = ⟨0, by omega⟩ ∧
    ∀ j, j < k → ¬ isingLineBoxBoundary m
      (isingLineChoiceRun m ⟨m - 1, by omega⟩ (ys.take j))}

noncomputable instance isingLineFarFirstBoundaryFamily_finite (m k : Nat) :
    Finite (IsingLineFarFirstBoundaryFamily m k) := by
  letI : Fintype {ys : List Bool // ys.length = k} :=
    (List.finite_length_eq Bool k).fintype
  exact Finite.of_injective
    (fun w : IsingLineFarFirstBoundaryFamily m k =>
      (⟨w.1, w.2.1⟩ : {ys : List Bool // ys.length = k}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = k} => z.1) h)

private def FarFirstBoundaryExtension (m K : Nat) :=
  Σ j : Fin (K + 1),
    IsingLineFarFirstBoundaryFamily m j ×
      {tail : List Bool // tail.length = K - j}

private theorem isingLineChoiceRun_append_endpointEscape
    (n : Nat) (p : IsingLineBox n) (a b : List Bool) :
    isingLineChoiceRun n p (a ++ b) =
      isingLineChoiceRun n (isingLineChoiceRun n p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih =>
      simp only [List.cons_append, isingLineChoiceRun]
      exact ih (isingLineChoiceNext n p x)

private theorem isingLineChoiceRun_boundary_endpointEscape
    (n : Nat) (p : IsingLineBox n) (hp : isingLineBoxBoundary n p)
    (bs : List Bool) : isingLineChoiceRun n p bs = p := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLineChoiceRun]
      rw [show isingLineChoiceNext n p b = p by
        simp [isingLineChoiceNext, hp]]
      exact ih

private def farFirstBoundaryExtend (m K : Nat) :
    FarFirstBoundaryExtension m K →
      IsingLineChoicePathFamily m K ⟨m - 1, by omega⟩ ⟨0, by omega⟩ :=
  fun w => ⟨w.2.1.1 ++ w.2.2.1, by
      rw [List.length_append, w.2.1.2.1, w.2.2.2]
      omega,
    by
      rw [isingLineChoiceRun_append_endpointEscape, w.2.1.2.2.1]
      exact isingLineChoiceRun_boundary_endpointEscape m ⟨0, by omega⟩
        (by simp [isingLineBoxBoundary]) _⟩

private theorem farFirstBoundaryExtend_injective (m K : Nat) :
    Function.Injective (farFirstBoundaryExtend m K) := by
  rintro ⟨aj, ap, atail⟩ ⟨bj, bp, btail⟩ hab
  have hfull : ap.1 ++ atail.1 = bp.1 ++ btail.1 :=
    congrArg Subtype.val hab
  have hj : (aj : Nat) = bj := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbavoid := bp.2.2.2 (aj : Nat) hlt
      apply hbavoid
      have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
      change (ap.1 ++ atail.1).take (aj : Nat) =
        (bp.1 ++ btail.1).take (aj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (aj : Nat) = ap.1 := by
        simpa [ap.2.1] using
          (List.take_left (l₁ := ap.1) (l₂ := atail.1))
      have hbTake : (bp.1 ++ btail.1).take (aj : Nat) =
          bp.1.take (aj : Nat) := by
        apply List.take_append_of_le_length
        rw [bp.2.1]
        omega
      rw [haTake, hbTake] at ht
      rw [← ht, ap.2.2.1]
      simp [isingLineBoxBoundary]
    · have haavoid := ap.2.2.2 (bj : Nat) hgt
      apply haavoid
      have ht := congrArg (fun z : List Bool => z.take (bj : Nat)) hfull
      change (ap.1 ++ atail.1).take (bj : Nat) =
        (bp.1 ++ btail.1).take (bj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (bj : Nat) =
          ap.1.take (bj : Nat) := by
        apply List.take_append_of_le_length
        rw [ap.2.1]
        omega
      have hbTake : (bp.1 ++ btail.1).take (bj : Nat) = bp.1 := by
        simpa [bp.2.1] using
          (List.take_left (l₁ := bp.1) (l₂ := btail.1))
      rw [haTake, hbTake] at ht
      rw [ht, bp.2.2.1]
      simp [isingLineBoxBoundary]
  have hjSubtype : aj = bj := Fin.ext hj
  subst bj
  have hpref : ap.1 = bp.1 := by
    have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using ht
  have htail : atail.1 = btail.1 := by
    have hd := congrArg (fun z : List Bool => z.drop (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using hd
  have hap : ap = bp := Subtype.ext hpref
  have hat : atail = btail := Subtype.ext htail
  subst bp
  subst btail
  rfl


theorem lineFarFirstBoundary_partial_weight_le_fifth
    (m K : Nat) (hm : 0 < m) :
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) ≤
      26 * (K + 1 : Real) ^ 2 / (m : Real) ^ 5 := by
  have hcard : Nat.card (FarFirstBoundaryExtension m K) ≤
      Nat.card (IsingLineChoicePathFamily m K
        ⟨m - 1, by omega⟩ ⟨0, by omega⟩) :=
    Nat.card_le_card_of_injective (farFirstBoundaryExtend m K)
      (farFirstBoundaryExtend_injective m K)
  have hext : Nat.card (FarFirstBoundaryExtension m K) =
      ∑ j : Fin (K + 1),
        Nat.card (IsingLineFarFirstBoundaryFamily m j) * 2 ^ (K - j) := by
    letI (j : Fin (K + 1)) :
        Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (K + 1)) :
        Fintype {tail : List Bool // tail.length = K - j} :=
      (List.finite_length_eq Bool (K - j)).fintype
    change Nat.card (Σ j : Fin (K + 1),
      IsingLineFarFirstBoundaryFamily m j ×
        {tail : List Bool // tail.length = K - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.card_prod]
    congr 1
    change Nat.card (List.Vector Bool (K - (j : Nat))) = 2 ^ (K - (j : Nat))
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool (K - (j : Nat))),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have hweightedNat :
      (∑ j : Fin (K + 1),
        Nat.card (IsingLineFarFirstBoundaryFamily m j) * 2 ^ (K - j)) ≤
          Nat.card (IsingLineChoicePathFamily m K
            ⟨m - 1, by omega⟩ ⟨0, by omega⟩) := by
    rw [← hext]
    exact hcard
  have hweightedReal :
      (∑ j : Fin (K + 1),
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) ≤
          (Nat.card (IsingLineChoicePathFamily m K
            ⟨m - 1, by omega⟩ ⟨0, by omega⟩) : Real) := by
    exact_mod_cast hweightedNat
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
      (2 : Real) ^ (K - j)) (K + 1)] at hweightedReal
  have htwo : 0 < (2 : Real) ^ K := by positivity
  have hdiv := div_le_div_of_nonneg_right hweightedReal htwo.le
  calc
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) =
      (∑ j ∈ Finset.range (K + 1),
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) / (2 : Real) ^ K := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := by
        have := Finset.mem_range.mp hj
        omega
      have hpow : (2 : Real) ^ K =
          (2 : Real) ^ j * (2 : Real) ^ (K - j) := by
        calc
          (2 : Real) ^ K = (2 : Real) ^ (j + (K - j)) := by
            congr 1
            omega
          _ = _ := pow_add _ _ _
      calc
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) /
            (2 : Real) ^ j =
          ((Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
            (2 : Real) ^ (K - j)) /
              ((2 : Real) ^ j * (2 : Real) ^ (K - j)) :=
            (mul_div_mul_right _ _ (by positivity)).symm
        _ = _ := by rw [hpow]
    _ ≤ (Nat.card (IsingLineChoicePathFamily m K
        ⟨m - 1, by omega⟩ ⟨0, by omega⟩) : Real) /
          (2 : Real) ^ K := hdiv
    _ = isingLineStoppedKernel m K
        ⟨m - 1, by omega⟩ ⟨0, by omega⟩ := by
      rw [isingLineStoppedKernel_eq_natCard_choicePath_div]
    _ ≤ 26 * (K + 1 : Real) ^ 2 / (m : Real) ^ 5 :=
      isingLineStoppedKernel_far_boundary_le_fifth m K hm

private theorem two_inv_sqrt_diff_mul_sq_le_sqrt (k : Nat) :
    (2 / Real.sqrt (k + 1 : Real) -
        2 / Real.sqrt (k + 2 : Real)) * (k + 1 : Real) ^ 2 ≤
      Real.sqrt (k + 1 : Real) := by
  let x := Real.sqrt (k + 1 : Real)
  let y := Real.sqrt (k + 2 : Real)
  have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
  have hy : 0 < y := Real.sqrt_pos.2 (by positivity)
  have hx2 : x ^ 2 = (k + 1 : Real) := by
    dsimp [x]
    rw [Real.sq_sqrt]
    positivity
  have hy2 : y ^ 2 = (k + 2 : Real) := by
    dsimp [y]
    rw [Real.sq_sqrt]
    positivity
  have hxy : x ≤ y := by
    dsimp [x, y]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hden : 0 < y * (y + x) := mul_pos hy (add_pos hy hx)
  have heq :
      (2 / x - 2 / y) * (k + 1 : Real) ^ 2 =
        2 * x ^ 3 / (y * (y + x)) := by
    field_simp [ne_of_gt hx, ne_of_gt hy]
    nlinarith [hx2, hy2]
  change (2 / x - 2 / y) * (k + 1 : Real) ^ 2 ≤ x
  rw [heq]
  apply (div_le_iff₀ hden).2
  have hxx : x ^ 2 ≤ x * y := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hxy)]
  have hsum : 2 * x ≤ y + x := by linarith
  have hmul := mul_le_mul hxx hsum (by positivity) (by positivity)
  nlinarith



theorem endpointKernel_farFirstBoundary_sum_le
    (m N : Nat) (hm : 0 < m) (hN : N ≤ m * m) :
    (∑ k ∈ Finset.range (N + 1),
      (2 / Real.sqrt (k + 1 : Real)) *
        ((Nat.card (IsingLineFarFirstBoundaryFamily m k) : Real) /
          (2 : Real) ^ k)) ≤
      468 / (m : Real) ^ 2 := by
  let a : Nat → Real := fun k => 2 / Real.sqrt (k + 1 : Real)
  let b : Nat → Real := fun k =>
    (Nat.card (IsingLineFarFirstBoundaryFamily m k) : Real) / (2 : Real) ^ k
  have hm2 : 0 < (m : Real) ^ 2 := by positivity
  have hm5 : 0 < (m : Real) ^ 5 := by positivity
  have hNReal : (N : Real) ≤ (m : Real) ^ 2 := by
    exact_mod_cast (show N ≤ m ^ 2 by simpa [pow_two] using hN)
  have hpartial (k : Nat) :
      (∑ j ∈ Finset.range (k + 1), b j) ≤
        26 * (k + 1 : Real) ^ 2 / (m : Real) ^ 5 := by
    simpa [b] using lineFarFirstBoundary_partial_weight_le_fifth m k hm
  have hA (k : Nat) (hk : k ≤ N) :
      (k + 1 : Real) ≤ 4 * (m : Real) ^ 2 := by
    have hkReal : (k : Real) ≤ (m : Real) ^ 2 :=
      le_trans (by exact_mod_cast hk) hNReal
    have hmOne : (1 : Real) ≤ (m : Real) ^ 2 := by
      have : (1 : Nat) ≤ m := hm
      nlinarith [show (1 : Real) ≤ m by exact_mod_cast this]
    nlinarith
  have hsqrt (k : Nat) (hk : k ≤ N) :
      Real.sqrt (k + 1 : Real) ≤ 2 * (m : Real) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have := hA k hk
      nlinarith
  have hlast :
      a N * (∑ k ∈ Finset.range (N + 1), b k) ≤
        416 / (m : Real) ^ 2 := by
    calc
      _ ≤ a N * (26 * (N + 1 : Real) ^ 2 / (m : Real) ^ 5) := by
        apply mul_le_mul_of_nonneg_left (hpartial N)
        dsimp [a]
        positivity
      _ ≤ 416 / (m : Real) ^ 2 := by
        dsimp [a]
        let x := Real.sqrt (N + 1 : Real)
        have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
        have hx2 : x ^ 2 = (N + 1 : Real) := by
          dsimp [x]
          rw [Real.sq_sqrt]
          positivity
        have hA' := hA N (le_refl _)
        have hx' := hsqrt N (le_refl _)
        change (2 / x) * (26 * (N + 1 : Real) ^ 2 / (m : Real) ^ 5) ≤
          416 / (m : Real) ^ 2
        have hprod : (N + 1 : Real) * x ≤ 8 * (m : Real) ^ 3 := by
          have := mul_le_mul hA' hx' (Real.sqrt_nonneg _) (by positivity)
          nlinarith
        have hprod26 := mul_le_mul_of_nonneg_left hprod
          (show (0 : Real) ≤ 52 by norm_num)
        have hprod26' : 52 * ((N + 1 : Real) * x) ≤
            416 * (m : Real) ^ 3 := by
          convert hprod26 using 1 <;> ring
        calc
          (2 / x) * (26 * (N + 1 : Real) ^ 2 / (m : Real) ^ 5) =
              52 * ((N + 1 : Real) * x) / (m : Real) ^ 5 := by
            field_simp [ne_of_gt hx]
            nlinarith [hx2]
          _ ≤ 416 * (m : Real) ^ 3 / (m : Real) ^ 5 :=
            div_le_div_of_nonneg_right hprod26' hm5.le
          _ = 416 / (m : Real) ^ 2 := by field_simp
  have hterm (k : Nat) :
      (a k - a (k + 1)) *
          (∑ j ∈ Finset.range (k + 1), b j) ≤
        26 * Real.sqrt (k + 1 : Real) / (m : Real) ^ 5 := by
    have hdiff : 0 ≤ a k - a (k + 1) := by
      dsimp [a]
      apply sub_nonneg.mpr
      apply div_le_div_of_nonneg_left (by norm_num)
        (Real.sqrt_pos.2 (by positivity))
      exact Real.sqrt_le_sqrt (by norm_num)
    calc
      _ ≤ (a k - a (k + 1)) *
          (26 * (k + 1 : Real) ^ 2 / (m : Real) ^ 5) :=
        mul_le_mul_of_nonneg_left (hpartial k) hdiff
      _ ≤ 26 * Real.sqrt (k + 1 : Real) / (m : Real) ^ 5 := by
        dsimp [a]
        rw [show (((k + 1 : Nat) : Real) + 1) = (k : Real) + 2 by
          push_cast
          ring]
        have hcore := two_inv_sqrt_diff_mul_sq_le_sqrt k
        have hcore26 := mul_le_mul_of_nonneg_left hcore
          (show (0 : Real) ≤ 26 by norm_num)
        calc
          (2 / Real.sqrt (k + 1 : Real) -
              2 / Real.sqrt (k + 2 : Real)) *
                (26 * (k + 1 : Real) ^ 2 / (m : Real) ^ 5) =
            (26 * ((2 / Real.sqrt (k + 1 : Real) -
              2 / Real.sqrt (k + 2 : Real)) *
                (k + 1 : Real) ^ 2)) / (m : Real) ^ 5 := by ring
          _ ≤ (26 * Real.sqrt (k + 1 : Real)) / (m : Real) ^ 5 :=
            div_le_div_of_nonneg_right hcore26 hm5.le
  rw [show (∑ k ∈ Finset.range (N + 1),
      (2 / Real.sqrt (k + 1 : Real)) *
        ((Nat.card (IsingLineFarFirstBoundaryFamily m k) : Real) /
          (2 : Real) ^ k)) =
      ∑ k ∈ Finset.range (N + 1), a k * b k by rfl]
  rw [endpointRace_sum_mul_eq_last_partial_add]
  calc
    _ ≤ 416 / (m : Real) ^ 2 +
        ∑ k ∈ Finset.range N,
          26 * Real.sqrt (k + 1 : Real) / (m : Real) ^ 5 := by
      exact add_le_add hlast (Finset.sum_le_sum fun k hk => hterm k)
    _ ≤ 416 / (m : Real) ^ 2 +
        (N : Real) * (52 * (m : Real) / (m : Real) ^ 5) := by
      apply add_le_add (le_refl _)
      calc
        _ ≤ ∑ k ∈ Finset.range N,
            52 * (m : Real) / (m : Real) ^ 5 := by
          apply Finset.sum_le_sum
          intro k hk
          have hkN : k ≤ N := (Finset.mem_range.mp hk).le
          apply div_le_div_of_nonneg_right _ hm5.le
          have := hsqrt k hkN
          nlinarith
        _ = (N : Real) * (52 * (m : Real) / (m : Real) ^ 5) := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
    _ ≤ 416 / (m : Real) ^ 2 + 52 / (m : Real) ^ 2 := by
      apply add_le_add (le_refl _)
      calc
        (N : Real) * (52 * (m : Real) / (m : Real) ^ 5) ≤
            (m : Real) ^ 2 * (52 * (m : Real) / (m : Real) ^ 5) :=
          mul_le_mul_of_nonneg_right hNReal (by positivity)
        _ = 52 / (m : Real) ^ 2 := by field_simp
    _ = 468 / (m : Real) ^ 2 := by ring



def IsingEndpointFarEscapeWitnessFamily
    (m t : Nat) (start target : Int) :=
  Σ j : Fin (t + 1),
    IsingLineFarFirstBoundaryFamily m j ×
      VerticalChoicePathFamily j start target ×
        {tail : List (Bool × Bool) // tail.length = t - j}

noncomputable instance isingEndpointFarEscapeWitnessFamily_finite
    (m t : Nat) (start target : Int) :
    Finite (IsingEndpointFarEscapeWitnessFamily m t start target) := by
  letI (j : Fin (t + 1)) :
      Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype (VerticalChoicePathFamily j start target) := Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - j} :=
    (List.finite_length_eq (Bool × Bool) (t - j)).fintype
  change Finite (Σ j : Fin (t + 1),
    IsingLineFarFirstBoundaryFamily m j ×
      VerticalChoicePathFamily j start target ×
        {tail : List (Bool × Bool) // tail.length = t - j})
  infer_instance


theorem endpointFarEscapeWitness_weight_le
    (m t : Nat) (start target : Int) (hm : 0 < m) (ht : t ≤ m * m) :
    Nat.card (IsingEndpointFarEscapeWitnessFamily m t start target) /
        (4 : Real) ^ t ≤
      468 / (m : Real) ^ 2 := by
  have hcard : Nat.card (IsingEndpointFarEscapeWitnessFamily
      m t start target) =
      ∑ j : Fin (t + 1),
        Nat.card (IsingLineFarFirstBoundaryFamily m j) *
          Nat.card (VerticalChoicePathFamily j start target) *
            4 ^ (t - j) := by
    letI (j : Fin (t + 1)) :
        Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (t + 1)) :
        Fintype (VerticalChoicePathFamily j start target) := Fintype.ofFinite _
    letI (j : Fin (t + 1)) :
        Fintype {tail : List (Bool × Bool) // tail.length = t - j} :=
      (List.finite_length_eq (Bool × Bool) (t - j)).fintype
    change Nat.card (Σ j : Fin (t + 1),
      IsingLineFarFirstBoundaryFamily m j ×
        VerticalChoicePathFamily j start target ×
          {tail : List (Bool × Bool) // tail.length = t - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    have htail : Nat.card
        {tail : List (Bool × Bool) // tail.length = t - (j : Nat)} =
        4 ^ (t - (j : Nat)) := by
      change Nat.card (List.Vector (Bool × Bool) (t - (j : Nat))) =
        4 ^ (t - (j : Nat))
      rw [Nat.card_congr
          (Equiv.vectorEquivFin (Bool × Bool) (t - (j : Nat))),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      norm_num
    calc
      Nat.card (IsingLineFarFirstBoundaryFamily m j ×
          VerticalChoicePathFamily j start target ×
            {tail : List (Bool × Bool) // tail.length = t - j}) =
        Nat.card (IsingLineFarFirstBoundaryFamily m j) *
          (Nat.card (VerticalChoicePathFamily j start target) *
            Nat.card {tail : List (Bool × Bool) // tail.length = t - j}) := by
          rw [Nat.card_prod, Nat.card_prod]
      _ = _ := by rw [htail]; ring
  have hmass :
      Nat.card (IsingEndpointFarEscapeWitnessFamily m t start target) /
          (4 : Real) ^ t =
        ∑ j ∈ Finset.range (t + 1),
          (Nat.card (VerticalChoicePathFamily j start target) /
              (2 : Real) ^ j) *
            (Nat.card (IsingLineFarFirstBoundaryFamily m j) /
              (2 : Real) ^ j) := by
    rw [hcard]
    push_cast
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat =>
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
          (Nat.card (VerticalChoicePathFamily j start target) : Real) *
            (4 : Real) ^ (t - j)) (t + 1)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hjt : j ≤ t := by
      have := Finset.mem_range.mp hj
      omega
    have hfour : (4 : Real) ^ t =
        (4 : Real) ^ j * (4 : Real) ^ (t - j) := by
      calc
        (4 : Real) ^ t = (4 : Real) ^ (j + (t - j)) := by
          congr 1
          omega
        _ = _ := pow_add _ _ _
    have htwo : (4 : Real) ^ j =
        (2 : Real) ^ j * (2 : Real) ^ j := by
      rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
    rw [hfour, htwo]
    field_simp
  rw [hmass]
  calc
    _ ≤ ∑ j ∈ Finset.range (t + 1),
        (2 / Real.sqrt (j + 1 : Real)) *
          (Nat.card (IsingLineFarFirstBoundaryFamily m j) /
            (2 : Real) ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right
      · rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
        let K := isingLineBinomialKernel j start target
        have hK0 : 0 ≤ K := isingLineBinomialKernel_nonneg _ _ _
        have hrad : 0 ≤ 2 / (j + 1 : Real) := by positivity
        have hK : K ≤ Real.sqrt (2 / (j + 1 : Real)) := by
          rw [Real.le_sqrt hK0 hrad]
          exact isingLineBinomialKernel_sq_le j start target
        calc
          K ≤ Real.sqrt (2 / (j + 1 : Real)) := hK
          _ ≤ 2 / Real.sqrt (j + 1 : Real) := by
            rw [Real.sqrt_div (by positivity)]
            apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
            have hsqrt2 : Real.sqrt (2 : Real) ≤ 2 := by
              rw [Real.sqrt_le_iff]
              norm_num
            exact hsqrt2
      · positivity
    _ ≤ 468 / (m : Real) ^ 2 :=
      endpointKernel_farFirstBoundary_sum_le m t hm ht

theorem endpointFarEscapeWitness_diffusive_weight_le
    (rho m : Nat) (start target : Int) (hρ : 0 < rho) (hm : rho ≤ m) :
    Nat.card (IsingEndpointFarEscapeWitnessFamily
          m (rho * rho) start target) /
        (4 : Real) ^ (rho * rho) ≤
      468 / (rho : Real) ^ 2 := by
  have hm0 : 0 < m := lt_of_lt_of_le hρ hm
  have ht : rho * rho ≤ m * m := Nat.mul_self_le_mul_self hm
  have h := endpointFarEscapeWitness_weight_le
    m (rho * rho) start target hm0 ht
  have hrm : (rho : Real) ^ 2 ≤ (m : Real) ^ 2 := by
    exact_mod_cast (show rho ^ 2 ≤ m ^ 2 by
      simpa [pow_two] using ht)
  calc
    _ ≤ 468 / (m : Real) ^ 2 := h
    _ ≤ 468 / (rho : Real) ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hrm

end

end StatMech.Universality
