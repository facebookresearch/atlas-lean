/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicWalkReflection









namespace StatMech.Universality

open Finset

noncomputable section

abbrev IsingLineBox (n : Nat) := Fin (n + 1)

def isingLineBoxBoundary (n : Nat) (p : IsingLineBox n) : Prop :=
  p.1 = 0 ∨ p.1 = n

private noncomputable instance isingLineBoxBoundary_decidable
    (n : Nat) (p : IsingLineBox n) :
    Decidable (isingLineBoxBoundary n p) := Classical.propDecidable _

def isingLineWest (n : Nat) (p : IsingLineBox n) : IsingLineBox n :=
  ⟨p.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) p.2⟩

def isingLineEast (n : Nat) (p : IsingLineBox n)
    (hp : ¬ isingLineBoxBoundary n p) : IsingLineBox n :=
  ⟨p.1 + 1, by
    have hle := p.2
    unfold isingLineBoxBoundary at hp
    omega⟩


noncomputable def isingLineStoppedKernel (n : Nat) :
    Nat → IsingLineBox n → IsingLineBox n → Real
  | 0, p, q => if p = q then 1 else 0
  | t + 1, p, q =>
      if hp : isingLineBoxBoundary n p then
        isingLineStoppedKernel n t p q
      else
        (isingLineStoppedKernel n t (isingLineWest n p) q +
          isingLineStoppedKernel n t (isingLineEast n p hp) q) / 2

theorem isingLineStoppedKernel_nonneg (n t : Nat)
    (p q : IsingLineBox n) :
    0 ≤ isingLineStoppedKernel n t p q := by
  induction t generalizing p with
  | zero =>
      unfold isingLineStoppedKernel
      split_ifs <;> norm_num
  | succ t ih =>
      simp only [isingLineStoppedKernel]
      split_ifs with hp
      · exact ih p
      · have hw := ih (isingLineWest n p)
        have he := ih (isingLineEast n p hp)
        positivity

theorem isingLineStoppedKernel_sum_eq_one (n t : Nat)
    (p : IsingLineBox n) :
    ∑ q, isingLineStoppedKernel n t p q = 1 := by
  induction t generalizing p with
  | zero => simp [isingLineStoppedKernel]
  | succ t ih =>
      simp only [isingLineStoppedKernel]
      split_ifs with hp
      · exact ih p
      · rw [← Finset.sum_div, Finset.sum_add_distrib, ih, ih]
        norm_num

noncomputable def isingLineStoppedMean (n t : Nat)
    (f : IsingLineBox n → Real) (p : IsingLineBox n) : Real :=
  ∑ q, isingLineStoppedKernel n t p q * f q

def IsingLineHarmonic (n : Nat) (f : IsingLineBox n → Real) : Prop :=
  ∀ p (hp : ¬ isingLineBoxBoundary n p),
    f (isingLineWest n p) + f (isingLineEast n p hp) = 2 * f p

theorem isingLineStoppedMean_succ (n t : Nat)
    (f : IsingLineBox n → Real) (p : IsingLineBox n) :
    isingLineStoppedMean n (t + 1) f p =
      if hp : isingLineBoxBoundary n p then
        isingLineStoppedMean n t f p
      else
        (isingLineStoppedMean n t f (isingLineWest n p) +
          isingLineStoppedMean n t f (isingLineEast n p hp)) / 2 := by
  classical
  unfold isingLineStoppedMean
  by_cases hp : isingLineBoxBoundary n p
  · simp [isingLineStoppedKernel, hp]
  · simp only [isingLineStoppedKernel, dif_neg hp]
    calc
      _ = ∑ x, (isingLineStoppedKernel n t (isingLineWest n p) x * f x +
          isingLineStoppedKernel n t (isingLineEast n p hp) x * f x) / 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_add_distrib]

theorem IsingLineHarmonic.stoppedMean_eq {n : Nat}
    {f : IsingLineBox n → Real} (hf : IsingLineHarmonic n f)
    (t : Nat) (p : IsingLineBox n) :
    isingLineStoppedMean n t f p = f p := by
  induction t generalizing p with
  | zero => simp [isingLineStoppedMean, isingLineStoppedKernel]
  | succ t ih =>
      rw [isingLineStoppedMean_succ]
      by_cases hp : isingLineBoxBoundary n p
      · simp [hp, ih]
      · simp only [dif_neg hp, ih]
        rw [hf p hp]
        ring


theorem isingLineDistanceToRight_harmonic (n : Nat) :
    IsingLineHarmonic n (fun p => (n - p.1 : Nat)) := by
  intro p hp
  unfold isingLineBoxBoundary at hp
  unfold isingLineWest isingLineEast
  change ((n - (p.1 - 1) : Nat) : Real) +
      ((n - (p.1 + 1) : Nat) : Real) =
    2 * ((n - p.1 : Nat) : Real)
  norm_cast
  omega

theorem isingLineStoppedMean_distanceToRight (n t : Nat)
    (p : IsingLineBox n) :
    isingLineStoppedMean n t (fun q => (n - q.1 : Nat)) p =
      (n - p.1 : Nat) :=
  (isingLineDistanceToRight_harmonic n).stoppedMean_eq t p



theorem isingLineStoppedKernel_left_mul_le (n t : Nat)
    (p : IsingLineBox n) :
    (n : Real) * isingLineStoppedKernel n t p ⟨0, by omega⟩ ≤
      (n - p.1 : Nat) := by
  classical
  let left : IsingLineBox n := ⟨0, by omega⟩
  have hterm : (n : Real) * isingLineStoppedKernel n t p left =
      isingLineStoppedKernel n t p left * (n - left.1 : Nat) := by
    simp [left]
    ring
  rw [hterm, ← isingLineStoppedMean_distanceToRight n t p]
  unfold isingLineStoppedMean
  let g : IsingLineBox n → Real := fun q =>
    isingLineStoppedKernel n t p q * (n - q.1 : Nat)
  change g left ≤ ∑ q, g q
  unfold g
  refine Finset.single_le_sum
    (f := fun q : IsingLineBox n =>
      isingLineStoppedKernel n t p q * ((n - q.1 : Nat) : Real)) ?_
    (Finset.mem_univ left)
  intro q hq
  exact mul_nonneg (isingLineStoppedKernel_nonneg n t p q) (by positivity)

theorem isingLineStoppedKernel_left_le (n t : Nat)
    (p : IsingLineBox n) (hn : 0 < n) :
    isingLineStoppedKernel n t p ⟨0, by omega⟩ ≤
      ((n - p.1 : Nat) : Real) / n := by
  apply (le_div_iff₀ (by exact_mod_cast hn)).2
  simpa [mul_comm] using isingLineStoppedKernel_left_mul_le n t p



theorem isingLineStoppedKernel_left_of_rightNeighbor (n t : Nat)
    (hn : 0 < n) :
    isingLineStoppedKernel n t ⟨n - 1, by omega⟩ ⟨0, by omega⟩ ≤
      1 / (n : Real) := by
  have h := isingLineStoppedKernel_left_le n t
    (⟨n - 1, by omega⟩ : IsingLineBox n) hn
  have hsub : n - (n - 1) = 1 := by omega
  simpa [hsub] using h



noncomputable def isingLineChoiceNext (n : Nat) (p : IsingLineBox n)
    (b : Bool) : IsingLineBox n :=
  if hp : isingLineBoxBoundary n p then p
  else if b then isingLineEast n p hp else isingLineWest n p

noncomputable def isingLineChoiceRun (n : Nat) :
    IsingLineBox n → List Bool → IsingLineBox n
  | p, [] => p
  | p, b :: bs => isingLineChoiceRun n (isingLineChoiceNext n p b) bs

def IsingLineChoicePathFamily (n t : Nat)
    (p q : IsingLineBox n) :=
  {bs : List Bool // bs.length = t ∧ isingLineChoiceRun n p bs = q}

noncomputable instance isingLineChoicePathFamily_finite
    (n t : Nat) (p q : IsingLineBox n) :
    Finite (IsingLineChoicePathFamily n t p q) := by
  letI : Fintype {bs : List Bool // bs.length = t} :=
    (List.finite_length_eq Bool t).fintype
  exact Finite.of_injective
    (fun w : IsingLineChoicePathFamily n t p q =>
      (⟨w.1, w.2.1⟩ : {bs : List Bool // bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun x : {bs : List Bool // bs.length = t} => x.1) h)

private def isingLineChoicePathFamilySuccEquiv (n t : Nat)
    (p q : IsingLineBox n) :
    IsingLineChoicePathFamily n (t + 1) p q ≃
      Σ b : Bool, IsingLineChoicePathFamily n t
        (isingLineChoiceNext n p b) q where
  toFun w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
        exact ⟨b, ⟨bs, by simpa using hlen, by
          simpa [isingLineChoiceRun] using hend⟩⟩
  invFun w := ⟨w.1 :: w.2.1, by simp [w.2.2.1], by
    simpa [isingLineChoiceRun] using w.2.2.2⟩
  left_inv w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs => rfl
  right_inv w := by
    rcases w with ⟨b, bs, hlen, hend⟩
    rfl

private def isingLineChoicePathFamilyZeroSelfEquiv (n : Nat)
    (p : IsingLineBox n) :
    IsingLineChoicePathFamily n 0 p p ≃ ULift.{1, 0} Unit where
  toFun _ := ⟨Unit.unit⟩
  invFun _ := ⟨[], rfl, rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.eq_nil_of_length_eq_zero w.2.1).symm
  right_inv _ := rfl

private def isingLineChoicePathFamilyZeroNeEquiv (n : Nat)
    (p q : IsingLineBox n) (hpq : p ≠ q) :
    IsingLineChoicePathFamily n 0 p q ≃ Empty where
  toFun w := by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    have : p = q := by simpa [hnil, isingLineChoiceRun] using w.2.2
    exact (hpq this).elim
  invFun e := e.elim
  left_inv w := (hpq (by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    simpa [hnil, isingLineChoiceRun] using w.2.2)).elim
  right_inv e := e.elim



theorem isingLineStoppedKernel_eq_natCard_choicePath_div (n t : Nat)
    (p q : IsingLineBox n) :
    isingLineStoppedKernel n t p q =
      Nat.card (IsingLineChoicePathFamily n t p q) / (2 : Real) ^ t := by
  induction t generalizing p with
  | zero =>
      by_cases hpq : p = q
      · subst q
        rw [Nat.card_congr (isingLineChoicePathFamilyZeroSelfEquiv n p)]
        simp [isingLineStoppedKernel]
      · rw [Nat.card_congr
          (isingLineChoicePathFamilyZeroNeEquiv n p q hpq)]
        simp [isingLineStoppedKernel, hpq]
  | succ t ih =>
      rw [show isingLineStoppedKernel n (t + 1) p q =
          if hp : isingLineBoxBoundary n p then
            isingLineStoppedKernel n t p q
          else
            (isingLineStoppedKernel n t (isingLineWest n p) q +
              isingLineStoppedKernel n t (isingLineEast n p hp) q) / 2 by
        rfl]
      rw [Nat.card_congr (isingLineChoicePathFamilySuccEquiv n t p q),
        Nat.card_sigma]
      by_cases hp : isingLineBoxBoundary n p
      · simp only [dif_pos hp, isingLineChoiceNext, hp, ↓reduceDIte]
        rw [ih]
        simp
        rw [pow_succ]
        ring
      · simp only [dif_neg hp, isingLineChoiceNext, hp, ↓reduceDIte]
        rw [ih, ih]
        simp
        push_cast
        rw [pow_succ]
        ring

end

end StatMech.Universality
