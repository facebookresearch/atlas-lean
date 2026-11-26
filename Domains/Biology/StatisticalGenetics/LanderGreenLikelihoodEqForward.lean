/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

/-!
# The Lander–Green forward recursion

In a pedigree with `n` meioses, the inheritance vector at a locus records, for each meiosis,
whether the grandpaternal or grandmaternal allele was transmitted. This module defines the
inheritance vector (`InheritanceVector`), the Lander–Green transition (`transition`), the
uniform prior (`uniformPrior`), the path weight (`pathWeight`), the pedigree likelihood
(`likelihood`) and the forward vectors (`forward`), and proves that the pedigree likelihood
equals the sum of the last forward vector (`likelihood_eq_forward`).

## References

* E. S. Lander and P. Green, "Construction of multilocus genetic linkage maps in humans",
  Proc. Natl. Acad. Sci. USA 84 (1987) 2363–2367, pp. 2365–2366.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.LanderGreenWanted

open Finset

/-- An inheritance vector for `n` meioses. -/
abbrev InheritanceVector (n : ℕ) := Fin n → Bool

/-- The Lander–Green transition probability between inheritance vectors at adjacent loci with
recombination fraction `θ` and no interference: `θᵈ (1 - θ)ⁿ⁻ᵈ`, where `d = hammingDist v w` is
the number of meioses whose transmitted grandparental origin differs (Mathlib's Hamming
distance). As a function of `θ` this is the bit-flip kernel; it models recombination for
`0 ≤ θ ≤ 1/2`. -/
noncomputable def transition {n : ℕ} (θ : ℝ) (v w : InheritanceVector n) : ℝ :=
  θ ^ hammingDist v w * (1 - θ) ^ (n - hammingDist v w)

/-- The uniform law of the inheritance vector at the first locus. -/
noncomputable def uniformPrior (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

/-- The joint weight of a path `v₀, …, vₘ` of inheritance vectors at `m + 1` ordered loci and of
the marker data: the uniform prior of `v₀`, the transitions with recombination fractions `θ i`
between loci `i` and `i + 1`, and the likelihoods `q i (v i)` of the data at each locus. -/
noncomputable def pathWeight {n m : ℕ} (θ : ℕ → ℝ) (q : ℕ → InheritanceVector n → ℝ)
    (v : Fin (m + 1) → InheritanceVector n) : ℝ :=
  uniformPrior n * (∏ i : Fin (m + 1), q i (v i)) *
    ∏ i : Fin m, transition (θ i) (v i.castSucc) (v i.succ)

/-- The pedigree likelihood of the marker data at `m + 1` loci: the sum of `pathWeight` over all
paths of inheritance vectors. -/
noncomputable def likelihood {n : ℕ} (m : ℕ) (θ : ℕ → ℝ) (q : ℕ → InheritanceVector n → ℝ) :
    ℝ :=
  ∑ v : Fin (m + 1) → InheritanceVector n, pathWeight θ q v

/-- The forward vectors of the hidden Markov chain: `α₀(w) = 2⁻ⁿ q₀(w)` and
`αᵢ₊₁(w) = qᵢ₊₁(w) ∑ᵥ αᵢ(v) T(θᵢ)_{vw}`. -/
noncomputable def forward {n : ℕ} (θ : ℕ → ℝ) (q : ℕ → InheritanceVector n → ℝ) :
    ℕ → InheritanceVector n → ℝ
  | 0, w => uniformPrior n * q 0 w
  | i + 1, w => q (i + 1) w * ∑ v, forward θ q i v * transition (θ i) v w

private theorem aux_q {n m : ℕ} (q : ℕ → InheritanceVector n → ℝ)
    (u : Fin (m + 1) → InheritanceVector n) (w : InheritanceVector n) :
    (∏ i : Fin (m + 1 + 1), q i ((Fin.snoc u w : Fin (m + 1 + 1) → InheritanceVector n) i)) =
      (∏ i : Fin (m + 1), q i (u i)) * q (m + 1) w := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

private theorem aux_t {n m : ℕ} (θ : ℕ → ℝ)
    (u : Fin (m + 1) → InheritanceVector n) (w : InheritanceVector n) :
    (∏ i : Fin (m + 1), transition (θ i)
      ((Fin.snoc u w : Fin (m + 1 + 1) → InheritanceVector n) i.castSucc)
      ((Fin.snoc u w : Fin (m + 1 + 1) → InheritanceVector n) i.succ)) =
      (∏ i : Fin m, transition (θ i) (u i.castSucc) (u i.succ)) *
        transition (θ m) (u (Fin.last m)) w := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc]
  have h_inner : ∀ x : Fin m,
      (Fin.snoc u w : Fin (m + 1 + 1) → InheritanceVector n) x.castSucc.succ =
        u x.succ := by
    intro x
    rw [← Fin.castSucc_succ x]
    simp only [Fin.snoc_castSucc]
  have h_last : (Fin.snoc u w : Fin (m + 1 + 1) → InheritanceVector n) (Fin.last m).succ = w := by
    have h : (Fin.last m).succ = Fin.last (m + 1) := rfl
    rw [h]
    simp only [Fin.snoc_last]
  simp_rw [h_inner]
  rw [h_last]
  rfl

private theorem pathWeight_snoc {n m : ℕ} (θ : ℕ → ℝ) (q : ℕ → InheritanceVector n → ℝ)
    (u : Fin (m + 1) → InheritanceVector n) (w : InheritanceVector n) :
    pathWeight (m := m + 1) θ q (Fin.snoc u w) =
      pathWeight (m := m) θ q u * q (m + 1) w *
        transition (θ m) (u (Fin.last m)) w := by
  unfold pathWeight
  rw [aux_q q u w, aux_t θ u w]
  ring

private def finOneEquiv (n : ℕ) : (Fin 1 → InheritanceVector n) ≃ InheritanceVector n where
  toFun v := v 0
  invFun w := fun _ => w
  left_inv v := by
    funext i
    have h : i = 0 := Subsingleton.elim i 0
    rw [h]
  right_inv w := rfl

private theorem sum_snoc {n m : ℕ}
    (g : (Fin (m + 1 + 1) → InheritanceVector n) → ℝ) :
    (∑ v, g v) = ∑ w : InheritanceVector n,
      ∑ u : Fin (m + 1) → InheritanceVector n, g (Fin.snoc u w) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (m + 1 + 1) => InheritanceVector n)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.snocEquiv_apply]

private theorem sum_pathWeight_mul {n : ℕ} (θ : ℕ → ℝ) (q : ℕ → InheritanceVector n → ℝ) (m : ℕ)
    (f : InheritanceVector n → ℝ) :
    ∑ v : Fin (m + 1) → InheritanceVector n, pathWeight θ q v * f (v (Fin.last m)) =
      ∑ w, forward θ q m w * f w := by
  induction m generalizing f with
  | zero =>
    rw [← (finOneEquiv n).symm.sum_comp _]
    apply Finset.sum_congr rfl
    intro w _
    unfold pathWeight forward
    rw [Fin.prod_univ_one, Fin.prod_univ_zero]
    simp [finOneEquiv]
  | succ m ih =>
    have h1 : (∑ v : Fin (m + 1 + 1) → InheritanceVector n,
          pathWeight (m := m + 1) θ q v * f (v (Fin.last (m + 1)))) =
        ∑ w : InheritanceVector n, ∑ u : Fin (m + 1) → InheritanceVector n,
          pathWeight (m := m) θ q u * q (m + 1) w *
            transition (θ m) (u (Fin.last m)) w * f w := by
      rw [sum_snoc]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro u _
      rw [pathWeight_snoc θ q u w, Fin.snoc_last]
    have h2 : (∑ w : InheritanceVector n, ∑ u : Fin (m + 1) → InheritanceVector n,
          pathWeight (m := m) θ q u * q (m + 1) w * transition (θ m) (u (Fin.last m)) w * f w) =
        ∑ u : Fin (m + 1) → InheritanceVector n, pathWeight (m := m) θ q u *
          (∑ w : InheritanceVector n, q (m + 1) w * transition (θ m) (u (Fin.last m)) w * f w) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    have h3 : (∑ u : Fin (m + 1) → InheritanceVector n, pathWeight (m := m) θ q u *
          (∑ w : InheritanceVector n, q (m + 1) w * transition (θ m) (u (Fin.last m)) w * f w)) =
        ∑ v, forward θ q m v *
          (∑ w : InheritanceVector n, q (m + 1) w * transition (θ m) v w * f w) :=
      ih (fun v => ∑ w : InheritanceVector n, q (m + 1) w * transition (θ m) v w * f w)
    have h4 : (∑ v : InheritanceVector n, forward θ q m v *
          (∑ w : InheritanceVector n, q (m + 1) w * transition (θ m) v w * f w)) =
        ∑ w : InheritanceVector n, forward θ q (m + 1) w * f w := by
      have e1 : (∑ v : InheritanceVector n, forward θ q m v *
            (∑ w : InheritanceVector n, q (m + 1) w * transition (θ m) v w * f w)) =
          ∑ v : InheritanceVector n, ∑ w : InheritanceVector n,
            forward θ q m v * q (m + 1) w * transition (θ m) v w * f w := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      have e2 : (∑ v : InheritanceVector n, ∑ w : InheritanceVector n,
            forward θ q m v * q (m + 1) w * transition (θ m) v w * f w) =
          ∑ w : InheritanceVector n, ∑ v : InheritanceVector n,
            forward θ q m v * q (m + 1) w * transition (θ m) v w * f w :=
        Finset.sum_comm
      have e3 : ∀ w : InheritanceVector n, (∑ v : InheritanceVector n,
            forward θ q m v * q (m + 1) w * transition (θ m) v w * f w) =
          forward θ q (m + 1) w * f w := by
        intro w
        have hfw : forward θ q (m + 1) w =
            q (m + 1) w * ∑ v, forward θ q m v * transition (θ m) v w := rfl
        rw [hfw, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v _
        ring
      rw [e1, e2]
      apply Finset.sum_congr rfl
      intro w _
      exact e3 w
    rw [h1, h2, h3]
    exact h4

/-- **The Lander–Green forward recursion** (Lander and Green 1987, pp. 2365–2366): for any
number `n` of meioses and `m + 1` ordered loci, recombination fractions `θ i` with
`0 ≤ θ i ≤ 1/2` between loci `i` and `i + 1`, and data likelihood vectors `q i` satisfying
`0 ≤ q i w ≤ 1` for every locus `i ≤ m` and inheritance vector `w`, the pedigree likelihood of
the data, a sum over all `2^(n(m + 1))` paths of inheritance vectors, equals the sum of the last
forward vector, which the recursion computes one locus at a time.

Source: Lander and Green (1987), pp. 2365–2366. -/
public theorem likelihood_eq_forward (n m : ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1 / 2) (q : ℕ → InheritanceVector n → ℝ)
    (hq : ∀ i ≤ m, ∀ w, 0 ≤ q i w ∧ q i w ≤ 1) :
    likelihood m θ q = ∑ w, forward θ q m w := by
  have _ := hθ
  have _ := hq
  have h := sum_pathWeight_mul θ q m (fun _ => 1)
  simpa [likelihood, mul_one] using h

end WantedExt.Biology.StatisticalGenetics.LanderGreenWanted
