/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The BLR linearity test over `ZMod 2`

The Blum–Luby–Rubinfeld (BLR) test checks whether a function `f : (ZMod 2)ⁿ → ZMod 2` is
linear: draw `x` and `y` independently and uniformly from `(ZMod 2)ⁿ` and accept when
`f (x + y) = f x + f y`. Probabilities are finite counts: `acceptProb f` is the number of
accepting pairs `(x, y)` (`blrAccepts f`) divided by the number `4ⁿ` of all pairs, and
`disagreeProb f g` is the fraction of the `2ⁿ` inputs on which `f` and `g` differ. The linear
functions are `linFun a`, the map `x ↦ a ⬝ᵥ x` given by Mathlib's `dotProduct` (`linFun_apply`).

## Main results

* `blr_complete`: a linear function passes the test with probability `1`.
* `blr_soundness`: if `f` passes with probability at least `1 - ε`, then
  `disagreeProb f (linFun a) ≤ ε` for some `a`. The soundness constant is normalized so that a
  rejection probability `ε` bounds the distance to the nearest linear function by `ε`, as in the
  Fourier-analytic proof.

## Proof

With the sign characters `χ_a x = (-1)^(a ⬝ᵥ x)` and `F x = (-1)^(f x)`, write
`F̂ a = ∑ x, F x * χ_a x`. Character orthogonality gives Parseval, `∑ a, F̂ a ^ 2 = 4ⁿ`, and the
cubic identity `∑ a, F̂ a ^ 3 = 2ⁿ ∑ x, ∑ y, F x * F y * F (x + y)`; the double sum counts
accepting minus rejecting pairs. So acceptance with probability at least `1 - ε` forces
`F̂ a ≥ (1 - 2ε) 2ⁿ` for some `a`, and the number of inputs where `f` and `linFun a` differ is
`(2ⁿ - F̂ a) / 2`.

## References

* M. Blum, M. Luby and R. Rubinfeld, *Self-testing/correcting with applications to numerical
  problems*, J. Comput. System Sci. 47 (1993) 549–595.
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press (2014), Chapter 1.
-/

@[expose] public section

open Finset

namespace MathlibExt.Complexity.LinearityTest

variable {n : ℕ}

/-- The linear function `x ↦ a ⬝ᵥ x` over `ZMod 2` (Mathlib's `dotProduct`), as a function that
can be passed to `acceptProb` and `disagreeProb`; `linFun_apply` unfolds it. -/
def linFun (a : Fin n → ZMod 2) (x : Fin n → ZMod 2) : ZMod 2 :=
  dotProduct a x

@[simp]
theorem linFun_apply (a x : Fin n → ZMod 2) : linFun a x = dotProduct a x :=
  rfl

/-- The pairs `(x, y)` on which the BLR linearity test accepts
`f`, i.e. `f (x + y) = f x + f y`. -/
def blrAccepts (f : (Fin n → ZMod 2) → ZMod 2) :
    Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  Finset.univ.filter (fun p => f (p.1 + p.2) = f p.1 + f p.2)

/-- Acceptance probability of the BLR test for `f`, as a ratio
of finite counts. -/
noncomputable def acceptProb (f : (Fin n → ZMod 2) → ZMod 2) : ℝ :=
  (blrAccepts f).card
    / (Fintype.card ((Fin n → ZMod 2) × (Fin n → ZMod 2)) : ℝ)

/-- Probability that `f` and `g` disagree on a uniform input. -/
noncomputable def disagreeProb (f g : (Fin n → ZMod 2) → ZMod 2) : ℝ :=
  (Finset.univ.filter (fun x => f x ≠ g x)).card
    / (Fintype.card (Fin n → ZMod 2) : ℝ)

private def sgn (t : ZMod 2) : ℝ := (-1 : ℝ) ^ (ZMod.val t)

private theorem two_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

private theorem sgn_one : sgn (1 : ZMod 2) = -1 := by
  have v1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  simp [sgn, v1]

private theorem sgn_zero : sgn (0 : ZMod 2) = 1 := by
  have v0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  simp [sgn, v0]

private theorem sgn_add (u v : ZMod 2) : sgn (u + v) = sgn u * sgn v := by
  have v0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  have v1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  have v00 : ZMod.val ((0 : ZMod 2) + 0) = 0 := by decide
  have v01 : ZMod.val ((0 : ZMod 2) + 1) = 1 := by decide
  have v10 : ZMod.val ((1 : ZMod 2) + 0) = 1 := by decide
  have v11 : ZMod.val ((1 : ZMod 2) + 1) = 0 := by decide
  rcases two_cases u with rfl | rfl <;> rcases two_cases v with rfl | rfl <;>
    simp only [sgn, v00, v01, v10, v11, v0, v1] <;> norm_num

private theorem linFun_add_left (a b x : Fin n → ZMod 2) :
    linFun (a + b) x = linFun a x + linFun b x := by
  simp only [linFun_apply, add_dotProduct]

private theorem linFun_zero_right (a : Fin n → ZMod 2) : linFun a 0 = 0 := by
  simp only [linFun_apply, dotProduct_zero]

private def chi (a x : Fin n → ZMod 2) : ℝ := sgn (linFun a x)

private theorem chi_add_left (a b x : Fin n → ZMod 2) :
    chi (a + b) x = chi a x * chi b x := by
  unfold chi
  rw [linFun_add_left]
  exact sgn_add _ _

private theorem chi_add_right (a x y : Fin n → ZMod 2) :
    chi a (x + y) = chi a x * chi a y := by
  unfold chi
  have h : linFun a (x + y) = linFun a x + linFun a y := by
    simp only [linFun_apply, dotProduct_add]
  rw [h]
  exact sgn_add _ _

private theorem chi_zero_right (a : Fin n → ZMod 2) : chi a 0 = 1 := by
  unfold chi
  rw [linFun_zero_right]
  exact sgn_zero

private theorem ortho (w : Fin n → ZMod 2) :
    ∑ a, chi a w = if w = 0 then (Fintype.card (Fin n → ZMod 2) : ℝ) else 0 := by
  by_cases hw : w = 0
  · subst hw
    simp [chi_zero_right]
  · simp only [hw, ↓reduceIte]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
    rw [Pi.zero_apply] at hj
    have hwj1 : w j = 1 := by
      rcases two_cases (w j) with h | h
      · exact absurd h hj
      · exact h
    set s : Fin n → ZMod 2 := Pi.single j 1 with hs
    have hsw : linFun s w = 1 := by
      have hsum : linFun s w = w j := by
        unfold linFun dotProduct
        rw [Finset.sum_eq_single j]
        · rw [hs, Pi.single_eq_same, one_mul]
        · intro i _ hij
          rw [hs, Pi.single_eq_of_ne hij, zero_mul]
        · intro hjc
          exact absurd (Finset.mem_univ j) hjc
      rw [hsum, hwj1]
    have hss : s + s = 0 := by
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      calc s + s = Pi.single j ((1 : ZMod 2) + 1) := by rw [hs]; exact (Pi.single_add j 1 1).symm
        _ = Pi.single j 0 := by rw [h11]
        _ = 0 := Pi.single_zero j
    have hflip : ∀ a : Fin n → ZMod 2, chi (a + s) w = -chi a w := by
      intro a
      rw [chi_add_left]
      have hchi : chi s w = -1 := by unfold chi; rw [hsw]; exact sgn_one
      rw [hchi]
      ring
    have hne : ∀ t : ZMod 2, t + 1 ≠ t := by decide
    apply Finset.sum_ninvolution (s := Finset.univ) (f := fun a => chi a w) (fun a => a + s)
    · intro a
      rw [hflip]
      ring
    · intro a _ hcon
      have hcj := congrFun hcon j
      rw [Pi.add_apply, hs, Pi.single_eq_same] at hcj
      exact hne _ hcj
    · intro a
      exact Finset.mem_univ _
    · intro a
      show (a + s) + s = a
      rw [add_assoc, hss, add_zero]

private theorem add_eq_zero_iff_eq (x y : Fin n → ZMod 2) : x + y = 0 ↔ y = x := by
  have h : ∀ u v : ZMod 2, u + v = 0 ↔ v = u := by decide
  constructor
  · intro hxy
    funext i
    have hi := congrFun hxy i
    rw [Pi.add_apply, Pi.zero_apply] at hi
    exact (h _ _).mp hi
  · intro hyx
    subst hyx
    have h2 : ∀ t : ZMod 2, t + t = 0 := by decide
    funext i
    rw [Pi.add_apply, Pi.zero_apply]
    exact h2 _

private theorem add3_eq_zero_iff_eq (x y z : Fin n → ZMod 2) :
    x + y + z = 0 ↔ z = x + y := by
  have h : ∀ u v w : ZMod 2, u + v + w = 0 ↔ w = u + v := by decide
  constructor
  · intro hxyz
    funext i
    have hi := congrFun hxyz i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    exact (h _ _ _).mp hi
  · intro hzyx
    subst hzyx
    have h2 : ∀ u v : ZMod 2, u + v + (u + v) = 0 := by decide
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact h2 _ _

private theorem collapse2 (G H : (Fin n → ZMod 2) → ℝ) :
    ∑ x, ∑ y, G x * H y * (if x + y = 0 then (Fintype.card (Fin n → ZMod 2) : ℝ) else 0)
      = (Fintype.card (Fin n → ZMod 2) : ℝ) * ∑ x, G x * H x := by
  have hcond : ∀ x y : Fin n → ZMod 2, (x + y = 0) ↔ (y = x) :=
    fun x y => add_eq_zero_iff_eq x y
  simp only [hcond]
  have hinner : ∀ x : Fin n → ZMod 2,
      (∑ y, G x * H y * (if y = x then (Fintype.card (Fin n → ZMod 2) : ℝ) else 0))
        = G x * H x * (Fintype.card (Fin n → ZMod 2) : ℝ) := by
    intro x
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x (fun y => G x * H y * (Fintype.card (Fin n → ZMod 2) : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem collapse3 (G H K : (Fin n → ZMod 2) → ℝ) :
    ∑ x, ∑ y, ∑ z, G x * H y * K z * (if x + y + z = 0 then (Fintype.card (Fin n → ZMod 2) : ℝ) else 0)
      = (Fintype.card (Fin n → ZMod 2) : ℝ) * ∑ x, ∑ y, G x * H y * K (x + y) := by
  have hcond : ∀ x y z : Fin n → ZMod 2, (x + y + z = 0) ↔ (z = x + y) :=
    fun x y z => add3_eq_zero_iff_eq x y z
  simp only [hcond]
  have hinner : ∀ x y : Fin n → ZMod 2,
      (∑ z, G x * H y * K z * (if z = x + y then (Fintype.card (Fin n → ZMod 2) : ℝ) else 0))
        = G x * H y * K (x + y) * (Fintype.card (Fin n → ZMod 2) : ℝ) := by
    intro x y
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ (x + y) (fun z => G x * H y * K z * (Fintype.card (Fin n → ZMod 2) : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hinner x y))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

private def pm1 (f : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) : ℝ := sgn (f x)

private theorem sgn_sq (t : ZMod 2) : sgn t * sgn t = 1 := by
  have v0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  have v1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  rcases two_cases t with rfl | rfl <;> simp only [sgn, v0, v1] <;> norm_num

private theorem parseval (f : (Fin n → ZMod 2) → ZMod 2) :
    ∑ a, (∑ x, pm1 f x * chi a x)^2 = (Fintype.card (Fin n → ZMod 2) : ℝ)^2 := by
  have step1 : ∀ a : Fin n → ZMod 2,
      (∑ x, pm1 f x * chi a x)^2
        = ∑ x, ∑ y, pm1 f x * pm1 f y * (chi a x * chi a y) := by
    intro a
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have step2 : (∑ a, ∑ x, ∑ y, pm1 f x * pm1 f y * (chi a x * chi a y))
      = ∑ x, ∑ y, pm1 f x * pm1 f y * (∑ a, chi a x * chi a y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.mul_sum]
  have hchi : ∀ x y : Fin n → ZMod 2, (∑ a, chi a x * chi a y)
      = (if x + y = 0 then (Fintype.card (Fin n → ZMod 2) : ℝ) else 0) := by
    intro x y
    calc (∑ a, chi a x * chi a y) = ∑ a, chi a (x + y) :=
            Finset.sum_congr rfl (fun a _ => (chi_add_right a x y).symm)
      _ = _ := ortho _
  have step3 : (∑ x, ∑ y, pm1 f x * pm1 f y * (∑ a, chi a x * chi a y))
      = ∑ x, ∑ y, pm1 f x * pm1 f y * (if x + y = 0 then (Fintype.card (Fin n → ZMod 2) : ℝ) else 0) :=
    Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
      congrArg (fun t => pm1 f x * pm1 f y * t) (hchi x y)))
  rw [Finset.sum_congr rfl (fun a _ => step1 a)]
  rw [step2, step3, collapse2]
  have hsq : ∀ x : Fin n → ZMod 2, pm1 f x * pm1 f x = 1 := fun x => sgn_sq (f x)
  rw [Finset.sum_congr rfl (fun x _ => hsq x)]
  have hsum1 : (∑ x : Fin n → ZMod 2, (1:ℝ)) = (Fintype.card (Fin n → ZMod 2) : ℝ) := by simp
  rw [hsum1, pow_two]

private theorem cubic (f : (Fin n → ZMod 2) → ZMod 2) :
    ∑ a, (∑ x, pm1 f x * chi a x)^3
      = (Fintype.card (Fin n → ZMod 2) : ℝ) * ∑ x, ∑ y, pm1 f x * pm1 f y * pm1 f (x + y) := by
  have step1 : ∀ a : Fin n → ZMod 2,
      (∑ x, pm1 f x * chi a x)^3
        = ∑ x, ∑ y, ∑ z, pm1 f x * pm1 f y * pm1 f z * (chi a x * chi a y * chi a z) := by
    intro a
    rw [pow_three, Finset.sum_mul_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hpush : ∀ j : Fin n → ZMod 2,
        (pm1 f x * chi a x) * (∑ k, (pm1 f j * chi a j) * (pm1 f k * chi a k))
        = ∑ k, ((pm1 f x * chi a x) * (pm1 f j * chi a j)) * (pm1 f k * chi a k) := by
      intro j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [Finset.sum_congr rfl (fun j _ => hpush j), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    ring
  have step2 : (∑ a, ∑ x, ∑ y, ∑ z, pm1 f x * pm1 f y * pm1 f z * (chi a x * chi a y * chi a z))
      = ∑ x, ∑ y, ∑ z, pm1 f x * pm1 f y * pm1 f z * (∑ a, chi a x * chi a y * chi a z) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [← Finset.mul_sum]
  have hchi : ∀ x y z : Fin n → ZMod 2, (∑ a, chi a x * chi a y * chi a z)
      = (if x + y + z = 0 then (Fintype.card (Fin n → ZMod 2) : ℝ) else 0) := by
    intro x y z
    have hper : ∀ a : Fin n → ZMod 2, chi a x * chi a y * chi a z = chi a (x + y + z) := by
      intro a
      rw [← chi_add_right a x y, ← chi_add_right a (x + y) z]
    calc (∑ a, chi a x * chi a y * chi a z) = ∑ a, chi a (x + y + z) :=
            Finset.sum_congr rfl (fun a _ => hper a)
      _ = _ := ortho _
  have step3 : (∑ x, ∑ y, ∑ z, pm1 f x * pm1 f y * pm1 f z * (∑ a, chi a x * chi a y * chi a z))
      = ∑ x, ∑ y, ∑ z, pm1 f x * pm1 f y * pm1 f z * (if x + y + z = 0 then (Fintype.card (Fin n → ZMod 2) : ℝ) else 0) :=
    Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ =>
      congrArg (fun t => pm1 f x * pm1 f y * pm1 f z * t) (hchi x y z))))
  rw [Finset.sum_congr rfl (fun a _ => step1 a)]
  rw [step2, step3, collapse3]

private theorem sum_avg {ι : Type*} (s : Finset ι) (h : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, (h i + c)/2) = ((∑ i ∈ s, h i) + s.card * c)/2 := by
  have hterm : ∀ i ∈ s, (h i + c)/2 = (h i)/2 + c/2 := by intros; ring
  have e1 : (∑ i ∈ s, (h i)/2) = (∑ i ∈ s, h i)/2 := by
    have hh : ∀ i ∈ s, (h i)/2 = (1/2) * h i := by intros; ring
    rw [Finset.sum_congr rfl hh, ← Finset.mul_sum]
    ring
  have e2 : (∑ i ∈ s, (c/2 : ℝ)) = s.card * c/2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, e1, e2]
  ring

private theorem count_disagree (f : (Fin n → ZMod 2) → ZMod 2) (a : Fin n → ZMod 2) :
    ((Finset.univ.filter (fun x => f x ≠ linFun a x)).card : ℝ)
      = ((Fintype.card (Fin n → ZMod 2) : ℝ) - ∑ x, pm1 f x * chi a x) / 2 := by
  have hper : ∀ x : Fin n → ZMod 2, pm1 f x * chi a x
      = (if f x = linFun a x then (1:ℝ) else -1) := by
    intro x
    have hsgn : pm1 f x * chi a x = sgn (f x + linFun a x) := by
      unfold pm1 chi
      exact (sgn_add _ _).symm
    rw [hsgn]
    by_cases hx : f x = linFun a x
    · rw [hx]
      simp only [↓reduceIte]
      have h2 : ∀ t : ZMod 2, t + t = 0 := by decide
      rw [h2 (linFun a x)]
      exact sgn_zero
    · simp only [hx, ↓reduceIte]
      have hne1 : ∀ u v : ZMod 2, u ≠ v → u + v = 1 := by decide
      rw [hne1 _ _ hx]
      exact sgn_one
  have hcard : ((Finset.univ.filter (fun x : Fin n → ZMod 2 => f x ≠ linFun a x)).card : ℝ)
      = ∑ x : Fin n → ZMod 2, (if f x ≠ linFun a x then (1:ℝ) else 0) := by
    rw [Finset.card_filter]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h <;> simp
  have hper2 : ∀ x : Fin n → ZMod 2, (if f x ≠ linFun a x then (1:ℝ) else 0)
      = (1 - (pm1 f x * chi a x))/2 := by
    intro x
    by_cases hx : f x = linFun a x
    · have h1 : (if f x ≠ linFun a x then (1:ℝ) else 0) = 0 := by simp [hx]
      have h2 : (if f x = linFun a x then (1:ℝ) else -1) = 1 := by simp [hx]
      rw [hper x, h1, h2]
      norm_num
    · have h1 : (if f x ≠ linFun a x then (1:ℝ) else 0) = 1 := ite_eq_left hx
      have h2 : (if f x = linFun a x then (1:ℝ) else -1) = -1 := ite_eq_right hx
      rw [hper x, h1, h2]
      norm_num
  rw [hcard, Finset.sum_congr rfl (fun x _ => hper2 x)]
  have hterm : ∀ x ∈ (Finset.univ : Finset (Fin n → ZMod 2)),
      (1 - pm1 f x * chi a x)/2 = ((-(pm1 f x * chi a x)) + 1)/2 := by intros; ring
  rw [Finset.sum_congr rfl hterm]
  rw [sum_avg]
  rw [Finset.sum_neg_distrib, Finset.card_univ]
  ring

private theorem count_accept (f : (Fin n → ZMod 2) → ZMod 2) :
    ((Finset.univ.filter (fun p : (Fin n → ZMod 2) × (Fin n → ZMod 2) =>
      f (p.1 + p.2) = f p.1 + f p.2)).card : ℝ)
      = ((Fintype.card ((Fin n → ZMod 2) × (Fin n → ZMod 2)) : ℝ)
        + ∑ x, ∑ y, pm1 f x * pm1 f y * pm1 f (x + y)) / 2 := by
  have hper : ∀ x y : Fin n → ZMod 2, pm1 f x * pm1 f y * pm1 f (x + y)
      = (if f (x + y) = f x + f y then (1:ℝ) else -1) := by
    intro x y
    have hsgn : pm1 f x * pm1 f y * pm1 f (x + y) = sgn (f x + f y + f (x + y)) := by
      unfold pm1
      rw [← sgn_add (f x) (f y), ← sgn_add (f x + f y) (f (x + y))]
    rw [hsgn]
    by_cases hxy : f (x + y) = f x + f y
    · rw [hxy]
      simp only [↓reduceIte]
      have h2 : ∀ u v : ZMod 2, u + v + (u + v) = 0 := by decide
      rw [h2]
      exact sgn_zero
    · simp only [hxy, ↓reduceIte]
      have hne : f x + f y + f (x + y) ≠ 0 := by
        intro hz
        apply hxy
        have hiff : ∀ u v w : ZMod 2, u + v + w = 0 → w = u + v := by decide
        exact hiff _ _ _ hz
      have h1 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
      rw [h1 _ hne]
      exact sgn_one
  have hcard : ((Finset.univ.filter (fun p : (Fin n → ZMod 2) × (Fin n → ZMod 2) =>
      f (p.1 + p.2) = f p.1 + f p.2)).card : ℝ)
      = ∑ p : (Fin n → ZMod 2) × (Fin n → ZMod 2),
        (if f (p.1 + p.2) = f p.1 + f p.2 then (1:ℝ) else 0) := by
    rw [Finset.card_filter]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs with h <;> simp
  have hper2 : ∀ x y : Fin n → ZMod 2,
      (if f (x + y) = f x + f y then (1:ℝ) else 0)
        = (pm1 f x * pm1 f y * pm1 f (x + y) + 1)/2 := by
    intro x y
    rw [hper x y]
    by_cases hxy : f (x + y) = f x + f y
    · have h1 : (if f (x + y) = f x + f y then (1:ℝ) else 0) = 1 := by simp [hxy]
      have h2 : (if f (x + y) = f x + f y then (1:ℝ) else -1) = 1 := by simp [hxy]
      rw [h1, h2]
      norm_num
    · have h1 : (if f (x + y) = f x + f y then (1:ℝ) else 0) = 0 := by simp [hxy]
      have h2 : (if f (x + y) = f x + f y then (1:ℝ) else -1) = -1 := by simp [hxy]
      rw [h1, h2]
      norm_num
  have hpair : (∑ p : (Fin n → ZMod 2) × (Fin n → ZMod 2),
      (if f (p.1 + p.2) = f p.1 + f p.2 then (1:ℝ) else 0))
      = ∑ x, ∑ y, (pm1 f x * pm1 f y * pm1 f (x + y) + 1)/2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hper2 x y
  rw [hcard, hpair]
  rw [Finset.sum_congr rfl (fun x _ =>
    sum_avg Finset.univ (fun y => pm1 f x * pm1 f y * pm1 f (x + y)) 1)]
  simp only [Finset.card_univ, mul_one]
  rw [sum_avg]
  rw [Finset.card_univ, Fintype.card_prod, Nat.cast_mul]
  ring

private theorem linFun_add (a x y : Fin n → ZMod 2) :
    linFun a (x + y) = linFun a x + linFun a y := by
  simp only [linFun_apply, dotProduct_add]

/-- Completeness: every linear function passes the BLR test
with probability `1`. -/
theorem blr_complete (a : Fin n → ZMod 2) :
    acceptProb (linFun a) = 1 := by
  unfold acceptProb blrAccepts
  rw [Finset.filter_true_of_mem (fun p _ => linFun_add a p.1 p.2)]
  rw [Finset.card_univ]
  exact div_self (Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos))

/-- Soundness (BLR): if `f` passes the linearity test with
probability at least `1 - ε`, then `f` is `ε`-close to some
linear function. -/
theorem blr_soundness (f : (Fin n → ZMod 2) → ZMod 2) (ε : ℝ)
    (hε : 0 ≤ ε) (h : 1 - ε ≤ acceptProb f) :
    ∃ a, disagreeProb f (linFun a) ≤ ε := by
  have hNpos : (0:ℝ) < (Fintype.card (Fin n → ZMod 2) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hN2pos : (0:ℝ) < (Fintype.card ((Fin n → ZMod 2) × (Fin n → ZMod 2)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have h2pos : (0:ℝ) < 2 := by norm_num
  obtain ⟨astar, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun a : Fin n → ZMod 2 => ∑ x, pm1 f x * chi a x) Finset.univ_nonempty
  have hcube_le : (∑ a, (∑ x, pm1 f x * chi a x)^3)
      ≤ (∑ x, pm1 f x * chi astar x) * (∑ a, (∑ x, pm1 f x * chi a x)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have h1 : (∑ x, pm1 f x * chi a x)^3
        = (∑ x, pm1 f x * chi a x) * (∑ x, pm1 f x * chi a x)^2 := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (hmax a ha) (sq_nonneg _)
  rw [parseval, cubic] at hcube_le
  have hSge : (∑ x, ∑ y, pm1 f x * pm1 f y * pm1 f (x + y))
      ≤ (Fintype.card (Fin n → ZMod 2) : ℝ) * (∑ x, pm1 f x * chi astar x) := by
    have h2 : (Fintype.card (Fin n → ZMod 2) : ℝ)
          * (∑ x, ∑ y, pm1 f x * pm1 f y * pm1 f (x + y))
        ≤ (Fintype.card (Fin n → ZMod 2) : ℝ)
          * ((Fintype.card (Fin n → ZMod 2) : ℝ) * (∑ x, pm1 f x * chi astar x)) := by
      calc (Fintype.card (Fin n → ZMod 2) : ℝ)
            * (∑ x, ∑ y, pm1 f x * pm1 f y * pm1 f (x + y))
          ≤ (∑ x, pm1 f x * chi astar x)
            * (Fintype.card (Fin n → ZMod 2) : ℝ)^2 := hcube_le
        _ = (Fintype.card (Fin n → ZMod 2) : ℝ)
            * ((Fintype.card (Fin n → ZMod 2) : ℝ) * (∑ x, pm1 f x * chi astar x)) := by ring
    exact (mul_le_mul_iff_of_pos_left hNpos).mp h2
  have hAcc := count_accept f
  have hDis := count_disagree f astar
  have hC : (Fintype.card ((Fin n → ZMod 2) × (Fin n → ZMod 2)) : ℝ)
      = (Fintype.card (Fin n → ZMod 2) : ℝ) * (Fintype.card (Fin n → ZMod 2) : ℝ) := by
    rw [Fintype.card_prod, Nat.cast_mul]
  unfold acceptProb blrAccepts at h
  rw [hAcc] at h
  have hle := (le_div_iff₀ hN2pos).mp h
  rw [hC] at hle
  have hTT : (((Fintype.card (Fin n → ZMod 2) : ℝ) * (Fintype.card (Fin n → ZMod 2) : ℝ))
        + (∑ x, ∑ y, pm1 f x * pm1 f y * pm1 f (x + y)))/2
      ≤ (((Fintype.card (Fin n → ZMod 2) : ℝ) * (Fintype.card (Fin n → ZMod 2) : ℝ))
        + (Fintype.card (Fin n → ZMod 2) : ℝ) * (∑ x, pm1 f x * chi astar x))/2 :=
    div_le_div_of_nonneg_right
      (add_le_add_right hSge ((Fintype.card (Fin n → ZMod 2) : ℝ) * (Fintype.card (Fin n → ZMod 2) : ℝ)))
      (le_of_lt h2pos)
  have h4 : (1 - ε) * ((Fintype.card (Fin n → ZMod 2) : ℝ) * (Fintype.card (Fin n → ZMod 2) : ℝ))
      ≤ (((Fintype.card (Fin n → ZMod 2) : ℝ) * (Fintype.card (Fin n → ZMod 2) : ℝ))
        + (Fintype.card (Fin n → ZMod 2) : ℝ) * (∑ x, pm1 f x * chi astar x))/2 :=
    le_trans hle hTT
  have h4' : (Fintype.card (Fin n → ZMod 2) : ℝ) * ((1 - ε) * (Fintype.card (Fin n → ZMod 2) : ℝ))
      ≤ (Fintype.card (Fin n → ZMod 2) : ℝ)
        * (((Fintype.card (Fin n → ZMod 2) : ℝ) + (∑ x, pm1 f x * chi astar x))/2) := by
    have e1 : (Fintype.card (Fin n → ZMod 2) : ℝ) * ((1 - ε) * (Fintype.card (Fin n → ZMod 2) : ℝ))
        = (1 - ε) * ((Fintype.card (Fin n → ZMod 2) : ℝ) * (Fintype.card (Fin n → ZMod 2) : ℝ)) := by ring
    have e2 : (Fintype.card (Fin n → ZMod 2) : ℝ)
          * (((Fintype.card (Fin n → ZMod 2) : ℝ) + (∑ x, pm1 f x * chi astar x))/2)
        = (((Fintype.card (Fin n → ZMod 2) : ℝ) * (Fintype.card (Fin n → ZMod 2) : ℝ))
          + (Fintype.card (Fin n → ZMod 2) : ℝ) * (∑ x, pm1 f x * chi astar x))/2 := by ring
    rw [e1, e2]
    exact h4
  have h5 : (1 - ε) * (Fintype.card (Fin n → ZMod 2) : ℝ)
      ≤ ((Fintype.card (Fin n → ZMod 2) : ℝ) + (∑ x, pm1 f x * chi astar x))/2 :=
    (mul_le_mul_iff_of_pos_left hNpos).mp h4'
  have h5b : 2 * ((1 - ε) * (Fintype.card (Fin n → ZMod 2) : ℝ))
      ≤ (Fintype.card (Fin n → ZMod 2) : ℝ) + (∑ x, pm1 f x * chi astar x) := by
    have h5c := (le_div_iff₀ h2pos).mp h5
    calc 2 * ((1 - ε) * (Fintype.card (Fin n → ZMod 2) : ℝ))
        = ((1 - ε) * (Fintype.card (Fin n → ZMod 2) : ℝ)) * 2 := by ring
      _ ≤ (Fintype.card (Fin n → ZMod 2) : ℝ) + (∑ x, pm1 f x * chi astar x) := h5c
  have h6 : (Fintype.card (Fin n → ZMod 2) : ℝ) - (∑ x, pm1 f x * chi astar x)
      ≤ 2 * (ε * (Fintype.card (Fin n → ZMod 2) : ℝ)) := by
    have key : (Fintype.card (Fin n → ZMod 2) : ℝ) - (∑ x, pm1 f x * chi astar x)
        = 2 * (Fintype.card (Fin n → ZMod 2) : ℝ)
          - ((Fintype.card (Fin n → ZMod 2) : ℝ) + (∑ x, pm1 f x * chi astar x)) := by ring
    have key2 : 2 * (ε * (Fintype.card (Fin n → ZMod 2) : ℝ))
        = 2 * (Fintype.card (Fin n → ZMod 2) : ℝ) - 2 * ((1 - ε) * (Fintype.card (Fin n → ZMod 2) : ℝ)) := by ring
    rw [key, key2]
    exact sub_le_sub_left h5b _
  refine ⟨astar, ?_⟩
  unfold disagreeProb
  rw [hDis]
  rw [div_le_iff₀ hNpos]
  calc (((Fintype.card (Fin n → ZMod 2) : ℝ) - (∑ x, pm1 f x * chi astar x))/2)
      ≤ (2 * (ε * (Fintype.card (Fin n → ZMod 2) : ℝ)))/2 :=
        div_le_div_of_nonneg_right h6 (le_of_lt h2pos)
    _ = ε * (Fintype.card (Fin n → ZMod 2) : ℝ) := by ring

end MathlibExt.Complexity.LinearityTest
