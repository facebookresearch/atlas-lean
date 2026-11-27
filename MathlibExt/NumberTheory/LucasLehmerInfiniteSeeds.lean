/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MersenneOmega
import Mathlib.Algebra.QuadraticAlgebra.Defs
import MathlibExt.NumberTheory.PellEulerSolutions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Infinitely many acceptable Lucas–Lehmer seeds

Euler's Pell orbit preserves the odd squarefree parts of `S − 2` and `S + 2`.
Taking powers in the kernel of reduction modulo the Mersenne number also preserves acceptability.
-/

namespace MetaMathlibExt

/-- Keep the original power of two and choose a positive square root for the square factor. -/
private theorem exists_pos_square_factor {N : ℤ} {k : ℕ} (hN : 0 < N)
    (hk : IsOddSquarefreePart N k) :
    ∃ e : ℕ, ∃ t : ℤ, 0 < t ∧ N = (2 ^ e * (k : ℤ)) * t ^ 2 := by
  obtain ⟨-, -, e, t, ht⟩ := hk
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    omega
  refine ⟨e, |t|, abs_pos.mpr ht0, ?_⟩
  rw [sq_abs, ht]
  ring

/-- A Pell solution has a positive period modulo any positive modulus, since its reduction
is a unit in a finite quadratic algebra. -/
private theorem pell_pow_modEq_one {d : ℤ} (ε : Pell.Solution₁ d) (m : ℕ) [NeZero m] :
    ∃ L : ℕ, 0 < L ∧ ∀ j : ℕ,
      (ε ^ (L * j)).x ≡ 1 [ZMOD (m : ℤ)] ∧ (ε ^ (L * j)).y ≡ 0 [ZMOD (m : ℤ)] := by
  let f : Pell.Solution₁ d →* QuadraticAlgebra (ZMod m) (d : ZMod m) 0 :=
    { toFun := fun z => ⟨z.x, z.y⟩
      map_one' := by simp
      map_mul' := fun x y => by
        apply QuadraticAlgebra.ext
        · simp [Pell.Solution₁.x_mul, mul_assoc]
        · simp [Pell.Solution₁.y_mul] }
  let _ : Finite (QuadraticAlgebra (ZMod m) (d : ZMod m) 0) :=
    Finite.of_injective _ (QuadraticAlgebra.equivProd (d : ZMod m) 0).injective
  obtain ⟨L, hL, hpow⟩ :=
    (isOfFinOrder_iff_isUnit.mpr ((Group.isUnit ε).map f)).exists_pow_eq_one
  refine ⟨L, hL, fun j => ?_⟩
  have h : f (ε ^ (L * j)) = 1 := by rw [map_pow, pow_mul, hpow, one_pow]
  have hx : ((ε ^ (L * j)).x : ZMod m) = 1 := congrArg QuadraticAlgebra.re h
  have hy : ((ε ^ (L * j)).y : ZMod m) = 0 := congrArg QuadraticAlgebra.im h
  exact ⟨(ZMod.intCast_eq_intCast_iff _ _ m).mp (by simpa only [Int.cast_one] using hx),
    (ZMod.intCast_eq_intCast_iff _ _ m).mp (by simpa only [Int.cast_zero] using hy)⟩

/-- Congruence of seeds persists under every Lucas–Lehmer iteration. -/
private theorem lucasLehmer_iterate_modEq {m s t : ℤ} (h : s ≡ t [ZMOD m]) (k : ℕ) :
    (fun x : ℤ => x ^ 2 - 2)^[k] s ≡ (fun x : ℤ => x ^ 2 - 2)^[k] t [ZMOD m] := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (ih.pow 2).sub (Int.ModEq.refl 2)

/-- **Infinitely many acceptable seeds with the same odd squarefree parts.** Let $n \ge 3$ be a
natural number and $M_n = 2^n - 1$. For an integer $S$ put $S_1 = S$ and $S_{k+1} = S_k^2 - 2$,
and call $S$ an acceptable seed for $M_n$ if $M_n$ is prime exactly when $M_n$ divides
$S_{n-1}$. Let $s_1 \ge 3$ be an integer that is an acceptable seed for $M_n$, and let $s_1^-$
and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and $s_1 + 2$. Then there are infinitely
many integers $S \ge 3$ that are acceptable seeds for $M_n$ and for which $s_1^-$ and $s_1^+$
are the odd squarefree parts of $S - 2$ and $S + 2$.

Seeds are taken $\ge 3$ (the paper's seeds are nonnegative, and the odd squarefree part of
$S - 2$ needs $S - 2 > 0$).

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 10. -/
public theorem infinite_acceptableSeeds_same_parts {n : ℕ} (h3 : 3 ≤ n) (s₁ : ℤ)
    (hs₁ : 3 ≤ s₁) (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm)
    (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (hacc : (mersenne n).Prime ↔
      (mersenne n : ℤ) ∣ (fun x : ℤ => x ^ 2 - 2)^[n - 2] s₁) :
    {S : ℤ | 3 ≤ S ∧ IsOddSquarefreePart (S - 2) sm ∧ IsOddSquarefreePart (S + 2) sp ∧
      ((mersenne n).Prime ↔ (mersenne n : ℤ) ∣ (fun x : ℤ => x ^ 2 - 2)^[n - 2] S)}.Infinite := by
  obtain ⟨ep, T₁, hT₁, hplus⟩ := exists_pos_square_factor (by omega) hsp
  obtain ⟨em, U₁, hU₁, hminus⟩ := exists_pos_square_factor (by omega) hsm
  let a : ℤ := 2 ^ ep * sp
  let b : ℤ := 2 ^ em * sm
  change s₁ + 2 = a * T₁ ^ 2 at hplus
  change s₁ - 2 = b * U₁ ^ 2 at hminus
  have ha : 0 < a := mul_pos (pow_pos (by decide) _) (by exact_mod_cast hsp.1.pos)
  have hb : 0 < b := mul_pos (pow_pos (by decide) _) (by exact_mod_cast hsm.1.pos)
  have hstart : a * T₁ ^ 2 - b * U₁ ^ 2 = 4 := by linarith
  -- A square discriminant would make `s₁² - 4` a square between consecutive squares.
  have hsq : ¬ IsSquare (a * b) := by
    rintro ⟨r, hr⟩
    have hprod : (r * T₁ * U₁) ^ 2 = s₁ ^ 2 - 4 := calc
      _ = (a * b) * T₁ ^ 2 * U₁ ^ 2 := by rw [hr]; ring
      _ = (a * T₁ ^ 2) * (b * U₁ ^ 2) := by ring
      _ = s₁ ^ 2 - 4 := by rw [← hplus, ← hminus]; ring
    have hlo : (s₁ - 1) ^ 2 < (r * T₁ * U₁) ^ 2 := by rw [hprod]; nlinarith
    have hhi : (r * T₁ * U₁) ^ 2 < s₁ ^ 2 := by rw [hprod]; omega
    have hlo' := sq_lt_sq.mp hlo
    have hhi' := sq_lt_sq.mp hhi
    rw [abs_of_nonneg (show 0 ≤ s₁ - 1 by omega)] at hlo'
    rw [abs_of_nonneg (show 0 ≤ s₁ by omega)] at hhi'
    omega
  have hab : 1 < a * b := by
    have hpos := mul_pos ha hb
    by_contra! h
    have hab : a * b = 1 := by omega
    exact hsq ⟨1, by simp [hab]⟩
  obtain ⟨ε, hε⟩ := Pell.IsFundamental.exists_of_not_isSquare (by omega) hsq
  obtain ⟨hsol, hinj⟩ := pell_euler_solutions a b 4 T₁ U₁ hab hsq (by decide) hstart ε hε
  let _ : NeZero (mersenne n) := ⟨(mersenne_pos.mpr (by omega)).ne'⟩
  obtain ⟨L, hL, hperiod⟩ := pell_pow_modEq_one ε (mersenne n)
  let T (j : ℕ) : ℤ := T₁ * (ε ^ (L * j)).x + b * U₁ * (ε ^ (L * j)).y
  let U (j : ℕ) : ℤ := a * T₁ * (ε ^ (L * j)).y + U₁ * (ε ^ (L * j)).x
  let S (j : ℕ) : ℤ := b * U j ^ 2 + 2
  have hTU (j : ℕ) : a * T j ^ 2 - b * U j ^ 2 = 4 := hsol (L * j)
  have hx (k : ℕ) : 0 < (ε ^ k).x := Pell.Solution₁.x_pow_pos hε.x_pos k
  have hy (k : ℕ) : 0 ≤ (ε ^ k).y := by
    cases k with
    | zero => simp
    | succ k => exact (Pell.Solution₁.y_pow_succ_pos hε.x_pos hε.2.1 k).le
  have hT (j : ℕ) : 0 < T j :=
    add_pos_of_pos_of_nonneg (mul_pos hT₁ (hx _)) (mul_nonneg (mul_pos hb hU₁).le (hy _))
  have hU (j : ℕ) : 0 < U j :=
    add_pos_of_nonneg_of_pos (mul_nonneg (mul_pos ha hT₁).le (hy _)) (mul_pos hU₁ (hx _))
  refine Set.infinite_of_injective_forall_mem (f := S) ?_ ?_
  · intro i j hij
    have hUij : b * U i ^ 2 = b * U j ^ 2 := add_right_cancel hij
    have hTij : a * T i ^ 2 = a * T j ^ 2 := by linarith [hTU i, hTU j]
    have hT' := (pow_left_inj₀ (hT i).le (hT j).le (by decide : 2 ≠ 0)).mp
      (mul_left_cancel₀ ha.ne' hTij)
    have hU' := (pow_left_inj₀ (hU i).le (hU j).le (by decide : 2 ≠ 0)).mp
      (mul_left_cancel₀ hb.ne' hUij)
    exact Nat.eq_of_mul_eq_mul_left hL (hinj (Prod.ext hT' hU'))
  · intro j
    have hSminus : S j - 2 = b * U j ^ 2 := by dsimp [S]; ring
    have hSplus : S j + 2 = a * T j ^ 2 := by dsimp [S]; linarith [hTU j]
    have hSpos : 3 ≤ S j := by
      have := mul_pos hb (pow_pos (hU j) 2)
      dsimp [S]
      omega
    have hUmod : U j ≡ U₁ [ZMOD (mersenne n : ℤ)] := by
      obtain ⟨hjx, hjy⟩ := hperiod j
      simpa [U] using (((Int.ModEq.refl (a * T₁)).mul hjy).add ((Int.ModEq.refl U₁).mul hjx))
    have hSmod : S j ≡ s₁ [ZMOD (mersenne n : ℤ)] := by
      have hs : s₁ = b * U₁ ^ 2 + 2 := by linarith
      rw [hs]
      exact ((Int.ModEq.refl b).mul (hUmod.pow 2)).add (Int.ModEq.refl 2)
    refine ⟨hSpos, ⟨hsm.1, hsm.2.1, em, U j, ?_⟩, ⟨hsp.1, hsp.2.1, ep, T j, ?_⟩,
      hacc.trans (lucasLehmer_iterate_modEq hSmod (n - 2)).dvd_iff.symm⟩
    · rw [hSminus]; dsimp [b]; ring
    · rw [hSplus]; dsimp [a]; ring

end MetaMathlibExt
